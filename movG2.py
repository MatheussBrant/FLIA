import sys
import subprocess
import re
from collections import defaultdict
import os

PLANNER_MADAGASCAR = "/home/software/planners/madagascar/M"
PLANNER_FDSS23 = "/home/software/planners/downward-fdss23/fast-downward.py"
PLANNER_SCORPION = "/home/software/planners/scorpion-maidu/fast-downward.py"
PLANNER_JULIA = "/home/software/planners/julia/planner.jl"
PLANNER_FDSS23MINHA = "/home/matheus-brant/Desktop/downward-fdss23/fast-downward.py"

class EnhancedGameMap:
    def __init__(self, lines):
        self.grid = [list(line.rstrip("\n")) for line in lines if line.strip() != ""]
        self.height = len(self.grid)
        self.width = len(self.grid[0]) if self.height > 0 else 0

        self.pacman_pos = None    # (x, y) onde 'P' aparece
        self.ghosts = []          # Lista de tuplas (x, y, símbolo) para fantasmas ('R','G','B')
        self.fruits = []          # Lista de tuplas (x, y, símbolo) para frutas ('!', '@', '$')
        self.cells = []           # Lista de coordenadas (x,y) de células que não são paredes

        for y in range(self.height):
            for x in range(self.width):
                char = self.grid[y][x]
                if char != '#':
                    self.cells.append((x, y))
                if char == 'P':
                    self.pacman_pos = (x, y)
                elif char in ('R', 'G', 'B'):
                    self.ghosts.append((x, y, char))
                elif char in ('!', '@', '$'):
                    self.fruits.append((x, y, char))

    def get_neighbor(self, x, y, direction):
        """Retorna a célula vizinha em 'direction' se estiver dentro dos limites e não for parede."""
        if direction == 'north':
            nx, ny = x, y - 1
        elif direction == 'south':
            nx, ny = x, y + 1
        elif direction == 'east':
            nx, ny = x + 1, y
        elif direction == 'west':
            nx, ny = x - 1, y
        else:
            return None
        if 0 <= nx < self.width and 0 <= ny < self.height and self.grid[ny][nx] != '#':
            return (nx, ny)
        else:
            return None

def generate_pddl(game_map):
    # Domínio com as alterações para incluir o predicado ghosts-pending e a modelagem de colisão.
    domain_str = """(define (domain pacman-agile)
  (:requirements :typing :negative-preconditions :conditional-effects :adl :action-costs)
  (:types cell ghost fruit)
  (:predicates
    (at-pacman ?c - cell)
    (ghost-at ?g - ghost ?c - cell)
    (ghost-type ?g - ghost ?f - fruit)
    (ghost-alive ?g - ghost)
    (fruit-at ?f - fruit ?c - cell)
    (active-fruit ?f - fruit)
    (connected-north ?from ?to - cell)
    (connected-south ?from ?to - cell)
    (connected-east ?from ?to - cell)
    (connected-west ?from ?to - cell)
    ;; Flags para o último movimento do Pac-Man
    (last-move-north)
    (last-move-south)
    (last-move-east)
    (last-move-west)
    (ghosts-pending) ;; Indica que os fantasmas ainda não se moveram após o último movimento do Pac-Man
  )
  (:functions (total-cost) - number)
  
  ;; Ação move-north: move o Pac-Man e marca que os fantasmas precisam se mover.
  (:action move-north
    :parameters (?from - cell ?to - cell)
    :precondition (and 
         (at-pacman ?from)
         (not (ghosts-pending))
         (connected-north ?from ?to)
         ;; Verifica que não há fantasma já na célula destino.
         (not (exists (?g - ghost)
                    (and (ghost-at ?g ?to)
                         (ghost-alive ?g)
                         (not (exists (?f - fruit)
                                     (and (active-fruit ?f) (ghost-type ?g ?f))))))
         )
         ;; NOVO: Verifica que não há fantasma em célula adjacente que se moveria para ?to na ghost-turn.
         (not (exists (?g - ghost ?x - cell)
                    (and (ghost-alive ?g)
                         (ghost-at ?g ?x)
                         (or 
                           (and (ghost-type ?g blue-fruit) (connected-south ?x ?to))
                           (and (ghost-type ?g green-fruit) (connected-north ?x ?to))
                         )
                         (not (exists (?f - fruit)
                                     (and (active-fruit ?f) (ghost-type ?g ?f))))
                    )
         ))
    )
    :effect (and 
         (not (at-pacman ?from))
         (at-pacman ?to)
         (forall (?g - ghost)
             (when (and (ghost-alive ?g) (ghost-at ?g ?to)
                        (exists (?f - fruit)
                                (and (active-fruit ?f) (ghost-type ?g ?f))))
                   (not (ghost-alive ?g))
             )
         )
         (not (last-move-south))
         (not (last-move-east))
         (not (last-move-west))
         (last-move-north)
         (increase (total-cost) 1)
         (ghosts-pending)  ;; Indica que os fantasmas ainda não se moveram
    )
  )
  
  ;; Ação move-south: similar, mas seta last-move-south.
  (:action move-south
    :parameters (?from - cell ?to - cell)
    :precondition (and 
         (at-pacman ?from)
         (not (ghosts-pending))
         (connected-south ?from ?to)
         (not (exists (?g - ghost)
                    (and (ghost-at ?g ?to)
                         (ghost-alive ?g)
                         (not (exists (?f - fruit)
                                     (and (active-fruit ?f) (ghost-type ?g ?f))))))
         )
         (not (exists (?g - ghost ?x - cell)
                    (and (ghost-alive ?g)
                         (ghost-at ?g ?x)
                         (or 
                           (and (ghost-type ?g blue-fruit) (connected-north ?x ?to))
                           (and (ghost-type ?g green-fruit) (connected-south ?x ?to))
                         )
                         (not (exists (?f - fruit)
                                     (and (active-fruit ?f) (ghost-type ?g ?f))))
                    )
         ))
    )
    :effect (and 
         (not (at-pacman ?from))
         (at-pacman ?to)
         (forall (?g - ghost)
             (when (and (ghost-alive ?g) (ghost-at ?g ?to)
                        (exists (?f - fruit)
                                (and (active-fruit ?f) (ghost-type ?g ?f))))
                   (not (ghost-alive ?g))
             )
         )
         (not (last-move-north))
         (not (last-move-east))
         (not (last-move-west))
         (last-move-south)
         (increase (total-cost) 1)
         (ghosts-pending)
    )
  )
  
  ;; Ação move-east: seta last-move-east.
  (:action move-east
    :parameters (?from - cell ?to - cell)
    :precondition (and 
         (at-pacman ?from)
         (not (ghosts-pending))
         (connected-east ?from ?to)
         (not (exists (?g - ghost)
                    (and (ghost-at ?g ?to)
                         (ghost-alive ?g)
                         (not (exists (?f - fruit)
                                     (and (active-fruit ?f) (ghost-type ?g ?f))))))
         )
         (not (exists (?g - ghost ?x - cell)
                    (and (ghost-alive ?g)
                         (ghost-at ?g ?x)
                         (or 
                           (and (ghost-type ?g blue-fruit) (connected-west ?x ?to))
                           (and (ghost-type ?g green-fruit) (connected-east ?x ?to))
                         )
                         (not (exists (?f - fruit)
                                     (and (active-fruit ?f) (ghost-type ?g ?f))))
                    )
         ))
    )
    :effect (and 
         (not (at-pacman ?from))
         (at-pacman ?to)
         (forall (?g - ghost)
             (when (and (ghost-alive ?g) (ghost-at ?g ?to)
                        (exists (?f - fruit)
                                (and (active-fruit ?f) (ghost-type ?g ?f))))
                   (not (ghost-alive ?g))
             )
         )
         (not (last-move-north))
         (not (last-move-south))
         (not (last-move-west))
         (last-move-east)
         (increase (total-cost) 1)
         (ghosts-pending)
    )
  )
  
  ;; Ação move-west: seta last-move-west.
  (:action move-west
    :parameters (?from - cell ?to - cell)
    :precondition (and 
         (at-pacman ?from)
         (not (ghosts-pending))
         (connected-west ?from ?to)
         (not (exists (?g - ghost)
                    (and (ghost-at ?g ?to)
                         (ghost-alive ?g)
                         (not (exists (?f - fruit)
                                     (and (active-fruit ?f) (ghost-type ?g ?f))))))
         )
         (not (exists (?g - ghost ?x - cell)
                    (and (ghost-alive ?g)
                         (ghost-at ?g ?x)
                         (or 
                           (and (ghost-type ?g blue-fruit) (connected-east ?x ?to))
                           (and (ghost-type ?g green-fruit) (connected-west ?x ?to))
                         )
                         (not (exists (?f - fruit)
                                     (and (active-fruit ?f) (ghost-type ?g ?f))))
                    )
         ))
    )
    :effect (and 
         (not (at-pacman ?from))
         (at-pacman ?to)
         (forall (?g - ghost)
             (when (and (ghost-alive ?g) (ghost-at ?g ?to)
                        (exists (?f - fruit)
                                (and (active-fruit ?f) (ghost-type ?g ?f))))
                   (not (ghost-alive ?g))
             )
         )
         (not (last-move-north))
         (not (last-move-south))
         (not (last-move-east))
         (last-move-west)
         (increase (total-cost) 1)
         (ghosts-pending)
    )
  )
  
  ;; Ação ghost-turn: movimenta os fantasmas e remove a marca de pendência.
  (:action ghost-turn
    :parameters ()
    :precondition (and 
         (ghosts-pending)
         (or (last-move-north) (last-move-south) (last-move-east) (last-move-west))
    )
    :effect (and
         ;; Para fantasmas azuis: movem-se na direção oposta ao movimento do Pac-Man.
         (forall (?g - ghost ?from - cell ?to - cell)
             (when (and (ghost-alive ?g)
                        (ghost-type ?g blue-fruit)
                        (ghost-at ?g ?from)
                        (last-move-north)
                        (connected-south ?from ?to))
                   (and (not (ghost-at ?g ?from))
                        (ghost-at ?g ?to))
             )
         )
         (forall (?g - ghost ?from - cell ?to - cell)
             (when (and (ghost-alive ?g)
                        (ghost-type ?g blue-fruit)
                        (ghost-at ?g ?from)
                        (last-move-south)
                        (connected-north ?from ?to))
                   (and (not (ghost-at ?g ?from))
                        (ghost-at ?g ?to))
             )
         )
         (forall (?g - ghost ?from - cell ?to - cell)
             (when (and (ghost-alive ?g)
                        (ghost-type ?g blue-fruit)
                        (ghost-at ?g ?from)
                        (last-move-east)
                        (connected-west ?from ?to))
                   (and (not (ghost-at ?g ?from))
                        (ghost-at ?g ?to))
             )
         )
         (forall (?g - ghost ?from - cell ?to - cell)
             (when (and (ghost-alive ?g)
                        (ghost-type ?g blue-fruit)
                        (ghost-at ?g ?from)
                        (last-move-west)
                        (connected-east ?from ?to))
                   (and (not (ghost-at ?g ?from))
                        (ghost-at ?g ?to))
             )
         )
         ;; Para fantasmas verdes: imitam o movimento do Pac-Man.
         (forall (?g - ghost ?from - cell ?to - cell)
             (when (and (ghost-alive ?g)
                        (ghost-type ?g green-fruit)
                        (ghost-at ?g ?from)
                        (last-move-north)
                        (connected-north ?from ?to))
                   (and (not (ghost-at ?g ?from))
                        (ghost-at ?g ?to))
             )
         )
         (forall (?g - ghost ?from - cell ?to - cell)
             (when (and (ghost-alive ?g)
                        (ghost-type ?g green-fruit)
                        (ghost-at ?g ?from)
                        (last-move-south)
                        (connected-south ?from ?to))
                   (and (not (ghost-at ?g ?from))
                        (ghost-at ?g ?to))
             )
         )
         (forall (?g - ghost ?from - cell ?to - cell)
             (when (and (ghost-alive ?g)
                        (ghost-type ?g green-fruit)
                        (ghost-at ?g ?from)
                        (last-move-east)
                        (connected-east ?from ?to))
                   (and (not (ghost-at ?g ?from))
                        (ghost-at ?g ?to))
             )
         )
         (forall (?g - ghost ?from - cell ?to - cell)
             (when (and (ghost-alive ?g)
                        (ghost-type ?g green-fruit)
                        (ghost-at ?g ?from)
                        (last-move-west)
                        (connected-west ?from ?to))
                   (and (not (ghost-at ?g ?from))
                        (ghost-at ?g ?to))
             )
         )
         ;; Limpa todas as flags de movimento e a marca de pendência dos fantasmas.
         (not (last-move-north))
         (not (last-move-south))
         (not (last-move-east))
         (not (last-move-west))
         (not (ghosts-pending))
    )
  )
  
  ;; Ações de comer fruta permanecem inalteradas.
  (:action eat-fruit-red
    :parameters (?c - cell)
    :precondition (and (at-pacman ?c) (fruit-at red-fruit ?c))
    :effect (and 
         (active-fruit red-fruit)
         (not (fruit-at red-fruit ?c))
         (forall (?f - fruit)
             (when (not (= ?f red-fruit))
                   (not (active-fruit ?f))
             )
         )
         (increase (total-cost) 2)
    )
  )
  
  (:action eat-fruit-green
    :parameters (?c - cell)
    :precondition (and (at-pacman ?c) (fruit-at green-fruit ?c))
    :effect (and 
         (active-fruit green-fruit)
         (not (fruit-at green-fruit ?c))
         (forall (?f - fruit)
             (when (not (= ?f green-fruit))
                   (not (active-fruit ?f))
             )
         )
         (increase (total-cost) 2)
    )
  )
  
  (:action eat-fruit-blue
    :parameters (?c - cell)
    :precondition (and (at-pacman ?c) (fruit-at blue-fruit ?c))
    :effect (and 
         (active-fruit blue-fruit)
         (not (fruit-at blue-fruit ?c))
         (forall (?f - fruit)
             (when (not (= ?f blue-fruit))
                   (not (active-fruit ?f))
             )
         )
         (increase (total-cost) 2)
    )
  )
)"""

    # Geração dos objetos e fatos para o problema:
    cell_names = {}
    cell_list = []
    counter = 1
    for coord in game_map.cells:
        name = f"c{counter}"
        cell_names[coord] = name
        cell_list.append(name)
        counter += 1

    # Gerar fatos de conectividade para cada direção.
    connections = []
    directions = {
        'north': (0, -1, 'connected-north'),
        'south': (0, 1, 'connected-south'),
        'east': (1, 0, 'connected-east'),
        'west': (-1, 0, 'connected-west')
    }
    for (x, y) in game_map.cells:
        for d, (dx, dy, pred) in directions.items():
            nx, ny = x + dx, y + dy
            if (nx, ny) in cell_names:
                connections.append(f"({pred} {cell_names[(x,y)]} {cell_names[(nx,ny)]})")

    ghost_names = []
    ghost_inits = []
    for i, (x, y, symbol) in enumerate(game_map.ghosts):
        gname = f"ghost{i+1}"
        ghost_names.append(gname)
        if symbol == 'R':
            ghost_fruit = "red-fruit"
        elif symbol == 'G':
            ghost_fruit = "green-fruit"
        elif symbol == 'B':
            ghost_fruit = "blue-fruit"
        else:
            ghost_fruit = "red-fruit"
        ghost_inits.append(f"(ghost-at {gname} {cell_names[(x,y)]})")
        ghost_inits.append(f"(ghost-type {gname} {ghost_fruit})")
        ghost_inits.append(f"(ghost-alive {gname})")

    fruit_inits = []
    for (x, y, symbol) in game_map.fruits:
        if symbol == '!':
            fruit_inits.append(f"(fruit-at red-fruit {cell_names[(x,y)]})")
        elif symbol == '@':
            fruit_inits.append(f"(fruit-at green-fruit {cell_names[(x,y)]})")
        elif symbol == '$':
            fruit_inits.append(f"(fruit-at blue-fruit {cell_names[(x,y)]})")

    pacman_init = f"(at-pacman {cell_names[game_map.pacman_pos]})"
    ghost_goals = [f"(not (ghost-alive {g}))" for g in ghost_names]

    problem_str = f"""(define (problem mapa-agile)
  (:domain pacman-agile)
  (:objects
    {" ".join(cell_list)} - cell
    {" ".join(ghost_names)} - ghost
    red-fruit green-fruit blue-fruit - fruit
  )
  (:init
    {pacman_init}
    {" ".join(connections)}
    {" ".join(fruit_inits)}
    {" ".join(ghost_inits)}
    (= (total-cost) 0)
  )
  (:goal (and {" ".join(ghost_goals)}))
  (:metric minimize (total-cost))
)
"""
    return domain_str, problem_str

def extract_moves(planner_output, cell_coords):
    moves = []
    pattern = r"^move\s+(\S+)\s+(\S+)\s+(\S+)"
    for line in planner_output.splitlines():
        line = line.strip()
        m = re.match(pattern, line, re.IGNORECASE)
        if m:
            d = m.group(3).upper()
            if d == "NORTH":
                moves.append("N")
            elif d == "SOUTH":
                moves.append("S")
            elif d == "EAST":
                moves.append("E")
            elif d == "WEST":
                moves.append("W")
    return ";".join(moves) + ";0"

def chamar_planejador():
    comando = [
        PLANNER_FDSS23,
        "--search-time-limit", "60",
        "--alias", "lama-first",
        "domain.pddl",
        "problem.pddl"
    ]
    result = subprocess.run(comando, capture_output=True, text=True)
    if result.returncode != 0:
        print("Erro ao executar Fast Downward:", file=sys.stderr)
        print(result.stderr, file=sys.stderr)
        sys.exit(result.returncode)
    return result.stdout

def extract_moves(planner_output):
    moves = []
    # O padrão agora captura linhas que iniciam com "move-<direção>"
    pattern = r"^move-(north|south|east|west)\s+\S+\s+\S+"
    for line in planner_output.splitlines():
        line = line.strip()
        m = re.match(pattern, line, re.IGNORECASE)
        if m:
            direcao = m.group(1).lower()
            if direcao == "north":
                moves.append("N")
            elif direcao == "south":
                moves.append("S")
            elif direcao == "east":
                moves.append("E")
            elif direcao == "west":
                moves.append("W")
    return ";".join(moves) + ";0"

def main():
    lines = [line.rstrip('\n') for line in sys.stdin]
    game_map = EnhancedGameMap(lines)
    domain, problem = generate_pddl(game_map)
    
    with open("domain.pddl", "w") as f:
        f.write(domain)
    with open("problem.pddl", "w") as f:
        f.write(problem)

    print("----- Conteúdo do domain.pddl -----")
    print(domain)
    print("----- Conteúdo do problem.pddl -----")
    print(problem)
    
    output = chamar_planejador()
    print("Saída completa do planejador:")
    print(output)
    
    movimentos = extract_moves(output)
    print(movimentos)

if __name__ == "__main__":
    main()

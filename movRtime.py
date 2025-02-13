import sys
import subprocess
import re
from collections import defaultdict
import os

PLANNER_MADAGASCAR = "/home/software/planners/madagascar/M"
PLANNER_FDSS23 = "/home/software/planners/downward-fdss23/fast-downward.py"
PLANNER_SCORPION = "/home/software/planners/scorpion-maidu/fast-downward.py"
PLANNER_JULIA = "/home/software/planners/julia/planner.jl"

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
    (red-next ?from - cell ?to - cell)
  )
  (:functions (total-cost) - number)
  
  ;; Ação move-north
  (:action move-north
    :parameters (?from - cell ?to - cell)
    :precondition (and 
         (at-pacman ?from)
         (connected-north ?from ?to)
         (not (exists (?g - ghost)
                    (and (ghost-at ?g ?to)
                         (ghost-alive ?g)
                         (not (exists (?f - fruit)
                                     (and (active-fruit ?f) (ghost-type ?g ?f))))))
         )
    )
    :effect (and 
         ;; Movimento do Pac-Man
         (not (at-pacman ?from))
         (at-pacman ?to)
         
         ;; Eliminação de fantasmas se aplicável
         (forall (?g - ghost)
             (when (and (ghost-alive ?g) (ghost-at ?g ?to)
                        (exists (?f - fruit)
                                (and (active-fruit ?f) (ghost-type ?g ?f))))
                   (not (ghost-alive ?g))
             )
         )
         
         ;; Movimento do fantasma azul: para move-north ele se desloca para o sul.
         (forall (?g - ghost ?gb_from - cell ?gb_to - cell)
             (when (and (ghost-alive ?g)
                        (ghost-type ?g blue-fruit)
                        (ghost-at ?g ?gb_from)
                        (connected-south ?gb_from ?gb_to))
                   (and 
                     (not (ghost-at ?g ?gb_from))
                     (ghost-at ?g ?gb_to)
                   )
             )
         )
         
         ;; Movimento do fantasma verde: para move-north ele se desloca para o norte.
         (forall (?g - ghost ?gb_from - cell ?gb_to - cell)
             (when (and (ghost-alive ?g)
                        (ghost-type ?g green-fruit)
                        (ghost-at ?g ?gb_from)
                        (connected-north ?gb_from ?gb_to))
                   (and 
                     (not (ghost-at ?g ?gb_from))
                     (ghost-at ?g ?gb_to)
                   )
             )
         )
         
         ;; Movimento do fantasma vermelho: segue o movimento pré-computado.
         (forall (?g - ghost ?rg_from - cell ?rg_to - cell)
             (when (and (ghost-alive ?g)
                        (ghost-type ?g red-fruit)
                        (ghost-at ?g ?rg_from)
                        (red-next ?rg_from ?rg_to))
                   (and 
                     (not (ghost-at ?g ?rg_from))
                     (ghost-at ?g ?rg_to)
                   )
             )
         )
         
         (increase (total-cost) 1)
    )
  )
  
  ;; Ação move-south
  (:action move-south
    :parameters (?from - cell ?to - cell)
    :precondition (and 
         (at-pacman ?from)
         (connected-south ?from ?to)
         (not (exists (?g - ghost)
                    (and (ghost-at ?g ?to)
                         (ghost-alive ?g)
                         (not (exists (?f - fruit)
                                     (and (active-fruit ?f) (ghost-type ?g ?f))))))
         )
    )
    :effect (and 
         ;; Movimento do Pac-Man
         (not (at-pacman ?from))
         (at-pacman ?to)
         
         ;; Eliminação de fantasmas se aplicável
         (forall (?g - ghost)
             (when (and (ghost-alive ?g) (ghost-at ?g ?to)
                        (exists (?f - fruit)
                                (and (active-fruit ?f) (ghost-type ?g ?f))))
                   (not (ghost-alive ?g))
             )
         )
         
         ;; Movimento do fantasma azul: para move-south o azul se move para o norte.
         (forall (?g - ghost ?gb_from - cell ?gb_to - cell)
             (when (and (ghost-alive ?g)
                        (ghost-type ?g blue-fruit)
                        (ghost-at ?g ?gb_from)
                        (connected-north ?gb_from ?gb_to))
                   (and 
                     (not (ghost-at ?g ?gb_from))
                     (ghost-at ?g ?gb_to)
                   )
             )
         )
         
         ;; Movimento do fantasma verde: para move-south ele se desloca para o sul.
         (forall (?g - ghost ?gb_from - cell ?gb_to - cell)
             (when (and (ghost-alive ?g)
                        (ghost-type ?g green-fruit)
                        (ghost-at ?g ?gb_from)
                        (connected-south ?gb_from ?gb_to))
                   (and 
                     (not (ghost-at ?g ?gb_from))
                     (ghost-at ?g ?gb_to)
                   )
             )
         )
         
         ;; Movimento do fantasma vermelho: segue o movimento pré-computado.
         (forall (?g - ghost ?rg_from - cell ?rg_to - cell)
             (when (and (ghost-alive ?g)
                        (ghost-type ?g red-fruit)
                        (ghost-at ?g ?rg_from)
                        (red-next ?rg_from ?rg_to))
                   (and 
                     (not (ghost-at ?g ?rg_from))
                     (ghost-at ?g ?rg_to)
                   )
             )
         )
         
         (increase (total-cost) 1)
    )
  )
  
  ;; Ação move-east
  (:action move-east
    :parameters (?from - cell ?to - cell)
    :precondition (and 
         (at-pacman ?from)
         (connected-east ?from ?to)
         (not (exists (?g - ghost)
                    (and (ghost-at ?g ?to)
                         (ghost-alive ?g)
                         (not (exists (?f - fruit)
                                     (and (active-fruit ?f) (ghost-type ?g ?f))))))
         )
    )
    :effect (and 
         ;; Movimento do Pac-Man
         (not (at-pacman ?from))
         (at-pacman ?to)
         
         ;; Eliminação de fantasmas se aplicável
         (forall (?g - ghost)
             (when (and (ghost-alive ?g) (ghost-at ?g ?to)
                        (exists (?f - fruit)
                                (and (active-fruit ?f) (ghost-type ?g ?f))))
                   (not (ghost-alive ?g))
             )
         )
         
         ;; Movimento do fantasma azul: para move-east o azul se move para o oeste.
         (forall (?g - ghost ?gb_from - cell ?gb_to - cell)
             (when (and (ghost-alive ?g)
                        (ghost-type ?g blue-fruit)
                        (ghost-at ?g ?gb_from)
                        (connected-west ?gb_from ?gb_to))
                   (and 
                     (not (ghost-at ?g ?gb_from))
                     (ghost-at ?g ?gb_to)
                   )
             )
         )
         
         ;; Movimento do fantasma verde: para move-east ele se desloca para o leste.
         (forall (?g - ghost ?gb_from - cell ?gb_to - cell)
             (when (and (ghost-alive ?g)
                        (ghost-type ?g green-fruit)
                        (ghost-at ?g ?gb_from)
                        (connected-east ?gb_from ?gb_to))
                   (and 
                     (not (ghost-at ?g ?gb_from))
                     (ghost-at ?g ?gb_to)
                   )
             )
         )
         
         ;; Movimento do fantasma vermelho: segue o movimento pré-computado.
         (forall (?g - ghost ?rg_from - cell ?rg_to - cell)
             (when (and (ghost-alive ?g)
                        (ghost-type ?g red-fruit)
                        (ghost-at ?g ?rg_from)
                        (red-next ?rg_from ?rg_to))
                   (and 
                     (not (ghost-at ?g ?rg_from))
                     (ghost-at ?g ?rg_to)
                   )
             )
         )
         
         (increase (total-cost) 1)
    )
  )
  
  ;; Ação move-west
  (:action move-west
    :parameters (?from - cell ?to - cell)
    :precondition (and 
         (at-pacman ?from)
         (connected-west ?from ?to)
         (not (exists (?g - ghost)
                    (and (ghost-at ?g ?to)
                         (ghost-alive ?g)
                         (not (exists (?f - fruit)
                                     (and (active-fruit ?f) (ghost-type ?g ?f))))))
         )
    )
    :effect (and 
         ;; Movimento do Pac-Man
         (not (at-pacman ?from))
         (at-pacman ?to)
         
         ;; Eliminação de fantasmas se aplicável
         (forall (?g - ghost)
             (when (and (ghost-alive ?g) (ghost-at ?g ?to)
                        (exists (?f - fruit)
                                (and (active-fruit ?f) (ghost-type ?g ?f))))
                   (not (ghost-alive ?g))
             )
         )
         
         ;; Movimento do fantasma azul: para move-west o azul se move para o leste.
         (forall (?g - ghost ?gb_from - cell ?gb_to - cell)
             (when (and (ghost-alive ?g)
                        (ghost-type ?g blue-fruit)
                        (ghost-at ?g ?gb_from)
                        (connected-east ?gb_from ?gb_to))
                   (and 
                     (not (ghost-at ?g ?gb_from))
                     (ghost-at ?g ?gb_to)
                   )
             )
         )
         
         ;; Movimento do fantasma verde: para move-west ele se desloca para o oeste.
         (forall (?g - ghost ?gb_from - cell ?gb_to - cell)
             (when (and (ghost-alive ?g)
                        (ghost-type ?g green-fruit)
                        (ghost-at ?g ?gb_from)
                        (connected-west ?gb_from ?gb_to))
                   (and 
                     (not (ghost-at ?g ?gb_from))
                     (ghost-at ?g ?gb_to)
                   )
             )
         )
         
         ;; Movimento do fantasma vermelho: segue o movimento pré-computado.
         (forall (?g - ghost ?rg_from - cell ?rg_to - cell)
             (when (and (ghost-alive ?g)
                        (ghost-type ?g red-fruit)
                        (ghost-at ?g ?rg_from)
                        (red-next ?rg_from ?rg_to))
                   (and 
                     (not (ghost-at ?g ?rg_from))
                     (ghost-at ?g ?rg_to)
                   )
             )
         )
         
         (increase (total-cost) 1)
    )
  )
  
  ;; Ação eat-fruit-red
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
  
  ;; Ação eat-fruit-green
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
  
  ;; Ação eat-fruit-blue
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

    # Gerar fatos de conectividade para cada direção
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

    # Gerar os fatos red-next para o fantasma vermelho: Ordem de tentativa: east, depois south, depois west e, por fim, north.
    red_next_facts = []
    for (x, y) in game_map.cells:
        from_cell = cell_names[(x, y)]
        east = game_map.get_neighbor(x, y, "east")
        if east is not None:
            red_next_facts.append(f"(red-next {from_cell} {cell_names[east]})")
        else:
            south = game_map.get_neighbor(x, y, "south")
            if south is not None:
                red_next_facts.append(f"(red-next {from_cell} {cell_names[south]})")
            else:
                west = game_map.get_neighbor(x, y, "west")
                if west is not None:
                    red_next_facts.append(f"(red-next {from_cell} {cell_names[west]})")
                else:
                    north = game_map.get_neighbor(x, y, "north")
                    if north is not None:
                        red_next_facts.append(f"(red-next {from_cell} {cell_names[north]})")

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
    {" ".join(red_next_facts)}
    {" ".join(fruit_inits)}
    {" ".join(ghost_inits)}
    (= (total-cost) 0)
  )
  (:goal (and {" ".join(ghost_goals)}))
  (:metric minimize (total-cost))
)
"""
    return domain_str, problem_str

def extract_moves(planner_output):
    moves = []
    # O padrão captura linhas que iniciam com "move-<direção>"
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

def chamar_planejador():
    comando = [
        PLANNER_FDSS23,
        "--search-time-limit", "180",
        "--alias", "seq-opt-fdss-2023",
        "domain.pddl",
        "problem.pddl"
    ]
    result = subprocess.run(comando, capture_output=True, text=True)
    if result.returncode != 0:
        print("Erro ao executar Fast Downward:", file=sys.stderr)
        print(result.stderr, file=sys.stderr)
        sys.exit(result.returncode)
    return result.stdout

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

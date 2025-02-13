import sys
import subprocess
import re
from collections import defaultdict

PLANNER_PATH = "/home/software/planners/madagascar/M"

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
  (:requirements :typing :negative-preconditions :conditional-effects :adl)

  (:types
    cell ghost fruit
  )

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
  )

  ;; Ações de Movimento com parâmetros explícitos
  (:action move-north
    :parameters (?from - cell ?to - cell)
    :precondition (and (at-pacman ?from) (connected-north ?from ?to))
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
            )
  )

  (:action move-south
    :parameters (?from - cell ?to - cell)
    :precondition (and (at-pacman ?from) (connected-south ?from ?to))
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
            )
  )

  (:action move-east
    :parameters (?from - cell ?to - cell)
    :precondition (and (at-pacman ?from) (connected-east ?from ?to))
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
            )
  )

  (:action move-west
    :parameters (?from - cell ?to - cell)
    :precondition (and (at-pacman ?from) (connected-west ?from ?to))
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
            )
  )

  ;; Ações para comer frutas (com ?c declarado como parâmetro)
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
            )
  )
)
"""


    # Mapeia cada célula (coordenada) para um nome (ex.: c1, c2, ...)
    cell_names = {}
    cell_list = []
    counter = 1
    for coord in game_map.cells:
        name = f"c{counter}"
        cell_names[coord] = name
        cell_list.append(name)
        counter += 1

    # Gera as conexões entre células adjacentes (norte, sul, leste, oeste)
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
            if (nx, ny) in cell_names:  # vizinho existe e não é parede
                connections.append(f"({pred} {cell_names[(x,y)]} {cell_names[(nx,ny)]})")

    # Geração dos objetos e dos fatos iniciais para os fantasmas
    ghost_names = []
    ghost_inits = []
    for i, (x, y, symbol) in enumerate(game_map.ghosts):
        gname = f"ghost{i+1}"
        ghost_names.append(gname)
        # Mapeia o símbolo do fantasma para a fruta correspondente
        if symbol == 'R':
            ghost_fruit = "red-fruit"
        elif symbol == 'G':
            ghost_fruit = "green-fruit"
        elif symbol == 'B':
            ghost_fruit = "blue-fruit"
        else:
            ghost_fruit = "red-fruit"  # default
        ghost_inits.append(f"(ghost-at {gname} {cell_names[(x,y)]})")
        ghost_inits.append(f"(ghost-type {gname} {ghost_fruit})")
        ghost_inits.append(f"(ghost-alive {gname})")

    # Geração dos fatos iniciais para as frutas (assumindo no máximo uma fruta de cada tipo)
    fruit_positions = {}
    for (x, y, symbol) in game_map.fruits:
        if symbol == '!':
            fruit_positions["red-fruit"] = cell_names[(x,y)]
        elif symbol == '@':
            fruit_positions["green-fruit"] = cell_names[(x,y)]
        elif symbol == '$':
            fruit_positions["blue-fruit"] = cell_names[(x,y)]

    fruit_inits = []
    for fruit, cell in fruit_positions.items():
        fruit_inits.append(f"(fruit-at {fruit} {cell})")

    # Fato inicial para a posição do Pac-Man
    pacman_init = f"(at-pacman {cell_names[game_map.pacman_pos]})"

    # Meta: todos os fantasmas devem estar mortos
    ghost_goals = []
    for g in ghost_names:
        ghost_goals.append(f"(not (ghost-alive {g}))")

    # Monta a string do problema
    problem_str = f"""(define (problem mapa-agile)
  (:domain pacman-agile)
  (:objects
    {" ".join(cell_list)} - cell
    {" ".join(ghost_names)} - ghost
    {" ".join(fruit_positions.keys())} - fruit
  )
  (:init
    {pacman_init}
    {" ".join(connections)}
    {" ".join(fruit_inits)}
    {" ".join(ghost_inits)}
  )
  (:goal (and 
    {" ".join(ghost_goals)}
  ))
)"""

    return domain_str, problem_str


def chamar_planejador():
    comando = [
        PLANNER_PATH,
        "-s1",
        "domain.pddl",
        "problem.pddl"
    ]
    result = subprocess.run(comando, capture_output=True, text=True)

    if result.returncode != 0:
        print("Erro ao executar Madagascar:", file=sys.stderr)
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

    output = chamar_planejador()

    print("Saída completa do planejador:")
    print(output)
    
    pattern = r"^STEP\s+\d+(\.\d+)?:\s+move-([nsew])"
    moves = []
    for line in output.splitlines():
        text = line.strip()
        match = re.match(pattern, text, re.IGNORECASE)
        if match:
            direction_char = match.group(2).upper()
            moves.append(direction_char)

    if moves:
        result_str = ";".join(moves) + ";0"
    else:
        result_str = "0"

    print(result_str) 

if __name__ == "__main__":
    main()

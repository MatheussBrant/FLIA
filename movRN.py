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
        # Armazena cada linha preservando seu tamanho original
        self.grid = [list(line.rstrip("\n")) for line in lines if line.strip() != ""]
        self.height = len(self.grid)
        # self.width não será mais usado como tamanho fixo para todas as linhas
        
        self.pacman_pos = None    # (x, y) onde 'P' aparece
        self.ghosts = []          # Lista de tuplas (x, y, símbolo) para fantasmas ('R','G','B')
        self.fruits = []          # Lista de tuplas (x, y, símbolo) para frutas ('!', '@', '$')
        self.cells = []           # Lista de coordenadas (x,y) de células que não são paredes

        for y, row in enumerate(self.grid):
            for x in range(len(row)):
                char = row[x]
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
        
        # Verifica se ny está dentro do grid e se nx está dentro do tamanho da linha ny
        if 0 <= ny < self.height and 0 <= nx < len(self.grid[ny]) and self.grid[ny][nx] != '#':
            return (nx, ny)
        else:
            return None

def simulate_red_ghost_move(pos, current_direction, game_map):
    """
    Dada a posição e direção corrente do fantasma vermelho, retorna (nova_pos, nova_direcao)
    seguindo a regra: tenta mover na direção corrente; se bloqueado, tenta as próximas (sentido horário).
    """
    direction_order = {
        "east":  ["east", "south", "west", "north"],
        "south": ["south", "west", "north", "east"],
        "west":  ["west", "north", "east", "south"],
        "north": ["north", "east", "south", "west"]
    }
    for d in direction_order[current_direction]:
        new_pos = game_map.get_neighbor(pos[0], pos[1], d)
        if new_pos is not None:
            return new_pos, d
    return pos, current_direction

def detect_cycle_in_red_ghost_movement(start_pos, start_direction, game_map, max_steps=1000):
    """
    Simula o movimento do fantasma vermelho e detecta o ciclo.
    
    :param start_pos: Tupla (x, y) com a posição inicial.
    :param start_direction: String com a direção inicial ("north", "south", "east", "west").
    :param game_map: Instância de EnhancedGameMap.
    :param max_steps: Número máximo de passos para evitar loop infinito.
    :return: Uma tupla (prefix, cycle) onde:
             - prefix é uma lista de movimentos (tuplas (from, to)) até o início do ciclo;
             - cycle é a lista de movimentos que se repetem ciclicamente.
    """
    seen_states = {}  # chave: (pos, direction), valor: índice do movimento
    moves = []        # cada movimento é uma tupla: (from_pos, to_pos)
    
    current_pos = start_pos
    current_direction = start_direction

    for _ in range(max_steps):
        state = (current_pos, current_direction)
        if state in seen_states:
            cycle_start_index = seen_states[state]
            prefix = moves[:cycle_start_index]
            cycle = moves[cycle_start_index:]
            return prefix, cycle
        else:
            seen_states[state] = len(moves)
        
        new_pos, new_direction = simulate_red_ghost_move(current_pos, current_direction, game_map)
        moves.append((current_pos, new_pos))
        current_pos, current_direction = new_pos, new_direction

    # Se não detectar ciclo, retorna tudo como prefix e ciclo vazio
    return moves, []

def generate_pddl(game_map):
    # Domínio modificado para incluir a modelagem do movimento pré-definido do fantasma vermelho.
    # A movimentação do red ghost será realizada por uma ação separada "move-red"
    # que utiliza os fatos pré-computados (expected-move) para determinar o movimento.
    domain_str = """(define (domain pacman-agile)
  (:requirements :typing :negative-preconditions :conditional-effects :adl :action-costs)
  (:types cell ghost fruit step)
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
    ;; A flag ghosts-pending será ativada somente se houver ghost azul ou verde vivos
    (ghosts-pending)
    ;; Flag para o red ghost
    (red-pending)
    ;; Predicados para o movimento pré-definido do fantasma vermelho
    (current-step ?s - step)
    (expected-move ?s - step ?from - cell ?to - cell)
    (next-step ?s - step ?ns - step)
  )
  (:functions (total-cost) - number)
  
  ;; Ação move-north: move o Pac-Man e marca que os fantasmas precisam se mover.
  (:action move-north
    :parameters (?from - cell ?to - cell)
    :precondition (and 
         (at-pacman ?from)
         (not (red-pending))
         (not (ghosts-pending))
         (connected-north ?from ?to)
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
                           (and (ghost-type ?g blue-fruit) (connected-south ?x ?to))
                           (and (ghost-type ?g green-fruit) (connected-north ?x ?to))
                           (and (ghost-type ?g red-fruit)
                                (or
                                    (and (connected-north ?x ?to))
                                    (and (connected-south ?x ?to))
                                    (and (connected-east  ?x ?to))
                                    (and (connected-west  ?x ?to))
                                )
                             )
                         )
                         (not (exists (?f - fruit)
                                     (and (active-fruit ?f) (ghost-type ?g ?f))))
                    )
         ))
         (not (or
            (and (active-fruit blue-fruit)
                 (exists (?g - ghost)
                    (and (ghost-type ?g blue-fruit) (ghost-alive ?g)))
                 (exists (?f - fruit)
                    (and (fruit-at ?f ?to) (not (= ?f blue-fruit)))))
            (and (active-fruit red-fruit)
                 (exists (?g - ghost)
                    (and (ghost-type ?g red-fruit) (ghost-alive ?g)))
                 (exists (?f - fruit)
                    (and (fruit-at ?f ?to) (not (= ?f red-fruit)))))
            (and (active-fruit green-fruit)
                 (exists (?g - ghost)
                    (and (ghost-type ?g green-fruit) (ghost-alive ?g)))
                 (exists (?f - fruit)
                    (and (fruit-at ?f ?to) (not (= ?f green-fruit)))))
         ))
    )
    :effect (and 
         (not (at-pacman ?from))
         (at-pacman ?to)
         (not (last-move-south))
         (not (last-move-east))
         (not (last-move-west))
         (last-move-north)
         (increase (total-cost) 1)
         (when (exists (?g - ghost)
                    (or (and (ghost-type ?g blue-fruit) (ghost-alive ?g))
                        (and (ghost-type ?g green-fruit) (ghost-alive ?g))))
               (ghosts-pending)
         )
         (when (exists (?g - ghost)
                    (and (ghost-type ?g red-fruit) (ghost-alive ?g)))
               (red-pending)
         )
    )
  )
  
  ;; Ação move-south:
  (:action move-south
    :parameters (?from - cell ?to - cell)
    :precondition (and 
         (at-pacman ?from)
         (not (ghosts-pending))
         (not (red-pending))
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
                           (and (ghost-type ?g red-fruit)
                                (or
                                    (and (connected-north ?x ?to))
                                    (and (connected-south ?x ?to))
                                    (and (connected-east  ?x ?to))
                                    (and (connected-west  ?x ?to))
                                )
                             )
                         )
                         (not (exists (?f - fruit)
                                     (and (active-fruit ?f) (ghost-type ?g ?f))))
                    )
         ))
         (not (or
            (and (active-fruit blue-fruit)
                 (exists (?g - ghost)
                    (and (ghost-type ?g blue-fruit) (ghost-alive ?g)))
                 (exists (?f - fruit)
                    (and (fruit-at ?f ?to) (not (= ?f blue-fruit)))))
            (and (active-fruit red-fruit)
                 (exists (?g - ghost)
                    (and (ghost-type ?g red-fruit) (ghost-alive ?g)))
                 (exists (?f - fruit)
                    (and (fruit-at ?f ?to) (not (= ?f red-fruit)))))
            (and (active-fruit green-fruit)
                 (exists (?g - ghost)
                    (and (ghost-type ?g green-fruit) (ghost-alive ?g)))
                 (exists (?f - fruit)
                    (and (fruit-at ?f ?to) (not (= ?f green-fruit)))))
         ))
    )
    :effect (and 
         (not (at-pacman ?from))
         (at-pacman ?to)
         (not (last-move-north))
         (not (last-move-east))
         (not (last-move-west))
         (last-move-south)
         (increase (total-cost) 1)
         (when (exists (?g - ghost)
                    (or (and (ghost-type ?g blue-fruit) (ghost-alive ?g))
                        (and (ghost-type ?g green-fruit) (ghost-alive ?g))))
               (ghosts-pending)
         )
         (when (exists (?g - ghost)
                    (and (ghost-type ?g red-fruit) (ghost-alive ?g)))
               (red-pending)
         )
    )
  )
  
  ;; Ação move-east:
  (:action move-east
    :parameters (?from - cell ?to - cell)
    :precondition (and 
         (at-pacman ?from)
         (not (ghosts-pending))
         (not (red-pending))
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
                           (and (ghost-type ?g red-fruit)
                                (or
                                    (and (connected-north ?x ?to))
                                    (and (connected-south ?x ?to))
                                    (and (connected-east  ?x ?to))
                                    (and (connected-west  ?x ?to))
                                )
                             )
                         )
                         (not (exists (?f - fruit)
                                     (and (active-fruit ?f) (ghost-type ?g ?f))))
                    )
         ))
         (not (or
            (and (active-fruit blue-fruit)
                 (exists (?g - ghost)
                    (and (ghost-type ?g blue-fruit) (ghost-alive ?g)))
                 (exists (?f - fruit)
                    (and (fruit-at ?f ?to) (not (= ?f blue-fruit)))))
            (and (active-fruit red-fruit)
                 (exists (?g - ghost)
                    (and (ghost-type ?g red-fruit) (ghost-alive ?g)))
                 (exists (?f - fruit)
                    (and (fruit-at ?f ?to) (not (= ?f red-fruit)))))
            (and (active-fruit green-fruit)
                 (exists (?g - ghost)
                    (and (ghost-type ?g green-fruit) (ghost-alive ?g)))
                 (exists (?f - fruit)
                    (and (fruit-at ?f ?to) (not (= ?f green-fruit)))))
         ))
    )
    :effect (and 
         (not (at-pacman ?from))
         (at-pacman ?to)
         (not (last-move-north))
         (not (last-move-south))
         (not (last-move-west))
         (last-move-east)
         (increase (total-cost) 1)
         (when (exists (?g - ghost)
                    (or (and (ghost-type ?g blue-fruit) (ghost-alive ?g))
                        (and (ghost-type ?g green-fruit) (ghost-alive ?g))))
               (ghosts-pending)
         )
         (when (exists (?g - ghost)
                    (and (ghost-type ?g red-fruit) (ghost-alive ?g)))
               (red-pending)
         )
    )
  )
  
  ;; Ação move-west:
  (:action move-west
    :parameters (?from - cell ?to - cell)
    :precondition (and 
         (at-pacman ?from)
         (not (ghosts-pending))
         (not (red-pending))
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
                           (and (ghost-type ?g red-fruit)
                                (or
                                    (and (connected-north ?x ?to))
                                    (and (connected-south ?x ?to))
                                    (and (connected-east  ?x ?to))
                                    (and (connected-west  ?x ?to))
                                )
                             )
                         )
                         (not (exists (?f - fruit)
                                     (and (active-fruit ?f) (ghost-type ?g ?f))))
                    )
         ))
         (not (or
            (and (active-fruit blue-fruit)
                 (exists (?g - ghost)
                    (and (ghost-type ?g blue-fruit) (ghost-alive ?g)))
                 (exists (?f - fruit)
                    (and (fruit-at ?f ?to) (not (= ?f blue-fruit)))))
            (and (active-fruit red-fruit)
                 (exists (?g - ghost)
                    (and (ghost-type ?g red-fruit) (ghost-alive ?g)))
                 (exists (?f - fruit)
                    (and (fruit-at ?f ?to) (not (= ?f red-fruit)))))
            (and (active-fruit green-fruit)
                 (exists (?g - ghost)
                    (and (ghost-type ?g green-fruit) (ghost-alive ?g)))
                 (exists (?f - fruit)
                    (and (fruit-at ?f ?to) (not (= ?f green-fruit)))))
         ))
    )
    :effect (and 
         (not (at-pacman ?from))
         (at-pacman ?to)
         (not (last-move-north))
         (not (last-move-south))
         (not (last-move-east))
         (last-move-west)
         (increase (total-cost) 1)
         (when (exists (?g - ghost)
                    (or (and (ghost-type ?g blue-fruit) (ghost-alive ?g))
                        (and (ghost-type ?g green-fruit) (ghost-alive ?g))))
               (ghosts-pending)
         )
         (when (exists (?g - ghost)
                    (and (ghost-type ?g red-fruit) (ghost-alive ?g)))
               (red-pending)
         )
    )
  )
  
  ;; Ação ghost-turn: movimenta os fantasmas azuis e verdes.
  ;; Agora, o movimento do red ghost NÃO está aqui.
  (:action ghost-turn
    :parameters ()
    :precondition (and 
         (ghosts-pending)
         (or (last-move-north) (last-move-south) (last-move-east) (last-move-west))
    )
    :effect (and
         ;; Blocos para fantasmas azuis:
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
         ;; Blocos para fantasmas verdes:
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
         ;; Limpa flags de movimento e a marca de pendência.
         (not (last-move-north))
         (not (last-move-south))
         (not (last-move-east))
         (not (last-move-west))
         (not (ghosts-pending))
    )
  )
  
  ;; Nova ação para movimentar o red ghost, usando a sequência pré-computada.
  (:action move-red
    :parameters (?g - ghost ?from - cell ?to - cell ?s - step ?next - step)
    :precondition (and
         (red-pending)
         (ghost-at ?g ?from)
         (ghost-type ?g red-fruit)
         (ghost-alive ?g)
         (current-step ?s)
         (expected-move ?s ?from ?to)
         (next-step ?s ?next)
    )
    :effect (and
         (not (ghost-at ?g ?from))
         (ghost-at ?g ?to)
         (not (red-pending))
         (not (current-step ?s))
         (current-step ?next)
         (increase (total-cost) 1)
    )
  )
  
  ;; Ações de comer fruta:
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

    ;; AÇÕES PARA MATAR FANTASMAS
  (:action kill-ghost-red
    :parameters (?c - cell ?g - ghost)
    :precondition (and 
         (at-pacman ?c)
         (ghost-at ?g ?c)
         (ghost-type ?g red-fruit)
         (ghost-alive ?g)
         (active-fruit red-fruit)
    )
    :effect (and 
         (not (ghost-alive ?g))
         (increase (total-cost) 1)
    )
  )
  
  (:action kill-ghost-green
    :parameters (?c - cell ?g - ghost)
    :precondition (and 
         (at-pacman ?c)
         (ghost-at ?g ?c)
         (ghost-type ?g green-fruit)
         (ghost-alive ?g)
         (active-fruit green-fruit)
    )
    :effect (and 
         (not (ghost-alive ?g))
         (increase (total-cost) 1)
    )
  )
  
  (:action kill-ghost-blue
    :parameters (?c - cell ?g - ghost)
    :precondition (and 
         (at-pacman ?c)
         (ghost-at ?g ?c)
         (ghost-type ?g blue-fruit)
         (ghost-alive ?g)
         (active-fruit blue-fruit)
    )
    :effect (and 
         (not (ghost-alive ?g))
         (increase (total-cost) 1)
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
    red_sequence = []  # Fatos para definir a sequência do fantasma vermelho.
    red_sequence_defined = False
    cycle_start = None  # Índice do primeiro step do ciclo (1-indexado)
    total_steps = 0     # Total de steps na sequência
    for i, (x, y, symbol) in enumerate(game_map.ghosts):
        gname = f"ghost{i+1}"
        ghost_names.append(gname)
        if symbol == 'R':
            ghost_fruit = "red-fruit"
            if not red_sequence_defined:
                prefix, cycle = detect_cycle_in_red_ghost_movement((x, y), "east", game_map)
                full_sequence = prefix.copy()
                if cycle:
                    # O primeiro movimento do ciclo está na posição len(prefix)+1 (indexação iniciando em 1)
                    cycle_start = len(prefix) + 1
                    # Ajusta o último movimento do ciclo para retornar ao início do ciclo
                    first_cycle_from, _ = cycle[0]
                    last_move_from, _ = cycle[-1]
                    cycle[-1] = (last_move_from, first_cycle_from)
                    full_sequence += cycle
                else:
                    full_sequence = prefix
                # Cria os fatos: o primeiro fato indica o step corrente, os demais definem os expected-move.
                red_sequence.append("(current-step step1)")
                step_facts = []
                for step_index, (from_pos, to_pos) in enumerate(full_sequence, start=1):
                    from_cell = cell_names.get(from_pos, f"cR_{from_pos[0]}_{from_pos[1]}")
                    to_cell = cell_names.get(to_pos, f"cR_{to_pos[0]}_{to_pos[1]}")
                    step_facts.append(f"(expected-move step{step_index} {from_cell} {to_cell})")
                red_sequence.extend(step_facts)
                total_steps = len(full_sequence)
                red_sequence_defined = True
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

    # Definição dos objetos do tipo step.
    if total_steps == 0:
        total_steps = 20  # Valor padrão caso não haja red ghost
    steps = [f"step{i}" for i in range(1, total_steps+1)]
    steps_obj = " ".join(steps) + " - step"

    # Geração dos fatos next-step para garantir a ordem dos steps.
    next_steps = []
    for i in range(1, total_steps):
        next_steps.append(f"(next-step step{i} step{i+1})")
    if cycle_start is not None:
        next_steps.append(f"(next-step step{total_steps} step{cycle_start})")
    else:
        next_steps.append(f"(next-step step{total_steps} step{total_steps})")

    problem_str = f"""(define (problem mapa-agile)
  (:domain pacman-agile)
  (:objects
    {" ".join(cell_list)} - cell
    {" ".join(ghost_names)} - ghost
    red-fruit green-fruit blue-fruit - fruit
    {steps_obj}
  )
  (:init
    {pacman_init}
    {" ".join(connections)}
    {" ".join(fruit_inits)}
    {" ".join(ghost_inits)}
    {" ".join(red_sequence)}
    {" ".join(next_steps)}
    (red-step-ok)
    (= (total-cost) 0)
  )
  (:goal (and {" ".join(ghost_goals)}))
  (:metric minimize (total-cost))
)
"""
    return domain_str, problem_str

def extract_moves(planner_output):
    moves = []
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

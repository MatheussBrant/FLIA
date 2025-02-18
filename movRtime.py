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
        
        if 0 <= ny < self.height and 0 <= nx < len(self.grid[ny]) and self.grid[ny][nx] != '#':
            return (nx, ny)
        else:
            return None

def generate_pddl(game_map):
    # Domínio PDDL modificado
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
    ;; Flags de pendência para os fantasmas
    (ghosts-pending)
    (red-pending)
    ;; Flags para o último movimento do fantasma vermelho
    (last-red-north ?g - ghost)
    (last-red-south ?g - ghost)
    (last-red-east ?g - ghost)
    (last-red-west ?g - ghost)
  )
  (:functions (total-cost) - number)

  ;; Ações de movimento do Pac-Man (sem alterações)
  (:action move-north
    :parameters (?from - cell ?to - cell)
    :precondition (and 
         (at-pacman ?from)
         (not (ghosts-pending))
         (not (red-pending))
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
                   (and (ghost-type ?g red-fruit) (ghost-alive ?g)))
               (red-pending))
         (when (exists (?g - ghost)
                   (or (and (ghost-type ?g green-fruit) (ghost-alive ?g))
                       (and (ghost-type ?g blue-fruit) (ghost-alive ?g))))
               (ghosts-pending))
    )
  )

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
                   (and (ghost-type ?g red-fruit) (ghost-alive ?g)))
               (red-pending))
         (when (exists (?g - ghost)
                   (or (and (ghost-type ?g green-fruit) (ghost-alive ?g))
                       (and (ghost-type ?g blue-fruit) (ghost-alive ?g))))
               (ghosts-pending))
    )
  )

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
                   (and (ghost-type ?g red-fruit) (ghost-alive ?g)))
               (red-pending))
         (when (exists (?g - ghost)
                   (or (and (ghost-type ?g green-fruit) (ghost-alive ?g))
                       (and (ghost-type ?g blue-fruit) (ghost-alive ?g))))
               (ghosts-pending))
    )
  )

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
                   (and (ghost-type ?g red-fruit) (ghost-alive ?g)))
               (red-pending))
         (when (exists (?g - ghost)
                   (or (and (ghost-type ?g green-fruit) (ghost-alive ?g))
                       (and (ghost-type ?g blue-fruit) (ghost-alive ?g))))
               (ghosts-pending))
    )
  )

  ;; Ação ghost-turn: movimenta os fantasmas (exceto os com movimento individual) e limpa as flags.
  (:action ghost-turn
    :parameters ()
    :precondition (or (last-move-north) (last-move-south) (last-move-east) (last-move-west))
    :effect (and
         ;; Movimento dos fantasmas azuis:
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
         ;; Movimento dos fantasmas verdes:
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
         (not (last-move-north))
         (not (last-move-south))
         (not (last-move-east))
         (not (last-move-west))
         (not (ghosts-pending))
    )
  )

  ;; AÇÕES PARA MOVIMENTAÇÃO DO FANTASMA VERMELHO
  ;; Para cada último movimento, definimos 4 ações com a ordem de prioridade (movimento atual, depois sentido horário)

  ;; Caso último movimento seja NORTH: ordem NORTH, EAST, SOUTH, WEST
  (:action move-red-north-from-north
    :parameters (?g - ghost ?from - cell ?to - cell)
    :precondition (and 
         (ghost-at ?g ?from)
         (ghost-type ?g red-fruit)
         (ghost-alive ?g)
         (red-pending)
         (last-red-north ?g)
         (connected-north ?from ?to)
    )
    :effect (and
         (not (ghost-at ?g ?from))
         (ghost-at ?g ?to)
         (not (last-red-east ?g))
         (not (last-red-south ?g))
         (not (last-red-west ?g))
         (not (last-red-north ?g))
         (last-red-north ?g)
         (not (red-pending))
    )
  )

  (:action move-red-east-from-north
    :parameters (?g - ghost ?from - cell ?to - cell ?dummy - cell)
    :precondition (and
         (ghost-at ?g ?from)
         (ghost-type ?g red-fruit)
         (ghost-alive ?g)
         (red-pending)
         (last-red-north ?g)
         (not (exists (?dummy - cell) (connected-north ?from ?dummy)))
         (connected-east ?from ?to)
    )
    :effect (and
         (not (ghost-at ?g ?from))
         (ghost-at ?g ?to)
         (not (last-red-east ?g))
         (not (last-red-south ?g))
         (not (last-red-west ?g))
         (not (last-red-north ?g))
         (last-red-east ?g)
         (not (red-pending))
    )
  )

  (:action move-red-south-from-north
    :parameters (?g - ghost ?from - cell ?to - cell ?dummy - cell)
    :precondition (and
         (ghost-at ?g ?from)
         (ghost-type ?g red-fruit)
         (ghost-alive ?g)
         (red-pending)
         (last-red-north ?g)
         (not (exists (?dummy - cell) (connected-north ?from ?dummy)))
         (not (exists (?dummy - cell) (connected-east ?from ?dummy)))
         (connected-south ?from ?to)
    )
    :effect (and
         (not (ghost-at ?g ?from))
         (ghost-at ?g ?to)
         (not (last-red-east ?g))
         (not (last-red-south ?g))
         (not (last-red-west ?g))
         (not (last-red-north ?g))
         (last-red-south ?g)
         (not (red-pending))
    )
  )

  (:action move-red-west-from-north
    :parameters (?g - ghost ?from - cell ?to - cell ?dummy - cell)
    :precondition (and
         (ghost-at ?g ?from)
         (ghost-type ?g red-fruit)
         (ghost-alive ?g)
         (red-pending)
         (last-red-north ?g)
         (not (exists (?dummy - cell) (connected-north ?from ?dummy)))
         (not (exists (?dummy - cell) (connected-east ?from ?dummy)))
         (not (exists (?dummy - cell) (connected-south ?from ?dummy)))
         (connected-west ?from ?to)
    )
    :effect (and
         (not (ghost-at ?g ?from))
         (ghost-at ?g ?to)
         (not (last-red-east ?g))
         (not (last-red-south ?g))
         (not (last-red-west ?g))
         (not (last-red-north ?g))
         (last-red-west ?g)
         (not (red-pending))
    )
  )

  ;; Caso último movimento seja EAST: ordem EAST, SOUTH, WEST, NORTH
  (:action move-red-east-from-east
    :parameters (?g - ghost ?from - cell ?to - cell)
    :precondition (and 
         (ghost-at ?g ?from)
         (ghost-type ?g red-fruit)
         (ghost-alive ?g)
         (red-pending)
         (last-red-east ?g)
         (connected-east ?from ?to)
    )
    :effect (and
         (not (ghost-at ?g ?from))
         (ghost-at ?g ?to)
         (not (last-red-east ?g))
         (not (last-red-south ?g))
         (not (last-red-west ?g))
         (not (last-red-north ?g))
         (last-red-east ?g)
         (not (red-pending))
    )
  )

  (:action move-red-south-from-east
    :parameters (?g - ghost ?from - cell ?to - cell ?dummy - cell)
    :precondition (and 
         (ghost-at ?g ?from)
         (ghost-type ?g red-fruit)
         (ghost-alive ?g)
         (red-pending)
         (last-red-east ?g)
         (not (exists (?dummy - cell) (connected-east ?from ?dummy)))
         (connected-south ?from ?to)
    )
    :effect (and
         (not (ghost-at ?g ?from))
         (ghost-at ?g ?to)
         (not (last-red-east ?g))
         (not (last-red-south ?g))
         (not (last-red-west ?g))
         (not (last-red-north ?g))
         (last-red-south ?g)
         (not (red-pending))
    )
  )

  (:action move-red-west-from-east
    :parameters (?g - ghost ?from - cell ?to - cell ?dummy - cell)
    :precondition (and 
         (ghost-at ?g ?from)
         (ghost-type ?g red-fruit)
         (ghost-alive ?g)
         (red-pending)
         (last-red-east ?g)
         (not (exists (?dummy - cell) (connected-east ?from ?dummy)))
         (not (exists (?dummy - cell) (connected-south ?from ?dummy)))
         (connected-west ?from ?to)
    )
    :effect (and
         (not (ghost-at ?g ?from))
         (ghost-at ?g ?to)
         (not (last-red-east ?g))
         (not (last-red-south ?g))
         (not (last-red-west ?g))
         (not (last-red-north ?g))
         (last-red-west ?g)
         (not (red-pending))
    )
  )

  (:action move-red-north-from-east
    :parameters (?g - ghost ?from - cell ?to - cell ?dummy - cell)
    :precondition (and 
         (ghost-at ?g ?from)
         (ghost-type ?g red-fruit)
         (ghost-alive ?g)
         (red-pending)
         (last-red-east ?g)
         (not (exists (?dummy - cell) (connected-east ?from ?dummy)))
         (not (exists (?dummy - cell) (connected-south ?from ?dummy)))
         (not (exists (?dummy - cell) (connected-west ?from ?dummy)))
         (connected-north ?from ?to)
    )
    :effect (and
         (not (ghost-at ?g ?from))
         (ghost-at ?g ?to)
         (not (last-red-east ?g))
         (not (last-red-south ?g))
         (not (last-red-west ?g))
         (not (last-red-north ?g))
         (last-red-north ?g)
         (not (red-pending))
    )
  )

  ;; Caso último movimento seja SOUTH: ordem SOUTH, WEST, NORTH, EAST
  (:action move-red-south-from-south
    :parameters (?g - ghost ?from - cell ?to - cell)
    :precondition (and 
         (ghost-at ?g ?from)
         (ghost-type ?g red-fruit)
         (ghost-alive ?g)
         (red-pending)
         (last-red-south ?g)
         (connected-south ?from ?to)
    )
    :effect (and
         (not (ghost-at ?g ?from))
         (ghost-at ?g ?to)
         (not (last-red-east ?g))
         (not (last-red-south ?g))
         (not (last-red-west ?g))
         (not (last-red-north ?g))
         (last-red-south ?g)
         (not (red-pending))
    )
  )

  (:action move-red-west-from-south
    :parameters (?g - ghost ?from - cell ?to - cell ?dummy - cell)
    :precondition (and 
         (ghost-at ?g ?from)
         (ghost-type ?g red-fruit)
         (ghost-alive ?g)
         (red-pending)
         (last-red-south ?g)
         (not (exists (?dummy - cell) (connected-south ?from ?dummy)))
         (connected-west ?from ?to)
    )
    :effect (and
         (not (ghost-at ?g ?from))
         (ghost-at ?g ?to)
         (not (last-red-east ?g))
         (not (last-red-south ?g))
         (not (last-red-west ?g))
         (not (last-red-north ?g))
         (last-red-west ?g)
         (not (red-pending))
    )
  )

  (:action move-red-north-from-south
    :parameters (?g - ghost ?from - cell ?to - cell ?dummy - cell)
    :precondition (and 
         (ghost-at ?g ?from)
         (ghost-type ?g red-fruit)
         (ghost-alive ?g)
         (red-pending)
         (last-red-south ?g)
         (not (exists (?dummy - cell) (connected-south ?from ?dummy)))
         (not (exists (?dummy - cell) (connected-west ?from ?dummy)))
         (connected-north ?from ?to)
    )
    :effect (and
         (not (ghost-at ?g ?from))
         (ghost-at ?g ?to)
         (not (last-red-east ?g))
         (not (last-red-south ?g))
         (not (last-red-west ?g))
         (not (last-red-north ?g))
         (last-red-north ?g)
         (not (red-pending))
    )
  )

  (:action move-red-east-from-south
    :parameters (?g - ghost ?from - cell ?to - cell ?dummy - cell)
    :precondition (and 
         (ghost-at ?g ?from)
         (ghost-type ?g red-fruit)
         (ghost-alive ?g)
         (red-pending)
         (last-red-south ?g)
         (not (exists (?dummy - cell) (connected-south ?from ?dummy)))
         (not (exists (?dummy - cell) (connected-west ?from ?dummy)))
         (not (exists (?dummy - cell) (connected-north ?from ?dummy)))
         (connected-east ?from ?to)
    )
    :effect (and
         (not (ghost-at ?g ?from))
         (ghost-at ?g ?to)
         (not (last-red-east ?g))
         (not (last-red-south ?g))
         (not (last-red-west ?g))
         (not (last-red-north ?g))
         (last-red-east ?g)
         (not (red-pending))
    )
  )

  ;; Caso último movimento seja WEST: ordem WEST, NORTH, EAST, SOUTH
  (:action move-red-west-from-west
    :parameters (?g - ghost ?from - cell ?to - cell)
    :precondition (and 
         (ghost-at ?g ?from)
         (ghost-type ?g red-fruit)
         (ghost-alive ?g)
         (red-pending)
         (last-red-west ?g)
         (connected-west ?from ?to)
    )
    :effect (and
         (not (ghost-at ?g ?from))
         (ghost-at ?g ?to)
         (not (last-red-east ?g))
         (not (last-red-south ?g))
         (not (last-red-west ?g))
         (not (last-red-north ?g))
         (last-red-west ?g)
         (not (red-pending))
    )
  )

  (:action move-red-north-from-west
    :parameters (?g - ghost ?from - cell ?to - cell ?dummy - cell)
    :precondition (and 
         (ghost-at ?g ?from)
         (ghost-type ?g red-fruit)
         (ghost-alive ?g)
         (red-pending)
         (last-red-west ?g)
         (not (exists (?dummy - cell) (connected-west ?from ?dummy)))
         (connected-north ?from ?to)
    )
    :effect (and
         (not (ghost-at ?g ?from))
         (ghost-at ?g ?to)
         (not (last-red-east ?g))
         (not (last-red-south ?g))
         (not (last-red-west ?g))
         (not (last-red-north ?g))
         (last-red-north ?g)
         (not (red-pending))
    )
  )

  (:action move-red-east-from-west
    :parameters (?g - ghost ?from - cell ?to - cell ?dummy - cell)
    :precondition (and 
         (ghost-at ?g ?from)
         (ghost-type ?g red-fruit)
         (ghost-alive ?g)
         (red-pending)
         (last-red-west ?g)
         (not (exists (?dummy - cell) (connected-west ?from ?dummy)))
         (not (exists (?dummy - cell) (connected-north ?from ?dummy)))
         (connected-east ?from ?to)
    )
    :effect (and
         (not (ghost-at ?g ?from))
         (ghost-at ?g ?to)
         (not (last-red-east ?g))
         (not (last-red-south ?g))
         (not (last-red-west ?g))
         (not (last-red-north ?g))
         (last-red-east ?g)
         (not (red-pending))
    )
  )

  (:action move-red-south-from-west
    :parameters (?g - ghost ?from - cell ?to - cell ?dummy - cell)
    :precondition (and 
         (ghost-at ?g ?from)
         (ghost-type ?g red-fruit)
         (ghost-alive ?g)
         (red-pending)
         (last-red-west ?g)
         (not (exists (?dummy - cell) (connected-west ?from ?dummy)))
         (not (exists (?dummy - cell) (connected-north ?from ?dummy)))
         (not (exists (?dummy - cell) (connected-east ?from ?dummy)))
         (connected-south ?from ?to)
    )
    :effect (and
         (not (ghost-at ?g ?from))
         (ghost-at ?g ?to)
         (not (last-red-east ?g))
         (not (last-red-south ?g))
         (not (last-red-west ?g))
         (not (last-red-north ?g))
         (last-red-south ?g)
         (not (red-pending))
    )
  )

  ;; AÇÕES DE COMER FRUTA
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

    # Geração dos objetos e fatos para o problema.
    cell_names = {}
    cell_list = []
    counter = 1
    for coord in game_map.cells:
        name = f"c{counter}"
        cell_names[coord] = name
        cell_list.append(name)
        counter += 1

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
            # Inicialmente, definimos last-red-east (pode ser ajustado conforme desejar)
            ghost_inits.append(f"(last-red-east {gname})")
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

# Especificação do Modelo: Organização de Monitorias (UFCG)

## Projeto de Lógica para Computação (2026.1)

**Objetivo:** Utilizar o Alloy Analyzer e a lógica de predicados para validar design de software dada uma especificação inicial.

**Especificação inicial**: "A UFCG deseja organizar as monitorias para disciplinas do curso de Ciência da Computação. Os monitores são necessariamente alunos da universidade e cada monitor é habilitado para auxiliar em uma disciplina. Todo aluno deve estar matriculado em, no mínimo, três disciplinas e só pode participar de uma sessão relacionada a uma disciplina na qual esteja matriculado. Cada sessão ocorre em uma sala, deve ser conduzida por um monitor e está associada a uma disciplina. Um monitor só pode conduzir sessões da disciplina para a qual está habilitado. Cada sessão possui entre um e dez participantes, e seu monitor não pode participar dela como aluno. Uma sala não pode sediar duas sessões simultâneas. Nenhum aluno pode estar envolvido em duas sessões no mesmo horário, seja como participante ou como monitor. Salas e disciplinas podem existir sem sessões."

---

## Entidades a serem Modeladas (Signatures)
Para representar o domínio, precisaremos criar as seguintes assinaturas (`sig`):

* **`Disciplina`**: Representa as matérias ofertadas. Pode existir independentemente de ter sessões.
* **`Sala`**: Local físico. Pode existir sem sediar nenhuma sessão.
* **`Horario`**: Necessário para lidar com a concorrência e garantir que não há choques de agenda.
* **`Aluno`**: Entidade base. Possui relação com as `Disciplinas` nas quais está matriculado.
* **`Monitor`**: Subconjunto/Especialização de `Aluno` (`sig Monitor in Aluno` ou `extends`). Possui uma habilitação específica.
* **`Sessao`**: O evento em si. Agrupa uma disciplina, um monitor, uma sala, um horário e um conjunto de alunos participantes.

---

## Regras de Negócio (Fatos)
Nossos blocos de `fact` deverão garantir as seguintes restrições:

### 1. Regras Acadêmicas (Cardinalidade e Matrícula)
- [X] Todo `Aluno` deve estar matriculado em, no mínimo, **3 disciplinas**.
- [X] Todo `Monitor` é habilitado para exatamente **1 disciplina**.

### 2. Regras de Formação da Sessão
- [X] Cada `Sessao` está associada a exatamente: **1 Sala**, **1 Disciplina** e **1 Monitor**.
- [X] A quantidade de alunos participantes em uma `Sessao` deve ser **entre 1 e 10**.
- [X] O `Monitor` da sessão **deve** ser habilitado na disciplina daquela sessão.

### 3. Regras de Participação e Conflitos de Interesse
- [X?] Um `Aluno` só pode participar de uma `Sessao` se a disciplina da sessão estiver na sua lista de matrículas.
- [X?] O `Monitor` que está conduzindo a sessão **não pode** estar na lista de participantes (alunos) desta mesma sessão.

### 4. Regras de Tempo e Espaço (Simultaneidade)
- [X] **Choque de Sala:** Uma `Sala` não pode sediar duas ou mais `Sessao`s no mesmo `Horario`.
- [ ] **Choque de Indivíduo:** Nenhum `Aluno` (seja atuando como participante ou como monitor) pode estar vinculado a duas `Sessao`s que ocorrem no mesmo `Horario`.

---

## Asserções (Asserts) e Verificações
A especificação exige pelo menos **duas asserções** que não sejam meras cópias dos fatos (eles reduzem a nota se testarmos o óbvio). Nossos asserts devem tentar "quebrar" o sistema para provar que os fatos que escrevemos realmente garantem as regras de negócio de forma emergente.

Abaixo estão opções de asserts que o grupo pode modelar. Escolham pelo menos duas para o arquivo final:

* **Opção 1: Impossibilidade de Onipresença (Choque de Horário)**
  * Tentar encontrar um cenário onde um `Aluno` (seja atuando como monitor ou como mero participante) consiga estar presente em duas `Sala`s diferentes no mesmo `Horario`. O assert deve falhar se o sistema permitir isso.
* **Opção 2: Integridade da Carga Horária Mínima**
  * Garantir que não existe nenhum universo possível no modelo onde um `Aluno` ativo no sistema possua relação com menos de 3 instâncias de `Disciplina`. 
* **Opção 3: Papel Exclusivo na Própria Sessão (Anti-clone)**
  * Garantir que nenhum `Monitor` consegue ser, simultaneamente, o condutor de uma `Sessao` e um dos alunos participantes dessa mesmíssima sessão. (Isso prova que a regra de conflito de interesse foi bem aplicada).
* **Opção 4: Isolamento de Habilitação**
  * Tentar forçar o modelo a gerar uma sessão onde o `Monitor` responsável não tenha habilitação para a `Disciplina` daquela sessão. O esperado é que o Alloy não consiga gerar essa instância.
* **Opção 5: Limites Estritos de Capacidade**
  * Checar se existe a possibilidade de uma `Sessao` existir no tempo-espaço vazia (com 0 participantes) ou superlotada (com 11 ou mais participantes).
* **Opção 6: Participação Inválida (Intruso)**
  * Verificar se o sistema impede totalmente que um aluno "ouvinte" ou "intruso" exista, ou seja, garantir que é impossível um aluno estar na lista de participantes de uma sessão se ele não estiver formalmente matriculado na disciplina daquela sessão.
---

## Checklist Técnico da Entrega
Para garantir a nota máxima, o código `.als` deve conter:
- [ ] Pelo menos **um predicado** (`pred`).
- [ ] Pelo menos **uma função** (`fun`).
- [ ] Uso de relações binárias e cardinalidades.
- [ ] Uso de `extends` ou `in` (ex: Monitor in Aluno).
- [ ] Uso de quantificadores nos fatos (`all`, `some`, `no`, etc.).
- [ ] Pelo menos **duas asserções** (`assert`) validadas pelo comando `check`.
- [ ] Um bloco `run` gerando um cenário exemplo com **escopo mínimo de 5** (`for 5`).
- [ ] Código bem documentado com comentários organizados.

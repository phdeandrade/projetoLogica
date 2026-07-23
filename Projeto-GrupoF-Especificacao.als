/*
Projeto de Lógica para Computação (2026.1)

A especificação abaixo descreve uma modelagem em termos lógicos
de um sistema que lida com as sessões de monitoria na UFCG. As entidades
presentes nele são Alunos, Monitores (extensão de Aluno), Disciplinas, Salas,
Horários e Sessões. A principal ideia é alocar corretamente Monitores, devidamente
habilitados, para darem Sessões de monitoria, as quais serão vistas por outros Alunos.
Os fatos, predicados, asserções, etc., buscam garantir que não existam incosistências nesse sistema,
tais como Monitores dando duas sessões ao mesmo tempo, validar a habilitação do Monitor
para uma única disciplina, controlar matrículas, dentre outros.

Alunos Responsáveis:
André Mikael;
Gabriela Ramalho;
Jesse Dias;
Miguel Melo;
Murilo Jadson;
Pedro Andrade;
Stefany Alves.

Monitor:
Davi Falcão.

Professor: 
Salatiel Dantas.
*/



// ASSINATURAS:

// Representação de um Aluno no modelo.
sig Aluno {
    matriculas: set Disciplina,
    disciplinasPagas: set Disciplina
}

// Representação de um Monitor no modelo. O Monitor é uma especialização do conjunto Aluno.
sig Monitor extends Aluno {
    habilitacao: one Disciplina
}

// Representa uma Disciplina no modelo. As Disciplinas possuem um conjunto de Monitores associados a ela.
sig Disciplina {
    monitoresDisciplina: set Monitor
}

// Representa uma sessão de Monitoria, dada por um único Monitor; possui Sala e Horário únicos e comporta um número limitado de Alunos.
sig Sessao {
    disciplinaSessao: one Disciplina,
    monitorSessao: one Monitor,
    sala: one Sala,
    horario: one Horario,
    alunosSessao: set Aluno
}

// Representam Sala e Horário das Sessões.
sig Sala {}
sig Horario {}



// FATOS:

/*
Representa as regras de validação para Alunos.
Garante que, para todos os Alunos, cada um tenha no máximo 3 matrículas ativas,
as quais não estão na lista de Disciplinas pagas.
*/
fact regrasAluno {
    all aluno: Aluno {
        #aluno.matriculas >= 3
        no (aluno.matriculas & aluno.disciplinasPagas)
    }
}

/*
Representa as regras de validação para Monitores.
Garante que, para todos os Monitores, cada um possui habilitação válida em uma disciplina
e que ele está monitorando alguma Disciplina.
*/
fact regrasMonitor {
    all monitor: Monitor {
        monitorHabilitado[monitor]
        monitorEstaNaListaDeAlgumaDisciplina[monitor]
    }
}

/*
Garante que todas as Disciplinas aceitem apenas Monitores habilitados para ela.
*/
fact regraMonitoresDisciplinaCorretos {
    all disciplina: Disciplina {
        disciplinaTemMonitoresComHabilitacaoCorreta[disciplina]
    }
}

/*
Representa as regras de validação para Sessões.
Garante que todas as Sessões possuem um Monitor habilitado e que cada Sessão
está respeitando seus limites de capacidade (quantidade de Alunos, alocação de Sala, Horário, etc.)
*/
fact regrasSessao {
    all sessao: Sessao {
        monitorHabilitadoSessao[sessao.monitorSessao, sessao]
        respeitaLimiteSessao[sessao]
    }
}

/*
Representa as regras de participação de Alunos nas Sessões.
*/
fact regrasParticipacao {
    all sessao: Sessao {
        participantesValidos[sessao]
    }
}

/*
Garante que não existem Sessões conflituosas, i.e., que ocorrem
ao mesmo tempo em mesmos locais.
*/
fact choqueDeSala { 
    no disj sessao1, sessao2: Sessao {
        salasConflitam[sessao1, sessao2]
        horariosIguais[sessao1, sessao2]
    } 
}

/*
Garante que um Monitor ou Aluno, em um mesmo Horário, estejam em duas Sessões diferentes.
*/
fact choqueDeHorarios {
    no disj sessao1, sessao2: Sessao {
        horariosIguais[sessao1, sessao2]
        some aluno: Aluno {
            alunoEmDuasSessoes[aluno, sessao1, sessao2]
        }
    }
}



// PREDICADOS:

/*
Predicado: "Um Monitor só pode ser habilitado em uma Disciplina que ele já pagou."
*/
pred monitorHabilitado[m: Monitor] {
    m.habilitacao in m.disciplinasPagas
}

/*
Predicado: "Um Monitor só pode ministrar uma Sessão se a Habilitação dele for a mesma dessa Sessão."
*/
pred monitorHabilitadoSessao[m: Monitor, s: Sessao] {
    monitorHabilitado[m]
    m.habilitacao = s.disciplinaSessao
}

/*
Predicado: "Um Monitor habilitado em certa Disciplina deve estar na lista
de Monitores habilitados dela."
*/
pred monitorEstaNaListaDeAlgumaDisciplina[m: Monitor] {
    m in m.habilitacao.monitoresDisciplina
}

/*
Predicado: "Todo Monitor associado a uma Disciplina deve possui Habilitação nela."
*/
pred disciplinaTemMonitoresComHabilitacaoCorreta[d: Disciplina] {
    all m: d.monitoresDisciplina {
        m.habilitacao = d
    }
}

/*
Predicado: "Toda Sessão possui exatamente entre 1 e 10 Alunos."
*/
pred respeitaLimiteSessao[s: Sessao] {
    #s.alunosSessao >= 1 and #s.alunosSessao <= 10
}

/*
Predicado: "Um participante (Aluno) de uma Sessão é válido se a Disciplina associada a Sessão
está nas matrículas ativas do Aluno e se esse mesmo Aluno não é Monitor dela."
*/
pred participantesValidos[s: Sessao] {
    all aluno: s.alunosSessao {
        s.disciplinaSessao in aluno.matriculas
        s.monitorSessao != aluno
    }
}

/*
Predicado: "Duas Sessões possuem Salas conflitantes se elas são a mesma."
*/
pred salasConflitam[s1, s2: Sessao] {
    s1.sala = s2.sala
}

/*
Predicado: "Duas Sessões ocorrem no mesmo Horário se ambas apontam para o mesmo Horário."
*/
pred horariosIguais[s1, s2: Sessao] {
    s1.horario = s2.horario
}

/*
Predicado: "Um Aluno, Monitor ou não, está em duas Sessões ao mesmo tempo se ele está simultaneamente
na lista de participantes delas."
*/
pred alunoEmDuasSessoes[a: Aluno, s1, s2: Sessao] {
    a in envolvidosSessao[s1]
    a in envolvidosSessao[s2]
}



// FUNÇÕES:

// Retorna o conjunto de Alunos vinculados a uma Sessão, seja como participante, seja como Monitor responsável por ela.
fun envolvidosSessao[s: Sessao]: set Aluno {
    s.alunosSessao + s.monitorSessao
}



// ASSERÇÕES:

/*
Assegura que se existem Sessões da mesma Disciplina ocorrendo no mesmo Horário, elas
não podem ser ministrados por um mesmo Monitor. 
*/
assert sessoesSimultaneasMonitoresDiferentes {
    all disj s1, s2: Sessao |
        (s1.disciplinaSessao = s2.disciplinaSessao and s1.horario = s2.horario) 
        implies s1.monitorSessao != s2.monitorSessao
}
check sessoesSimultaneasMonitoresDiferentes for 7 but 5 int

/*
Assegura  que a Habilitação (Disciplina) de um Monitor não está
na sua lista de matrículas ativas.
*/
assert habilitacaoForaDaMatricula {
    all m: Monitor | m.habilitacao not in m.matriculas
}
check habilitacaoForaDaMatricula for 7 but 5 int



run {
    #Sessao >= 2
    #Aluno >= 4
} for 7 but 5 int
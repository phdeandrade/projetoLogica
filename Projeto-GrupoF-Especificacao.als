sig Aluno {
    matriculas: set Disciplina
}
sig Monitor extends Aluno {
    habilitacao: one Disciplina
}

sig Disciplina {
    monitoresDisciplina: set Monitor
}

sig Sala {}

sig Horario {}

sig Sessao {
    disciplinaSessao: one Disciplina,
    monitorSessao: one Monitor,
    sala: one Sala,
    horario: one Horario,
    alunosSessao: set Aluno
}

fact regrasAluno {
    all aluno: Aluno | #aluno.matriculas >= 3
}

// nesse fact aqui eu adicionei que o monitor tem q estar na lista
// de alguma disciplina, achei melhor do que colocar no fact novo que fiz
// mas fiquem a vontade pra mudar, só tem q ter essa condicao
fact regrasMonitor {
    all monitor: Monitor {
        monitorHabilitado[monitor]
        monitorEstaNaListaDeAlgumaDisciplina[monitor]
    }
}

// aqui fiz um fato que corrige o bug que encontramos ontem
// antes não era obrigatorio que todos os monitores que tinham
// habilitacao para a disciplina estivessem na lista de monitores
// da disciplina, com esse fact da certo
fact regraMonitoresDisciplinaCorretos {
    all disciplina: Disciplina {
        disciplinaTemMonitoresComHabilitacaoCorreta[disciplina]
    }
}

fact regrasSessao {
    all sessao: Sessao {
        monitorHabilitadoSessao[sessao.monitorSessao, sessao]
        respeitaLimiteSessao[sessao]
    }
}

fact regrasParticipacao {
    all sessao: Sessao {
        participantesValidos[sessao]
    }
}

fact choqueDeSala { 
    no disj sessao1, sessao2: Sessao {
        salasConflitam[sessao1, sessao2]
        horariosIguais[sessao1, sessao2]
    } 
}

fact choqueDeHorarios {
    no disj sessao1, sessao2: Sessao {
        horariosIguais[sessao1, sessao2]
        some aluno: Aluno {
            alunoEmDuasSessoes[aluno, sessao1, sessao2]
        }
    }
}

pred monitorHabilitado[m: Monitor] {
    #m.habilitacao = 1
    m.habilitacao not in m.matriculas
}

pred monitorHabilitadoSessao[m: Monitor, s: Sessao] {
    monitorHabilitado[m]
    m.habilitacao = s.disciplinaSessao
}

// aqui ta o predicado que usei pra organizar o fact la em cima
pred monitorEstaNaListaDeAlgumaDisciplina[m: Monitor] {
    m in m.habilitacao.monitoresDisciplina
}

// aqui checa se os monitores da disciplina sao habilitados pra ela mesmo
pred disciplinaTemMonitoresComHabilitacaoCorreta[d: Disciplina] {
    all m: d.monitoresDisciplina {
        m.habilitacao = d
    }
}

pred respeitaLimiteSessao[s: Sessao] {
    #s.disciplinaSessao = 1
    #s.sala = 1
    #s.monitorSessao = 1
    #s.alunosSessao >= 1 and #s.alunosSessao <= 10
}

pred participantesValidos[s: Sessao] {
    all aluno: s.alunosSessao {
        s.disciplinaSessao in aluno.matriculas
        s.monitorSessao != aluno
    }
}

pred salasConflitam[s1, s2: Sessao] {
    s1.sala = s2.sala
}

pred horariosIguais[s1, s2: Sessao] {
    s1.horario = s2.horario
}

pred alunoEmDuasSessoes[a: Aluno, s1, s2: Sessao] {
    a in s1.alunosSessao or a = s1.monitorSessao
    a in s2.alunosSessao or a = s2.monitorSessao
}

run {
    #Sessao >= 2
    #Aluno >= 4
} for 7 but 5 int
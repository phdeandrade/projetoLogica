// ASSINATURAS

// Representa os alunos e os conjuntos de disciplinas que cursam e já concluíram.
sig Aluno {
    matriculas: set Disciplina,
    disciplinasPagas: set Disciplina
}

// Especialização de Aluno que atua como monitor, habilitado em uma única disciplina.
sig Monitor extends Aluno {
    habilitacao: one Disciplina
}

// Representa as disciplinas e a lista oficial de monitores vinculados a elas.
sig Disciplina {
    monitoresDisciplina: set Monitor
}

// Representam o espaço físico e o momento temporal das sessões.
sig Sala {}
sig Horario {}

// Evento que agrupa as restrições de disciplina, monitor, espaço, tempo e público.
sig Sessao {
    disciplinaSessao: one Disciplina,
    monitorSessao: one Monitor,
    sala: one Sala,
    horario: one Horario,
    alunosSessao: set Aluno
}


// FATOS

// Garante o mínimo de 3 matrículas ativas e que disciplinas já pagas não sejam cursadas novamente.
fact regrasAluno {
    all aluno: Aluno {
        #aluno.matriculas >= 3
        no (aluno.matriculas & aluno.disciplinasPagas)
    }
}

// Garante que todo monitor possui habilitação válida e consta na lista oficial de alguma disciplina.
fact regrasMonitor {
    all monitor: Monitor {
        monitorHabilitado[monitor]
        monitorEstaNaListaDeAlgumaDisciplina[monitor]
    }
}

// Garante a integridade bidirecional: a disciplina só aceita monitores habilitados para ela.
fact regraMonitoresDisciplinaCorretos {
    all disciplina: Disciplina {
        disciplinaTemMonitoresComHabilitacaoCorreta[disciplina]
    }
}

// Aplica as regras de limite estrutural e a correta alocação do monitor para a sessão.
fact regrasSessao {
    all sessao: Sessao {
        monitorHabilitadoSessao[sessao.monitorSessao, sessao]
        respeitaLimiteSessao[sessao]
    }
}

// Impõe que apenas alunos elegíveis participem das sessões de monitoria.
fact regrasParticipacao {
    all sessao: Sessao {
        participantesValidos[sessao]
    }
}

// Impede que o sistema aloque duas sessões distintas na mesma sala simultaneamente.
fact choqueDeSala { 
    no disj sessao1, sessao2: Sessao {
        salasConflitam[sessao1, sessao2]
        horariosIguais[sessao1, sessao2]
    } 
}

// Impede a onipresença: um mesmo aluno/monitor não pode estar em dois eventos ao mesmo tempo.
fact choqueDeHorarios {
    no disj sessao1, sessao2: Sessao {
        horariosIguais[sessao1, sessao2]
        some aluno: Aluno {
            alunoEmDuasSessoes[aluno, sessao1, sessao2]
        }
    }
}


// PREDICADOS

// Verifica se a habilitação do monitor provém das disciplinas que ele já cursou.
pred monitorHabilitado[m: Monitor] {
    m.habilitacao in disciplinasAptasParaMonitoria[m]
}

// Valida se o monitor alocado para a sessão é habilitado para a disciplina alvo.
pred monitorHabilitadoSessao[m: Monitor, s: Sessao] {
    monitorHabilitado[m]
    m.habilitacao = s.disciplinaSessao
}

// Confirma o vínculo do monitor com a lista de monitores da sua disciplina de habilitação.
pred monitorEstaNaListaDeAlgumaDisciplina[m: Monitor] {
    m in m.habilitacao.monitoresDisciplina
}

// Confirma que todos os monitores vinculados a uma disciplina são, de fato, focados nela.
pred disciplinaTemMonitoresComHabilitacaoCorreta[d: Disciplina] {
    all m: d.monitoresDisciplina {
        m.habilitacao = d
    }
}

// Define a cardinalidade exata dos atributos da sessão e restringe a lotação entre 1 e 10 participantes.
pred respeitaLimiteSessao[s: Sessao] {
    #s.disciplinaSessao = 1
    #s.sala = 1
    #s.monitorSessao = 1
    #s.alunosSessao >= 1 and #s.alunosSessao <= 10
}

// Valida se o aluno está matriculado na disciplina da sessão e proíbe o monitor de ser aluno.
pred participantesValidos[s: Sessao] {
    all aluno: s.alunosSessao {
        s.disciplinaSessao in aluno.matriculas
        s.monitorSessao != aluno
    }
}

// Identifica se há conflito espacial entre duas sessões.
pred salasConflitam[s1, s2: Sessao] {
    s1.sala = s2.sala
}

// Identifica se há simultaneidade temporal entre duas sessões.
pred horariosIguais[s1, s2: Sessao] {
    s1.horario = s2.horario
}

// Identifica se um indivíduo está envolvido (como monitor ou participante) em duas sessões ao mesmo tempo.
pred alunoEmDuasSessoes[a: Aluno, s1, s2: Sessao] {
    a in s1.alunosSessao or a = s1.monitorSessao
    a in s2.alunosSessao or a = s2.monitorSessao
}


// FUNÇÕES

// Retorna o conjunto de disciplinas já pagas pelo aluno, subtraindo as matrículas ativas.
fun disciplinasAptasParaMonitoria[a: Aluno]: set Disciplina {
    a.disciplinasPagas - a.matriculas
}


// ASSERÇÕES E VALIDAÇÕES

// Teste de Conflito de Interesse: Confirma que o modelo impossibilita um monitor de assistir à própria aula.
assert papelExclusivo {
    all s: Sessao | s.monitorSessao not in s.alunosSessao
}
check papelExclusivo for 5

// Teste de Onipresença: Confirma que as regras impedem choques de horário para qualquer indivíduo.
assert semOnipresenca {
    no s1, s2: Sessao, a: Aluno |
        s1 != s2 and
        s1.horario = s2.horario and
        (a in s1.alunosSessao or a = s1.monitorSessao) and
        (a in s2.alunosSessao or a = s2.monitorSessao)
}
check semOnipresenca for 5


// COMANDOS DE EXECUÇÃO

// Gera um cenário funcional garantindo a criação de pelo menos 2 sessões e 4 alunos, usando inteiros de 5 bits.
run {
    #Sessao >= 2
    #Aluno >= 4
} for 7 but 5 int
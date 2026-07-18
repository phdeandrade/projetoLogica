sig Aluno {
    matriculas: set Disciplina
}
sig Monitor extends Aluno {
    habilitacao: one Disciplina 
}

sig Disciplina {
    monitores: set Monitor
}

sig Sala {}

sig Horario {}

sig Sessao {
    disciplina: one Disciplina,
    monitor: one Monitor,
    sala: one Sala,
    horario: one Horario,
    alunos: set Aluno
}

fact regrasAluno {
    all aluno: Aluno | #aluno.matriculas >= 3
}

fact regrasMonitor {
    all monitor: Monitor {
        #monitor.habilitacao = 1
        monitor.habilitacao not in monitor.matriculas 
    }
}

fact regrasSessao {
    all sessao: Sessao {
        #sessao.disciplina = 1
        #sessao.sala = 1
        #sessao.monitor = 1
        sessao.monitor.habilitacao = sessao.disciplina
        #sessao.alunos >= 1 and #sessao.alunos <= 10
    }
}

fact regrasParticipacao {
    all sessao: Sessao {
        all aluno: sessao.alunos {
            sessao.disciplina in aluno.matriculas
            sessao.monitor != aluno
        }
    }
}

fact choqueDeSala { 
    no sessao1, sessao2: Sessao {
        sessao1 != sessao2
        sessao1.sala = sessao2.sala
        sessao1.horario = sessao2.horario
    } 
}

fact choqueDeHorarios {
    no sessao1, sessao2: Sessao {
        sessao1 != sessao2
        sessao1.sala = sessao2.sala
        sessao1.horario = sessao2.horario
        all aluno1: sessao1.alunos {
            all aluno2: sessao2.alunos {
                aluno1 = aluno2
            }
        }
    } 
}

fact choqueDeHorarios {
    no sessao1, sessao2: Sessao {
        sessao1 != sessao2
        sessao1.horario = sessao2.horario
        some aluno: Aluno {
            aluno in sessao1.alunos or aluno = sessao1.monitor
            aluno in sessao2.alunos or aluno = sessao2.monitor
        }
    }
}
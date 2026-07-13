//Teste para ver o Alloy funcionando

abstract sig Objeto {}

sig Arquivo extends Objeto {}

sig Diretorio extends Objeto {
    conteudo: set Objeto
}

one sig Raiz extends Diretorio {}

fact RegrasDoSistema {
    all o: Objeto - Raiz | one d: Diretorio | o in d.conteudo
    no Raiz.(~conteudo)
    all d: Diretorio | d not in d.^conteudo
}

assert SemDiretoriosOrfaos {
    all d: Diretorio - Raiz | d in Raiz.^conteudo
}

GerarExemplo: run {} for 3 but exactly 2 Diretorio

check SemDiretoriosOrfaos for 4

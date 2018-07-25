module restaurante

sig Restaurante {
	variacoes: one Cardapio
}

sig Cardapio {
	pratos: set Prato
}

sig Preco {}

abstract sig Prato {
	acompanhamentos: set Acompanhamento,
	preco: one Preco
}

abstract sig Acompanhamento {}

sig Fruta extends Acompanhamento {}

sig Suco extends Acompanhamento {}

sig PorcaoSalada extends Acompanhamento {}

sig Vegetariano extends Prato {}

sig Vegano extends Prato {}

sig Carne extends Prato {}

abstract sig Refeicao {
	pratos: set Prato
}

sig Almoco extends Refeicao {}

sig Janta extends Refeicao {}

sig Cliente {
	refeicao: set Refeicao
}

pred show {}

run show

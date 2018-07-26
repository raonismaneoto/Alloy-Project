module restaurante

sig Restaurante {
	cardapioVegano: set PratoVegano,
	cardapioVegetariano: set PratoVegetariano,
	cardapioComCarne: set PratoComCarne
}


sig Preco {}

abstract sig Prato {
	acompanhamento: one Acompanhamento,
	preco: one Preco
}

abstract sig Acompanhamento {}

sig Fruta extends Acompanhamento {}

sig Suco extends Acompanhamento {}

sig PorcaoSalada extends Acompanhamento {}

sig PratoVegetariano extends Prato {}

sig PratoVegano extends Prato {}

sig PratoComCarne extends Prato {}

abstract sig Refeicao {
	pratos: set Prato
}

sig Almoco extends Refeicao {
}

sig Janta extends Refeicao {}

sig Cliente {
	pedidoAlmoco: lone Almoco,
	pedidoJantar: lone Janta
}

fact quantidadeDePratosCardapio {
	#(Restaurante.cardapioVegano) = 10
	#(Restaurante.cardapioVegetariano) = 10
	#(Restaurante.cardapioComCarne) = 10
}

fact acompanhamentos {
	all a: PratoVegetariano.acompanhamento + PratoVegano.acompanhamento | a in Fruta + Suco
	all a: PratoComCarne.acompanhamento | a in PorcaoSalada + Suco
}

fact quantidadeDePratosRefeicao {
	#(Refeicao.pratos) = 3
}

assert apenasPratosDoTipoCorreto {
	all p: Restaurante.cardapioVegano | p in PratoVegano
	all p: Restaurante.cardapioComCarne | p in PratoComCarne
	all p: Restaurante.cardapioVegetariano | p in PratoVegetariano
}

check apenasPratosDoTipoCorreto

pred show {}

run show

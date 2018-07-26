module restaurante
----------------------------------- Assinaturas -----------------------

one sig Restaurante {
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

------------------------------------- Fatos -------------------------------

fact quantidadeDePratosCardapio {
	#Restaurante.cardapioVegano > 1 and #Restaurante.cardapioVegano <= 10
	#Restaurante.cardapioVegetariano > 1 and #Restaurante.cardapioVegetariano <= 10
	#Restaurante.cardapioComCarne > 1 and #Restaurante.cardapioComCarne <= 10
}

fact acompanhamentos {
	all a: PratoVegetariano.acompanhamento + PratoVegano.acompanhamento | a in Fruta + Suco
	all a: PratoComCarne.acompanhamento | a in PorcaoSalada + Suco
}

fact quantidadeDePratosRefeicao {
	all r: Refeicao | #r.pratos <= 3
}

fact cliente_tem_pedido {
	all c: Cliente | some c.pedidoAlmoco + c.pedidoJantar
}

fact limite_refeicoes {
	all c: Cliente | some c.pedidoAlmoco and #get_pedidos_almoco[c] <= 3
	all c: Cliente | some c.pedidoJantar and #get_pedidos_jantar[c] <= 3
}

fact variacoes_almoco {
	all c: Cliente | limite_refeicao_almoco[c]
}

fact variacoes_jantar {
	all c: Cliente | limite_refeicao_jantar[c]
}

----------------------------------- Predicados -----------------------------

pred limite_refeicao_almoco[c : Cliente] {
    some c.pedidoAlmoco and
	((#get_pedidos_almoco_vegetariano[c] <= 2 and #get_pedidos_almoco_vegano[c] <= 1) or
	(#get_pedidos_almoco_vegetariano[c] <= 1 and #get_pedidos_almoco_vegano[c] <= 2) or
	(#get_pedidos_almoco_com_carne[c] <= 2 and #get_pedidos_almoco_vegetariano[c] <= 1))
}

pred limite_refeicao_jantar[c : Cliente] {
	some c.pedidoJantar and
	((#get_pedidos_jantar_vegetariano[c] <= 2 and #get_pedidos_jantar_vegano[c] <= 1) or
	(#get_pedidos_jantar_vegetariano[c] <= 1 and #get_pedidos_jantar_vegano[c] <= 2) or
	(#get_pedidos_jantar_com_carne[c] <= 2 and #get_pedidos_jantar_vegetariano[c] <= 1))
}

----------------------------------- Funcoes ----------------------------------

fun get_pedidos_almoco[c : Cliente]: set Prato {
	c.pedidoAlmoco.pratos
}

fun get_pedidos_jantar[c : Cliente]: set Prato {
	c.pedidoJantar.pratos
}

fun get_pedidos_almoco_vegano[c : Cliente]: set PratoVegano {
	c.pedidoAlmoco.pratos & PratoVegano
}

fun get_pedidos_almoco_vegetariano[c : Cliente]: set PratoVegetariano {
	c.pedidoAlmoco.pratos & PratoVegetariano
}

fun get_pedidos_almoco_com_carne[c : Cliente]: set PratoComCarne {
	c.pedidoAlmoco.pratos & PratoComCarne
}

fun get_pedidos_jantar_vegano[c : Cliente]: set PratoVegano {
	c.pedidoJantar.pratos & PratoVegano
}

fun get_pedidos_jantar_vegetariano[c : Cliente]: set PratoVegetariano {
	c.pedidoJantar.pratos & PratoVegetariano
}

fun get_pedidos_jantar_com_carne[c : Cliente]: set PratoComCarne {
	c.pedidoJantar.pratos & PratoComCarne
}


----------------------------------- Testes -------------------------------------

assert apenasPratosDoTipoCorreto {
	all p: Restaurante.cardapioVegano | p in PratoVegano
	all p: Restaurante.cardapioComCarne | p in PratoComCarne
	all p: Restaurante.cardapioVegetariano | p in PratoVegetariano
}

----------------------------------- Checks --------------------------------------

check apenasPratosDoTipoCorreto

----------------------------------- Run --------------------------------------------
pred show[] {}
run show for 10

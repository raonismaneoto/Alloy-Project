module restaurante
----------------------------------- Assinaturas -----------------------

one sig Restaurante {
	cardapioVegano: set PratoVegano,
	cardapioVegetariano: set PratoVegetariano,
	cardapioComCarne: set PratoComCarne,
	clientes: set Cliente
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
	all a: Acompanhamento | one a.~acompanhamento
}

fact quantidadeDePratosRefeicao {
	all r: Refeicao | #r.pratos <= 3 and #r.pratos >= 1
}

fact restricoes_cliente {
	all c: Cliente | some c.pedidoAlmoco + c.pedidoJantar
	all c: Cliente | #(c.~clientes) = 1
}

fact limite_refeicoes {
	all c: Cliente |  #get_pedidos_almoco[c] <= 3
	all c: Cliente |  #get_pedidos_jantar[c] <= 3
}

fact variacoes_almoco {
	all c: Cliente | limite_refeicao_almoco[c]
	all a: Almoco | #(a.~pedidoAlmoco) = 1
}

fact variacoes_jantar {
	all c: Cliente | limite_refeicao_jantar[c]
	all j: Janta | #(j.~pedidoJantar) = 1
}

fact restricoes_de_prato {
	all p: Prato | #(p.preco) = 1
	all p: Prato | #(p.~pratos) = 1
	all p: Prato | p in Restaurante.cardapioVegano + Restaurante.cardapioVegetariano + Restaurante.cardapioComCarne
}

fact restricoes_preco {
	all p: Preco | preco_sempre_ligado[p]
}

----------------------------------- Predicados -----------------------------

pred limite_refeicao_almoco[c : Cliente] {
	((#get_pedidos_almoco_vegetariano[c] <= 2 and #get_pedidos_almoco_vegano[c] <= 1 and
	 #get_pedidos_almoco_com_carne[c] = 0) or
	(#get_pedidos_almoco_vegetariano[c] <= 1 and #get_pedidos_almoco_vegano[c] <= 2 and
	 #get_pedidos_almoco_com_carne[c] = 0) or
	(#get_pedidos_almoco_com_carne[c] <= 2 and #get_pedidos_almoco_vegetariano[c] <= 1 and
	 #get_pedidos_almoco_vegano[c] = 0))
}

pred limite_refeicao_jantar[c : Cliente] {
	((#get_pedidos_jantar_vegetariano[c] <= 2 and #get_pedidos_jantar_vegano[c] <= 1  and
	 #get_pedidos_jantar_com_carne[c] = 0) or
	(#get_pedidos_jantar_vegetariano[c] <= 1 and #get_pedidos_jantar_vegano[c] <= 2  and
	 #get_pedidos_jantar_com_carne[c] = 0) or
	(#get_pedidos_jantar_com_carne[c] <= 2 and #get_pedidos_jantar_vegetariano[c] <= 1 and
	 #get_pedidos_jantar_vegano[c] = 0))
}

pred preco_sempre_ligado[p : Preco] {
	some p.~preco
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

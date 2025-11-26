# Apister
Uma ferramenta usada para testes no desenvolvimento de `APIs`, com as funcionalidades mais básicas de outras ferramentas populares como o `Insomnia` e `Postman`. Desenvolvida durante a disciplina de `Linguagem de Programação II` ofertada na `UFRN` no `IMD`.

# Links
- [Apresentação](https://youtu.be/TEhxNYLkJ60);
- [Projeto](https://github.com/users/L-Marcel/projects/4).

# Contribuidores
- [Antonio Henrique](https://github.com/Henrique-Barbosaa);
- [Artur Nobre](https://github.com/x0cuoxq8w5);
- [Lucas Marcel](https://github.com/L-Marcel).

# Instruções de execução
Para executar você precisará do `Java JDK 23.0.1`, mas é provável que o `Java JDK 21` também funcione. Além disso, será necessário ter o `Apache Maven 3.9.9` instalado, é possível que uma versão superior também funcione.

Cumprindo com esses dois requisitos, basta executar o seguinte comando na raíz do projeto clonado:
```cmd
mvn javafx:run
```

# Executar OpenJML

**Antes de tudo, deve renomear o arquivo *module-info.java* para que ele não esteja incluso na compilação do OpenJML. \
Pode renomear para *module-info.java.bak*, por exemplo.**

Comando para crair o arquivo classpath.txt, que possui o caminho para as dependências do JavaFX. \

```cmd
mvn dependency:build-classpath -Dmdep.outputFile=classpath.txt
```

Comando para executar o OpenJML num arquivo, por exemplo, Node.java.

```cmd
openjml -esc -sourcepath src/main/java -classpath $(cat classpath.txt) -progress src/main/java/app/core/Node.java
```

A flag *-progress* serve para acompanhar quais funções e classes estão a ser analisadas no momento.

**Ambos os comandos devem ser executados no diretório raiz do projeto.**
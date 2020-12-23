%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0723+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fQUF2KAfb5

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:23 EST 2020

% Result     : Theorem 56.11s
% Output     : Refutation 56.11s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 184 expanded)
%              Number of leaves         :   13 (  54 expanded)
%              Depth                    :   18
%              Number of atoms          :  905 (2090 expanded)
%              Number of equality atoms :   68 ( 159 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(t3_ordinal1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ B @ C )
        & ( r2_hidden @ C @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ B @ C )
          & ( r2_hidden @ C @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t3_ordinal1])).

thf('0',plain,(
    r2_hidden @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 )
      | ( r2_hidden @ X5 @ X9 )
      | ( X9
       != ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('2',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X5 @ ( k1_enumset1 @ X8 @ X7 @ X6 ) )
      | ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X4 )
      | ( X1 = X2 )
      | ( X1 = X3 )
      | ( X1 = X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X5 @ ( k1_enumset1 @ X8 @ X7 @ X6 ) )
      | ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t7_tarski,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ B )
                    & ( r2_hidden @ D @ C ) ) ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 )
      | ( r2_hidden @ ( sk_C @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( zip_tseitin_0 @ X10 @ X6 @ X7 @ X8 )
      | ( X9
       != ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('8',plain,(
    ! [X6: $i,X7: $i,X8: $i,X10: $i] :
      ( ~ ( zip_tseitin_0 @ X10 @ X6 @ X7 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) @ X0 @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( sk_C @ ( k1_enumset1 @ X0 @ X1 @ X2 ) )
        = X0 )
      | ( ( sk_C @ ( k1_enumset1 @ X0 @ X1 @ X2 ) )
        = X1 )
      | ( ( sk_C @ ( k1_enumset1 @ X0 @ X1 @ X2 ) )
        = X2 )
      | ( zip_tseitin_0 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 != X2 )
      | ( zip_tseitin_0 @ X3 @ X1 @ X2 @ X0 )
      | ( ( sk_C @ ( k1_enumset1 @ X0 @ X2 @ X1 ) )
        = X1 )
      | ( ( sk_C @ ( k1_enumset1 @ X0 @ X2 @ X1 ) )
        = X2 ) ) ),
    inference(eq_fact,[status(thm)],['10'])).

thf('12',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( ( sk_C @ ( k1_enumset1 @ X2 @ X2 @ X1 ) )
        = X2 )
      | ( ( sk_C @ ( k1_enumset1 @ X2 @ X2 @ X1 ) )
        = X1 )
      | ( zip_tseitin_0 @ X3 @ X1 @ X2 @ X2 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('14',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ~ ( zip_tseitin_0 @ X0 @ X2 @ X3 @ X0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ ( k1_enumset1 @ X0 @ X0 @ X1 ) )
        = X1 )
      | ( ( sk_C @ ( k1_enumset1 @ X0 @ X0 @ X1 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 )
      | ( r2_hidden @ ( sk_C @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      | ( ( sk_C @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
        = X1 )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ~ ( zip_tseitin_0 @ X0 @ X2 @ X3 @ X0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ ( k1_enumset1 @ X0 @ X0 @ X1 ) )
        = X0 )
      | ( r2_hidden @ X1 @ ( k1_enumset1 @ X0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( r2_hidden @ X14 @ ( sk_C @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( sk_C @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_enumset1 @ X0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_enumset1 @ X0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 )
      | ( r2_hidden @ X0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_enumset1 @ sk_C_1 @ sk_C_1 @ X0 ) )
      | ( zip_tseitin_0 @ sk_B @ X0 @ sk_C_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','23'])).

thf('25',plain,(
    r2_hidden @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X5 @ ( k1_enumset1 @ X8 @ X7 @ X6 ) )
      | ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ ( k1_enumset1 @ X0 @ X0 @ X1 ) )
        = X1 )
      | ( ( sk_C @ ( k1_enumset1 @ X0 @ X0 @ X1 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( sk_C @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['20'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( ( sk_C @ ( k1_enumset1 @ X0 @ X0 @ X1 ) )
        = X1 )
      | ~ ( r2_hidden @ X2 @ ( k1_enumset1 @ X0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 )
      | ( ( sk_C @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
        = X0 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k1_enumset1 @ sk_C_1 @ sk_C_1 @ X0 ) )
        = X0 )
      | ( zip_tseitin_0 @ sk_B @ X0 @ sk_C_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X2 )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('33',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ~ ( zip_tseitin_0 @ X2 @ X2 @ X3 @ X0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( sk_C @ ( k1_enumset1 @ sk_C_1 @ sk_C_1 @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( sk_C @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['20'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_enumset1 @ sk_C_1 @ sk_C_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( zip_tseitin_0 @ sk_B @ sk_B @ sk_C_1 @ sk_C_1 )
    | ~ ( r2_hidden @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['24','36'])).

thf('38',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ~ ( zip_tseitin_0 @ X2 @ X2 @ X3 @ X0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('39',plain,(
    ~ ( r2_hidden @ sk_B @ sk_B ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    r2_hidden @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X5 @ ( k1_enumset1 @ X8 @ X7 @ X6 ) )
      | ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('43',plain,(
    r2_hidden @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X5 @ ( k1_enumset1 @ X8 @ X7 @ X6 ) )
      | ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( sk_C @ ( k1_enumset1 @ X0 @ X1 @ X2 ) )
        = X0 )
      | ( ( sk_C @ ( k1_enumset1 @ X0 @ X1 @ X2 ) )
        = X1 )
      | ( ( sk_C @ ( k1_enumset1 @ X0 @ X1 @ X2 ) )
        = X2 )
      | ( zip_tseitin_0 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('46',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ~ ( zip_tseitin_0 @ X0 @ X2 @ X3 @ X0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ ( k1_enumset1 @ X0 @ X1 @ X2 ) )
        = X2 )
      | ( ( sk_C @ ( k1_enumset1 @ X0 @ X1 @ X2 ) )
        = X1 )
      | ( ( sk_C @ ( k1_enumset1 @ X0 @ X1 @ X2 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( sk_C @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['20'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X0 )
      | ( ( sk_C @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
        = X2 )
      | ( ( sk_C @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
        = X1 )
      | ~ ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 )
      | ( ( sk_C @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
        = X1 )
      | ( ( sk_C @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
        = X2 )
      | ~ ( r2_hidden @ X3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ ( k1_enumset1 @ X1 @ X0 @ sk_C_1 ) )
        = X1 )
      | ( ( sk_C @ ( k1_enumset1 @ X1 @ X0 @ sk_C_1 ) )
        = X0 )
      | ( zip_tseitin_0 @ sk_B @ sk_C_1 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X3 )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('53',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ~ ( zip_tseitin_0 @ X3 @ X2 @ X3 @ X0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k1_enumset1 @ X0 @ sk_B @ sk_C_1 ) )
        = sk_B )
      | ( ( sk_C @ ( k1_enumset1 @ X0 @ sk_B @ sk_C_1 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X5 @ ( k1_enumset1 @ X8 @ X7 @ X6 ) )
      | ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ ( k1_enumset1 @ X0 @ X1 @ X2 ) )
        = X2 )
      | ( ( sk_C @ ( k1_enumset1 @ X0 @ X1 @ X2 ) )
        = X1 )
      | ( ( sk_C @ ( k1_enumset1 @ X0 @ X1 @ X2 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( sk_C @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['20'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X0 )
      | ( ( sk_C @ ( k1_enumset1 @ X2 @ X0 @ X1 ) )
        = X2 )
      | ( ( sk_C @ ( k1_enumset1 @ X2 @ X0 @ X1 ) )
        = X1 )
      | ~ ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 )
      | ( ( sk_C @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
        = X0 )
      | ( ( sk_C @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
        = X2 )
      | ~ ( r2_hidden @ X3 @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ ( k1_enumset1 @ X1 @ sk_B @ X0 ) )
        = X1 )
      | ( ( sk_C @ ( k1_enumset1 @ X1 @ sk_B @ X0 ) )
        = X0 )
      | ( zip_tseitin_0 @ sk_A @ X0 @ sk_B @ X1 ) ) ),
    inference('sup-',[status(thm)],['55','60'])).

thf('62',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ~ ( zip_tseitin_0 @ X0 @ X2 @ X3 @ X0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k1_enumset1 @ sk_A @ sk_B @ X0 ) )
        = X0 )
      | ( ( sk_C @ ( k1_enumset1 @ sk_A @ sk_B @ X0 ) )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( sk_B = sk_C_1 )
    | ( ( sk_C @ ( k1_enumset1 @ sk_A @ sk_B @ sk_C_1 ) )
      = sk_A )
    | ( ( sk_C @ ( k1_enumset1 @ sk_A @ sk_B @ sk_C_1 ) )
      = sk_A ) ),
    inference('sup+',[status(thm)],['54','63'])).

thf('65',plain,
    ( ( ( sk_C @ ( k1_enumset1 @ sk_A @ sk_B @ sk_C_1 ) )
      = sk_A )
    | ( sk_B = sk_C_1 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( sk_C @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['20'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_B = sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_enumset1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ X0 @ sk_C_1 @ sk_B @ sk_A )
      | ( sk_B = sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','67'])).

thf('69',plain,
    ( ( sk_B = sk_C_1 )
    | ( zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['41','68'])).

thf('70',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ~ ( zip_tseitin_0 @ X2 @ X2 @ X3 @ X0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('71',plain,(
    sk_B = sk_C_1 ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    r2_hidden @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['40','71'])).

thf('73',plain,(
    $false ),
    inference(demod,[status(thm)],['39','72'])).


%------------------------------------------------------------------------------

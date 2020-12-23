%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.a0bizooUrv

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:40 EST 2020

% Result     : Theorem 5.72s
% Output     : Refutation 5.72s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 524 expanded)
%              Number of leaves         :   16 ( 161 expanded)
%              Depth                    :   19
%              Number of atoms          : 1134 (4729 expanded)
%              Number of equality atoms :   96 ( 423 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('3',plain,(
    ! [X13: $i] :
      ( ( k3_xboole_0 @ X13 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('7',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('11',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('15',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['0','15'])).

thf(t83_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_xboole_0 @ A @ B )
      <=> ( ( k4_xboole_0 @ A @ B )
          = A ) ) ),
    inference('cnf.neg',[status(esa)],[t83_xboole_1])).

thf('17',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['17'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('22',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('23',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['19'])).

thf('25',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['17'])).

thf('27',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['20','25','26'])).

thf('28',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(simpl_trail,[status(thm)],['18','27'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('29',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('30',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('32',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('33',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['30','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('38',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('39',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_B @ k1_xboole_0 ) )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ k1_xboole_0 ) @ X0 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ k1_xboole_0 ) ) @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','42'])).

thf('44',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('45',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ k1_xboole_0 ) @ ( k4_xboole_0 @ sk_B @ sk_A ) ) )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) @ ( k4_xboole_0 @ sk_B @ k1_xboole_0 ) ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ k1_xboole_0 ) @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) @ ( k4_xboole_0 @ sk_B @ k1_xboole_0 ) ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ k1_xboole_0 ) @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('48',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ k1_xboole_0 ) @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('50',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ k1_xboole_0 ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B @ k1_xboole_0 ) @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('52',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['54'])).

thf('56',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('57',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['53','57'])).

thf('59',plain,(
    ! [X13: $i] :
      ( ( k3_xboole_0 @ X13 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','67'])).

thf('69',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B @ k1_xboole_0 ) @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['54'])).

thf('76',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['54'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('82',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('84',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('85',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ X3 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X3 )
      | ( X3
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X3 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X2 )
      | ( X2
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X2 )
      | ( X2
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('97',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['74','82','83','95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('99',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('100',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['98','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('108',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['97','109'])).

thf('111',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('112',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['20','25'])).

thf('113',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['111','112'])).

thf('114',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['110','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.a0bizooUrv
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:45:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 5.72/5.91  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.72/5.91  % Solved by: fo/fo7.sh
% 5.72/5.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.72/5.91  % done 4197 iterations in 5.446s
% 5.72/5.91  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.72/5.91  % SZS output start Refutation
% 5.72/5.91  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 5.72/5.91  thf(sk_A_type, type, sk_A: $i).
% 5.72/5.91  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 5.72/5.91  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.72/5.91  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.72/5.91  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 5.72/5.91  thf(sk_B_type, type, sk_B: $i).
% 5.72/5.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.72/5.91  thf(d5_xboole_0, axiom,
% 5.72/5.91    (![A:$i,B:$i,C:$i]:
% 5.72/5.91     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 5.72/5.91       ( ![D:$i]:
% 5.72/5.91         ( ( r2_hidden @ D @ C ) <=>
% 5.72/5.91           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 5.72/5.91  thf('0', plain,
% 5.72/5.91      (![X3 : $i, X4 : $i, X7 : $i]:
% 5.72/5.91         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 5.72/5.91          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 5.72/5.91          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 5.72/5.91      inference('cnf', [status(esa)], [d5_xboole_0])).
% 5.72/5.91  thf(t48_xboole_1, axiom,
% 5.72/5.91    (![A:$i,B:$i]:
% 5.72/5.91     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 5.72/5.91  thf('1', plain,
% 5.72/5.91      (![X16 : $i, X17 : $i]:
% 5.72/5.91         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 5.72/5.91           = (k3_xboole_0 @ X16 @ X17))),
% 5.72/5.91      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.72/5.91  thf(commutativity_k3_xboole_0, axiom,
% 5.72/5.91    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 5.72/5.91  thf('2', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.72/5.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.72/5.91  thf(t2_boole, axiom,
% 5.72/5.91    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 5.72/5.91  thf('3', plain,
% 5.72/5.91      (![X13 : $i]: ((k3_xboole_0 @ X13 @ k1_xboole_0) = (k1_xboole_0))),
% 5.72/5.91      inference('cnf', [status(esa)], [t2_boole])).
% 5.72/5.91  thf('4', plain,
% 5.72/5.91      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 5.72/5.91      inference('sup+', [status(thm)], ['2', '3'])).
% 5.72/5.91  thf('5', plain,
% 5.72/5.91      (![X16 : $i, X17 : $i]:
% 5.72/5.91         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 5.72/5.91           = (k3_xboole_0 @ X16 @ X17))),
% 5.72/5.91      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.72/5.91  thf('6', plain,
% 5.72/5.91      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 5.72/5.91         (~ (r2_hidden @ X6 @ X5)
% 5.72/5.91          | ~ (r2_hidden @ X6 @ X4)
% 5.72/5.91          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 5.72/5.91      inference('cnf', [status(esa)], [d5_xboole_0])).
% 5.72/5.91  thf('7', plain,
% 5.72/5.91      (![X3 : $i, X4 : $i, X6 : $i]:
% 5.72/5.91         (~ (r2_hidden @ X6 @ X4)
% 5.72/5.91          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 5.72/5.91      inference('simplify', [status(thm)], ['6'])).
% 5.72/5.91  thf('8', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.72/5.91         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 5.72/5.91          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 5.72/5.91      inference('sup-', [status(thm)], ['5', '7'])).
% 5.72/5.91  thf('9', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i]:
% 5.72/5.91         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 5.72/5.91          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 5.72/5.91      inference('sup-', [status(thm)], ['4', '8'])).
% 5.72/5.91  thf('10', plain,
% 5.72/5.91      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 5.72/5.91         (~ (r2_hidden @ X6 @ X5)
% 5.72/5.91          | (r2_hidden @ X6 @ X3)
% 5.72/5.91          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 5.72/5.91      inference('cnf', [status(esa)], [d5_xboole_0])).
% 5.72/5.91  thf('11', plain,
% 5.72/5.91      (![X3 : $i, X4 : $i, X6 : $i]:
% 5.72/5.91         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 5.72/5.91      inference('simplify', [status(thm)], ['10'])).
% 5.72/5.91  thf('12', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i]:
% 5.72/5.91         ~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 5.72/5.91      inference('clc', [status(thm)], ['9', '11'])).
% 5.72/5.91  thf('13', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i]:
% 5.72/5.91         ~ (r2_hidden @ X1 @ (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 5.72/5.91      inference('sup-', [status(thm)], ['1', '12'])).
% 5.72/5.91  thf('14', plain,
% 5.72/5.91      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 5.72/5.91      inference('sup+', [status(thm)], ['2', '3'])).
% 5.72/5.91  thf('15', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 5.72/5.91      inference('demod', [status(thm)], ['13', '14'])).
% 5.72/5.91  thf('16', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i]:
% 5.72/5.91         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 5.72/5.91          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 5.72/5.91      inference('sup-', [status(thm)], ['0', '15'])).
% 5.72/5.91  thf(t83_xboole_1, conjecture,
% 5.72/5.91    (![A:$i,B:$i]:
% 5.72/5.91     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 5.72/5.91  thf(zf_stmt_0, negated_conjecture,
% 5.72/5.91    (~( ![A:$i,B:$i]:
% 5.72/5.91        ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ) )),
% 5.72/5.91    inference('cnf.neg', [status(esa)], [t83_xboole_1])).
% 5.72/5.91  thf('17', plain,
% 5.72/5.91      ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)) | (r1_xboole_0 @ sk_A @ sk_B))),
% 5.72/5.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.72/5.91  thf('18', plain,
% 5.72/5.91      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 5.72/5.91      inference('split', [status(esa)], ['17'])).
% 5.72/5.91  thf('19', plain,
% 5.72/5.91      ((((k4_xboole_0 @ sk_A @ sk_B) != (sk_A)) | ~ (r1_xboole_0 @ sk_A @ sk_B))),
% 5.72/5.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.72/5.91  thf('20', plain,
% 5.72/5.91      (~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))) | 
% 5.72/5.91       ~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 5.72/5.91      inference('split', [status(esa)], ['19'])).
% 5.72/5.91  thf('21', plain,
% 5.72/5.91      ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))
% 5.72/5.91         <= ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 5.72/5.91      inference('split', [status(esa)], ['17'])).
% 5.72/5.91  thf(t79_xboole_1, axiom,
% 5.72/5.91    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 5.72/5.91  thf('22', plain,
% 5.72/5.91      (![X18 : $i, X19 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X19)),
% 5.72/5.91      inference('cnf', [status(esa)], [t79_xboole_1])).
% 5.72/5.91  thf('23', plain,
% 5.72/5.91      (((r1_xboole_0 @ sk_A @ sk_B))
% 5.72/5.91         <= ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 5.72/5.91      inference('sup+', [status(thm)], ['21', '22'])).
% 5.72/5.91  thf('24', plain,
% 5.72/5.91      ((~ (r1_xboole_0 @ sk_A @ sk_B)) <= (~ ((r1_xboole_0 @ sk_A @ sk_B)))),
% 5.72/5.91      inference('split', [status(esa)], ['19'])).
% 5.72/5.91  thf('25', plain,
% 5.72/5.91      (((r1_xboole_0 @ sk_A @ sk_B)) | 
% 5.72/5.91       ~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 5.72/5.91      inference('sup-', [status(thm)], ['23', '24'])).
% 5.72/5.91  thf('26', plain,
% 5.72/5.91      (((r1_xboole_0 @ sk_A @ sk_B)) | (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 5.72/5.91      inference('split', [status(esa)], ['17'])).
% 5.72/5.91  thf('27', plain, (((r1_xboole_0 @ sk_A @ sk_B))),
% 5.72/5.91      inference('sat_resolution*', [status(thm)], ['20', '25', '26'])).
% 5.72/5.91  thf('28', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 5.72/5.91      inference('simpl_trail', [status(thm)], ['18', '27'])).
% 5.72/5.91  thf(d7_xboole_0, axiom,
% 5.72/5.91    (![A:$i,B:$i]:
% 5.72/5.91     ( ( r1_xboole_0 @ A @ B ) <=>
% 5.72/5.91       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 5.72/5.91  thf('29', plain,
% 5.72/5.91      (![X8 : $i, X9 : $i]:
% 5.72/5.91         (((k3_xboole_0 @ X8 @ X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 5.72/5.91      inference('cnf', [status(esa)], [d7_xboole_0])).
% 5.72/5.91  thf('30', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 5.72/5.91      inference('sup-', [status(thm)], ['28', '29'])).
% 5.72/5.91  thf('31', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.72/5.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.72/5.91  thf('32', plain,
% 5.72/5.91      (![X16 : $i, X17 : $i]:
% 5.72/5.91         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 5.72/5.91           = (k3_xboole_0 @ X16 @ X17))),
% 5.72/5.91      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.72/5.91  thf('33', plain,
% 5.72/5.91      (![X16 : $i, X17 : $i]:
% 5.72/5.91         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 5.72/5.91           = (k3_xboole_0 @ X16 @ X17))),
% 5.72/5.91      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.72/5.91  thf('34', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i]:
% 5.72/5.91         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 5.72/5.91           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 5.72/5.91      inference('sup+', [status(thm)], ['32', '33'])).
% 5.72/5.91  thf('35', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i]:
% 5.72/5.91         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 5.72/5.91           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 5.72/5.91      inference('sup+', [status(thm)], ['31', '34'])).
% 5.72/5.91  thf('36', plain,
% 5.72/5.91      (((k4_xboole_0 @ sk_B @ k1_xboole_0)
% 5.72/5.91         = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_A)))),
% 5.72/5.91      inference('sup+', [status(thm)], ['30', '35'])).
% 5.72/5.91  thf('37', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.72/5.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.72/5.91  thf('38', plain,
% 5.72/5.91      (![X16 : $i, X17 : $i]:
% 5.72/5.91         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 5.72/5.91           = (k3_xboole_0 @ X16 @ X17))),
% 5.72/5.91      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.72/5.91  thf('39', plain,
% 5.72/5.91      (![X3 : $i, X4 : $i, X6 : $i]:
% 5.72/5.91         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 5.72/5.91      inference('simplify', [status(thm)], ['10'])).
% 5.72/5.91  thf('40', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.72/5.91         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 5.72/5.91      inference('sup-', [status(thm)], ['38', '39'])).
% 5.72/5.91  thf('41', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.72/5.91         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X0))),
% 5.72/5.91      inference('sup-', [status(thm)], ['37', '40'])).
% 5.72/5.91  thf('42', plain,
% 5.72/5.91      (![X0 : $i]:
% 5.72/5.91         (~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_B @ k1_xboole_0))
% 5.72/5.91          | (r2_hidden @ X0 @ (k4_xboole_0 @ sk_B @ sk_A)))),
% 5.72/5.91      inference('sup-', [status(thm)], ['36', '41'])).
% 5.72/5.91  thf('43', plain,
% 5.72/5.91      (![X0 : $i]:
% 5.72/5.91         (((k1_xboole_0)
% 5.72/5.91            = (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ k1_xboole_0) @ X0))
% 5.72/5.91          | (r2_hidden @ 
% 5.72/5.91             (sk_D @ k1_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ k1_xboole_0)) @ 
% 5.72/5.91             (k4_xboole_0 @ sk_B @ sk_A)))),
% 5.72/5.91      inference('sup-', [status(thm)], ['16', '42'])).
% 5.72/5.91  thf('44', plain,
% 5.72/5.91      (![X3 : $i, X4 : $i, X7 : $i]:
% 5.72/5.91         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 5.72/5.91          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 5.72/5.91          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 5.72/5.91      inference('cnf', [status(esa)], [d5_xboole_0])).
% 5.72/5.91  thf('45', plain,
% 5.72/5.91      ((((k1_xboole_0)
% 5.72/5.91          = (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ k1_xboole_0) @ 
% 5.72/5.91             (k4_xboole_0 @ sk_B @ sk_A)))
% 5.72/5.91        | (r2_hidden @ 
% 5.72/5.91           (sk_D @ k1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A) @ 
% 5.72/5.91            (k4_xboole_0 @ sk_B @ k1_xboole_0)) @ 
% 5.72/5.91           k1_xboole_0)
% 5.72/5.91        | ((k1_xboole_0)
% 5.72/5.91            = (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ k1_xboole_0) @ 
% 5.72/5.91               (k4_xboole_0 @ sk_B @ sk_A))))),
% 5.72/5.91      inference('sup-', [status(thm)], ['43', '44'])).
% 5.72/5.91  thf('46', plain,
% 5.72/5.91      (((r2_hidden @ 
% 5.72/5.91         (sk_D @ k1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A) @ 
% 5.72/5.91          (k4_xboole_0 @ sk_B @ k1_xboole_0)) @ 
% 5.72/5.91         k1_xboole_0)
% 5.72/5.91        | ((k1_xboole_0)
% 5.72/5.91            = (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ k1_xboole_0) @ 
% 5.72/5.91               (k4_xboole_0 @ sk_B @ sk_A))))),
% 5.72/5.91      inference('simplify', [status(thm)], ['45'])).
% 5.72/5.91  thf('47', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 5.72/5.91      inference('demod', [status(thm)], ['13', '14'])).
% 5.72/5.91  thf('48', plain,
% 5.72/5.91      (((k1_xboole_0)
% 5.72/5.91         = (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ k1_xboole_0) @ 
% 5.72/5.91            (k4_xboole_0 @ sk_B @ sk_A)))),
% 5.72/5.91      inference('clc', [status(thm)], ['46', '47'])).
% 5.72/5.91  thf('49', plain,
% 5.72/5.91      (![X16 : $i, X17 : $i]:
% 5.72/5.91         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 5.72/5.91           = (k3_xboole_0 @ X16 @ X17))),
% 5.72/5.91      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.72/5.91  thf('50', plain,
% 5.72/5.91      (((k4_xboole_0 @ (k4_xboole_0 @ sk_B @ k1_xboole_0) @ k1_xboole_0)
% 5.72/5.91         = (k3_xboole_0 @ (k4_xboole_0 @ sk_B @ k1_xboole_0) @ 
% 5.72/5.91            (k4_xboole_0 @ sk_B @ sk_A)))),
% 5.72/5.91      inference('sup+', [status(thm)], ['48', '49'])).
% 5.72/5.91  thf('51', plain,
% 5.72/5.91      (![X3 : $i, X4 : $i, X7 : $i]:
% 5.72/5.91         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 5.72/5.91          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 5.72/5.91          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 5.72/5.91      inference('cnf', [status(esa)], [d5_xboole_0])).
% 5.72/5.91  thf('52', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 5.72/5.91      inference('demod', [status(thm)], ['13', '14'])).
% 5.72/5.91  thf('53', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i]:
% 5.72/5.91         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 5.72/5.91          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 5.72/5.91      inference('sup-', [status(thm)], ['51', '52'])).
% 5.72/5.91  thf('54', plain,
% 5.72/5.91      (![X3 : $i, X4 : $i, X7 : $i]:
% 5.72/5.91         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 5.72/5.91          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 5.72/5.91          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 5.72/5.91      inference('cnf', [status(esa)], [d5_xboole_0])).
% 5.72/5.91  thf('55', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i]:
% 5.72/5.91         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 5.72/5.91          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 5.72/5.91      inference('eq_fact', [status(thm)], ['54'])).
% 5.72/5.91  thf('56', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 5.72/5.91      inference('demod', [status(thm)], ['13', '14'])).
% 5.72/5.91  thf('57', plain,
% 5.72/5.91      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 5.72/5.91      inference('sup-', [status(thm)], ['55', '56'])).
% 5.72/5.91  thf('58', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i]:
% 5.72/5.91         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 5.72/5.91          | ((X1) = (k1_xboole_0)))),
% 5.72/5.91      inference('demod', [status(thm)], ['53', '57'])).
% 5.72/5.91  thf('59', plain,
% 5.72/5.91      (![X13 : $i]: ((k3_xboole_0 @ X13 @ k1_xboole_0) = (k1_xboole_0))),
% 5.72/5.91      inference('cnf', [status(esa)], [t2_boole])).
% 5.72/5.91  thf('60', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i]:
% 5.72/5.91         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 5.72/5.91           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 5.72/5.91      inference('sup+', [status(thm)], ['32', '33'])).
% 5.72/5.91  thf('61', plain,
% 5.72/5.91      (![X0 : $i]:
% 5.72/5.91         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 5.72/5.91           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 5.72/5.91      inference('sup+', [status(thm)], ['59', '60'])).
% 5.72/5.91  thf('62', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.72/5.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.72/5.91  thf('63', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.72/5.91         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 5.72/5.91          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 5.72/5.91      inference('sup-', [status(thm)], ['5', '7'])).
% 5.72/5.91  thf('64', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.72/5.91         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 5.72/5.91          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 5.72/5.91      inference('sup-', [status(thm)], ['62', '63'])).
% 5.72/5.91  thf('65', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i]:
% 5.72/5.91         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ k1_xboole_0))
% 5.72/5.91          | ~ (r2_hidden @ X1 @ 
% 5.72/5.91               (k4_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ X0)))),
% 5.72/5.91      inference('sup-', [status(thm)], ['61', '64'])).
% 5.72/5.91  thf('66', plain,
% 5.72/5.91      (![X3 : $i, X4 : $i, X6 : $i]:
% 5.72/5.91         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 5.72/5.91      inference('simplify', [status(thm)], ['10'])).
% 5.72/5.91  thf('67', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i]:
% 5.72/5.91         ~ (r2_hidden @ X1 @ 
% 5.72/5.91            (k4_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ X0))),
% 5.72/5.91      inference('clc', [status(thm)], ['65', '66'])).
% 5.72/5.91  thf('68', plain,
% 5.72/5.91      (![X0 : $i]:
% 5.72/5.91         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ X0) = (k1_xboole_0))),
% 5.72/5.91      inference('sup-', [status(thm)], ['58', '67'])).
% 5.72/5.91  thf('69', plain,
% 5.72/5.91      (![X16 : $i, X17 : $i]:
% 5.72/5.91         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 5.72/5.91           = (k3_xboole_0 @ X16 @ X17))),
% 5.72/5.91      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.72/5.91  thf('70', plain,
% 5.72/5.91      (![X0 : $i]:
% 5.72/5.91         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 5.72/5.91           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ X0))),
% 5.72/5.91      inference('sup+', [status(thm)], ['68', '69'])).
% 5.72/5.91  thf('71', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.72/5.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.72/5.91  thf('72', plain,
% 5.72/5.91      (![X0 : $i]:
% 5.72/5.91         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 5.72/5.91           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 5.72/5.91      inference('sup+', [status(thm)], ['59', '60'])).
% 5.72/5.91  thf('73', plain,
% 5.72/5.91      (![X0 : $i]:
% 5.72/5.91         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 5.72/5.91           = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 5.72/5.91      inference('demod', [status(thm)], ['70', '71', '72'])).
% 5.72/5.91  thf('74', plain,
% 5.72/5.91      (((k4_xboole_0 @ sk_B @ k1_xboole_0)
% 5.72/5.91         = (k3_xboole_0 @ (k4_xboole_0 @ sk_B @ k1_xboole_0) @ 
% 5.72/5.91            (k4_xboole_0 @ sk_B @ sk_A)))),
% 5.72/5.91      inference('demod', [status(thm)], ['50', '73'])).
% 5.72/5.91  thf('75', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i]:
% 5.72/5.91         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 5.72/5.91          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 5.72/5.91      inference('eq_fact', [status(thm)], ['54'])).
% 5.72/5.91  thf('76', plain,
% 5.72/5.91      (![X3 : $i, X4 : $i, X7 : $i]:
% 5.72/5.91         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 5.72/5.91          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 5.72/5.91          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 5.72/5.91          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 5.72/5.91      inference('cnf', [status(esa)], [d5_xboole_0])).
% 5.72/5.91  thf('77', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i]:
% 5.72/5.91         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 5.72/5.91          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 5.72/5.91          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 5.72/5.91          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 5.72/5.91      inference('sup-', [status(thm)], ['75', '76'])).
% 5.72/5.91  thf('78', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i]:
% 5.72/5.91         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 5.72/5.91          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 5.72/5.91          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 5.72/5.91      inference('simplify', [status(thm)], ['77'])).
% 5.72/5.91  thf('79', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i]:
% 5.72/5.91         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 5.72/5.91          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 5.72/5.91      inference('eq_fact', [status(thm)], ['54'])).
% 5.72/5.91  thf('80', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i]:
% 5.72/5.91         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 5.72/5.91          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 5.72/5.91      inference('clc', [status(thm)], ['78', '79'])).
% 5.72/5.91  thf('81', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 5.72/5.91      inference('demod', [status(thm)], ['13', '14'])).
% 5.72/5.91  thf('82', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 5.72/5.91      inference('sup-', [status(thm)], ['80', '81'])).
% 5.72/5.91  thf('83', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 5.72/5.91      inference('sup-', [status(thm)], ['80', '81'])).
% 5.72/5.91  thf('84', plain,
% 5.72/5.91      (![X3 : $i, X4 : $i, X7 : $i]:
% 5.72/5.91         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 5.72/5.91          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 5.72/5.91          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 5.72/5.91      inference('cnf', [status(esa)], [d5_xboole_0])).
% 5.72/5.91  thf('85', plain,
% 5.72/5.91      (![X3 : $i, X4 : $i, X6 : $i]:
% 5.72/5.91         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 5.72/5.91      inference('simplify', [status(thm)], ['10'])).
% 5.72/5.91  thf('86', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.72/5.91         ((r2_hidden @ (sk_D @ X3 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X3)
% 5.72/5.91          | ((X3) = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))
% 5.72/5.91          | (r2_hidden @ (sk_D @ X3 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 5.72/5.91      inference('sup-', [status(thm)], ['84', '85'])).
% 5.72/5.91  thf('87', plain,
% 5.72/5.91      (![X3 : $i, X4 : $i, X7 : $i]:
% 5.72/5.91         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 5.72/5.91          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 5.72/5.91          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 5.72/5.91      inference('cnf', [status(esa)], [d5_xboole_0])).
% 5.72/5.91  thf('88', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.72/5.91         (((X2) = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))
% 5.72/5.91          | (r2_hidden @ (sk_D @ X2 @ X0 @ (k4_xboole_0 @ X0 @ X1)) @ X2)
% 5.72/5.91          | (r2_hidden @ (sk_D @ X2 @ X0 @ (k4_xboole_0 @ X0 @ X1)) @ X2)
% 5.72/5.91          | ((X2) = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)))),
% 5.72/5.91      inference('sup-', [status(thm)], ['86', '87'])).
% 5.72/5.91  thf('89', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.72/5.91         ((r2_hidden @ (sk_D @ X2 @ X0 @ (k4_xboole_0 @ X0 @ X1)) @ X2)
% 5.72/5.91          | ((X2) = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)))),
% 5.72/5.91      inference('simplify', [status(thm)], ['88'])).
% 5.72/5.91  thf('90', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 5.72/5.91      inference('demod', [status(thm)], ['13', '14'])).
% 5.72/5.91  thf('91', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i]:
% 5.72/5.91         ((k1_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 5.72/5.91      inference('sup-', [status(thm)], ['89', '90'])).
% 5.72/5.91  thf('92', plain,
% 5.72/5.91      (![X16 : $i, X17 : $i]:
% 5.72/5.91         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 5.72/5.91           = (k3_xboole_0 @ X16 @ X17))),
% 5.72/5.91      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.72/5.91  thf('93', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i]:
% 5.72/5.91         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 5.72/5.91           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 5.72/5.91      inference('sup+', [status(thm)], ['91', '92'])).
% 5.72/5.91  thf('94', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.72/5.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.72/5.91  thf('95', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i]:
% 5.72/5.91         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 5.72/5.91           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 5.72/5.91      inference('demod', [status(thm)], ['93', '94'])).
% 5.72/5.91  thf('96', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 5.72/5.91      inference('sup-', [status(thm)], ['80', '81'])).
% 5.72/5.91  thf('97', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_A))),
% 5.72/5.91      inference('demod', [status(thm)], ['74', '82', '83', '95', '96'])).
% 5.72/5.91  thf('98', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i]:
% 5.72/5.91         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 5.72/5.91           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 5.72/5.91      inference('demod', [status(thm)], ['93', '94'])).
% 5.72/5.91  thf('99', plain,
% 5.72/5.91      (![X18 : $i, X19 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X19)),
% 5.72/5.91      inference('cnf', [status(esa)], [t79_xboole_1])).
% 5.72/5.91  thf(symmetry_r1_xboole_0, axiom,
% 5.72/5.91    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 5.72/5.91  thf('100', plain,
% 5.72/5.91      (![X11 : $i, X12 : $i]:
% 5.72/5.91         ((r1_xboole_0 @ X11 @ X12) | ~ (r1_xboole_0 @ X12 @ X11))),
% 5.72/5.91      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 5.72/5.91  thf('101', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 5.72/5.91      inference('sup-', [status(thm)], ['99', '100'])).
% 5.72/5.91  thf('102', plain,
% 5.72/5.91      (![X8 : $i, X9 : $i]:
% 5.72/5.91         (((k3_xboole_0 @ X8 @ X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 5.72/5.91      inference('cnf', [status(esa)], [d7_xboole_0])).
% 5.72/5.91  thf('103', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i]:
% 5.72/5.91         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 5.72/5.91      inference('sup-', [status(thm)], ['101', '102'])).
% 5.72/5.91  thf('104', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i]:
% 5.72/5.91         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 5.72/5.91           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 5.72/5.91      inference('sup+', [status(thm)], ['32', '33'])).
% 5.72/5.91  thf('105', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i]:
% 5.72/5.91         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 5.72/5.91           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 5.72/5.91      inference('sup+', [status(thm)], ['103', '104'])).
% 5.72/5.91  thf('106', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i]:
% 5.72/5.91         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 5.72/5.91           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 5.72/5.91              k1_xboole_0))),
% 5.72/5.91      inference('sup+', [status(thm)], ['98', '105'])).
% 5.72/5.91  thf('107', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 5.72/5.91      inference('sup-', [status(thm)], ['80', '81'])).
% 5.72/5.91  thf('108', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 5.72/5.91      inference('sup-', [status(thm)], ['80', '81'])).
% 5.72/5.91  thf('109', plain,
% 5.72/5.91      (![X0 : $i, X1 : $i]:
% 5.72/5.91         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 5.72/5.91      inference('demod', [status(thm)], ['106', '107', '108'])).
% 5.72/5.91  thf('110', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_B))),
% 5.72/5.91      inference('sup+', [status(thm)], ['97', '109'])).
% 5.72/5.91  thf('111', plain,
% 5.72/5.91      ((((k4_xboole_0 @ sk_A @ sk_B) != (sk_A)))
% 5.72/5.91         <= (~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 5.72/5.91      inference('split', [status(esa)], ['19'])).
% 5.72/5.91  thf('112', plain, (~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 5.72/5.91      inference('sat_resolution*', [status(thm)], ['20', '25'])).
% 5.72/5.91  thf('113', plain, (((k4_xboole_0 @ sk_A @ sk_B) != (sk_A))),
% 5.72/5.91      inference('simpl_trail', [status(thm)], ['111', '112'])).
% 5.72/5.91  thf('114', plain, ($false),
% 5.72/5.91      inference('simplify_reflect-', [status(thm)], ['110', '113'])).
% 5.72/5.91  
% 5.72/5.91  % SZS output end Refutation
% 5.72/5.91  
% 5.72/5.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

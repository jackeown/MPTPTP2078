%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TUXHeYXqmO

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:04 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 213 expanded)
%              Number of leaves         :   29 (  75 expanded)
%              Depth                    :   18
%              Number of atoms          :  829 (1691 expanded)
%              Number of equality atoms :   66 ( 148 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('0',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 @ X29 @ X30 )
      | ( X27 = X28 )
      | ( X27 = X29 )
      | ( X27 = X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 @ X29 @ X30 )
      | ( X27 = X28 )
      | ( X27 = X29 )
      | ( X27 = X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t13_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t13_zfmisc_1])).

thf('3',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('5',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('7',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ sk_B ) ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('11',plain,(
    ! [X38: $i] :
      ( ( k2_tarski @ X38 @ X38 )
      = ( k1_tarski @ X38 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_enumset1 @ X39 @ X39 @ X40 )
      = ( k2_tarski @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X36 @ X35 )
      | ~ ( zip_tseitin_0 @ X36 @ X32 @ X33 @ X34 )
      | ( X35
       != ( k1_enumset1 @ X34 @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('14',plain,(
    ! [X32: $i,X33: $i,X34: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X32 @ X33 @ X34 )
      | ~ ( r2_hidden @ X36 @ ( k1_enumset1 @ X34 @ X33 @ X32 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ X0 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ X0 @ ( k1_tarski @ sk_B ) ) @ sk_A @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ ( k1_tarski @ sk_B ) )
        = sk_A )
      | ( ( sk_C @ X0 @ ( k1_tarski @ sk_B ) )
        = sk_A )
      | ( ( sk_C @ X0 @ ( k1_tarski @ sk_B ) )
        = sk_A )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ X0 )
      | ( ( sk_C @ X0 @ ( k1_tarski @ sk_B ) )
        = sk_A ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ X0 )
      | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ( X13 != X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X14: $i] :
      ( r1_tarski @ X14 @ X14 ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('26',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('30',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ( r2_hidden @ X9 @ X11 )
      | ~ ( r2_hidden @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('34',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X11 )
      | ~ ( r2_hidden @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['32','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['23','37'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('39',plain,(
    ! [X21: $i] :
      ( r1_tarski @ k1_xboole_0 @ X21 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('40',plain,(
    ! [X13: $i,X15: $i] :
      ( ( X13 = X15 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf('47',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','47'])).

thf('49',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( sk_A = sk_B ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('51',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X38: $i] :
      ( ( k2_tarski @ X38 @ X38 )
      = ( k1_tarski @ X38 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('53',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_enumset1 @ X39 @ X39 @ X40 )
      = ( k2_tarski @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('54',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 @ X33 @ X34 )
      | ( r2_hidden @ X31 @ X35 )
      | ( X35
       != ( k1_enumset1 @ X34 @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('55',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( r2_hidden @ X31 @ ( k1_enumset1 @ X34 @ X33 @ X32 ) )
      | ( zip_tseitin_0 @ X31 @ X32 @ X33 @ X34 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['53','55'])).

thf('57',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X27 != X26 )
      | ~ ( zip_tseitin_0 @ X27 @ X28 @ X29 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X26: $i,X28: $i,X29: $i] :
      ~ ( zip_tseitin_0 @ X26 @ X28 @ X29 @ X26 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','59'])).

thf('61',plain,(
    r2_hidden @ sk_B @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['51','60'])).

thf('62',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('63',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('64',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('66',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ( r2_hidden @ X9 @ X11 )
      | ~ ( r2_hidden @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('71',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X11 )
      | ~ ( r2_hidden @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['69','73'])).

thf('75',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('76',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['69','73'])).

thf('77',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('79',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['74','79'])).

thf('81',plain,(
    $false ),
    inference('sup-',[status(thm)],['61','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TUXHeYXqmO
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:49:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.42/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.61  % Solved by: fo/fo7.sh
% 0.42/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.61  % done 627 iterations in 0.156s
% 0.42/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.61  % SZS output start Refutation
% 0.42/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.42/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.42/0.61  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.42/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.42/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.42/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.42/0.61  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.42/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.42/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.42/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.61  thf(d1_enumset1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.61     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.42/0.61       ( ![E:$i]:
% 0.42/0.61         ( ( r2_hidden @ E @ D ) <=>
% 0.42/0.61           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.42/0.61  thf(zf_stmt_0, axiom,
% 0.42/0.61    (![E:$i,C:$i,B:$i,A:$i]:
% 0.42/0.61     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.42/0.61       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.42/0.61  thf('0', plain,
% 0.42/0.61      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.42/0.61         ((zip_tseitin_0 @ X27 @ X28 @ X29 @ X30)
% 0.42/0.61          | ((X27) = (X28))
% 0.42/0.61          | ((X27) = (X29))
% 0.42/0.61          | ((X27) = (X30)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('1', plain,
% 0.42/0.61      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.42/0.61         ((zip_tseitin_0 @ X27 @ X28 @ X29 @ X30)
% 0.42/0.61          | ((X27) = (X28))
% 0.42/0.61          | ((X27) = (X29))
% 0.42/0.61          | ((X27) = (X30)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(d3_tarski, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( r1_tarski @ A @ B ) <=>
% 0.42/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.42/0.61  thf('2', plain,
% 0.42/0.61      (![X5 : $i, X7 : $i]:
% 0.42/0.61         ((r1_tarski @ X5 @ X7) | (r2_hidden @ (sk_C @ X7 @ X5) @ X5))),
% 0.42/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.42/0.61  thf(t13_zfmisc_1, conjecture,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.42/0.61         ( k1_tarski @ A ) ) =>
% 0.42/0.61       ( ( A ) = ( B ) ) ))).
% 0.42/0.61  thf(zf_stmt_1, negated_conjecture,
% 0.42/0.61    (~( ![A:$i,B:$i]:
% 0.42/0.61        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.42/0.61            ( k1_tarski @ A ) ) =>
% 0.42/0.61          ( ( A ) = ( B ) ) ) )),
% 0.42/0.61    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 0.42/0.61  thf('3', plain,
% 0.42/0.61      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.42/0.61         = (k1_tarski @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.61  thf(commutativity_k2_xboole_0, axiom,
% 0.42/0.61    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.42/0.61  thf('4', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.42/0.61      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.42/0.61  thf('5', plain,
% 0.42/0.61      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.42/0.61         = (k1_tarski @ sk_A))),
% 0.42/0.61      inference('demod', [status(thm)], ['3', '4'])).
% 0.42/0.61  thf(t7_xboole_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.42/0.61  thf('6', plain,
% 0.42/0.61      (![X22 : $i, X23 : $i]: (r1_tarski @ X22 @ (k2_xboole_0 @ X22 @ X23))),
% 0.42/0.61      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.42/0.61  thf('7', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))),
% 0.42/0.61      inference('sup+', [status(thm)], ['5', '6'])).
% 0.42/0.61  thf('8', plain,
% 0.42/0.61      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.42/0.61         (~ (r2_hidden @ X4 @ X5)
% 0.42/0.61          | (r2_hidden @ X4 @ X6)
% 0.42/0.61          | ~ (r1_tarski @ X5 @ X6))),
% 0.42/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.42/0.61  thf('9', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.42/0.61          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['7', '8'])).
% 0.42/0.61  thf('10', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((r1_tarski @ (k1_tarski @ sk_B) @ X0)
% 0.42/0.61          | (r2_hidden @ (sk_C @ X0 @ (k1_tarski @ sk_B)) @ (k1_tarski @ sk_A)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['2', '9'])).
% 0.42/0.61  thf(t69_enumset1, axiom,
% 0.42/0.61    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.42/0.61  thf('11', plain,
% 0.42/0.61      (![X38 : $i]: ((k2_tarski @ X38 @ X38) = (k1_tarski @ X38))),
% 0.42/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.42/0.61  thf(t70_enumset1, axiom,
% 0.42/0.61    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.42/0.61  thf('12', plain,
% 0.42/0.61      (![X39 : $i, X40 : $i]:
% 0.42/0.61         ((k1_enumset1 @ X39 @ X39 @ X40) = (k2_tarski @ X39 @ X40))),
% 0.42/0.61      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.42/0.61  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.42/0.61  thf(zf_stmt_3, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.61     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.42/0.61       ( ![E:$i]:
% 0.42/0.61         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.42/0.61  thf('13', plain,
% 0.42/0.61      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.42/0.61         (~ (r2_hidden @ X36 @ X35)
% 0.42/0.61          | ~ (zip_tseitin_0 @ X36 @ X32 @ X33 @ X34)
% 0.42/0.61          | ((X35) != (k1_enumset1 @ X34 @ X33 @ X32)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.42/0.61  thf('14', plain,
% 0.42/0.61      (![X32 : $i, X33 : $i, X34 : $i, X36 : $i]:
% 0.42/0.61         (~ (zip_tseitin_0 @ X36 @ X32 @ X33 @ X34)
% 0.42/0.61          | ~ (r2_hidden @ X36 @ (k1_enumset1 @ X34 @ X33 @ X32)))),
% 0.42/0.61      inference('simplify', [status(thm)], ['13'])).
% 0.42/0.61  thf('15', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.61         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.42/0.61          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.42/0.61      inference('sup-', [status(thm)], ['12', '14'])).
% 0.42/0.61  thf('16', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.42/0.61          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['11', '15'])).
% 0.42/0.61  thf('17', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((r1_tarski @ (k1_tarski @ sk_B) @ X0)
% 0.42/0.61          | ~ (zip_tseitin_0 @ (sk_C @ X0 @ (k1_tarski @ sk_B)) @ sk_A @ 
% 0.42/0.61               sk_A @ sk_A))),
% 0.42/0.61      inference('sup-', [status(thm)], ['10', '16'])).
% 0.42/0.61  thf('18', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (((sk_C @ X0 @ (k1_tarski @ sk_B)) = (sk_A))
% 0.42/0.61          | ((sk_C @ X0 @ (k1_tarski @ sk_B)) = (sk_A))
% 0.42/0.61          | ((sk_C @ X0 @ (k1_tarski @ sk_B)) = (sk_A))
% 0.42/0.61          | (r1_tarski @ (k1_tarski @ sk_B) @ X0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['1', '17'])).
% 0.42/0.61  thf('19', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((r1_tarski @ (k1_tarski @ sk_B) @ X0)
% 0.42/0.61          | ((sk_C @ X0 @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.42/0.61      inference('simplify', [status(thm)], ['18'])).
% 0.42/0.61  thf('20', plain,
% 0.42/0.61      (![X5 : $i, X7 : $i]:
% 0.42/0.61         ((r1_tarski @ X5 @ X7) | (r2_hidden @ (sk_C @ X7 @ X5) @ X5))),
% 0.42/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.42/0.61  thf('21', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))
% 0.42/0.61          | (r1_tarski @ (k1_tarski @ sk_B) @ X0)
% 0.42/0.61          | (r1_tarski @ (k1_tarski @ sk_B) @ X0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['19', '20'])).
% 0.42/0.61  thf('22', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((r1_tarski @ (k1_tarski @ sk_B) @ X0)
% 0.42/0.61          | (r2_hidden @ sk_A @ (k1_tarski @ sk_B)))),
% 0.42/0.61      inference('simplify', [status(thm)], ['21'])).
% 0.42/0.61  thf('23', plain,
% 0.42/0.61      (![X5 : $i, X7 : $i]:
% 0.42/0.61         ((r1_tarski @ X5 @ X7) | (r2_hidden @ (sk_C @ X7 @ X5) @ X5))),
% 0.42/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.42/0.61  thf(d10_xboole_0, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.42/0.61  thf('24', plain,
% 0.42/0.61      (![X13 : $i, X14 : $i]: ((r1_tarski @ X13 @ X14) | ((X13) != (X14)))),
% 0.42/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.42/0.61  thf('25', plain, (![X14 : $i]: (r1_tarski @ X14 @ X14)),
% 0.42/0.61      inference('simplify', [status(thm)], ['24'])).
% 0.42/0.61  thf(t28_xboole_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.42/0.61  thf('26', plain,
% 0.42/0.61      (![X19 : $i, X20 : $i]:
% 0.42/0.61         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 0.42/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.42/0.61  thf('27', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['25', '26'])).
% 0.42/0.61  thf(t100_xboole_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.42/0.61  thf('28', plain,
% 0.42/0.61      (![X16 : $i, X17 : $i]:
% 0.42/0.61         ((k4_xboole_0 @ X16 @ X17)
% 0.42/0.61           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.42/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.42/0.61  thf('29', plain,
% 0.42/0.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['27', '28'])).
% 0.42/0.61  thf(t1_xboole_0, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.42/0.61       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.42/0.61  thf('30', plain,
% 0.42/0.61      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.42/0.61         ((r2_hidden @ X9 @ X10)
% 0.42/0.61          | (r2_hidden @ X9 @ X11)
% 0.42/0.61          | ~ (r2_hidden @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 0.42/0.61      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.42/0.61  thf('31', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.42/0.61          | (r2_hidden @ X1 @ X0)
% 0.42/0.61          | (r2_hidden @ X1 @ X0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['29', '30'])).
% 0.42/0.61  thf('32', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.42/0.61      inference('simplify', [status(thm)], ['31'])).
% 0.42/0.61  thf('33', plain,
% 0.42/0.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['27', '28'])).
% 0.42/0.61  thf('34', plain,
% 0.42/0.61      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.42/0.61         (~ (r2_hidden @ X9 @ X10)
% 0.42/0.61          | ~ (r2_hidden @ X9 @ X11)
% 0.42/0.61          | ~ (r2_hidden @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 0.42/0.61      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.42/0.61  thf('35', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.42/0.61          | ~ (r2_hidden @ X1 @ X0)
% 0.42/0.61          | ~ (r2_hidden @ X1 @ X0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['33', '34'])).
% 0.42/0.61  thf('36', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (~ (r2_hidden @ X1 @ X0)
% 0.42/0.61          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.42/0.61      inference('simplify', [status(thm)], ['35'])).
% 0.42/0.61  thf('37', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.42/0.61      inference('clc', [status(thm)], ['32', '36'])).
% 0.42/0.61  thf('38', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)),
% 0.42/0.61      inference('sup-', [status(thm)], ['23', '37'])).
% 0.42/0.61  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.42/0.61  thf('39', plain, (![X21 : $i]: (r1_tarski @ k1_xboole_0 @ X21)),
% 0.42/0.61      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.42/0.61  thf('40', plain,
% 0.42/0.61      (![X13 : $i, X15 : $i]:
% 0.42/0.61         (((X13) = (X15))
% 0.42/0.61          | ~ (r1_tarski @ X15 @ X13)
% 0.42/0.61          | ~ (r1_tarski @ X13 @ X15))),
% 0.42/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.42/0.61  thf('41', plain,
% 0.42/0.61      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['39', '40'])).
% 0.42/0.61  thf('42', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['38', '41'])).
% 0.42/0.61  thf('43', plain,
% 0.42/0.61      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['39', '40'])).
% 0.42/0.61  thf('44', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (~ (r1_tarski @ X1 @ (k4_xboole_0 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['42', '43'])).
% 0.42/0.61  thf('45', plain,
% 0.42/0.61      (((r2_hidden @ sk_A @ (k1_tarski @ sk_B))
% 0.42/0.61        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['22', '44'])).
% 0.42/0.61  thf('46', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.42/0.61          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['11', '15'])).
% 0.42/0.61  thf('47', plain,
% 0.42/0.61      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.42/0.61        | ~ (zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B))),
% 0.42/0.61      inference('sup-', [status(thm)], ['45', '46'])).
% 0.42/0.61  thf('48', plain,
% 0.42/0.61      ((((sk_A) = (sk_B))
% 0.42/0.61        | ((sk_A) = (sk_B))
% 0.42/0.61        | ((sk_A) = (sk_B))
% 0.42/0.61        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['0', '47'])).
% 0.42/0.61  thf('49', plain,
% 0.42/0.61      ((((k1_tarski @ sk_B) = (k1_xboole_0)) | ((sk_A) = (sk_B)))),
% 0.42/0.61      inference('simplify', [status(thm)], ['48'])).
% 0.42/0.61  thf('50', plain, (((sk_A) != (sk_B))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.61  thf('51', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.42/0.61      inference('simplify_reflect-', [status(thm)], ['49', '50'])).
% 0.42/0.61  thf('52', plain,
% 0.42/0.61      (![X38 : $i]: ((k2_tarski @ X38 @ X38) = (k1_tarski @ X38))),
% 0.42/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.42/0.61  thf('53', plain,
% 0.42/0.61      (![X39 : $i, X40 : $i]:
% 0.42/0.61         ((k1_enumset1 @ X39 @ X39 @ X40) = (k2_tarski @ X39 @ X40))),
% 0.42/0.61      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.42/0.61  thf('54', plain,
% 0.42/0.61      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.42/0.61         ((zip_tseitin_0 @ X31 @ X32 @ X33 @ X34)
% 0.42/0.61          | (r2_hidden @ X31 @ X35)
% 0.42/0.61          | ((X35) != (k1_enumset1 @ X34 @ X33 @ X32)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.42/0.61  thf('55', plain,
% 0.42/0.61      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.42/0.61         ((r2_hidden @ X31 @ (k1_enumset1 @ X34 @ X33 @ X32))
% 0.42/0.61          | (zip_tseitin_0 @ X31 @ X32 @ X33 @ X34))),
% 0.42/0.61      inference('simplify', [status(thm)], ['54'])).
% 0.42/0.61  thf('56', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.61         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.42/0.61          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.42/0.61      inference('sup+', [status(thm)], ['53', '55'])).
% 0.42/0.61  thf('57', plain,
% 0.42/0.61      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.42/0.61         (((X27) != (X26)) | ~ (zip_tseitin_0 @ X27 @ X28 @ X29 @ X26))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('58', plain,
% 0.42/0.61      (![X26 : $i, X28 : $i, X29 : $i]:
% 0.42/0.61         ~ (zip_tseitin_0 @ X26 @ X28 @ X29 @ X26)),
% 0.42/0.61      inference('simplify', [status(thm)], ['57'])).
% 0.42/0.61  thf('59', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.42/0.61      inference('sup-', [status(thm)], ['56', '58'])).
% 0.42/0.61  thf('60', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['52', '59'])).
% 0.42/0.61  thf('61', plain, ((r2_hidden @ sk_B @ k1_xboole_0)),
% 0.42/0.61      inference('sup+', [status(thm)], ['51', '60'])).
% 0.42/0.61  thf('62', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))),
% 0.42/0.61      inference('sup+', [status(thm)], ['5', '6'])).
% 0.42/0.61  thf('63', plain,
% 0.42/0.61      (![X19 : $i, X20 : $i]:
% 0.42/0.61         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 0.42/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.42/0.61  thf('64', plain,
% 0.42/0.61      (((k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.42/0.61         = (k1_tarski @ sk_B))),
% 0.42/0.61      inference('sup-', [status(thm)], ['62', '63'])).
% 0.42/0.61  thf('65', plain,
% 0.42/0.61      (![X16 : $i, X17 : $i]:
% 0.42/0.61         ((k4_xboole_0 @ X16 @ X17)
% 0.42/0.61           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.42/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.42/0.61  thf('66', plain,
% 0.42/0.61      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.42/0.61         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B)))),
% 0.42/0.61      inference('sup+', [status(thm)], ['64', '65'])).
% 0.42/0.61  thf('67', plain,
% 0.42/0.61      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.42/0.61         ((r2_hidden @ X9 @ X10)
% 0.42/0.61          | (r2_hidden @ X9 @ X11)
% 0.42/0.61          | ~ (r2_hidden @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 0.42/0.61      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.42/0.61  thf('68', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (r2_hidden @ X0 @ 
% 0.42/0.61             (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))
% 0.42/0.61          | (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.42/0.61          | (r2_hidden @ X0 @ (k1_tarski @ sk_B)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['66', '67'])).
% 0.42/0.61  thf('69', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.42/0.61          | ~ (r2_hidden @ X0 @ 
% 0.42/0.61               (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))))),
% 0.42/0.61      inference('simplify', [status(thm)], ['68'])).
% 0.42/0.61  thf('70', plain,
% 0.42/0.61      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.42/0.61         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B)))),
% 0.42/0.61      inference('sup+', [status(thm)], ['64', '65'])).
% 0.42/0.61  thf('71', plain,
% 0.42/0.61      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.42/0.61         (~ (r2_hidden @ X9 @ X10)
% 0.42/0.61          | ~ (r2_hidden @ X9 @ X11)
% 0.42/0.61          | ~ (r2_hidden @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 0.42/0.61      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.42/0.61  thf('72', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (r2_hidden @ X0 @ 
% 0.42/0.61             (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))
% 0.42/0.61          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.42/0.61          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['70', '71'])).
% 0.42/0.61  thf('73', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.42/0.61          | ~ (r2_hidden @ X0 @ 
% 0.42/0.61               (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))))),
% 0.42/0.61      inference('simplify', [status(thm)], ['72'])).
% 0.42/0.61  thf('74', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ~ (r2_hidden @ X0 @ 
% 0.42/0.61            (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.42/0.61      inference('clc', [status(thm)], ['69', '73'])).
% 0.42/0.61  thf('75', plain,
% 0.42/0.61      (![X5 : $i, X7 : $i]:
% 0.42/0.61         ((r1_tarski @ X5 @ X7) | (r2_hidden @ (sk_C @ X7 @ X5) @ X5))),
% 0.42/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.42/0.61  thf('76', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ~ (r2_hidden @ X0 @ 
% 0.42/0.61            (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.42/0.61      inference('clc', [status(thm)], ['69', '73'])).
% 0.42/0.61  thf('77', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (r1_tarski @ 
% 0.42/0.61          (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ X0)),
% 0.42/0.61      inference('sup-', [status(thm)], ['75', '76'])).
% 0.42/0.61  thf('78', plain,
% 0.42/0.61      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['39', '40'])).
% 0.42/0.61  thf('79', plain,
% 0.42/0.61      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['77', '78'])).
% 0.42/0.61  thf('80', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.42/0.61      inference('demod', [status(thm)], ['74', '79'])).
% 0.42/0.61  thf('81', plain, ($false), inference('sup-', [status(thm)], ['61', '80'])).
% 0.42/0.61  
% 0.42/0.61  % SZS output end Refutation
% 0.42/0.61  
% 0.42/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

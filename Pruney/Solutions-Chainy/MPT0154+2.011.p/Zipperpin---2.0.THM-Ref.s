%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WW4bqDw4pm

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:23 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 107 expanded)
%              Number of leaves         :   28 (  43 expanded)
%              Depth                    :   15
%              Number of atoms          :  583 ( 751 expanded)
%              Number of equality atoms :   69 (  89 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t70_enumset1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_enumset1 @ A @ A @ B )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t70_enumset1])).

thf('0',plain,(
    ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('1',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( X30 != X32 )
      | ( r2_hidden @ X30 @ X31 )
      | ( X31
       != ( k2_tarski @ X32 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('2',plain,(
    ! [X29: $i,X32: $i] :
      ( r2_hidden @ X32 @ ( k2_tarski @ X32 @ X29 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('4',plain,(
    ! [X24: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X27 @ X26 )
      | ( X27 = X24 )
      | ( X26
       != ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('5',plain,(
    ! [X24: $i,X27: $i] :
      ( ( X27 = X24 )
      | ~ ( r2_hidden @ X27 @ ( k1_tarski @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_tarski @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('22',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('26',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('28',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('29',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('32',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('33',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('36',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','27','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('45',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('47',plain,(
    ! [X11: $i] :
      ( ( k2_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('48',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = X1 ) ),
    inference(demod,[status(thm)],['43','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['14','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','51'])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('53',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k1_enumset1 @ X35 @ X36 @ X37 )
      = ( k2_xboole_0 @ ( k1_tarski @ X35 ) @ ( k2_tarski @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','54'])).

thf('56',plain,(
    $false ),
    inference(simplify,[status(thm)],['55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WW4bqDw4pm
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:27:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.42/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.61  % Solved by: fo/fo7.sh
% 0.42/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.61  % done 473 iterations in 0.153s
% 0.42/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.61  % SZS output start Refutation
% 0.42/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.42/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.42/0.61  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.42/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.42/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.42/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.42/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.61  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.42/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.42/0.61  thf(t70_enumset1, conjecture,
% 0.42/0.61    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.42/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.61    (~( ![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ) )),
% 0.42/0.61    inference('cnf.neg', [status(esa)], [t70_enumset1])).
% 0.42/0.61  thf('0', plain,
% 0.42/0.61      (((k1_enumset1 @ sk_A @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(d2_tarski, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.42/0.61       ( ![D:$i]:
% 0.42/0.61         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.42/0.61  thf('1', plain,
% 0.42/0.61      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.42/0.61         (((X30) != (X32))
% 0.42/0.61          | (r2_hidden @ X30 @ X31)
% 0.42/0.61          | ((X31) != (k2_tarski @ X32 @ X29)))),
% 0.42/0.61      inference('cnf', [status(esa)], [d2_tarski])).
% 0.42/0.61  thf('2', plain,
% 0.42/0.61      (![X29 : $i, X32 : $i]: (r2_hidden @ X32 @ (k2_tarski @ X32 @ X29))),
% 0.42/0.61      inference('simplify', [status(thm)], ['1'])).
% 0.42/0.61  thf(d3_tarski, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( r1_tarski @ A @ B ) <=>
% 0.42/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.42/0.61  thf('3', plain,
% 0.42/0.61      (![X3 : $i, X5 : $i]:
% 0.42/0.61         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.42/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.42/0.61  thf(d1_tarski, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.42/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.42/0.61  thf('4', plain,
% 0.42/0.61      (![X24 : $i, X26 : $i, X27 : $i]:
% 0.42/0.61         (~ (r2_hidden @ X27 @ X26)
% 0.42/0.61          | ((X27) = (X24))
% 0.42/0.61          | ((X26) != (k1_tarski @ X24)))),
% 0.42/0.61      inference('cnf', [status(esa)], [d1_tarski])).
% 0.42/0.61  thf('5', plain,
% 0.42/0.61      (![X24 : $i, X27 : $i]:
% 0.42/0.61         (((X27) = (X24)) | ~ (r2_hidden @ X27 @ (k1_tarski @ X24)))),
% 0.42/0.61      inference('simplify', [status(thm)], ['4'])).
% 0.42/0.61  thf('6', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.42/0.61          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['3', '5'])).
% 0.42/0.61  thf('7', plain,
% 0.42/0.61      (![X3 : $i, X5 : $i]:
% 0.42/0.61         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.42/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.42/0.61  thf('8', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (~ (r2_hidden @ X0 @ X1)
% 0.42/0.61          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.42/0.61          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.42/0.61      inference('sup-', [status(thm)], ['6', '7'])).
% 0.42/0.61  thf('9', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.42/0.61      inference('simplify', [status(thm)], ['8'])).
% 0.42/0.61  thf('10', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (r1_tarski @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['2', '9'])).
% 0.42/0.61  thf(t28_xboole_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.42/0.61  thf('11', plain,
% 0.42/0.61      (![X14 : $i, X15 : $i]:
% 0.42/0.61         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 0.42/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.42/0.61  thf('12', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         ((k3_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.42/0.61           = (k1_tarski @ X1))),
% 0.42/0.61      inference('sup-', [status(thm)], ['10', '11'])).
% 0.42/0.61  thf(commutativity_k3_xboole_0, axiom,
% 0.42/0.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.42/0.61  thf('13', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.42/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.42/0.61  thf(t48_xboole_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.42/0.61  thf('14', plain,
% 0.42/0.61      (![X17 : $i, X18 : $i]:
% 0.42/0.61         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.42/0.61           = (k3_xboole_0 @ X17 @ X18))),
% 0.42/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.42/0.61  thf(d10_xboole_0, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.42/0.61  thf('15', plain,
% 0.42/0.61      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 0.42/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.42/0.61  thf('16', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.42/0.61      inference('simplify', [status(thm)], ['15'])).
% 0.42/0.61  thf('17', plain,
% 0.42/0.61      (![X14 : $i, X15 : $i]:
% 0.42/0.61         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 0.42/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.42/0.61  thf('18', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['16', '17'])).
% 0.42/0.61  thf(t100_xboole_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.42/0.61  thf('19', plain,
% 0.42/0.61      (![X9 : $i, X10 : $i]:
% 0.42/0.61         ((k4_xboole_0 @ X9 @ X10)
% 0.42/0.61           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.42/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.42/0.61  thf('20', plain,
% 0.42/0.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['18', '19'])).
% 0.42/0.61  thf('21', plain,
% 0.42/0.61      (![X9 : $i, X10 : $i]:
% 0.42/0.61         ((k4_xboole_0 @ X9 @ X10)
% 0.42/0.61           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.42/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.42/0.61  thf(t91_xboole_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.42/0.61       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.42/0.61  thf('22', plain,
% 0.42/0.61      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.42/0.61         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 0.42/0.61           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 0.42/0.61      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.42/0.61  thf('23', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.61         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.42/0.61           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 0.42/0.61      inference('sup+', [status(thm)], ['21', '22'])).
% 0.42/0.61  thf('24', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.42/0.61           = (k5_xboole_0 @ X1 @ 
% 0.42/0.61              (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))))),
% 0.42/0.61      inference('sup+', [status(thm)], ['20', '23'])).
% 0.42/0.61  thf('25', plain,
% 0.42/0.61      (![X17 : $i, X18 : $i]:
% 0.42/0.61         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.42/0.61           = (k3_xboole_0 @ X17 @ X18))),
% 0.42/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.42/0.61  thf(t98_xboole_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.42/0.61  thf('26', plain,
% 0.42/0.61      (![X22 : $i, X23 : $i]:
% 0.42/0.61         ((k2_xboole_0 @ X22 @ X23)
% 0.42/0.61           = (k5_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22)))),
% 0.42/0.61      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.42/0.61  thf('27', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 0.42/0.61           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.42/0.61      inference('sup+', [status(thm)], ['25', '26'])).
% 0.42/0.61  thf(t3_boole, axiom,
% 0.42/0.61    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.42/0.61  thf('28', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.42/0.61      inference('cnf', [status(esa)], [t3_boole])).
% 0.42/0.61  thf('29', plain,
% 0.42/0.61      (![X17 : $i, X18 : $i]:
% 0.42/0.61         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.42/0.61           = (k3_xboole_0 @ X17 @ X18))),
% 0.42/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.42/0.61  thf('30', plain,
% 0.42/0.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['28', '29'])).
% 0.42/0.61  thf('31', plain,
% 0.42/0.61      (![X9 : $i, X10 : $i]:
% 0.42/0.61         ((k4_xboole_0 @ X9 @ X10)
% 0.42/0.61           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.42/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.42/0.61  thf('32', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.42/0.61      inference('cnf', [status(esa)], [t3_boole])).
% 0.42/0.61  thf('33', plain,
% 0.42/0.61      (![X22 : $i, X23 : $i]:
% 0.42/0.61         ((k2_xboole_0 @ X22 @ X23)
% 0.42/0.61           = (k5_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22)))),
% 0.42/0.61      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.42/0.61  thf('34', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['32', '33'])).
% 0.42/0.61  thf('35', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0))
% 0.42/0.61           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['31', '34'])).
% 0.42/0.61  thf(t22_xboole_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.42/0.61  thf('36', plain,
% 0.42/0.61      (![X12 : $i, X13 : $i]:
% 0.42/0.61         ((k2_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)) = (X12))),
% 0.42/0.61      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.42/0.61  thf('37', plain,
% 0.42/0.61      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.42/0.61      inference('demod', [status(thm)], ['35', '36'])).
% 0.42/0.61  thf('38', plain,
% 0.42/0.61      (![X17 : $i, X18 : $i]:
% 0.42/0.61         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.42/0.61           = (k3_xboole_0 @ X17 @ X18))),
% 0.42/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.42/0.61  thf('39', plain,
% 0.42/0.61      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['37', '38'])).
% 0.42/0.61  thf('40', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.42/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.42/0.61  thf('41', plain,
% 0.42/0.61      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['39', '40'])).
% 0.42/0.61  thf('42', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.42/0.61      inference('demod', [status(thm)], ['30', '41'])).
% 0.42/0.61  thf('43', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 0.42/0.61           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.42/0.61      inference('demod', [status(thm)], ['24', '27', '42'])).
% 0.42/0.61  thf('44', plain,
% 0.42/0.61      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.42/0.61      inference('demod', [status(thm)], ['35', '36'])).
% 0.42/0.61  thf('45', plain,
% 0.42/0.61      (![X22 : $i, X23 : $i]:
% 0.42/0.61         ((k2_xboole_0 @ X22 @ X23)
% 0.42/0.61           = (k5_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22)))),
% 0.42/0.61      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.42/0.61  thf('46', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['44', '45'])).
% 0.42/0.61  thf(t1_boole, axiom,
% 0.42/0.61    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.42/0.61  thf('47', plain, (![X11 : $i]: ((k2_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.42/0.61      inference('cnf', [status(esa)], [t1_boole])).
% 0.42/0.61  thf('48', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.42/0.61      inference('demod', [status(thm)], ['46', '47'])).
% 0.42/0.61  thf('49', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) = (X1))),
% 0.42/0.61      inference('demod', [status(thm)], ['43', '48'])).
% 0.42/0.61  thf('50', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (X1))),
% 0.42/0.61      inference('sup+', [status(thm)], ['14', '49'])).
% 0.42/0.61  thf('51', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['13', '50'])).
% 0.42/0.61  thf('52', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))
% 0.42/0.61           = (k2_tarski @ X0 @ X1))),
% 0.42/0.61      inference('sup+', [status(thm)], ['12', '51'])).
% 0.42/0.61  thf(t42_enumset1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.42/0.61       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.42/0.61  thf('53', plain,
% 0.42/0.61      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.42/0.61         ((k1_enumset1 @ X35 @ X36 @ X37)
% 0.42/0.61           = (k2_xboole_0 @ (k1_tarski @ X35) @ (k2_tarski @ X36 @ X37)))),
% 0.42/0.61      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.42/0.61  thf('54', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         ((k1_enumset1 @ X0 @ X0 @ X1) = (k2_tarski @ X0 @ X1))),
% 0.42/0.61      inference('demod', [status(thm)], ['52', '53'])).
% 0.42/0.61  thf('55', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.42/0.61      inference('demod', [status(thm)], ['0', '54'])).
% 0.42/0.61  thf('56', plain, ($false), inference('simplify', [status(thm)], ['55'])).
% 0.42/0.61  
% 0.42/0.61  % SZS output end Refutation
% 0.42/0.61  
% 0.42/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

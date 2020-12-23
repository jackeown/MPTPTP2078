%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.D8HJ6LL8ea

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:23 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 118 expanded)
%              Number of leaves         :   27 (  47 expanded)
%              Depth                    :   15
%              Number of atoms          :  571 ( 827 expanded)
%              Number of equality atoms :   68 ( 101 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X27 != X29 )
      | ( r2_hidden @ X27 @ X28 )
      | ( X28
       != ( k2_tarski @ X29 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('2',plain,(
    ! [X26: $i,X29: $i] :
      ( r2_hidden @ X29 @ ( k2_tarski @ X29 @ X26 ) ) ),
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
    ! [X21: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X24 @ X23 )
      | ( X24 = X21 )
      | ( X23
       != ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('5',plain,(
    ! [X21: $i,X24: $i] :
      ( ( X24 = X21 )
      | ~ ( r2_hidden @ X24 @ ( k1_tarski @ X21 ) ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('15',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('25',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('26',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('31',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('32',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('35',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','24','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','38'])).

thf('42',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('45',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = X1 ) ),
    inference(demod,[status(thm)],['40','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['14','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','50'])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('52',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X32 @ X33 @ X34 )
      = ( k2_xboole_0 @ ( k1_tarski @ X32 ) @ ( k2_tarski @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','53'])).

thf('55',plain,(
    $false ),
    inference(simplify,[status(thm)],['54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.D8HJ6LL8ea
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:46:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.62  % Solved by: fo/fo7.sh
% 0.45/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.62  % done 461 iterations in 0.168s
% 0.45/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.62  % SZS output start Refutation
% 0.45/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.45/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.62  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.45/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.62  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.45/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.62  thf(t70_enumset1, conjecture,
% 0.45/0.62    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.45/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.62    (~( ![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ) )),
% 0.45/0.62    inference('cnf.neg', [status(esa)], [t70_enumset1])).
% 0.45/0.62  thf('0', plain,
% 0.45/0.62      (((k1_enumset1 @ sk_A @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.45/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.62  thf(d2_tarski, axiom,
% 0.45/0.62    (![A:$i,B:$i,C:$i]:
% 0.45/0.62     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.45/0.62       ( ![D:$i]:
% 0.45/0.62         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.45/0.62  thf('1', plain,
% 0.45/0.62      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.45/0.62         (((X27) != (X29))
% 0.45/0.62          | (r2_hidden @ X27 @ X28)
% 0.45/0.62          | ((X28) != (k2_tarski @ X29 @ X26)))),
% 0.45/0.62      inference('cnf', [status(esa)], [d2_tarski])).
% 0.45/0.62  thf('2', plain,
% 0.45/0.62      (![X26 : $i, X29 : $i]: (r2_hidden @ X29 @ (k2_tarski @ X29 @ X26))),
% 0.45/0.62      inference('simplify', [status(thm)], ['1'])).
% 0.45/0.62  thf(d3_tarski, axiom,
% 0.45/0.62    (![A:$i,B:$i]:
% 0.45/0.62     ( ( r1_tarski @ A @ B ) <=>
% 0.45/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.45/0.62  thf('3', plain,
% 0.45/0.62      (![X3 : $i, X5 : $i]:
% 0.45/0.62         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.45/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.62  thf(d1_tarski, axiom,
% 0.45/0.62    (![A:$i,B:$i]:
% 0.45/0.62     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.45/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.45/0.62  thf('4', plain,
% 0.45/0.62      (![X21 : $i, X23 : $i, X24 : $i]:
% 0.45/0.62         (~ (r2_hidden @ X24 @ X23)
% 0.45/0.62          | ((X24) = (X21))
% 0.45/0.62          | ((X23) != (k1_tarski @ X21)))),
% 0.45/0.62      inference('cnf', [status(esa)], [d1_tarski])).
% 0.45/0.62  thf('5', plain,
% 0.45/0.62      (![X21 : $i, X24 : $i]:
% 0.45/0.62         (((X24) = (X21)) | ~ (r2_hidden @ X24 @ (k1_tarski @ X21)))),
% 0.45/0.62      inference('simplify', [status(thm)], ['4'])).
% 0.45/0.62  thf('6', plain,
% 0.45/0.62      (![X0 : $i, X1 : $i]:
% 0.45/0.62         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.45/0.62          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.45/0.62      inference('sup-', [status(thm)], ['3', '5'])).
% 0.45/0.62  thf('7', plain,
% 0.45/0.62      (![X3 : $i, X5 : $i]:
% 0.45/0.62         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.45/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.62  thf('8', plain,
% 0.45/0.62      (![X0 : $i, X1 : $i]:
% 0.45/0.62         (~ (r2_hidden @ X0 @ X1)
% 0.45/0.62          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.45/0.62          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.45/0.62      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.62  thf('9', plain,
% 0.45/0.62      (![X0 : $i, X1 : $i]:
% 0.45/0.62         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.45/0.62      inference('simplify', [status(thm)], ['8'])).
% 0.45/0.62  thf('10', plain,
% 0.45/0.62      (![X0 : $i, X1 : $i]:
% 0.45/0.62         (r1_tarski @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.45/0.62      inference('sup-', [status(thm)], ['2', '9'])).
% 0.45/0.62  thf(t28_xboole_1, axiom,
% 0.45/0.62    (![A:$i,B:$i]:
% 0.45/0.62     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.45/0.62  thf('11', plain,
% 0.45/0.62      (![X11 : $i, X12 : $i]:
% 0.45/0.62         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.45/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.45/0.62  thf('12', plain,
% 0.45/0.62      (![X0 : $i, X1 : $i]:
% 0.45/0.62         ((k3_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.45/0.62           = (k1_tarski @ X1))),
% 0.45/0.62      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.62  thf(commutativity_k3_xboole_0, axiom,
% 0.45/0.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.45/0.62  thf('13', plain,
% 0.45/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.62  thf(t48_xboole_1, axiom,
% 0.45/0.62    (![A:$i,B:$i]:
% 0.45/0.62     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.62  thf('14', plain,
% 0.45/0.62      (![X14 : $i, X15 : $i]:
% 0.45/0.62         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.45/0.62           = (k3_xboole_0 @ X14 @ X15))),
% 0.45/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.62  thf(idempotence_k3_xboole_0, axiom,
% 0.45/0.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.45/0.62  thf('15', plain, (![X6 : $i]: ((k3_xboole_0 @ X6 @ X6) = (X6))),
% 0.45/0.62      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.45/0.62  thf(t100_xboole_1, axiom,
% 0.45/0.62    (![A:$i,B:$i]:
% 0.45/0.62     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.45/0.62  thf('16', plain,
% 0.45/0.62      (![X7 : $i, X8 : $i]:
% 0.45/0.62         ((k4_xboole_0 @ X7 @ X8)
% 0.45/0.62           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.45/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.62  thf('17', plain,
% 0.45/0.62      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.45/0.62      inference('sup+', [status(thm)], ['15', '16'])).
% 0.45/0.62  thf('18', plain,
% 0.45/0.62      (![X7 : $i, X8 : $i]:
% 0.45/0.62         ((k4_xboole_0 @ X7 @ X8)
% 0.45/0.62           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.45/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.62  thf(t91_xboole_1, axiom,
% 0.45/0.62    (![A:$i,B:$i,C:$i]:
% 0.45/0.62     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.45/0.62       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.45/0.62  thf('19', plain,
% 0.45/0.62      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.45/0.62         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.45/0.62           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.45/0.62      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.45/0.62  thf('20', plain,
% 0.45/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.62         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.45/0.62           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 0.45/0.62      inference('sup+', [status(thm)], ['18', '19'])).
% 0.45/0.62  thf('21', plain,
% 0.45/0.62      (![X0 : $i, X1 : $i]:
% 0.45/0.62         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.45/0.62           = (k5_xboole_0 @ X1 @ 
% 0.45/0.62              (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))))),
% 0.45/0.62      inference('sup+', [status(thm)], ['17', '20'])).
% 0.45/0.62  thf('22', plain,
% 0.45/0.62      (![X14 : $i, X15 : $i]:
% 0.45/0.62         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.45/0.62           = (k3_xboole_0 @ X14 @ X15))),
% 0.45/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.62  thf(t98_xboole_1, axiom,
% 0.45/0.62    (![A:$i,B:$i]:
% 0.45/0.62     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.45/0.62  thf('23', plain,
% 0.45/0.62      (![X19 : $i, X20 : $i]:
% 0.45/0.62         ((k2_xboole_0 @ X19 @ X20)
% 0.45/0.62           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 0.45/0.62      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.45/0.62  thf('24', plain,
% 0.45/0.62      (![X0 : $i, X1 : $i]:
% 0.45/0.62         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 0.45/0.62           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.45/0.62      inference('sup+', [status(thm)], ['22', '23'])).
% 0.45/0.62  thf(t3_boole, axiom,
% 0.45/0.62    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.45/0.62  thf('25', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.45/0.62      inference('cnf', [status(esa)], [t3_boole])).
% 0.45/0.62  thf('26', plain,
% 0.45/0.62      (![X14 : $i, X15 : $i]:
% 0.45/0.62         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.45/0.62           = (k3_xboole_0 @ X14 @ X15))),
% 0.45/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.62  thf('27', plain,
% 0.45/0.62      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.62      inference('sup+', [status(thm)], ['25', '26'])).
% 0.45/0.62  thf('28', plain,
% 0.45/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.62  thf('29', plain,
% 0.45/0.62      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.45/0.62      inference('sup+', [status(thm)], ['27', '28'])).
% 0.45/0.62  thf('30', plain,
% 0.45/0.62      (![X7 : $i, X8 : $i]:
% 0.45/0.62         ((k4_xboole_0 @ X7 @ X8)
% 0.45/0.62           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.45/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.62  thf('31', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.45/0.62      inference('cnf', [status(esa)], [t3_boole])).
% 0.45/0.62  thf('32', plain,
% 0.45/0.62      (![X19 : $i, X20 : $i]:
% 0.45/0.62         ((k2_xboole_0 @ X19 @ X20)
% 0.45/0.62           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 0.45/0.62      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.45/0.62  thf('33', plain,
% 0.45/0.62      (![X0 : $i]:
% 0.45/0.62         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.45/0.62      inference('sup+', [status(thm)], ['31', '32'])).
% 0.45/0.62  thf('34', plain,
% 0.45/0.62      (![X0 : $i]:
% 0.45/0.62         ((k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0))
% 0.45/0.62           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.45/0.62      inference('sup+', [status(thm)], ['30', '33'])).
% 0.45/0.62  thf(t22_xboole_1, axiom,
% 0.45/0.62    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.45/0.62  thf('35', plain,
% 0.45/0.62      (![X9 : $i, X10 : $i]:
% 0.45/0.62         ((k2_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)) = (X9))),
% 0.45/0.62      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.45/0.62  thf('36', plain,
% 0.45/0.62      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.45/0.62      inference('demod', [status(thm)], ['34', '35'])).
% 0.45/0.62  thf('37', plain,
% 0.45/0.62      (![X14 : $i, X15 : $i]:
% 0.45/0.62         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.45/0.62           = (k3_xboole_0 @ X14 @ X15))),
% 0.45/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.62  thf('38', plain,
% 0.45/0.62      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.45/0.62      inference('sup+', [status(thm)], ['36', '37'])).
% 0.45/0.62  thf('39', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.45/0.62      inference('demod', [status(thm)], ['29', '38'])).
% 0.45/0.62  thf('40', plain,
% 0.45/0.62      (![X0 : $i, X1 : $i]:
% 0.45/0.62         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 0.45/0.62           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.45/0.62      inference('demod', [status(thm)], ['21', '24', '39'])).
% 0.45/0.62  thf('41', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.45/0.62      inference('demod', [status(thm)], ['29', '38'])).
% 0.45/0.62  thf('42', plain,
% 0.45/0.62      (![X19 : $i, X20 : $i]:
% 0.45/0.62         ((k2_xboole_0 @ X19 @ X20)
% 0.45/0.62           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 0.45/0.62      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.45/0.62  thf('43', plain,
% 0.45/0.62      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.62      inference('sup+', [status(thm)], ['41', '42'])).
% 0.45/0.62  thf('44', plain, (![X6 : $i]: ((k3_xboole_0 @ X6 @ X6) = (X6))),
% 0.45/0.62      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.45/0.62  thf('45', plain,
% 0.45/0.62      (![X9 : $i, X10 : $i]:
% 0.45/0.62         ((k2_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)) = (X9))),
% 0.45/0.62      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.45/0.62  thf('46', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.45/0.62      inference('sup+', [status(thm)], ['44', '45'])).
% 0.45/0.62  thf('47', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.62      inference('demod', [status(thm)], ['43', '46'])).
% 0.45/0.62  thf('48', plain,
% 0.45/0.62      (![X0 : $i, X1 : $i]:
% 0.45/0.62         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) = (X1))),
% 0.45/0.62      inference('demod', [status(thm)], ['40', '47'])).
% 0.45/0.62  thf('49', plain,
% 0.45/0.62      (![X0 : $i, X1 : $i]:
% 0.45/0.62         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (X1))),
% 0.45/0.62      inference('sup+', [status(thm)], ['14', '48'])).
% 0.45/0.62  thf('50', plain,
% 0.45/0.62      (![X0 : $i, X1 : $i]:
% 0.45/0.62         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 0.45/0.62      inference('sup+', [status(thm)], ['13', '49'])).
% 0.45/0.62  thf('51', plain,
% 0.45/0.62      (![X0 : $i, X1 : $i]:
% 0.45/0.62         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))
% 0.45/0.62           = (k2_tarski @ X0 @ X1))),
% 0.45/0.62      inference('sup+', [status(thm)], ['12', '50'])).
% 0.45/0.62  thf(t42_enumset1, axiom,
% 0.45/0.62    (![A:$i,B:$i,C:$i]:
% 0.45/0.62     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.45/0.62       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.45/0.62  thf('52', plain,
% 0.45/0.62      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.45/0.62         ((k1_enumset1 @ X32 @ X33 @ X34)
% 0.45/0.62           = (k2_xboole_0 @ (k1_tarski @ X32) @ (k2_tarski @ X33 @ X34)))),
% 0.45/0.62      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.45/0.62  thf('53', plain,
% 0.45/0.62      (![X0 : $i, X1 : $i]:
% 0.45/0.62         ((k1_enumset1 @ X0 @ X0 @ X1) = (k2_tarski @ X0 @ X1))),
% 0.45/0.62      inference('demod', [status(thm)], ['51', '52'])).
% 0.45/0.62  thf('54', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.45/0.62      inference('demod', [status(thm)], ['0', '53'])).
% 0.45/0.62  thf('55', plain, ($false), inference('simplify', [status(thm)], ['54'])).
% 0.45/0.62  
% 0.45/0.62  % SZS output end Refutation
% 0.45/0.62  
% 0.45/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

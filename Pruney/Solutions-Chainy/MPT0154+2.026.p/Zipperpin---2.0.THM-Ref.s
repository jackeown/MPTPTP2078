%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vRC0Viu1EK

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:25 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 230 expanded)
%              Number of leaves         :   25 (  84 expanded)
%              Depth                    :   20
%              Number of atoms          :  545 (1583 expanded)
%              Number of equality atoms :   69 ( 216 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X23: $i] :
      ( ( k2_tarski @ X23 @ X23 )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_tarski @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k1_tarski @ X18 ) @ ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('11',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('12',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('19',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','26'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('28',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','26'])).

thf('31',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','26'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','42'])).

thf('44',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','45'])).

thf('47',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','48'])).

thf('50',plain,(
    ! [X23: $i] :
      ( ( k2_tarski @ X23 @ X23 )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('51',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X20 @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k1_tarski @ X20 ) @ ( k2_tarski @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['49','52','53'])).

thf('55',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','54'])).

thf('56',plain,(
    $false ),
    inference(simplify,[status(thm)],['55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vRC0Viu1EK
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:54:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.41/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.62  % Solved by: fo/fo7.sh
% 0.41/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.62  % done 358 iterations in 0.165s
% 0.41/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.62  % SZS output start Refutation
% 0.41/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.41/0.62  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.41/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.62  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.41/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.41/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.41/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.41/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.41/0.62  thf(t70_enumset1, conjecture,
% 0.41/0.62    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.41/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.62    (~( ![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ) )),
% 0.41/0.62    inference('cnf.neg', [status(esa)], [t70_enumset1])).
% 0.41/0.62  thf('0', plain,
% 0.41/0.62      (((k1_enumset1 @ sk_A @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(t69_enumset1, axiom,
% 0.41/0.62    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.41/0.62  thf('1', plain, (![X23 : $i]: ((k2_tarski @ X23 @ X23) = (k1_tarski @ X23))),
% 0.41/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.41/0.62  thf(t41_enumset1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( k2_tarski @ A @ B ) =
% 0.41/0.62       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.41/0.62  thf('2', plain,
% 0.41/0.62      (![X18 : $i, X19 : $i]:
% 0.41/0.62         ((k2_tarski @ X18 @ X19)
% 0.41/0.62           = (k2_xboole_0 @ (k1_tarski @ X18) @ (k1_tarski @ X19)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.41/0.62  thf('3', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         ((k2_tarski @ X0 @ X1)
% 0.41/0.62           = (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X1)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['1', '2'])).
% 0.41/0.62  thf(t7_xboole_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.41/0.62  thf('4', plain,
% 0.41/0.62      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 0.41/0.62      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.41/0.62  thf(t28_xboole_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.41/0.62  thf('5', plain,
% 0.41/0.62      (![X5 : $i, X6 : $i]:
% 0.41/0.62         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.41/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.41/0.62  thf('6', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['4', '5'])).
% 0.41/0.62  thf(commutativity_k3_xboole_0, axiom,
% 0.41/0.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.41/0.62  thf('7', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.41/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.41/0.62  thf(t100_xboole_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.41/0.62  thf('8', plain,
% 0.41/0.62      (![X3 : $i, X4 : $i]:
% 0.41/0.62         ((k4_xboole_0 @ X3 @ X4)
% 0.41/0.62           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.41/0.62  thf('9', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         ((k4_xboole_0 @ X0 @ X1)
% 0.41/0.62           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['7', '8'])).
% 0.41/0.62  thf('10', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 0.41/0.62           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 0.41/0.62      inference('sup+', [status(thm)], ['6', '9'])).
% 0.41/0.62  thf(idempotence_k3_xboole_0, axiom,
% 0.41/0.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.41/0.62  thf('11', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.41/0.62      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.41/0.62  thf('12', plain,
% 0.41/0.62      (![X3 : $i, X4 : $i]:
% 0.41/0.62         ((k4_xboole_0 @ X3 @ X4)
% 0.41/0.62           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.41/0.62  thf('13', plain,
% 0.41/0.62      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.41/0.62      inference('sup+', [status(thm)], ['11', '12'])).
% 0.41/0.62  thf(t48_xboole_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.41/0.62  thf('14', plain,
% 0.41/0.62      (![X7 : $i, X8 : $i]:
% 0.41/0.62         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.41/0.62           = (k3_xboole_0 @ X7 @ X8))),
% 0.41/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.41/0.62  thf(t4_boole, axiom,
% 0.41/0.62    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.41/0.62  thf('15', plain,
% 0.41/0.62      (![X9 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 0.41/0.62      inference('cnf', [status(esa)], [t4_boole])).
% 0.41/0.62  thf('16', plain,
% 0.41/0.62      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.41/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.41/0.62  thf('17', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         ((k4_xboole_0 @ X0 @ X1)
% 0.41/0.62           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['7', '8'])).
% 0.41/0.62  thf('18', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.41/0.62      inference('sup+', [status(thm)], ['16', '17'])).
% 0.41/0.62  thf(t5_boole, axiom,
% 0.41/0.62    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.41/0.62  thf('19', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.41/0.62      inference('cnf', [status(esa)], [t5_boole])).
% 0.41/0.62  thf('20', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.41/0.62      inference('sup+', [status(thm)], ['18', '19'])).
% 0.41/0.62  thf('21', plain,
% 0.41/0.62      (![X7 : $i, X8 : $i]:
% 0.41/0.62         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.41/0.62           = (k3_xboole_0 @ X7 @ X8))),
% 0.41/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.41/0.62  thf('22', plain,
% 0.41/0.62      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.41/0.62      inference('sup+', [status(thm)], ['20', '21'])).
% 0.41/0.62  thf('23', plain,
% 0.41/0.62      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.41/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.41/0.62  thf('24', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.41/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.41/0.62  thf('25', plain,
% 0.41/0.62      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.41/0.62      inference('sup+', [status(thm)], ['23', '24'])).
% 0.41/0.62  thf('26', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.41/0.62      inference('demod', [status(thm)], ['22', '25'])).
% 0.41/0.62  thf('27', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.41/0.62      inference('demod', [status(thm)], ['13', '26'])).
% 0.41/0.62  thf(t91_xboole_1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.41/0.62       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.41/0.62  thf('28', plain,
% 0.41/0.62      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.41/0.62         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.41/0.62           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.41/0.62  thf('29', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         ((k1_xboole_0)
% 0.41/0.62           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 0.41/0.62      inference('sup+', [status(thm)], ['27', '28'])).
% 0.41/0.62  thf('30', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.41/0.62      inference('demod', [status(thm)], ['13', '26'])).
% 0.41/0.62  thf('31', plain,
% 0.41/0.62      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.41/0.62         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.41/0.62           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.41/0.62  thf('32', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.41/0.62           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['30', '31'])).
% 0.41/0.62  thf('33', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.41/0.62      inference('sup+', [status(thm)], ['18', '19'])).
% 0.41/0.62  thf(t98_xboole_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.41/0.62  thf('34', plain,
% 0.41/0.62      (![X16 : $i, X17 : $i]:
% 0.41/0.62         ((k2_xboole_0 @ X16 @ X17)
% 0.41/0.62           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.41/0.62  thf('35', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.41/0.62      inference('sup+', [status(thm)], ['33', '34'])).
% 0.41/0.62  thf('36', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.41/0.62           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.41/0.62      inference('demod', [status(thm)], ['32', '35'])).
% 0.41/0.62  thf('37', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.41/0.62      inference('demod', [status(thm)], ['13', '26'])).
% 0.41/0.62  thf('38', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.41/0.62           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.41/0.62      inference('demod', [status(thm)], ['32', '35'])).
% 0.41/0.62  thf('39', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.41/0.62      inference('sup+', [status(thm)], ['37', '38'])).
% 0.41/0.62  thf('40', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.41/0.62      inference('cnf', [status(esa)], [t5_boole])).
% 0.41/0.62  thf('41', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.41/0.62      inference('sup+', [status(thm)], ['39', '40'])).
% 0.41/0.62  thf('42', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.41/0.62      inference('demod', [status(thm)], ['36', '41'])).
% 0.41/0.62  thf('43', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 0.41/0.62           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.41/0.62      inference('sup+', [status(thm)], ['29', '42'])).
% 0.41/0.62  thf('44', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.41/0.62      inference('cnf', [status(esa)], [t5_boole])).
% 0.41/0.62  thf('45', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 0.41/0.62      inference('demod', [status(thm)], ['43', '44'])).
% 0.41/0.62  thf('46', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))
% 0.41/0.62           = (k2_xboole_0 @ X0 @ X1))),
% 0.41/0.62      inference('sup+', [status(thm)], ['10', '45'])).
% 0.41/0.62  thf('47', plain,
% 0.41/0.62      (![X16 : $i, X17 : $i]:
% 0.41/0.62         ((k2_xboole_0 @ X16 @ X17)
% 0.41/0.62           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.41/0.62  thf('48', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.41/0.62           = (k2_xboole_0 @ X0 @ X1))),
% 0.41/0.62      inference('demod', [status(thm)], ['46', '47'])).
% 0.41/0.62  thf('49', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         ((k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ (k2_tarski @ X1 @ X0))
% 0.41/0.62           = (k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ (k1_tarski @ X0)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['3', '48'])).
% 0.41/0.62  thf('50', plain,
% 0.41/0.62      (![X23 : $i]: ((k2_tarski @ X23 @ X23) = (k1_tarski @ X23))),
% 0.41/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.41/0.62  thf(t42_enumset1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.41/0.62       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.41/0.62  thf('51', plain,
% 0.41/0.62      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.41/0.62         ((k1_enumset1 @ X20 @ X21 @ X22)
% 0.41/0.62           = (k2_xboole_0 @ (k1_tarski @ X20) @ (k2_tarski @ X21 @ X22)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.41/0.62  thf('52', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.62         ((k1_enumset1 @ X0 @ X2 @ X1)
% 0.41/0.62           = (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k2_tarski @ X2 @ X1)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['50', '51'])).
% 0.41/0.62  thf('53', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         ((k2_tarski @ X0 @ X1)
% 0.41/0.62           = (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X1)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['1', '2'])).
% 0.41/0.62  thf('54', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         ((k1_enumset1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.41/0.62      inference('demod', [status(thm)], ['49', '52', '53'])).
% 0.41/0.62  thf('55', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.41/0.62      inference('demod', [status(thm)], ['0', '54'])).
% 0.41/0.62  thf('56', plain, ($false), inference('simplify', [status(thm)], ['55'])).
% 0.41/0.62  
% 0.41/0.62  % SZS output end Refutation
% 0.41/0.62  
% 0.41/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

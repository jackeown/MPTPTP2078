%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ttBfc9opKh

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 128 expanded)
%              Number of leaves         :   23 (  50 expanded)
%              Depth                    :   18
%              Number of atoms          :  533 ( 896 expanded)
%              Number of equality atoms :   65 ( 110 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_tarski @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k1_tarski @ X21 ) @ ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_tarski @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('8',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('19',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('22',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('23',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('26',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','32'])).

thf('34',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','17','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('42',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('46',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = X1 ) ),
    inference(demod,[status(thm)],['39','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['7','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['6','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','49'])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('51',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k1_enumset1 @ X23 @ X24 @ X25 )
      = ( k2_xboole_0 @ ( k1_tarski @ X23 ) @ ( k2_tarski @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','52'])).

thf('54',plain,(
    $false ),
    inference(simplify,[status(thm)],['53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ttBfc9opKh
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:38:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.68  % Solved by: fo/fo7.sh
% 0.21/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.68  % done 660 iterations in 0.218s
% 0.21/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.68  % SZS output start Refutation
% 0.21/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.68  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.68  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.68  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.68  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.68  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.68  thf(t70_enumset1, conjecture,
% 0.21/0.68    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.68    (~( ![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ) )),
% 0.21/0.68    inference('cnf.neg', [status(esa)], [t70_enumset1])).
% 0.21/0.68  thf('0', plain,
% 0.21/0.68      (((k1_enumset1 @ sk_A @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.21/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.68  thf(t41_enumset1, axiom,
% 0.21/0.68    (![A:$i,B:$i]:
% 0.21/0.68     ( ( k2_tarski @ A @ B ) =
% 0.21/0.68       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.21/0.68  thf('1', plain,
% 0.21/0.68      (![X21 : $i, X22 : $i]:
% 0.21/0.68         ((k2_tarski @ X21 @ X22)
% 0.21/0.68           = (k2_xboole_0 @ (k1_tarski @ X21) @ (k1_tarski @ X22)))),
% 0.21/0.68      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.21/0.68  thf(t7_xboole_1, axiom,
% 0.21/0.68    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.68  thf('2', plain,
% 0.21/0.68      (![X10 : $i, X11 : $i]: (r1_tarski @ X10 @ (k2_xboole_0 @ X10 @ X11))),
% 0.21/0.68      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.21/0.68  thf(t28_xboole_1, axiom,
% 0.21/0.68    (![A:$i,B:$i]:
% 0.21/0.68     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.68  thf('3', plain,
% 0.21/0.68      (![X5 : $i, X6 : $i]:
% 0.21/0.68         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.21/0.68      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.68  thf('4', plain,
% 0.21/0.68      (![X0 : $i, X1 : $i]:
% 0.21/0.68         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.21/0.68      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.68  thf('5', plain,
% 0.21/0.68      (![X0 : $i, X1 : $i]:
% 0.21/0.68         ((k3_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.21/0.68           = (k1_tarski @ X1))),
% 0.21/0.68      inference('sup+', [status(thm)], ['1', '4'])).
% 0.21/0.68  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.68    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.68  thf('6', plain,
% 0.21/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.68  thf(t48_xboole_1, axiom,
% 0.21/0.68    (![A:$i,B:$i]:
% 0.21/0.68     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.68  thf('7', plain,
% 0.21/0.68      (![X8 : $i, X9 : $i]:
% 0.21/0.68         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.21/0.68           = (k3_xboole_0 @ X8 @ X9))),
% 0.21/0.68      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.68  thf(idempotence_k3_xboole_0, axiom,
% 0.21/0.68    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.21/0.68  thf('8', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.21/0.68      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.21/0.68  thf(t100_xboole_1, axiom,
% 0.21/0.68    (![A:$i,B:$i]:
% 0.21/0.68     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.68  thf('9', plain,
% 0.21/0.68      (![X3 : $i, X4 : $i]:
% 0.21/0.68         ((k4_xboole_0 @ X3 @ X4)
% 0.21/0.68           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.21/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.68  thf('10', plain,
% 0.21/0.68      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.21/0.68      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.68  thf('11', plain,
% 0.21/0.68      (![X3 : $i, X4 : $i]:
% 0.21/0.68         ((k4_xboole_0 @ X3 @ X4)
% 0.21/0.68           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.21/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.68  thf(t91_xboole_1, axiom,
% 0.21/0.68    (![A:$i,B:$i,C:$i]:
% 0.21/0.68     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.21/0.68       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.21/0.68  thf('12', plain,
% 0.21/0.68      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.68         ((k5_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ X14)
% 0.21/0.68           = (k5_xboole_0 @ X12 @ (k5_xboole_0 @ X13 @ X14)))),
% 0.21/0.68      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.21/0.68  thf('13', plain,
% 0.21/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.68         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.21/0.68           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 0.21/0.68      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.68  thf('14', plain,
% 0.21/0.68      (![X0 : $i, X1 : $i]:
% 0.21/0.68         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.68           = (k5_xboole_0 @ X1 @ 
% 0.21/0.68              (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))))),
% 0.21/0.68      inference('sup+', [status(thm)], ['10', '13'])).
% 0.21/0.68  thf('15', plain,
% 0.21/0.68      (![X8 : $i, X9 : $i]:
% 0.21/0.68         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.21/0.68           = (k3_xboole_0 @ X8 @ X9))),
% 0.21/0.68      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.68  thf(t98_xboole_1, axiom,
% 0.21/0.68    (![A:$i,B:$i]:
% 0.21/0.68     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.21/0.68  thf('16', plain,
% 0.21/0.68      (![X15 : $i, X16 : $i]:
% 0.21/0.68         ((k2_xboole_0 @ X15 @ X16)
% 0.21/0.68           = (k5_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15)))),
% 0.21/0.68      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.21/0.68  thf('17', plain,
% 0.21/0.68      (![X0 : $i, X1 : $i]:
% 0.21/0.68         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 0.21/0.68           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.68      inference('sup+', [status(thm)], ['15', '16'])).
% 0.21/0.68  thf(t3_boole, axiom,
% 0.21/0.68    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.68  thf('18', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.21/0.68      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.68  thf('19', plain,
% 0.21/0.68      (![X8 : $i, X9 : $i]:
% 0.21/0.68         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.21/0.68           = (k3_xboole_0 @ X8 @ X9))),
% 0.21/0.68      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.68  thf('20', plain,
% 0.21/0.68      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.68      inference('sup+', [status(thm)], ['18', '19'])).
% 0.21/0.68  thf('21', plain,
% 0.21/0.68      (![X3 : $i, X4 : $i]:
% 0.21/0.68         ((k4_xboole_0 @ X3 @ X4)
% 0.21/0.68           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.21/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.68  thf('22', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.21/0.68      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.68  thf('23', plain,
% 0.21/0.68      (![X15 : $i, X16 : $i]:
% 0.21/0.68         ((k2_xboole_0 @ X15 @ X16)
% 0.21/0.68           = (k5_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15)))),
% 0.21/0.68      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.21/0.68  thf('24', plain,
% 0.21/0.68      (![X0 : $i]:
% 0.21/0.68         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.21/0.68      inference('sup+', [status(thm)], ['22', '23'])).
% 0.21/0.68  thf('25', plain,
% 0.21/0.68      (![X0 : $i, X1 : $i]:
% 0.21/0.68         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.21/0.68      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.68  thf('26', plain,
% 0.21/0.68      (![X3 : $i, X4 : $i]:
% 0.21/0.68         ((k4_xboole_0 @ X3 @ X4)
% 0.21/0.68           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.21/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.68  thf('27', plain,
% 0.21/0.68      (![X0 : $i, X1 : $i]:
% 0.21/0.68         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.21/0.68           = (k5_xboole_0 @ X0 @ X0))),
% 0.21/0.68      inference('sup+', [status(thm)], ['25', '26'])).
% 0.21/0.68  thf('28', plain,
% 0.21/0.68      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.21/0.68      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.68  thf('29', plain,
% 0.21/0.68      (![X0 : $i, X1 : $i]:
% 0.21/0.68         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.21/0.68           = (k4_xboole_0 @ X0 @ X0))),
% 0.21/0.68      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.68  thf('30', plain,
% 0.21/0.68      (![X0 : $i]:
% 0.21/0.68         ((k4_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ k1_xboole_0 @ X0))
% 0.21/0.68           = (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.21/0.68      inference('sup+', [status(thm)], ['24', '29'])).
% 0.21/0.68  thf('31', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.21/0.68      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.68  thf('32', plain,
% 0.21/0.68      (![X0 : $i]:
% 0.21/0.68         ((k4_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ k1_xboole_0 @ X0))
% 0.21/0.68           = (k1_xboole_0))),
% 0.21/0.68      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.68  thf('33', plain,
% 0.21/0.68      (![X0 : $i]:
% 0.21/0.68         ((k4_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.21/0.68           = (k1_xboole_0))),
% 0.21/0.68      inference('sup+', [status(thm)], ['21', '32'])).
% 0.21/0.68  thf('34', plain,
% 0.21/0.68      (![X8 : $i, X9 : $i]:
% 0.21/0.68         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.21/0.68           = (k3_xboole_0 @ X8 @ X9))),
% 0.21/0.68      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.68  thf('35', plain,
% 0.21/0.68      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.68      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.68  thf('36', plain,
% 0.21/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.68  thf('37', plain,
% 0.21/0.68      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.68      inference('sup+', [status(thm)], ['35', '36'])).
% 0.21/0.68  thf('38', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.68      inference('demod', [status(thm)], ['20', '37'])).
% 0.21/0.68  thf('39', plain,
% 0.21/0.68      (![X0 : $i, X1 : $i]:
% 0.21/0.68         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 0.21/0.68           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.21/0.68      inference('demod', [status(thm)], ['14', '17', '38'])).
% 0.21/0.68  thf('40', plain,
% 0.21/0.68      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.68      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.68  thf('41', plain,
% 0.21/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.68  thf('42', plain,
% 0.21/0.68      (![X3 : $i, X4 : $i]:
% 0.21/0.68         ((k4_xboole_0 @ X3 @ X4)
% 0.21/0.68           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.21/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.68  thf('43', plain,
% 0.21/0.68      (![X0 : $i, X1 : $i]:
% 0.21/0.68         ((k4_xboole_0 @ X0 @ X1)
% 0.21/0.68           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.68      inference('sup+', [status(thm)], ['41', '42'])).
% 0.21/0.68  thf('44', plain,
% 0.21/0.68      (![X0 : $i]:
% 0.21/0.68         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.68      inference('sup+', [status(thm)], ['40', '43'])).
% 0.21/0.68  thf('45', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.21/0.68      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.68  thf('46', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.68      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.68  thf('47', plain,
% 0.21/0.68      (![X0 : $i, X1 : $i]:
% 0.21/0.68         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) = (X1))),
% 0.21/0.68      inference('demod', [status(thm)], ['39', '46'])).
% 0.21/0.68  thf('48', plain,
% 0.21/0.68      (![X0 : $i, X1 : $i]:
% 0.21/0.68         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (X1))),
% 0.21/0.68      inference('sup+', [status(thm)], ['7', '47'])).
% 0.21/0.68  thf('49', plain,
% 0.21/0.68      (![X0 : $i, X1 : $i]:
% 0.21/0.68         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 0.21/0.68      inference('sup+', [status(thm)], ['6', '48'])).
% 0.21/0.68  thf('50', plain,
% 0.21/0.68      (![X0 : $i, X1 : $i]:
% 0.21/0.68         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))
% 0.21/0.68           = (k2_tarski @ X0 @ X1))),
% 0.21/0.68      inference('sup+', [status(thm)], ['5', '49'])).
% 0.21/0.68  thf(t42_enumset1, axiom,
% 0.21/0.68    (![A:$i,B:$i,C:$i]:
% 0.21/0.68     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.21/0.68       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.21/0.68  thf('51', plain,
% 0.21/0.68      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.68         ((k1_enumset1 @ X23 @ X24 @ X25)
% 0.21/0.68           = (k2_xboole_0 @ (k1_tarski @ X23) @ (k2_tarski @ X24 @ X25)))),
% 0.21/0.68      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.21/0.68  thf('52', plain,
% 0.21/0.68      (![X0 : $i, X1 : $i]:
% 0.21/0.68         ((k1_enumset1 @ X0 @ X0 @ X1) = (k2_tarski @ X0 @ X1))),
% 0.21/0.68      inference('demod', [status(thm)], ['50', '51'])).
% 0.21/0.68  thf('53', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.21/0.68      inference('demod', [status(thm)], ['0', '52'])).
% 0.21/0.68  thf('54', plain, ($false), inference('simplify', [status(thm)], ['53'])).
% 0.21/0.68  
% 0.21/0.68  % SZS output end Refutation
% 0.21/0.68  
% 0.21/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

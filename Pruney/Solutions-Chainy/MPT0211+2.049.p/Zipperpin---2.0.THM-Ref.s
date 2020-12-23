%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zFIL6PYVad

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:36 EST 2020

% Result     : Theorem 6.42s
% Output     : Refutation 6.42s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 238 expanded)
%              Number of leaves         :   26 (  89 expanded)
%              Depth                    :   13
%              Number of atoms          :  626 (2222 expanded)
%              Number of equality atoms :   62 ( 225 expanded)
%              Maximal formula depth    :   12 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t137_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) )
        = ( k1_enumset1 @ A @ B @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t137_enumset1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_tarski @ sk_C @ sk_A ) )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X45: $i] :
      ( ( k2_tarski @ X45 @ X45 )
      = ( k1_tarski @ X45 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k1_enumset1 @ X46 @ X46 @ X47 )
      = ( k2_tarski @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('3',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( k2_enumset1 @ X41 @ X42 @ X43 @ X44 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X41 @ X42 @ X43 ) @ ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('5',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( k2_enumset1 @ X48 @ X48 @ X49 @ X50 )
      = ( k1_enumset1 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k1_enumset1 @ X46 @ X46 @ X47 )
      = ( k2_tarski @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k5_xboole_0 @ X4 @ ( k5_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X8 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['10','13','14'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t119_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ C @ D @ B @ A ) ) )).

thf('25',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k2_enumset1 @ X27 @ X26 @ X24 @ X25 )
      = ( k2_enumset1 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t119_enumset1])).

thf('26',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( k2_enumset1 @ X48 @ X48 @ X49 @ X50 )
      = ( k1_enumset1 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k2_enumset1 @ X27 @ X26 @ X24 @ X25 )
      = ( k2_enumset1 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t119_enumset1])).

thf('29',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( k2_enumset1 @ X48 @ X48 @ X49 @ X50 )
      = ( k1_enumset1 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_tarski @ sk_C @ sk_A ) )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['0','24','31'])).

thf('33',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k1_enumset1 @ X46 @ X46 @ X47 )
      = ( k2_tarski @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(l57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) )).

thf('34',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k3_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X11 @ X12 @ X13 ) @ ( k2_tarski @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t113_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ D @ C @ A ) ) )).

thf('36',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k2_enumset1 @ X23 @ X20 @ X22 @ X21 )
      = ( k2_enumset1 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t113_enumset1])).

thf('37',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( k2_enumset1 @ X48 @ X48 @ X49 @ X50 )
      = ( k1_enumset1 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('39',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( k3_enumset1 @ X51 @ X51 @ X52 @ X53 @ X54 )
      = ( k2_enumset1 @ X51 @ X52 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X2 @ X1 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ( k1_enumset1 @ sk_B @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['32','35','40','45'])).

thf('47',plain,(
    $false ),
    inference(simplify,[status(thm)],['46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zFIL6PYVad
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:35:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 6.42/6.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.42/6.65  % Solved by: fo/fo7.sh
% 6.42/6.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.42/6.65  % done 3488 iterations in 6.191s
% 6.42/6.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.42/6.65  % SZS output start Refutation
% 6.42/6.65  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 6.42/6.65  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 6.42/6.65  thf(sk_A_type, type, sk_A: $i).
% 6.42/6.65  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 6.42/6.65  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 6.42/6.65  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 6.42/6.65  thf(sk_B_type, type, sk_B: $i).
% 6.42/6.65  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 6.42/6.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 6.42/6.65  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 6.42/6.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 6.42/6.65  thf(sk_C_type, type, sk_C: $i).
% 6.42/6.65  thf(t137_enumset1, conjecture,
% 6.42/6.65    (![A:$i,B:$i,C:$i]:
% 6.42/6.65     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 6.42/6.65       ( k1_enumset1 @ A @ B @ C ) ))).
% 6.42/6.65  thf(zf_stmt_0, negated_conjecture,
% 6.42/6.65    (~( ![A:$i,B:$i,C:$i]:
% 6.42/6.65        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 6.42/6.65          ( k1_enumset1 @ A @ B @ C ) ) )),
% 6.42/6.65    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 6.42/6.65  thf('0', plain,
% 6.42/6.65      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 6.42/6.65         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 6.42/6.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.42/6.65  thf(t69_enumset1, axiom,
% 6.42/6.65    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 6.42/6.65  thf('1', plain, (![X45 : $i]: ((k2_tarski @ X45 @ X45) = (k1_tarski @ X45))),
% 6.42/6.65      inference('cnf', [status(esa)], [t69_enumset1])).
% 6.42/6.65  thf(t70_enumset1, axiom,
% 6.42/6.65    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 6.42/6.65  thf('2', plain,
% 6.42/6.65      (![X46 : $i, X47 : $i]:
% 6.42/6.65         ((k1_enumset1 @ X46 @ X46 @ X47) = (k2_tarski @ X46 @ X47))),
% 6.42/6.65      inference('cnf', [status(esa)], [t70_enumset1])).
% 6.42/6.65  thf(t46_enumset1, axiom,
% 6.42/6.65    (![A:$i,B:$i,C:$i,D:$i]:
% 6.42/6.65     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 6.42/6.65       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 6.42/6.65  thf('3', plain,
% 6.42/6.65      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 6.42/6.65         ((k2_enumset1 @ X41 @ X42 @ X43 @ X44)
% 6.42/6.65           = (k2_xboole_0 @ (k1_enumset1 @ X41 @ X42 @ X43) @ (k1_tarski @ X44)))),
% 6.42/6.65      inference('cnf', [status(esa)], [t46_enumset1])).
% 6.42/6.65  thf('4', plain,
% 6.42/6.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.42/6.65         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 6.42/6.65           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 6.42/6.65      inference('sup+', [status(thm)], ['2', '3'])).
% 6.42/6.65  thf(t71_enumset1, axiom,
% 6.42/6.65    (![A:$i,B:$i,C:$i]:
% 6.42/6.65     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 6.42/6.65  thf('5', plain,
% 6.42/6.65      (![X48 : $i, X49 : $i, X50 : $i]:
% 6.42/6.65         ((k2_enumset1 @ X48 @ X48 @ X49 @ X50)
% 6.42/6.65           = (k1_enumset1 @ X48 @ X49 @ X50))),
% 6.42/6.65      inference('cnf', [status(esa)], [t71_enumset1])).
% 6.42/6.65  thf('6', plain,
% 6.42/6.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.42/6.65         ((k1_enumset1 @ X1 @ X0 @ X2)
% 6.42/6.65           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 6.42/6.65      inference('demod', [status(thm)], ['4', '5'])).
% 6.42/6.65  thf('7', plain,
% 6.42/6.65      (![X0 : $i, X1 : $i]:
% 6.42/6.65         ((k1_enumset1 @ X0 @ X0 @ X1)
% 6.42/6.65           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 6.42/6.65      inference('sup+', [status(thm)], ['1', '6'])).
% 6.42/6.65  thf('8', plain,
% 6.42/6.65      (![X46 : $i, X47 : $i]:
% 6.42/6.65         ((k1_enumset1 @ X46 @ X46 @ X47) = (k2_tarski @ X46 @ X47))),
% 6.42/6.65      inference('cnf', [status(esa)], [t70_enumset1])).
% 6.42/6.65  thf('9', plain,
% 6.42/6.65      (![X0 : $i, X1 : $i]:
% 6.42/6.65         ((k2_tarski @ X0 @ X1)
% 6.42/6.65           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 6.42/6.65      inference('demod', [status(thm)], ['7', '8'])).
% 6.42/6.65  thf(t94_xboole_1, axiom,
% 6.42/6.65    (![A:$i,B:$i]:
% 6.42/6.65     ( ( k2_xboole_0 @ A @ B ) =
% 6.42/6.65       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 6.42/6.65  thf('10', plain,
% 6.42/6.65      (![X7 : $i, X8 : $i]:
% 6.42/6.65         ((k2_xboole_0 @ X7 @ X8)
% 6.42/6.65           = (k5_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ (k3_xboole_0 @ X7 @ X8)))),
% 6.42/6.65      inference('cnf', [status(esa)], [t94_xboole_1])).
% 6.42/6.65  thf(commutativity_k5_xboole_0, axiom,
% 6.42/6.65    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 6.42/6.65  thf('11', plain,
% 6.42/6.65      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 6.42/6.65      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 6.42/6.65  thf(t91_xboole_1, axiom,
% 6.42/6.65    (![A:$i,B:$i,C:$i]:
% 6.42/6.65     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 6.42/6.65       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 6.42/6.65  thf('12', plain,
% 6.42/6.65      (![X4 : $i, X5 : $i, X6 : $i]:
% 6.42/6.65         ((k5_xboole_0 @ (k5_xboole_0 @ X4 @ X5) @ X6)
% 6.42/6.65           = (k5_xboole_0 @ X4 @ (k5_xboole_0 @ X5 @ X6)))),
% 6.42/6.65      inference('cnf', [status(esa)], [t91_xboole_1])).
% 6.42/6.65  thf('13', plain,
% 6.42/6.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.42/6.65         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 6.42/6.65           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 6.42/6.65      inference('sup+', [status(thm)], ['11', '12'])).
% 6.42/6.65  thf(t100_xboole_1, axiom,
% 6.42/6.65    (![A:$i,B:$i]:
% 6.42/6.65     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 6.42/6.65  thf('14', plain,
% 6.42/6.65      (![X2 : $i, X3 : $i]:
% 6.42/6.65         ((k4_xboole_0 @ X2 @ X3)
% 6.42/6.65           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 6.42/6.65      inference('cnf', [status(esa)], [t100_xboole_1])).
% 6.42/6.65  thf('15', plain,
% 6.42/6.65      (![X7 : $i, X8 : $i]:
% 6.42/6.65         ((k2_xboole_0 @ X7 @ X8)
% 6.42/6.65           = (k5_xboole_0 @ X8 @ (k4_xboole_0 @ X7 @ X8)))),
% 6.42/6.65      inference('demod', [status(thm)], ['10', '13', '14'])).
% 6.42/6.65  thf(t98_xboole_1, axiom,
% 6.42/6.65    (![A:$i,B:$i]:
% 6.42/6.65     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 6.42/6.65  thf('16', plain,
% 6.42/6.65      (![X9 : $i, X10 : $i]:
% 6.42/6.65         ((k2_xboole_0 @ X9 @ X10)
% 6.42/6.65           = (k5_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9)))),
% 6.42/6.65      inference('cnf', [status(esa)], [t98_xboole_1])).
% 6.42/6.65  thf('17', plain,
% 6.42/6.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 6.42/6.65      inference('sup+', [status(thm)], ['15', '16'])).
% 6.42/6.65  thf('18', plain,
% 6.42/6.65      (![X0 : $i, X1 : $i]:
% 6.42/6.65         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 6.42/6.65           = (k2_tarski @ X1 @ X0))),
% 6.42/6.65      inference('sup+', [status(thm)], ['9', '17'])).
% 6.42/6.65  thf('19', plain,
% 6.42/6.65      (![X0 : $i, X1 : $i]:
% 6.42/6.65         ((k2_tarski @ X0 @ X1)
% 6.42/6.65           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 6.42/6.65      inference('demod', [status(thm)], ['7', '8'])).
% 6.42/6.65  thf('20', plain,
% 6.42/6.65      (![X0 : $i, X1 : $i]: ((k2_tarski @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 6.42/6.65      inference('sup+', [status(thm)], ['18', '19'])).
% 6.42/6.65  thf('21', plain,
% 6.42/6.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.42/6.65         ((k1_enumset1 @ X1 @ X0 @ X2)
% 6.42/6.65           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 6.42/6.65      inference('demod', [status(thm)], ['4', '5'])).
% 6.42/6.65  thf('22', plain,
% 6.42/6.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.42/6.65         ((k1_enumset1 @ X0 @ X1 @ X2)
% 6.42/6.65           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 6.42/6.65      inference('sup+', [status(thm)], ['20', '21'])).
% 6.42/6.65  thf('23', plain,
% 6.42/6.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.42/6.65         ((k1_enumset1 @ X1 @ X0 @ X2)
% 6.42/6.65           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 6.42/6.65      inference('demod', [status(thm)], ['4', '5'])).
% 6.42/6.65  thf('24', plain,
% 6.42/6.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.42/6.65         ((k1_enumset1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 6.42/6.65      inference('sup+', [status(thm)], ['22', '23'])).
% 6.42/6.65  thf(t119_enumset1, axiom,
% 6.42/6.65    (![A:$i,B:$i,C:$i,D:$i]:
% 6.42/6.65     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ C @ D @ B @ A ) ))).
% 6.42/6.65  thf('25', plain,
% 6.42/6.65      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 6.42/6.65         ((k2_enumset1 @ X27 @ X26 @ X24 @ X25)
% 6.42/6.65           = (k2_enumset1 @ X24 @ X25 @ X26 @ X27))),
% 6.42/6.65      inference('cnf', [status(esa)], [t119_enumset1])).
% 6.42/6.65  thf('26', plain,
% 6.42/6.65      (![X48 : $i, X49 : $i, X50 : $i]:
% 6.42/6.65         ((k2_enumset1 @ X48 @ X48 @ X49 @ X50)
% 6.42/6.65           = (k1_enumset1 @ X48 @ X49 @ X50))),
% 6.42/6.65      inference('cnf', [status(esa)], [t71_enumset1])).
% 6.42/6.65  thf('27', plain,
% 6.42/6.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.42/6.65         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 6.42/6.65      inference('sup+', [status(thm)], ['25', '26'])).
% 6.42/6.65  thf('28', plain,
% 6.42/6.65      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 6.42/6.65         ((k2_enumset1 @ X27 @ X26 @ X24 @ X25)
% 6.42/6.65           = (k2_enumset1 @ X24 @ X25 @ X26 @ X27))),
% 6.42/6.65      inference('cnf', [status(esa)], [t119_enumset1])).
% 6.42/6.65  thf('29', plain,
% 6.42/6.65      (![X48 : $i, X49 : $i, X50 : $i]:
% 6.42/6.65         ((k2_enumset1 @ X48 @ X48 @ X49 @ X50)
% 6.42/6.65           = (k1_enumset1 @ X48 @ X49 @ X50))),
% 6.42/6.65      inference('cnf', [status(esa)], [t71_enumset1])).
% 6.42/6.65  thf('30', plain,
% 6.42/6.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.42/6.65         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 6.42/6.65      inference('sup+', [status(thm)], ['28', '29'])).
% 6.42/6.65  thf('31', plain,
% 6.42/6.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.42/6.65         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 6.42/6.65      inference('sup+', [status(thm)], ['27', '30'])).
% 6.42/6.65  thf('32', plain,
% 6.42/6.65      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 6.42/6.65         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 6.42/6.65      inference('demod', [status(thm)], ['0', '24', '31'])).
% 6.42/6.65  thf('33', plain,
% 6.42/6.65      (![X46 : $i, X47 : $i]:
% 6.42/6.65         ((k1_enumset1 @ X46 @ X46 @ X47) = (k2_tarski @ X46 @ X47))),
% 6.42/6.65      inference('cnf', [status(esa)], [t70_enumset1])).
% 6.42/6.65  thf(l57_enumset1, axiom,
% 6.42/6.65    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 6.42/6.65     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 6.42/6.65       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ))).
% 6.42/6.65  thf('34', plain,
% 6.42/6.65      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 6.42/6.65         ((k3_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15)
% 6.42/6.65           = (k2_xboole_0 @ (k1_enumset1 @ X11 @ X12 @ X13) @ 
% 6.42/6.65              (k2_tarski @ X14 @ X15)))),
% 6.42/6.65      inference('cnf', [status(esa)], [l57_enumset1])).
% 6.42/6.65  thf('35', plain,
% 6.42/6.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.42/6.65         ((k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2)
% 6.42/6.65           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 6.42/6.65      inference('sup+', [status(thm)], ['33', '34'])).
% 6.42/6.65  thf(t113_enumset1, axiom,
% 6.42/6.65    (![A:$i,B:$i,C:$i,D:$i]:
% 6.42/6.65     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ D @ C @ A ) ))).
% 6.42/6.65  thf('36', plain,
% 6.42/6.65      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 6.42/6.65         ((k2_enumset1 @ X23 @ X20 @ X22 @ X21)
% 6.42/6.65           = (k2_enumset1 @ X20 @ X21 @ X22 @ X23))),
% 6.42/6.65      inference('cnf', [status(esa)], [t113_enumset1])).
% 6.42/6.65  thf('37', plain,
% 6.42/6.65      (![X48 : $i, X49 : $i, X50 : $i]:
% 6.42/6.65         ((k2_enumset1 @ X48 @ X48 @ X49 @ X50)
% 6.42/6.65           = (k1_enumset1 @ X48 @ X49 @ X50))),
% 6.42/6.65      inference('cnf', [status(esa)], [t71_enumset1])).
% 6.42/6.65  thf('38', plain,
% 6.42/6.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.42/6.65         ((k2_enumset1 @ X2 @ X0 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 6.42/6.65      inference('sup+', [status(thm)], ['36', '37'])).
% 6.42/6.65  thf(t72_enumset1, axiom,
% 6.42/6.65    (![A:$i,B:$i,C:$i,D:$i]:
% 6.42/6.65     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 6.42/6.65  thf('39', plain,
% 6.42/6.65      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 6.42/6.65         ((k3_enumset1 @ X51 @ X51 @ X52 @ X53 @ X54)
% 6.42/6.65           = (k2_enumset1 @ X51 @ X52 @ X53 @ X54))),
% 6.42/6.65      inference('cnf', [status(esa)], [t72_enumset1])).
% 6.42/6.65  thf('40', plain,
% 6.42/6.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.42/6.65         ((k3_enumset1 @ X0 @ X0 @ X2 @ X1 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 6.42/6.65      inference('sup+', [status(thm)], ['38', '39'])).
% 6.42/6.65  thf('41', plain,
% 6.42/6.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.42/6.65         ((k1_enumset1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 6.42/6.65      inference('sup+', [status(thm)], ['22', '23'])).
% 6.42/6.65  thf('42', plain,
% 6.42/6.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.42/6.65         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 6.42/6.65      inference('sup+', [status(thm)], ['27', '30'])).
% 6.42/6.65  thf('43', plain,
% 6.42/6.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.42/6.65         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 6.42/6.65      inference('sup+', [status(thm)], ['41', '42'])).
% 6.42/6.65  thf('44', plain,
% 6.42/6.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.42/6.65         ((k1_enumset1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 6.42/6.65      inference('sup+', [status(thm)], ['22', '23'])).
% 6.42/6.65  thf('45', plain,
% 6.42/6.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.42/6.65         ((k1_enumset1 @ X0 @ X1 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 6.42/6.65      inference('sup+', [status(thm)], ['43', '44'])).
% 6.42/6.65  thf('46', plain,
% 6.42/6.65      (((k1_enumset1 @ sk_B @ sk_C @ sk_A)
% 6.42/6.65         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 6.42/6.65      inference('demod', [status(thm)], ['32', '35', '40', '45'])).
% 6.42/6.65  thf('47', plain, ($false), inference('simplify', [status(thm)], ['46'])).
% 6.42/6.65  
% 6.42/6.65  % SZS output end Refutation
% 6.42/6.65  
% 6.50/6.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

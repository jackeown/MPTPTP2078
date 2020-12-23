%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xDxkzhLpdR

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:34 EST 2020

% Result     : Theorem 0.65s
% Output     : Refutation 0.65s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 251 expanded)
%              Number of leaves         :   25 (  95 expanded)
%              Depth                    :   14
%              Number of atoms          :  679 (2300 expanded)
%              Number of equality atoms :   69 ( 239 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k2_tarski @ X11 @ X12 ) @ ( k2_tarski @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf(t104_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ B @ D ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k2_enumset1 @ X20 @ X22 @ X21 @ X23 )
      = ( k2_enumset1 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t104_enumset1])).

thf('3',plain,(
    ( k2_enumset1 @ sk_B @ sk_C @ sk_A @ sk_A )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(t125_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ D @ C @ B @ A ) ) )).

thf('4',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k2_enumset1 @ X35 @ X34 @ X33 @ X32 )
      = ( k2_enumset1 @ X32 @ X33 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('5',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( k2_enumset1 @ X57 @ X57 @ X58 @ X59 )
      = ( k1_enumset1 @ X57 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ( k1_enumset1 @ sk_A @ sk_C @ sk_B )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['3','6'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X55: $i,X56: $i] :
      ( ( k1_enumset1 @ X55 @ X55 @ X56 )
      = ( k2_tarski @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('9',plain,(
    ! [X54: $i] :
      ( ( k2_tarski @ X54 @ X54 )
      = ( k1_tarski @ X54 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('11',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( k2_enumset1 @ X45 @ X46 @ X47 @ X48 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X45 @ X46 @ X47 ) @ ( k1_tarski @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( k2_enumset1 @ X57 @ X57 @ X58 @ X59 )
      = ( k1_enumset1 @ X57 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X55: $i,X56: $i] :
      ( ( k1_enumset1 @ X55 @ X55 @ X56 )
      = ( k2_tarski @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k5_xboole_0 @ X4 @ ( k5_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('19',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k5_xboole_0 @ X4 @ ( k5_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X55: $i,X56: $i] :
      ( ( k1_enumset1 @ X55 @ X55 @ X56 )
      = ( k2_tarski @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X55: $i,X56: $i] :
      ( ( k1_enumset1 @ X55 @ X55 @ X56 )
      = ( k2_tarski @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( k2_enumset1 @ X45 @ X46 @ X47 @ X48 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X45 @ X46 @ X47 ) @ ( k1_tarski @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( k2_enumset1 @ X57 @ X57 @ X58 @ X59 )
      = ( k1_enumset1 @ X57 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('39',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( k2_enumset1 @ X45 @ X46 @ X47 @ X48 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X45 @ X46 @ X47 ) @ ( k1_tarski @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('40',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( k2_enumset1 @ X57 @ X57 @ X58 @ X59 )
      = ( k1_enumset1 @ X57 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('43',plain,(
    ( k1_enumset1 @ sk_C @ sk_A @ sk_B )
 != ( k1_enumset1 @ sk_B @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['7','41','42'])).

thf('44',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k2_enumset1 @ X20 @ X22 @ X21 @ X23 )
      = ( k2_enumset1 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t104_enumset1])).

thf('45',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( k2_enumset1 @ X57 @ X57 @ X58 @ X59 )
      = ( k1_enumset1 @ X57 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf(t107_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ D @ C @ B ) ) )).

thf('47',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k2_enumset1 @ X24 @ X27 @ X26 @ X25 )
      = ( k2_enumset1 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X2 @ X1 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('53',plain,(
    ( k1_enumset1 @ sk_B @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['43','50','51','52'])).

thf('54',plain,(
    $false ),
    inference(simplify,[status(thm)],['53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xDxkzhLpdR
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:04:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.65/0.83  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.65/0.83  % Solved by: fo/fo7.sh
% 0.65/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.65/0.83  % done 392 iterations in 0.369s
% 0.65/0.83  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.65/0.83  % SZS output start Refutation
% 0.65/0.83  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.65/0.83  thf(sk_B_type, type, sk_B: $i).
% 0.65/0.83  thf(sk_C_type, type, sk_C: $i).
% 0.65/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.65/0.83  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.65/0.83  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.65/0.83  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.65/0.83  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.65/0.83  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.65/0.83  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.65/0.83  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.65/0.83  thf(t137_enumset1, conjecture,
% 0.65/0.83    (![A:$i,B:$i,C:$i]:
% 0.65/0.83     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.65/0.83       ( k1_enumset1 @ A @ B @ C ) ))).
% 0.65/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.65/0.83    (~( ![A:$i,B:$i,C:$i]:
% 0.65/0.83        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.65/0.83          ( k1_enumset1 @ A @ B @ C ) ) )),
% 0.65/0.83    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 0.65/0.83  thf('0', plain,
% 0.65/0.83      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 0.65/0.83         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf(l53_enumset1, axiom,
% 0.65/0.83    (![A:$i,B:$i,C:$i,D:$i]:
% 0.65/0.83     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.65/0.83       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.65/0.83  thf('1', plain,
% 0.65/0.83      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.65/0.83         ((k2_enumset1 @ X11 @ X12 @ X13 @ X14)
% 0.65/0.83           = (k2_xboole_0 @ (k2_tarski @ X11 @ X12) @ (k2_tarski @ X13 @ X14)))),
% 0.65/0.83      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.65/0.83  thf(t104_enumset1, axiom,
% 0.65/0.83    (![A:$i,B:$i,C:$i,D:$i]:
% 0.65/0.83     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ B @ D ) ))).
% 0.65/0.83  thf('2', plain,
% 0.65/0.83      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.65/0.83         ((k2_enumset1 @ X20 @ X22 @ X21 @ X23)
% 0.65/0.83           = (k2_enumset1 @ X20 @ X21 @ X22 @ X23))),
% 0.65/0.83      inference('cnf', [status(esa)], [t104_enumset1])).
% 0.65/0.83  thf('3', plain,
% 0.65/0.83      (((k2_enumset1 @ sk_B @ sk_C @ sk_A @ sk_A)
% 0.65/0.83         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.65/0.83      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.65/0.83  thf(t125_enumset1, axiom,
% 0.65/0.83    (![A:$i,B:$i,C:$i,D:$i]:
% 0.65/0.83     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ C @ B @ A ) ))).
% 0.65/0.83  thf('4', plain,
% 0.65/0.83      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.65/0.83         ((k2_enumset1 @ X35 @ X34 @ X33 @ X32)
% 0.65/0.83           = (k2_enumset1 @ X32 @ X33 @ X34 @ X35))),
% 0.65/0.83      inference('cnf', [status(esa)], [t125_enumset1])).
% 0.65/0.83  thf(t71_enumset1, axiom,
% 0.65/0.83    (![A:$i,B:$i,C:$i]:
% 0.65/0.83     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.65/0.83  thf('5', plain,
% 0.65/0.83      (![X57 : $i, X58 : $i, X59 : $i]:
% 0.65/0.83         ((k2_enumset1 @ X57 @ X57 @ X58 @ X59)
% 0.65/0.83           = (k1_enumset1 @ X57 @ X58 @ X59))),
% 0.65/0.83      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.65/0.83  thf('6', plain,
% 0.65/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.83         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.65/0.83      inference('sup+', [status(thm)], ['4', '5'])).
% 0.65/0.83  thf('7', plain,
% 0.65/0.83      (((k1_enumset1 @ sk_A @ sk_C @ sk_B)
% 0.65/0.83         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.65/0.83      inference('demod', [status(thm)], ['3', '6'])).
% 0.65/0.83  thf(t70_enumset1, axiom,
% 0.65/0.83    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.65/0.83  thf('8', plain,
% 0.65/0.83      (![X55 : $i, X56 : $i]:
% 0.65/0.83         ((k1_enumset1 @ X55 @ X55 @ X56) = (k2_tarski @ X55 @ X56))),
% 0.65/0.83      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.65/0.83  thf(t69_enumset1, axiom,
% 0.65/0.83    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.65/0.83  thf('9', plain, (![X54 : $i]: ((k2_tarski @ X54 @ X54) = (k1_tarski @ X54))),
% 0.65/0.83      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.65/0.83  thf('10', plain,
% 0.65/0.83      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.65/0.83      inference('sup+', [status(thm)], ['8', '9'])).
% 0.65/0.83  thf(t46_enumset1, axiom,
% 0.65/0.83    (![A:$i,B:$i,C:$i,D:$i]:
% 0.65/0.83     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.65/0.83       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.65/0.83  thf('11', plain,
% 0.65/0.83      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.65/0.83         ((k2_enumset1 @ X45 @ X46 @ X47 @ X48)
% 0.65/0.83           = (k2_xboole_0 @ (k1_enumset1 @ X45 @ X46 @ X47) @ (k1_tarski @ X48)))),
% 0.65/0.83      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.65/0.83  thf('12', plain,
% 0.65/0.83      (![X0 : $i, X1 : $i]:
% 0.65/0.83         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 0.65/0.83           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.65/0.83      inference('sup+', [status(thm)], ['10', '11'])).
% 0.65/0.83  thf('13', plain,
% 0.65/0.83      (![X57 : $i, X58 : $i, X59 : $i]:
% 0.65/0.83         ((k2_enumset1 @ X57 @ X57 @ X58 @ X59)
% 0.65/0.83           = (k1_enumset1 @ X57 @ X58 @ X59))),
% 0.65/0.83      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.65/0.83  thf('14', plain,
% 0.65/0.83      (![X0 : $i, X1 : $i]:
% 0.65/0.83         ((k1_enumset1 @ X0 @ X0 @ X1)
% 0.65/0.83           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.65/0.83      inference('demod', [status(thm)], ['12', '13'])).
% 0.65/0.83  thf('15', plain,
% 0.65/0.83      (![X55 : $i, X56 : $i]:
% 0.65/0.83         ((k1_enumset1 @ X55 @ X55 @ X56) = (k2_tarski @ X55 @ X56))),
% 0.65/0.83      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.65/0.83  thf('16', plain,
% 0.65/0.83      (![X0 : $i, X1 : $i]:
% 0.65/0.83         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.65/0.83           = (k2_tarski @ X1 @ X0))),
% 0.65/0.83      inference('sup+', [status(thm)], ['14', '15'])).
% 0.65/0.83  thf(t94_xboole_1, axiom,
% 0.65/0.83    (![A:$i,B:$i]:
% 0.65/0.83     ( ( k2_xboole_0 @ A @ B ) =
% 0.65/0.83       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.65/0.83  thf('17', plain,
% 0.65/0.83      (![X7 : $i, X8 : $i]:
% 0.65/0.83         ((k2_xboole_0 @ X7 @ X8)
% 0.65/0.83           = (k5_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ (k3_xboole_0 @ X7 @ X8)))),
% 0.65/0.83      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.65/0.83  thf(t91_xboole_1, axiom,
% 0.65/0.83    (![A:$i,B:$i,C:$i]:
% 0.65/0.83     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.65/0.83       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.65/0.83  thf('18', plain,
% 0.65/0.83      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.65/0.83         ((k5_xboole_0 @ (k5_xboole_0 @ X4 @ X5) @ X6)
% 0.65/0.83           = (k5_xboole_0 @ X4 @ (k5_xboole_0 @ X5 @ X6)))),
% 0.65/0.83      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.65/0.83  thf('19', plain,
% 0.65/0.83      (![X7 : $i, X8 : $i]:
% 0.65/0.83         ((k2_xboole_0 @ X7 @ X8)
% 0.65/0.83           = (k5_xboole_0 @ X7 @ (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X7 @ X8))))),
% 0.65/0.83      inference('demod', [status(thm)], ['17', '18'])).
% 0.65/0.83  thf('20', plain,
% 0.65/0.83      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.65/0.83         ((k5_xboole_0 @ (k5_xboole_0 @ X4 @ X5) @ X6)
% 0.65/0.83           = (k5_xboole_0 @ X4 @ (k5_xboole_0 @ X5 @ X6)))),
% 0.65/0.83      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.65/0.83  thf(commutativity_k5_xboole_0, axiom,
% 0.65/0.83    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.65/0.83  thf('21', plain,
% 0.65/0.83      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.65/0.83      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.65/0.83  thf('22', plain,
% 0.65/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.83         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.65/0.83           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.65/0.83      inference('sup+', [status(thm)], ['20', '21'])).
% 0.65/0.83  thf('23', plain,
% 0.65/0.83      (![X0 : $i, X1 : $i]:
% 0.65/0.83         ((k2_xboole_0 @ X1 @ X0)
% 0.65/0.83           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 0.65/0.83      inference('sup+', [status(thm)], ['19', '22'])).
% 0.65/0.83  thf('24', plain,
% 0.65/0.83      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.65/0.83      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.65/0.83  thf(t100_xboole_1, axiom,
% 0.65/0.83    (![A:$i,B:$i]:
% 0.65/0.83     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.65/0.83  thf('25', plain,
% 0.65/0.83      (![X2 : $i, X3 : $i]:
% 0.65/0.83         ((k4_xboole_0 @ X2 @ X3)
% 0.65/0.83           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.65/0.83      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.65/0.83  thf('26', plain,
% 0.65/0.83      (![X0 : $i, X1 : $i]:
% 0.65/0.83         ((k2_xboole_0 @ X1 @ X0)
% 0.65/0.83           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.65/0.83      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.65/0.83  thf(t98_xboole_1, axiom,
% 0.65/0.83    (![A:$i,B:$i]:
% 0.65/0.83     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.65/0.83  thf('27', plain,
% 0.65/0.83      (![X9 : $i, X10 : $i]:
% 0.65/0.83         ((k2_xboole_0 @ X9 @ X10)
% 0.65/0.83           = (k5_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9)))),
% 0.65/0.83      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.65/0.83  thf('28', plain,
% 0.65/0.83      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 0.65/0.83      inference('sup+', [status(thm)], ['26', '27'])).
% 0.65/0.83  thf('29', plain,
% 0.65/0.83      (![X0 : $i, X1 : $i]:
% 0.65/0.83         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.65/0.83           = (k2_tarski @ X1 @ X0))),
% 0.65/0.83      inference('sup+', [status(thm)], ['16', '28'])).
% 0.65/0.83  thf('30', plain,
% 0.65/0.83      (![X0 : $i, X1 : $i]:
% 0.65/0.83         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.65/0.83           = (k2_tarski @ X1 @ X0))),
% 0.65/0.83      inference('sup+', [status(thm)], ['14', '15'])).
% 0.65/0.83  thf('31', plain,
% 0.65/0.83      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.65/0.83      inference('sup+', [status(thm)], ['29', '30'])).
% 0.65/0.83  thf('32', plain,
% 0.65/0.83      (![X55 : $i, X56 : $i]:
% 0.65/0.83         ((k1_enumset1 @ X55 @ X55 @ X56) = (k2_tarski @ X55 @ X56))),
% 0.65/0.83      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.65/0.83  thf('33', plain,
% 0.65/0.83      (![X0 : $i, X1 : $i]:
% 0.65/0.83         ((k1_enumset1 @ X0 @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 0.65/0.83      inference('sup+', [status(thm)], ['31', '32'])).
% 0.65/0.83  thf('34', plain,
% 0.65/0.83      (![X55 : $i, X56 : $i]:
% 0.65/0.83         ((k1_enumset1 @ X55 @ X55 @ X56) = (k2_tarski @ X55 @ X56))),
% 0.65/0.83      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.65/0.83  thf('35', plain,
% 0.65/0.83      (![X0 : $i, X1 : $i]:
% 0.65/0.83         ((k1_enumset1 @ X0 @ X0 @ X1) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.65/0.83      inference('sup+', [status(thm)], ['33', '34'])).
% 0.65/0.83  thf('36', plain,
% 0.65/0.83      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.65/0.83         ((k2_enumset1 @ X45 @ X46 @ X47 @ X48)
% 0.65/0.83           = (k2_xboole_0 @ (k1_enumset1 @ X45 @ X46 @ X47) @ (k1_tarski @ X48)))),
% 0.65/0.83      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.65/0.83  thf('37', plain,
% 0.65/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.83         ((k2_enumset1 @ X0 @ X0 @ X1 @ X2)
% 0.65/0.83           = (k2_xboole_0 @ (k1_enumset1 @ X1 @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.65/0.83      inference('sup+', [status(thm)], ['35', '36'])).
% 0.65/0.83  thf('38', plain,
% 0.65/0.83      (![X57 : $i, X58 : $i, X59 : $i]:
% 0.65/0.83         ((k2_enumset1 @ X57 @ X57 @ X58 @ X59)
% 0.65/0.83           = (k1_enumset1 @ X57 @ X58 @ X59))),
% 0.65/0.83      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.65/0.83  thf('39', plain,
% 0.65/0.83      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.65/0.83         ((k2_enumset1 @ X45 @ X46 @ X47 @ X48)
% 0.65/0.83           = (k2_xboole_0 @ (k1_enumset1 @ X45 @ X46 @ X47) @ (k1_tarski @ X48)))),
% 0.65/0.83      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.65/0.83  thf('40', plain,
% 0.65/0.83      (![X57 : $i, X58 : $i, X59 : $i]:
% 0.65/0.83         ((k2_enumset1 @ X57 @ X57 @ X58 @ X59)
% 0.65/0.83           = (k1_enumset1 @ X57 @ X58 @ X59))),
% 0.65/0.83      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.65/0.83  thf('41', plain,
% 0.65/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.83         ((k1_enumset1 @ X0 @ X1 @ X2) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 0.65/0.83      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 0.65/0.83  thf('42', plain,
% 0.65/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.83         ((k1_enumset1 @ X0 @ X1 @ X2) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 0.65/0.83      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 0.65/0.83  thf('43', plain,
% 0.65/0.83      (((k1_enumset1 @ sk_C @ sk_A @ sk_B)
% 0.65/0.83         != (k1_enumset1 @ sk_B @ sk_A @ sk_C))),
% 0.65/0.83      inference('demod', [status(thm)], ['7', '41', '42'])).
% 0.65/0.83  thf('44', plain,
% 0.65/0.83      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.65/0.83         ((k2_enumset1 @ X20 @ X22 @ X21 @ X23)
% 0.65/0.83           = (k2_enumset1 @ X20 @ X21 @ X22 @ X23))),
% 0.65/0.83      inference('cnf', [status(esa)], [t104_enumset1])).
% 0.65/0.83  thf('45', plain,
% 0.65/0.83      (![X57 : $i, X58 : $i, X59 : $i]:
% 0.65/0.83         ((k2_enumset1 @ X57 @ X57 @ X58 @ X59)
% 0.65/0.83           = (k1_enumset1 @ X57 @ X58 @ X59))),
% 0.65/0.83      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.65/0.83  thf('46', plain,
% 0.65/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.83         ((k2_enumset1 @ X1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 0.65/0.83      inference('sup+', [status(thm)], ['44', '45'])).
% 0.65/0.83  thf(t107_enumset1, axiom,
% 0.65/0.83    (![A:$i,B:$i,C:$i,D:$i]:
% 0.65/0.83     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ D @ C @ B ) ))).
% 0.65/0.83  thf('47', plain,
% 0.65/0.83      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.65/0.83         ((k2_enumset1 @ X24 @ X27 @ X26 @ X25)
% 0.65/0.83           = (k2_enumset1 @ X24 @ X25 @ X26 @ X27))),
% 0.65/0.83      inference('cnf', [status(esa)], [t107_enumset1])).
% 0.65/0.83  thf('48', plain,
% 0.65/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.83         ((k2_enumset1 @ X2 @ X0 @ X2 @ X1) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.65/0.83      inference('sup+', [status(thm)], ['46', '47'])).
% 0.65/0.83  thf('49', plain,
% 0.65/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.83         ((k2_enumset1 @ X1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 0.65/0.83      inference('sup+', [status(thm)], ['44', '45'])).
% 0.65/0.83  thf('50', plain,
% 0.65/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.83         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 0.65/0.83      inference('sup+', [status(thm)], ['48', '49'])).
% 0.65/0.83  thf('51', plain,
% 0.65/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.83         ((k1_enumset1 @ X0 @ X1 @ X2) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 0.65/0.83      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 0.65/0.83  thf('52', plain,
% 0.65/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.83         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 0.65/0.83      inference('sup+', [status(thm)], ['48', '49'])).
% 0.65/0.83  thf('53', plain,
% 0.65/0.83      (((k1_enumset1 @ sk_B @ sk_C @ sk_A)
% 0.65/0.83         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 0.65/0.83      inference('demod', [status(thm)], ['43', '50', '51', '52'])).
% 0.65/0.83  thf('54', plain, ($false), inference('simplify', [status(thm)], ['53'])).
% 0.65/0.83  
% 0.65/0.83  % SZS output end Refutation
% 0.65/0.83  
% 0.65/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

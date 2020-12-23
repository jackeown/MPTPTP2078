%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4ruZSjHLoz

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:36 EST 2020

% Result     : Theorem 5.78s
% Output     : Refutation 5.78s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 188 expanded)
%              Number of leaves         :   27 (  72 expanded)
%              Depth                    :   12
%              Number of atoms          :  742 (1743 expanded)
%              Number of equality atoms :   73 ( 175 expanded)
%              Maximal formula depth    :   12 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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

thf(t107_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ D @ C @ B ) ) )).

thf('25',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k2_enumset1 @ X20 @ X23 @ X22 @ X21 )
      = ( k2_enumset1 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('26',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( k2_enumset1 @ X48 @ X48 @ X49 @ X50 )
      = ( k1_enumset1 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t105_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ D @ B ) ) )).

thf('28',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k2_enumset1 @ X16 @ X19 @ X17 @ X18 )
      = ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('29',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( k2_enumset1 @ X48 @ X48 @ X49 @ X50 )
      = ( k1_enumset1 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k2_enumset1 @ X27 @ X24 @ X26 @ X25 )
      = ( k2_enumset1 @ X24 @ X25 @ X26 @ X27 ) ) ),
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
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('42',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( k2_enumset1 @ X48 @ X48 @ X49 @ X50 )
      = ( k1_enumset1 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('43',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k2_enumset1 @ X16 @ X19 @ X17 @ X18 )
      = ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('44',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( k2_enumset1 @ X48 @ X48 @ X49 @ X50 )
      = ( k1_enumset1 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k1_enumset1 @ X46 @ X46 @ X47 )
      = ( k2_tarski @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( k2_enumset1 @ X41 @ X42 @ X43 @ X44 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X41 @ X42 @ X43 ) @ ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X2 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ( k1_enumset1 @ sk_B @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['32','35','40','55'])).

thf('57',plain,(
    $false ),
    inference(simplify,[status(thm)],['56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4ruZSjHLoz
% 0.15/0.36  % Computer   : n004.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 12:25:24 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.21/0.36  % Number of cores: 8
% 0.21/0.36  % Python version: Python 3.6.8
% 0.21/0.37  % Running in FO mode
% 5.78/6.00  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.78/6.00  % Solved by: fo/fo7.sh
% 5.78/6.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.78/6.00  % done 3469 iterations in 5.536s
% 5.78/6.00  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.78/6.00  % SZS output start Refutation
% 5.78/6.00  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 5.78/6.00  thf(sk_B_type, type, sk_B: $i).
% 5.78/6.00  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 5.78/6.00  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 5.78/6.00  thf(sk_A_type, type, sk_A: $i).
% 5.78/6.00  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 5.78/6.00  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 5.78/6.00  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 5.78/6.00  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.78/6.00  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 5.78/6.00  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.78/6.00  thf(sk_C_type, type, sk_C: $i).
% 5.78/6.00  thf(t137_enumset1, conjecture,
% 5.78/6.00    (![A:$i,B:$i,C:$i]:
% 5.78/6.00     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 5.78/6.00       ( k1_enumset1 @ A @ B @ C ) ))).
% 5.78/6.00  thf(zf_stmt_0, negated_conjecture,
% 5.78/6.00    (~( ![A:$i,B:$i,C:$i]:
% 5.78/6.00        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 5.78/6.00          ( k1_enumset1 @ A @ B @ C ) ) )),
% 5.78/6.00    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 5.78/6.00  thf('0', plain,
% 5.78/6.00      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 5.78/6.00         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 5.78/6.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.78/6.00  thf(t69_enumset1, axiom,
% 5.78/6.00    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 5.78/6.00  thf('1', plain, (![X45 : $i]: ((k2_tarski @ X45 @ X45) = (k1_tarski @ X45))),
% 5.78/6.00      inference('cnf', [status(esa)], [t69_enumset1])).
% 5.78/6.00  thf(t70_enumset1, axiom,
% 5.78/6.00    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 5.78/6.00  thf('2', plain,
% 5.78/6.00      (![X46 : $i, X47 : $i]:
% 5.78/6.00         ((k1_enumset1 @ X46 @ X46 @ X47) = (k2_tarski @ X46 @ X47))),
% 5.78/6.00      inference('cnf', [status(esa)], [t70_enumset1])).
% 5.78/6.00  thf(t46_enumset1, axiom,
% 5.78/6.00    (![A:$i,B:$i,C:$i,D:$i]:
% 5.78/6.00     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 5.78/6.00       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 5.78/6.00  thf('3', plain,
% 5.78/6.00      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 5.78/6.00         ((k2_enumset1 @ X41 @ X42 @ X43 @ X44)
% 5.78/6.00           = (k2_xboole_0 @ (k1_enumset1 @ X41 @ X42 @ X43) @ (k1_tarski @ X44)))),
% 5.78/6.00      inference('cnf', [status(esa)], [t46_enumset1])).
% 5.78/6.00  thf('4', plain,
% 5.78/6.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.78/6.00         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 5.78/6.00           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 5.78/6.00      inference('sup+', [status(thm)], ['2', '3'])).
% 5.78/6.00  thf(t71_enumset1, axiom,
% 5.78/6.00    (![A:$i,B:$i,C:$i]:
% 5.78/6.00     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 5.78/6.00  thf('5', plain,
% 5.78/6.00      (![X48 : $i, X49 : $i, X50 : $i]:
% 5.78/6.00         ((k2_enumset1 @ X48 @ X48 @ X49 @ X50)
% 5.78/6.00           = (k1_enumset1 @ X48 @ X49 @ X50))),
% 5.78/6.00      inference('cnf', [status(esa)], [t71_enumset1])).
% 5.78/6.00  thf('6', plain,
% 5.78/6.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.78/6.00         ((k1_enumset1 @ X1 @ X0 @ X2)
% 5.78/6.00           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 5.78/6.00      inference('demod', [status(thm)], ['4', '5'])).
% 5.78/6.00  thf('7', plain,
% 5.78/6.00      (![X0 : $i, X1 : $i]:
% 5.78/6.00         ((k1_enumset1 @ X0 @ X0 @ X1)
% 5.78/6.00           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 5.78/6.00      inference('sup+', [status(thm)], ['1', '6'])).
% 5.78/6.00  thf('8', plain,
% 5.78/6.00      (![X46 : $i, X47 : $i]:
% 5.78/6.00         ((k1_enumset1 @ X46 @ X46 @ X47) = (k2_tarski @ X46 @ X47))),
% 5.78/6.00      inference('cnf', [status(esa)], [t70_enumset1])).
% 5.78/6.00  thf('9', plain,
% 5.78/6.00      (![X0 : $i, X1 : $i]:
% 5.78/6.00         ((k2_tarski @ X0 @ X1)
% 5.78/6.00           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 5.78/6.00      inference('demod', [status(thm)], ['7', '8'])).
% 5.78/6.00  thf(t94_xboole_1, axiom,
% 5.78/6.00    (![A:$i,B:$i]:
% 5.78/6.00     ( ( k2_xboole_0 @ A @ B ) =
% 5.78/6.00       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 5.78/6.00  thf('10', plain,
% 5.78/6.00      (![X7 : $i, X8 : $i]:
% 5.78/6.00         ((k2_xboole_0 @ X7 @ X8)
% 5.78/6.00           = (k5_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ (k3_xboole_0 @ X7 @ X8)))),
% 5.78/6.00      inference('cnf', [status(esa)], [t94_xboole_1])).
% 5.78/6.00  thf(commutativity_k5_xboole_0, axiom,
% 5.78/6.00    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 5.78/6.00  thf('11', plain,
% 5.78/6.00      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 5.78/6.00      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 5.78/6.00  thf(t91_xboole_1, axiom,
% 5.78/6.00    (![A:$i,B:$i,C:$i]:
% 5.78/6.00     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 5.78/6.00       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 5.78/6.00  thf('12', plain,
% 5.78/6.00      (![X4 : $i, X5 : $i, X6 : $i]:
% 5.78/6.00         ((k5_xboole_0 @ (k5_xboole_0 @ X4 @ X5) @ X6)
% 5.78/6.00           = (k5_xboole_0 @ X4 @ (k5_xboole_0 @ X5 @ X6)))),
% 5.78/6.00      inference('cnf', [status(esa)], [t91_xboole_1])).
% 5.78/6.00  thf('13', plain,
% 5.78/6.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.78/6.00         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 5.78/6.00           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 5.78/6.00      inference('sup+', [status(thm)], ['11', '12'])).
% 5.78/6.00  thf(t100_xboole_1, axiom,
% 5.78/6.00    (![A:$i,B:$i]:
% 5.78/6.00     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 5.78/6.00  thf('14', plain,
% 5.78/6.00      (![X2 : $i, X3 : $i]:
% 5.78/6.00         ((k4_xboole_0 @ X2 @ X3)
% 5.78/6.00           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 5.78/6.00      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.78/6.00  thf('15', plain,
% 5.78/6.00      (![X7 : $i, X8 : $i]:
% 5.78/6.00         ((k2_xboole_0 @ X7 @ X8)
% 5.78/6.00           = (k5_xboole_0 @ X8 @ (k4_xboole_0 @ X7 @ X8)))),
% 5.78/6.00      inference('demod', [status(thm)], ['10', '13', '14'])).
% 5.78/6.00  thf(t98_xboole_1, axiom,
% 5.78/6.00    (![A:$i,B:$i]:
% 5.78/6.00     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 5.78/6.00  thf('16', plain,
% 5.78/6.00      (![X9 : $i, X10 : $i]:
% 5.78/6.00         ((k2_xboole_0 @ X9 @ X10)
% 5.78/6.00           = (k5_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9)))),
% 5.78/6.00      inference('cnf', [status(esa)], [t98_xboole_1])).
% 5.78/6.00  thf('17', plain,
% 5.78/6.00      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 5.78/6.00      inference('sup+', [status(thm)], ['15', '16'])).
% 5.78/6.00  thf('18', plain,
% 5.78/6.00      (![X0 : $i, X1 : $i]:
% 5.78/6.00         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 5.78/6.00           = (k2_tarski @ X1 @ X0))),
% 5.78/6.00      inference('sup+', [status(thm)], ['9', '17'])).
% 5.78/6.00  thf('19', plain,
% 5.78/6.00      (![X0 : $i, X1 : $i]:
% 5.78/6.00         ((k2_tarski @ X0 @ X1)
% 5.78/6.00           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 5.78/6.00      inference('demod', [status(thm)], ['7', '8'])).
% 5.78/6.00  thf('20', plain,
% 5.78/6.00      (![X0 : $i, X1 : $i]: ((k2_tarski @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 5.78/6.00      inference('sup+', [status(thm)], ['18', '19'])).
% 5.78/6.00  thf('21', plain,
% 5.78/6.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.78/6.00         ((k1_enumset1 @ X1 @ X0 @ X2)
% 5.78/6.00           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 5.78/6.00      inference('demod', [status(thm)], ['4', '5'])).
% 5.78/6.00  thf('22', plain,
% 5.78/6.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.78/6.00         ((k1_enumset1 @ X0 @ X1 @ X2)
% 5.78/6.00           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 5.78/6.00      inference('sup+', [status(thm)], ['20', '21'])).
% 5.78/6.00  thf('23', plain,
% 5.78/6.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.78/6.00         ((k1_enumset1 @ X1 @ X0 @ X2)
% 5.78/6.00           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 5.78/6.00      inference('demod', [status(thm)], ['4', '5'])).
% 5.78/6.00  thf('24', plain,
% 5.78/6.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.78/6.00         ((k1_enumset1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 5.78/6.00      inference('sup+', [status(thm)], ['22', '23'])).
% 5.78/6.00  thf(t107_enumset1, axiom,
% 5.78/6.00    (![A:$i,B:$i,C:$i,D:$i]:
% 5.78/6.00     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ D @ C @ B ) ))).
% 5.78/6.00  thf('25', plain,
% 5.78/6.00      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 5.78/6.00         ((k2_enumset1 @ X20 @ X23 @ X22 @ X21)
% 5.78/6.00           = (k2_enumset1 @ X20 @ X21 @ X22 @ X23))),
% 5.78/6.00      inference('cnf', [status(esa)], [t107_enumset1])).
% 5.78/6.00  thf('26', plain,
% 5.78/6.00      (![X48 : $i, X49 : $i, X50 : $i]:
% 5.78/6.00         ((k2_enumset1 @ X48 @ X48 @ X49 @ X50)
% 5.78/6.00           = (k1_enumset1 @ X48 @ X49 @ X50))),
% 5.78/6.00      inference('cnf', [status(esa)], [t71_enumset1])).
% 5.78/6.00  thf('27', plain,
% 5.78/6.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.78/6.00         ((k2_enumset1 @ X0 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 5.78/6.00      inference('sup+', [status(thm)], ['25', '26'])).
% 5.78/6.00  thf(t105_enumset1, axiom,
% 5.78/6.00    (![A:$i,B:$i,C:$i,D:$i]:
% 5.78/6.00     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ D @ B ) ))).
% 5.78/6.00  thf('28', plain,
% 5.78/6.00      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 5.78/6.00         ((k2_enumset1 @ X16 @ X19 @ X17 @ X18)
% 5.78/6.00           = (k2_enumset1 @ X16 @ X17 @ X18 @ X19))),
% 5.78/6.00      inference('cnf', [status(esa)], [t105_enumset1])).
% 5.78/6.00  thf('29', plain,
% 5.78/6.00      (![X48 : $i, X49 : $i, X50 : $i]:
% 5.78/6.00         ((k2_enumset1 @ X48 @ X48 @ X49 @ X50)
% 5.78/6.00           = (k1_enumset1 @ X48 @ X49 @ X50))),
% 5.78/6.00      inference('cnf', [status(esa)], [t71_enumset1])).
% 5.78/6.00  thf('30', plain,
% 5.78/6.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.78/6.00         ((k2_enumset1 @ X0 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 5.78/6.00      inference('sup+', [status(thm)], ['28', '29'])).
% 5.78/6.00  thf('31', plain,
% 5.78/6.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.78/6.00         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 5.78/6.00      inference('sup+', [status(thm)], ['27', '30'])).
% 5.78/6.00  thf('32', plain,
% 5.78/6.00      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 5.78/6.00         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 5.78/6.00      inference('demod', [status(thm)], ['0', '24', '31'])).
% 5.78/6.00  thf('33', plain,
% 5.78/6.00      (![X46 : $i, X47 : $i]:
% 5.78/6.00         ((k1_enumset1 @ X46 @ X46 @ X47) = (k2_tarski @ X46 @ X47))),
% 5.78/6.00      inference('cnf', [status(esa)], [t70_enumset1])).
% 5.78/6.00  thf(l57_enumset1, axiom,
% 5.78/6.00    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 5.78/6.00     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 5.78/6.00       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ))).
% 5.78/6.00  thf('34', plain,
% 5.78/6.00      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 5.78/6.00         ((k3_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15)
% 5.78/6.00           = (k2_xboole_0 @ (k1_enumset1 @ X11 @ X12 @ X13) @ 
% 5.78/6.00              (k2_tarski @ X14 @ X15)))),
% 5.78/6.00      inference('cnf', [status(esa)], [l57_enumset1])).
% 5.78/6.00  thf('35', plain,
% 5.78/6.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.78/6.00         ((k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2)
% 5.78/6.00           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 5.78/6.00      inference('sup+', [status(thm)], ['33', '34'])).
% 5.78/6.00  thf(t113_enumset1, axiom,
% 5.78/6.00    (![A:$i,B:$i,C:$i,D:$i]:
% 5.78/6.00     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ D @ C @ A ) ))).
% 5.78/6.00  thf('36', plain,
% 5.78/6.00      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 5.78/6.00         ((k2_enumset1 @ X27 @ X24 @ X26 @ X25)
% 5.78/6.00           = (k2_enumset1 @ X24 @ X25 @ X26 @ X27))),
% 5.78/6.00      inference('cnf', [status(esa)], [t113_enumset1])).
% 5.78/6.00  thf('37', plain,
% 5.78/6.00      (![X48 : $i, X49 : $i, X50 : $i]:
% 5.78/6.00         ((k2_enumset1 @ X48 @ X48 @ X49 @ X50)
% 5.78/6.00           = (k1_enumset1 @ X48 @ X49 @ X50))),
% 5.78/6.00      inference('cnf', [status(esa)], [t71_enumset1])).
% 5.78/6.00  thf('38', plain,
% 5.78/6.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.78/6.00         ((k2_enumset1 @ X2 @ X0 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 5.78/6.00      inference('sup+', [status(thm)], ['36', '37'])).
% 5.78/6.00  thf(t72_enumset1, axiom,
% 5.78/6.00    (![A:$i,B:$i,C:$i,D:$i]:
% 5.78/6.00     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 5.78/6.00  thf('39', plain,
% 5.78/6.00      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 5.78/6.00         ((k3_enumset1 @ X51 @ X51 @ X52 @ X53 @ X54)
% 5.78/6.00           = (k2_enumset1 @ X51 @ X52 @ X53 @ X54))),
% 5.78/6.00      inference('cnf', [status(esa)], [t72_enumset1])).
% 5.78/6.00  thf('40', plain,
% 5.78/6.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.78/6.00         ((k3_enumset1 @ X0 @ X0 @ X2 @ X1 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 5.78/6.00      inference('sup+', [status(thm)], ['38', '39'])).
% 5.78/6.00  thf('41', plain,
% 5.78/6.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.78/6.00         ((k1_enumset1 @ X0 @ X1 @ X2)
% 5.78/6.00           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 5.78/6.00      inference('sup+', [status(thm)], ['20', '21'])).
% 5.78/6.00  thf('42', plain,
% 5.78/6.00      (![X48 : $i, X49 : $i, X50 : $i]:
% 5.78/6.00         ((k2_enumset1 @ X48 @ X48 @ X49 @ X50)
% 5.78/6.00           = (k1_enumset1 @ X48 @ X49 @ X50))),
% 5.78/6.00      inference('cnf', [status(esa)], [t71_enumset1])).
% 5.78/6.00  thf('43', plain,
% 5.78/6.00      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 5.78/6.00         ((k2_enumset1 @ X16 @ X19 @ X17 @ X18)
% 5.78/6.00           = (k2_enumset1 @ X16 @ X17 @ X18 @ X19))),
% 5.78/6.00      inference('cnf', [status(esa)], [t105_enumset1])).
% 5.78/6.00  thf('44', plain,
% 5.78/6.00      (![X48 : $i, X49 : $i, X50 : $i]:
% 5.78/6.00         ((k2_enumset1 @ X48 @ X48 @ X49 @ X50)
% 5.78/6.00           = (k1_enumset1 @ X48 @ X49 @ X50))),
% 5.78/6.00      inference('cnf', [status(esa)], [t71_enumset1])).
% 5.78/6.00  thf('45', plain,
% 5.78/6.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.78/6.00         ((k2_enumset1 @ X1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 5.78/6.00      inference('sup+', [status(thm)], ['43', '44'])).
% 5.78/6.00  thf('46', plain,
% 5.78/6.00      (![X0 : $i, X1 : $i]:
% 5.78/6.00         ((k1_enumset1 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X1))),
% 5.78/6.00      inference('sup+', [status(thm)], ['42', '45'])).
% 5.78/6.00  thf('47', plain,
% 5.78/6.00      (![X46 : $i, X47 : $i]:
% 5.78/6.00         ((k1_enumset1 @ X46 @ X46 @ X47) = (k2_tarski @ X46 @ X47))),
% 5.78/6.00      inference('cnf', [status(esa)], [t70_enumset1])).
% 5.78/6.00  thf('48', plain,
% 5.78/6.00      (![X0 : $i, X1 : $i]:
% 5.78/6.00         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X1))),
% 5.78/6.00      inference('demod', [status(thm)], ['46', '47'])).
% 5.78/6.00  thf('49', plain,
% 5.78/6.00      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 5.78/6.00         ((k2_enumset1 @ X41 @ X42 @ X43 @ X44)
% 5.78/6.00           = (k2_xboole_0 @ (k1_enumset1 @ X41 @ X42 @ X43) @ (k1_tarski @ X44)))),
% 5.78/6.00      inference('cnf', [status(esa)], [t46_enumset1])).
% 5.78/6.00  thf('50', plain,
% 5.78/6.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.78/6.00         ((k2_enumset1 @ X1 @ X0 @ X1 @ X2)
% 5.78/6.00           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 5.78/6.00      inference('sup+', [status(thm)], ['48', '49'])).
% 5.78/6.00  thf('51', plain,
% 5.78/6.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.78/6.00         ((k2_enumset1 @ X1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 5.78/6.00      inference('sup+', [status(thm)], ['43', '44'])).
% 5.78/6.00  thf('52', plain,
% 5.78/6.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.78/6.00         ((k1_enumset1 @ X1 @ X2 @ X0)
% 5.78/6.00           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 5.78/6.00      inference('demod', [status(thm)], ['50', '51'])).
% 5.78/6.00  thf('53', plain,
% 5.78/6.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.78/6.00         ((k1_enumset1 @ X1 @ X0 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 5.78/6.00      inference('sup+', [status(thm)], ['41', '52'])).
% 5.78/6.00  thf('54', plain,
% 5.78/6.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.78/6.00         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 5.78/6.00      inference('sup+', [status(thm)], ['27', '30'])).
% 5.78/6.00  thf('55', plain,
% 5.78/6.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.78/6.00         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 5.78/6.00      inference('sup+', [status(thm)], ['53', '54'])).
% 5.78/6.00  thf('56', plain,
% 5.78/6.00      (((k1_enumset1 @ sk_B @ sk_C @ sk_A)
% 5.78/6.00         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 5.78/6.00      inference('demod', [status(thm)], ['32', '35', '40', '55'])).
% 5.78/6.00  thf('57', plain, ($false), inference('simplify', [status(thm)], ['56'])).
% 5.78/6.00  
% 5.78/6.00  % SZS output end Refutation
% 5.78/6.00  
% 5.78/6.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

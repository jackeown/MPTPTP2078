%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Np4X8miaau

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:36 EST 2020

% Result     : Theorem 3.32s
% Output     : Refutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 281 expanded)
%              Number of leaves         :   27 ( 105 expanded)
%              Depth                    :   15
%              Number of atoms          :  888 (2609 expanded)
%              Number of equality atoms :   88 ( 268 expanded)
%              Maximal formula depth    :   12 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k1_enumset1 @ X51 @ X51 @ X52 )
      = ( k2_tarski @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X50: $i] :
      ( ( k2_tarski @ X50 @ X50 )
      = ( k1_tarski @ X50 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('4',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( k2_enumset1 @ X41 @ X42 @ X43 @ X44 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X41 @ X42 @ X43 ) @ ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('6',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( k2_enumset1 @ X53 @ X53 @ X54 @ X55 )
      = ( k1_enumset1 @ X53 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k1_enumset1 @ X51 @ X51 @ X52 )
      = ( k2_tarski @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k5_xboole_0 @ X4 @ ( k5_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k5_xboole_0 @ X4 @ ( k5_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k1_enumset1 @ X51 @ X51 @ X52 )
      = ( k2_tarski @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k1_enumset1 @ X51 @ X51 @ X52 )
      = ( k2_tarski @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( k2_enumset1 @ X41 @ X42 @ X43 @ X44 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X41 @ X42 @ X43 ) @ ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( k2_enumset1 @ X53 @ X53 @ X54 @ X55 )
      = ( k1_enumset1 @ X53 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('32',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( k2_enumset1 @ X41 @ X42 @ X43 @ X44 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X41 @ X42 @ X43 ) @ ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('33',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( k2_enumset1 @ X53 @ X53 @ X54 @ X55 )
      = ( k1_enumset1 @ X53 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('35',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_tarski @ sk_C @ sk_A ) )
 != ( k1_enumset1 @ sk_B @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['0','34'])).

thf(t119_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ C @ D @ B @ A ) ) )).

thf('36',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k2_enumset1 @ X27 @ X26 @ X24 @ X25 )
      = ( k2_enumset1 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t119_enumset1])).

thf('37',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( k2_enumset1 @ X53 @ X53 @ X54 @ X55 )
      = ( k1_enumset1 @ X53 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k2_enumset1 @ X27 @ X26 @ X24 @ X25 )
      = ( k2_enumset1 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t119_enumset1])).

thf('40',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( k2_enumset1 @ X53 @ X53 @ X54 @ X55 )
      = ( k1_enumset1 @ X53 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_tarski @ sk_C @ sk_A ) )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['35','42'])).

thf('44',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k1_enumset1 @ X51 @ X51 @ X52 )
      = ( k2_tarski @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(l57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) )).

thf('45',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k3_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X11 @ X12 @ X13 ) @ ( k2_tarski @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('47',plain,(
    ! [X56: $i,X57: $i,X58: $i,X59: $i] :
      ( ( k3_enumset1 @ X56 @ X56 @ X57 @ X58 @ X59 )
      = ( k2_enumset1 @ X56 @ X57 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t125_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ D @ C @ B @ A ) ) )).

thf('48',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k2_enumset1 @ X31 @ X30 @ X29 @ X28 )
      = ( k2_enumset1 @ X28 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 )
      = ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(t107_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ D @ C @ B ) ) )).

thf('51',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k2_enumset1 @ X16 @ X19 @ X18 @ X17 )
      = ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('52',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( k2_enumset1 @ X53 @ X53 @ X54 @ X55 )
      = ( k1_enumset1 @ X53 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k1_enumset1 @ X51 @ X51 @ X52 )
      = ( k2_tarski @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('58',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( k2_enumset1 @ X41 @ X42 @ X43 @ X44 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X41 @ X42 @ X43 ) @ ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( k2_enumset1 @ X53 @ X53 @ X54 @ X55 )
      = ( k1_enumset1 @ X53 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X0 @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['56','61'])).

thf('63',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( k2_enumset1 @ X41 @ X42 @ X43 @ X44 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X41 @ X42 @ X43 ) @ ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k2_enumset1 @ X0 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('71',plain,(
    ( k1_enumset1 @ sk_B @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['43','46','49','64','69','70'])).

thf('72',plain,(
    $false ),
    inference(simplify,[status(thm)],['71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Np4X8miaau
% 0.13/0.36  % Computer   : n005.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 15:35:18 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 3.32/3.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.32/3.53  % Solved by: fo/fo7.sh
% 3.32/3.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.32/3.53  % done 2690 iterations in 3.053s
% 3.32/3.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.32/3.53  % SZS output start Refutation
% 3.32/3.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.32/3.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.32/3.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.32/3.53  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 3.32/3.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 3.32/3.53  thf(sk_C_type, type, sk_C: $i).
% 3.32/3.53  thf(sk_B_type, type, sk_B: $i).
% 3.32/3.53  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 3.32/3.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.32/3.53  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 3.32/3.53  thf(sk_A_type, type, sk_A: $i).
% 3.32/3.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.32/3.53  thf(t137_enumset1, conjecture,
% 3.32/3.53    (![A:$i,B:$i,C:$i]:
% 3.32/3.53     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 3.32/3.53       ( k1_enumset1 @ A @ B @ C ) ))).
% 3.32/3.53  thf(zf_stmt_0, negated_conjecture,
% 3.32/3.53    (~( ![A:$i,B:$i,C:$i]:
% 3.32/3.53        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 3.32/3.53          ( k1_enumset1 @ A @ B @ C ) ) )),
% 3.32/3.53    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 3.32/3.53  thf('0', plain,
% 3.32/3.53      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 3.32/3.53         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 3.32/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.32/3.53  thf(t70_enumset1, axiom,
% 3.32/3.53    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 3.32/3.53  thf('1', plain,
% 3.32/3.53      (![X51 : $i, X52 : $i]:
% 3.32/3.53         ((k1_enumset1 @ X51 @ X51 @ X52) = (k2_tarski @ X51 @ X52))),
% 3.32/3.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 3.32/3.53  thf(t69_enumset1, axiom,
% 3.32/3.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 3.32/3.53  thf('2', plain, (![X50 : $i]: ((k2_tarski @ X50 @ X50) = (k1_tarski @ X50))),
% 3.32/3.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.32/3.53  thf('3', plain,
% 3.32/3.53      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 3.32/3.53      inference('sup+', [status(thm)], ['1', '2'])).
% 3.32/3.53  thf(t46_enumset1, axiom,
% 3.32/3.53    (![A:$i,B:$i,C:$i,D:$i]:
% 3.32/3.53     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 3.32/3.53       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 3.32/3.53  thf('4', plain,
% 3.32/3.53      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 3.32/3.53         ((k2_enumset1 @ X41 @ X42 @ X43 @ X44)
% 3.32/3.53           = (k2_xboole_0 @ (k1_enumset1 @ X41 @ X42 @ X43) @ (k1_tarski @ X44)))),
% 3.32/3.53      inference('cnf', [status(esa)], [t46_enumset1])).
% 3.32/3.53  thf('5', plain,
% 3.32/3.53      (![X0 : $i, X1 : $i]:
% 3.32/3.53         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 3.32/3.53           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 3.32/3.53      inference('sup+', [status(thm)], ['3', '4'])).
% 3.32/3.53  thf(t71_enumset1, axiom,
% 3.32/3.53    (![A:$i,B:$i,C:$i]:
% 3.32/3.53     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 3.32/3.53  thf('6', plain,
% 3.32/3.53      (![X53 : $i, X54 : $i, X55 : $i]:
% 3.32/3.53         ((k2_enumset1 @ X53 @ X53 @ X54 @ X55)
% 3.32/3.53           = (k1_enumset1 @ X53 @ X54 @ X55))),
% 3.32/3.53      inference('cnf', [status(esa)], [t71_enumset1])).
% 3.32/3.53  thf('7', plain,
% 3.32/3.53      (![X0 : $i, X1 : $i]:
% 3.32/3.53         ((k1_enumset1 @ X0 @ X0 @ X1)
% 3.32/3.53           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 3.32/3.53      inference('demod', [status(thm)], ['5', '6'])).
% 3.32/3.53  thf('8', plain,
% 3.32/3.53      (![X51 : $i, X52 : $i]:
% 3.32/3.53         ((k1_enumset1 @ X51 @ X51 @ X52) = (k2_tarski @ X51 @ X52))),
% 3.32/3.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 3.32/3.53  thf('9', plain,
% 3.32/3.53      (![X0 : $i, X1 : $i]:
% 3.32/3.53         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 3.32/3.53           = (k2_tarski @ X1 @ X0))),
% 3.32/3.53      inference('sup+', [status(thm)], ['7', '8'])).
% 3.32/3.53  thf(t94_xboole_1, axiom,
% 3.32/3.53    (![A:$i,B:$i]:
% 3.32/3.53     ( ( k2_xboole_0 @ A @ B ) =
% 3.32/3.53       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 3.32/3.53  thf('10', plain,
% 3.32/3.53      (![X7 : $i, X8 : $i]:
% 3.32/3.53         ((k2_xboole_0 @ X7 @ X8)
% 3.32/3.53           = (k5_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ (k3_xboole_0 @ X7 @ X8)))),
% 3.32/3.53      inference('cnf', [status(esa)], [t94_xboole_1])).
% 3.32/3.53  thf(t91_xboole_1, axiom,
% 3.32/3.53    (![A:$i,B:$i,C:$i]:
% 3.32/3.53     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 3.32/3.53       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 3.32/3.53  thf('11', plain,
% 3.32/3.53      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.32/3.53         ((k5_xboole_0 @ (k5_xboole_0 @ X4 @ X5) @ X6)
% 3.32/3.53           = (k5_xboole_0 @ X4 @ (k5_xboole_0 @ X5 @ X6)))),
% 3.32/3.53      inference('cnf', [status(esa)], [t91_xboole_1])).
% 3.32/3.53  thf('12', plain,
% 3.32/3.53      (![X7 : $i, X8 : $i]:
% 3.32/3.53         ((k2_xboole_0 @ X7 @ X8)
% 3.32/3.53           = (k5_xboole_0 @ X7 @ (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X7 @ X8))))),
% 3.32/3.53      inference('demod', [status(thm)], ['10', '11'])).
% 3.32/3.53  thf('13', plain,
% 3.32/3.53      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.32/3.53         ((k5_xboole_0 @ (k5_xboole_0 @ X4 @ X5) @ X6)
% 3.32/3.53           = (k5_xboole_0 @ X4 @ (k5_xboole_0 @ X5 @ X6)))),
% 3.32/3.53      inference('cnf', [status(esa)], [t91_xboole_1])).
% 3.32/3.53  thf(commutativity_k5_xboole_0, axiom,
% 3.32/3.53    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 3.32/3.53  thf('14', plain,
% 3.32/3.53      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 3.32/3.53      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 3.32/3.53  thf('15', plain,
% 3.32/3.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.32/3.53         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 3.32/3.53           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 3.32/3.53      inference('sup+', [status(thm)], ['13', '14'])).
% 3.32/3.53  thf('16', plain,
% 3.32/3.53      (![X0 : $i, X1 : $i]:
% 3.32/3.53         ((k2_xboole_0 @ X1 @ X0)
% 3.32/3.53           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 3.32/3.53      inference('sup+', [status(thm)], ['12', '15'])).
% 3.32/3.53  thf('17', plain,
% 3.32/3.53      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 3.32/3.53      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 3.32/3.53  thf(t100_xboole_1, axiom,
% 3.32/3.53    (![A:$i,B:$i]:
% 3.32/3.53     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 3.32/3.53  thf('18', plain,
% 3.32/3.53      (![X2 : $i, X3 : $i]:
% 3.32/3.53         ((k4_xboole_0 @ X2 @ X3)
% 3.32/3.53           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 3.32/3.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.32/3.53  thf('19', plain,
% 3.32/3.53      (![X0 : $i, X1 : $i]:
% 3.32/3.53         ((k2_xboole_0 @ X1 @ X0)
% 3.32/3.53           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.32/3.53      inference('demod', [status(thm)], ['16', '17', '18'])).
% 3.32/3.53  thf(t98_xboole_1, axiom,
% 3.32/3.53    (![A:$i,B:$i]:
% 3.32/3.53     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 3.32/3.53  thf('20', plain,
% 3.32/3.53      (![X9 : $i, X10 : $i]:
% 3.32/3.53         ((k2_xboole_0 @ X9 @ X10)
% 3.32/3.53           = (k5_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9)))),
% 3.32/3.53      inference('cnf', [status(esa)], [t98_xboole_1])).
% 3.32/3.53  thf('21', plain,
% 3.32/3.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 3.32/3.53      inference('sup+', [status(thm)], ['19', '20'])).
% 3.32/3.53  thf('22', plain,
% 3.32/3.53      (![X0 : $i, X1 : $i]:
% 3.32/3.53         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 3.32/3.53           = (k2_tarski @ X1 @ X0))),
% 3.32/3.53      inference('sup+', [status(thm)], ['9', '21'])).
% 3.32/3.53  thf('23', plain,
% 3.32/3.53      (![X0 : $i, X1 : $i]:
% 3.32/3.53         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 3.32/3.53           = (k2_tarski @ X1 @ X0))),
% 3.32/3.53      inference('sup+', [status(thm)], ['7', '8'])).
% 3.32/3.53  thf('24', plain,
% 3.32/3.53      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 3.32/3.53      inference('sup+', [status(thm)], ['22', '23'])).
% 3.32/3.53  thf('25', plain,
% 3.32/3.53      (![X51 : $i, X52 : $i]:
% 3.32/3.53         ((k1_enumset1 @ X51 @ X51 @ X52) = (k2_tarski @ X51 @ X52))),
% 3.32/3.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 3.32/3.53  thf('26', plain,
% 3.32/3.53      (![X0 : $i, X1 : $i]:
% 3.32/3.53         ((k1_enumset1 @ X0 @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 3.32/3.53      inference('sup+', [status(thm)], ['24', '25'])).
% 3.32/3.53  thf('27', plain,
% 3.32/3.53      (![X51 : $i, X52 : $i]:
% 3.32/3.53         ((k1_enumset1 @ X51 @ X51 @ X52) = (k2_tarski @ X51 @ X52))),
% 3.32/3.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 3.32/3.53  thf('28', plain,
% 3.32/3.53      (![X0 : $i, X1 : $i]:
% 3.32/3.53         ((k1_enumset1 @ X0 @ X0 @ X1) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 3.32/3.53      inference('sup+', [status(thm)], ['26', '27'])).
% 3.32/3.53  thf('29', plain,
% 3.32/3.53      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 3.32/3.53         ((k2_enumset1 @ X41 @ X42 @ X43 @ X44)
% 3.32/3.53           = (k2_xboole_0 @ (k1_enumset1 @ X41 @ X42 @ X43) @ (k1_tarski @ X44)))),
% 3.32/3.53      inference('cnf', [status(esa)], [t46_enumset1])).
% 3.32/3.53  thf('30', plain,
% 3.32/3.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.32/3.53         ((k2_enumset1 @ X0 @ X0 @ X1 @ X2)
% 3.32/3.53           = (k2_xboole_0 @ (k1_enumset1 @ X1 @ X1 @ X0) @ (k1_tarski @ X2)))),
% 3.32/3.53      inference('sup+', [status(thm)], ['28', '29'])).
% 3.32/3.53  thf('31', plain,
% 3.32/3.53      (![X53 : $i, X54 : $i, X55 : $i]:
% 3.32/3.53         ((k2_enumset1 @ X53 @ X53 @ X54 @ X55)
% 3.32/3.53           = (k1_enumset1 @ X53 @ X54 @ X55))),
% 3.32/3.53      inference('cnf', [status(esa)], [t71_enumset1])).
% 3.32/3.53  thf('32', plain,
% 3.32/3.53      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 3.32/3.53         ((k2_enumset1 @ X41 @ X42 @ X43 @ X44)
% 3.32/3.53           = (k2_xboole_0 @ (k1_enumset1 @ X41 @ X42 @ X43) @ (k1_tarski @ X44)))),
% 3.32/3.53      inference('cnf', [status(esa)], [t46_enumset1])).
% 3.32/3.53  thf('33', plain,
% 3.32/3.53      (![X53 : $i, X54 : $i, X55 : $i]:
% 3.32/3.53         ((k2_enumset1 @ X53 @ X53 @ X54 @ X55)
% 3.32/3.53           = (k1_enumset1 @ X53 @ X54 @ X55))),
% 3.32/3.53      inference('cnf', [status(esa)], [t71_enumset1])).
% 3.32/3.53  thf('34', plain,
% 3.32/3.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.32/3.53         ((k1_enumset1 @ X0 @ X1 @ X2) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 3.32/3.53      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 3.32/3.53  thf('35', plain,
% 3.32/3.53      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 3.32/3.53         != (k1_enumset1 @ sk_B @ sk_A @ sk_C))),
% 3.32/3.53      inference('demod', [status(thm)], ['0', '34'])).
% 3.32/3.53  thf(t119_enumset1, axiom,
% 3.32/3.53    (![A:$i,B:$i,C:$i,D:$i]:
% 3.32/3.53     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ C @ D @ B @ A ) ))).
% 3.32/3.53  thf('36', plain,
% 3.32/3.53      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 3.32/3.53         ((k2_enumset1 @ X27 @ X26 @ X24 @ X25)
% 3.32/3.53           = (k2_enumset1 @ X24 @ X25 @ X26 @ X27))),
% 3.32/3.53      inference('cnf', [status(esa)], [t119_enumset1])).
% 3.32/3.53  thf('37', plain,
% 3.32/3.53      (![X53 : $i, X54 : $i, X55 : $i]:
% 3.32/3.53         ((k2_enumset1 @ X53 @ X53 @ X54 @ X55)
% 3.32/3.53           = (k1_enumset1 @ X53 @ X54 @ X55))),
% 3.32/3.53      inference('cnf', [status(esa)], [t71_enumset1])).
% 3.32/3.53  thf('38', plain,
% 3.32/3.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.32/3.53         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 3.32/3.53      inference('sup+', [status(thm)], ['36', '37'])).
% 3.32/3.53  thf('39', plain,
% 3.32/3.53      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 3.32/3.53         ((k2_enumset1 @ X27 @ X26 @ X24 @ X25)
% 3.32/3.53           = (k2_enumset1 @ X24 @ X25 @ X26 @ X27))),
% 3.32/3.53      inference('cnf', [status(esa)], [t119_enumset1])).
% 3.32/3.53  thf('40', plain,
% 3.32/3.53      (![X53 : $i, X54 : $i, X55 : $i]:
% 3.32/3.53         ((k2_enumset1 @ X53 @ X53 @ X54 @ X55)
% 3.32/3.53           = (k1_enumset1 @ X53 @ X54 @ X55))),
% 3.32/3.53      inference('cnf', [status(esa)], [t71_enumset1])).
% 3.32/3.53  thf('41', plain,
% 3.32/3.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.32/3.53         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 3.32/3.53      inference('sup+', [status(thm)], ['39', '40'])).
% 3.32/3.53  thf('42', plain,
% 3.32/3.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.32/3.53         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 3.32/3.53      inference('sup+', [status(thm)], ['38', '41'])).
% 3.32/3.53  thf('43', plain,
% 3.32/3.53      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 3.32/3.53         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 3.32/3.53      inference('demod', [status(thm)], ['35', '42'])).
% 3.32/3.53  thf('44', plain,
% 3.32/3.53      (![X51 : $i, X52 : $i]:
% 3.32/3.53         ((k1_enumset1 @ X51 @ X51 @ X52) = (k2_tarski @ X51 @ X52))),
% 3.32/3.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 3.32/3.53  thf(l57_enumset1, axiom,
% 3.32/3.53    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 3.32/3.53     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 3.32/3.53       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ))).
% 3.32/3.53  thf('45', plain,
% 3.32/3.53      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 3.32/3.53         ((k3_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15)
% 3.32/3.53           = (k2_xboole_0 @ (k1_enumset1 @ X11 @ X12 @ X13) @ 
% 3.32/3.53              (k2_tarski @ X14 @ X15)))),
% 3.32/3.53      inference('cnf', [status(esa)], [l57_enumset1])).
% 3.32/3.53  thf('46', plain,
% 3.32/3.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.32/3.53         ((k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2)
% 3.32/3.53           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 3.32/3.53      inference('sup+', [status(thm)], ['44', '45'])).
% 3.32/3.53  thf(t72_enumset1, axiom,
% 3.32/3.53    (![A:$i,B:$i,C:$i,D:$i]:
% 3.32/3.53     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 3.32/3.53  thf('47', plain,
% 3.32/3.53      (![X56 : $i, X57 : $i, X58 : $i, X59 : $i]:
% 3.32/3.53         ((k3_enumset1 @ X56 @ X56 @ X57 @ X58 @ X59)
% 3.32/3.53           = (k2_enumset1 @ X56 @ X57 @ X58 @ X59))),
% 3.32/3.53      inference('cnf', [status(esa)], [t72_enumset1])).
% 3.32/3.53  thf(t125_enumset1, axiom,
% 3.32/3.53    (![A:$i,B:$i,C:$i,D:$i]:
% 3.32/3.53     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ C @ B @ A ) ))).
% 3.32/3.53  thf('48', plain,
% 3.32/3.53      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 3.32/3.53         ((k2_enumset1 @ X31 @ X30 @ X29 @ X28)
% 3.32/3.53           = (k2_enumset1 @ X28 @ X29 @ X30 @ X31))),
% 3.32/3.53      inference('cnf', [status(esa)], [t125_enumset1])).
% 3.32/3.53  thf('49', plain,
% 3.32/3.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.32/3.53         ((k2_enumset1 @ X0 @ X1 @ X2 @ X3)
% 3.32/3.53           = (k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0))),
% 3.32/3.53      inference('sup+', [status(thm)], ['47', '48'])).
% 3.32/3.53  thf('50', plain,
% 3.32/3.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.32/3.53         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 3.32/3.53      inference('sup+', [status(thm)], ['39', '40'])).
% 3.32/3.53  thf(t107_enumset1, axiom,
% 3.32/3.53    (![A:$i,B:$i,C:$i,D:$i]:
% 3.32/3.53     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ D @ C @ B ) ))).
% 3.32/3.53  thf('51', plain,
% 3.32/3.53      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 3.32/3.53         ((k2_enumset1 @ X16 @ X19 @ X18 @ X17)
% 3.32/3.53           = (k2_enumset1 @ X16 @ X17 @ X18 @ X19))),
% 3.32/3.53      inference('cnf', [status(esa)], [t107_enumset1])).
% 3.32/3.53  thf('52', plain,
% 3.32/3.53      (![X53 : $i, X54 : $i, X55 : $i]:
% 3.32/3.53         ((k2_enumset1 @ X53 @ X53 @ X54 @ X55)
% 3.32/3.53           = (k1_enumset1 @ X53 @ X54 @ X55))),
% 3.32/3.53      inference('cnf', [status(esa)], [t71_enumset1])).
% 3.32/3.53  thf('53', plain,
% 3.32/3.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.32/3.53         ((k2_enumset1 @ X0 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 3.32/3.53      inference('sup+', [status(thm)], ['51', '52'])).
% 3.32/3.53  thf('54', plain,
% 3.32/3.53      (![X0 : $i, X1 : $i]:
% 3.32/3.53         ((k1_enumset1 @ X0 @ X1 @ X0) = (k1_enumset1 @ X0 @ X0 @ X1))),
% 3.32/3.53      inference('sup+', [status(thm)], ['50', '53'])).
% 3.32/3.53  thf('55', plain,
% 3.32/3.53      (![X0 : $i, X1 : $i]:
% 3.32/3.53         ((k1_enumset1 @ X0 @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 3.32/3.53      inference('sup+', [status(thm)], ['24', '25'])).
% 3.32/3.53  thf('56', plain,
% 3.32/3.53      (![X0 : $i, X1 : $i]:
% 3.32/3.53         ((k1_enumset1 @ X0 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 3.32/3.53      inference('sup+', [status(thm)], ['54', '55'])).
% 3.32/3.53  thf('57', plain,
% 3.32/3.53      (![X51 : $i, X52 : $i]:
% 3.32/3.53         ((k1_enumset1 @ X51 @ X51 @ X52) = (k2_tarski @ X51 @ X52))),
% 3.32/3.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 3.32/3.53  thf('58', plain,
% 3.32/3.53      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 3.32/3.53         ((k2_enumset1 @ X41 @ X42 @ X43 @ X44)
% 3.32/3.53           = (k2_xboole_0 @ (k1_enumset1 @ X41 @ X42 @ X43) @ (k1_tarski @ X44)))),
% 3.32/3.53      inference('cnf', [status(esa)], [t46_enumset1])).
% 3.32/3.53  thf('59', plain,
% 3.32/3.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.32/3.53         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 3.32/3.53           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 3.32/3.53      inference('sup+', [status(thm)], ['57', '58'])).
% 3.32/3.53  thf('60', plain,
% 3.32/3.53      (![X53 : $i, X54 : $i, X55 : $i]:
% 3.32/3.53         ((k2_enumset1 @ X53 @ X53 @ X54 @ X55)
% 3.32/3.53           = (k1_enumset1 @ X53 @ X54 @ X55))),
% 3.32/3.53      inference('cnf', [status(esa)], [t71_enumset1])).
% 3.32/3.53  thf('61', plain,
% 3.32/3.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.32/3.53         ((k1_enumset1 @ X1 @ X0 @ X2)
% 3.32/3.53           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 3.32/3.53      inference('demod', [status(thm)], ['59', '60'])).
% 3.32/3.53  thf('62', plain,
% 3.32/3.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.32/3.53         ((k1_enumset1 @ X1 @ X0 @ X2)
% 3.32/3.53           = (k2_xboole_0 @ (k1_enumset1 @ X0 @ X1 @ X0) @ (k1_tarski @ X2)))),
% 3.32/3.53      inference('sup+', [status(thm)], ['56', '61'])).
% 3.32/3.53  thf('63', plain,
% 3.32/3.53      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 3.32/3.53         ((k2_enumset1 @ X41 @ X42 @ X43 @ X44)
% 3.32/3.53           = (k2_xboole_0 @ (k1_enumset1 @ X41 @ X42 @ X43) @ (k1_tarski @ X44)))),
% 3.32/3.53      inference('cnf', [status(esa)], [t46_enumset1])).
% 3.32/3.53  thf('64', plain,
% 3.32/3.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.32/3.53         ((k1_enumset1 @ X1 @ X0 @ X2) = (k2_enumset1 @ X0 @ X1 @ X0 @ X2))),
% 3.32/3.53      inference('demod', [status(thm)], ['62', '63'])).
% 3.32/3.53  thf('65', plain,
% 3.32/3.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.32/3.53         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 3.32/3.53      inference('sup+', [status(thm)], ['38', '41'])).
% 3.32/3.53  thf('66', plain,
% 3.32/3.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.32/3.53         ((k1_enumset1 @ X0 @ X1 @ X2) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 3.32/3.53      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 3.32/3.53  thf('67', plain,
% 3.32/3.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.32/3.53         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 3.32/3.53      inference('sup+', [status(thm)], ['65', '66'])).
% 3.32/3.53  thf('68', plain,
% 3.32/3.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.32/3.53         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 3.32/3.53      inference('sup+', [status(thm)], ['38', '41'])).
% 3.32/3.53  thf('69', plain,
% 3.32/3.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.32/3.53         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 3.32/3.53      inference('sup+', [status(thm)], ['67', '68'])).
% 3.32/3.53  thf('70', plain,
% 3.32/3.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.32/3.53         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 3.32/3.53      inference('sup+', [status(thm)], ['38', '41'])).
% 3.32/3.53  thf('71', plain,
% 3.32/3.53      (((k1_enumset1 @ sk_B @ sk_C @ sk_A)
% 3.32/3.53         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 3.32/3.53      inference('demod', [status(thm)], ['43', '46', '49', '64', '69', '70'])).
% 3.32/3.53  thf('72', plain, ($false), inference('simplify', [status(thm)], ['71'])).
% 3.32/3.53  
% 3.32/3.53  % SZS output end Refutation
% 3.32/3.53  
% 3.32/3.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

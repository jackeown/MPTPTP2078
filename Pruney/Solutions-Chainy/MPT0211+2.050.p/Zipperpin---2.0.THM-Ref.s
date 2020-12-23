%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fNWgw8dOFA

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:36 EST 2020

% Result     : Theorem 3.04s
% Output     : Refutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 316 expanded)
%              Number of leaves         :   27 ( 117 expanded)
%              Depth                    :   21
%              Number of atoms          : 1034 (2961 expanded)
%              Number of equality atoms :  101 ( 303 expanded)
%              Maximal formula depth    :   12 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

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
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X40: $i] :
      ( ( k2_tarski @ X40 @ X40 )
      = ( k1_tarski @ X40 ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k2_enumset1 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X28 @ X29 @ X30 ) @ ( k1_tarski @ X31 ) ) ) ),
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
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X43 @ X43 @ X44 @ X45 )
      = ( k1_enumset1 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
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
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k2_enumset1 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X28 @ X29 @ X30 ) @ ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X43 @ X43 @ X44 @ X45 )
      = ( k1_enumset1 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('32',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k2_enumset1 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X28 @ X29 @ X30 ) @ ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('33',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X43 @ X43 @ X44 @ X45 )
      = ( k1_enumset1 @ X43 @ X44 @ X45 ) ) ),
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

thf(t107_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ D @ C @ B ) ) )).

thf('36',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k2_enumset1 @ X16 @ X19 @ X18 @ X17 )
      = ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('37',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X43 @ X43 @ X44 @ X45 )
      = ( k1_enumset1 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t125_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ D @ C @ B @ A ) ) )).

thf('39',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k2_enumset1 @ X27 @ X26 @ X25 @ X24 )
      = ( k2_enumset1 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_tarski @ sk_C @ sk_A ) )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['35','42'])).

thf('44',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
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
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( k3_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49 )
      = ( k2_enumset1 @ X46 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('48',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k2_enumset1 @ X27 @ X26 @ X25 @ X24 )
      = ( k2_enumset1 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 )
      = ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k2_enumset1 @ X27 @ X26 @ X25 @ X24 )
      = ( k2_enumset1 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf('51',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X43 @ X43 @ X44 @ X45 )
      = ( k1_enumset1 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

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
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('58',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k2_enumset1 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X28 @ X29 @ X30 ) @ ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_enumset1 @ X3 @ X2 @ X1 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('63',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X43 @ X43 @ X44 @ X45 )
      = ( k1_enumset1 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k2_enumset1 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X28 @ X29 @ X30 ) @ ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X0 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf(t113_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ D @ C @ A ) ) )).

thf('69',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k2_enumset1 @ X23 @ X20 @ X22 @ X21 )
      = ( k2_enumset1 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t113_enumset1])).

thf('70',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X43 @ X43 @ X44 @ X45 )
      = ( k1_enumset1 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k2_enumset1 @ X27 @ X26 @ X25 @ X24 )
      = ( k2_enumset1 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k2_enumset1 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X28 @ X29 @ X30 ) @ ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k2_enumset1 @ X1 @ X0 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['68','73','74'])).

thf('76',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k2_enumset1 @ X16 @ X19 @ X18 @ X17 )
      = ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X1 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k2_enumset1 @ X27 @ X26 @ X25 @ X24 )
      = ( k2_enumset1 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['61','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k1_enumset1 @ X0 @ X1 @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_enumset1 @ X3 @ X2 @ X1 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X0 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ( k1_enumset1 @ sk_B @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['43','46','49','83'])).

thf('85',plain,(
    $false ),
    inference(simplify,[status(thm)],['84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fNWgw8dOFA
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:52:48 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 3.04/3.30  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.04/3.30  % Solved by: fo/fo7.sh
% 3.04/3.30  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.04/3.30  % done 2082 iterations in 2.839s
% 3.04/3.30  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.04/3.30  % SZS output start Refutation
% 3.04/3.30  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.04/3.30  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.04/3.30  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.04/3.30  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 3.04/3.30  thf(sk_C_type, type, sk_C: $i).
% 3.04/3.30  thf(sk_B_type, type, sk_B: $i).
% 3.04/3.30  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 3.04/3.30  thf(sk_A_type, type, sk_A: $i).
% 3.04/3.30  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 3.04/3.30  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.04/3.30  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 3.04/3.30  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.04/3.30  thf(t137_enumset1, conjecture,
% 3.04/3.30    (![A:$i,B:$i,C:$i]:
% 3.04/3.30     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 3.04/3.30       ( k1_enumset1 @ A @ B @ C ) ))).
% 3.04/3.30  thf(zf_stmt_0, negated_conjecture,
% 3.04/3.30    (~( ![A:$i,B:$i,C:$i]:
% 3.04/3.30        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 3.04/3.30          ( k1_enumset1 @ A @ B @ C ) ) )),
% 3.04/3.30    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 3.04/3.30  thf('0', plain,
% 3.04/3.30      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 3.04/3.30         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 3.04/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.04/3.30  thf(t70_enumset1, axiom,
% 3.04/3.30    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 3.04/3.30  thf('1', plain,
% 3.04/3.30      (![X41 : $i, X42 : $i]:
% 3.04/3.30         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 3.04/3.30      inference('cnf', [status(esa)], [t70_enumset1])).
% 3.04/3.30  thf(t69_enumset1, axiom,
% 3.04/3.30    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 3.04/3.30  thf('2', plain, (![X40 : $i]: ((k2_tarski @ X40 @ X40) = (k1_tarski @ X40))),
% 3.04/3.30      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.04/3.30  thf('3', plain,
% 3.04/3.30      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 3.04/3.30      inference('sup+', [status(thm)], ['1', '2'])).
% 3.04/3.30  thf(t46_enumset1, axiom,
% 3.04/3.30    (![A:$i,B:$i,C:$i,D:$i]:
% 3.04/3.30     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 3.04/3.30       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 3.04/3.30  thf('4', plain,
% 3.04/3.30      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 3.04/3.30         ((k2_enumset1 @ X28 @ X29 @ X30 @ X31)
% 3.04/3.30           = (k2_xboole_0 @ (k1_enumset1 @ X28 @ X29 @ X30) @ (k1_tarski @ X31)))),
% 3.04/3.30      inference('cnf', [status(esa)], [t46_enumset1])).
% 3.04/3.30  thf('5', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i]:
% 3.04/3.30         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 3.04/3.30           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 3.04/3.30      inference('sup+', [status(thm)], ['3', '4'])).
% 3.04/3.30  thf(t71_enumset1, axiom,
% 3.04/3.30    (![A:$i,B:$i,C:$i]:
% 3.04/3.30     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 3.04/3.30  thf('6', plain,
% 3.04/3.30      (![X43 : $i, X44 : $i, X45 : $i]:
% 3.04/3.30         ((k2_enumset1 @ X43 @ X43 @ X44 @ X45)
% 3.04/3.30           = (k1_enumset1 @ X43 @ X44 @ X45))),
% 3.04/3.30      inference('cnf', [status(esa)], [t71_enumset1])).
% 3.04/3.30  thf('7', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i]:
% 3.04/3.30         ((k1_enumset1 @ X0 @ X0 @ X1)
% 3.04/3.30           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 3.04/3.30      inference('demod', [status(thm)], ['5', '6'])).
% 3.04/3.30  thf('8', plain,
% 3.04/3.30      (![X41 : $i, X42 : $i]:
% 3.04/3.30         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 3.04/3.30      inference('cnf', [status(esa)], [t70_enumset1])).
% 3.04/3.30  thf('9', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i]:
% 3.04/3.30         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 3.04/3.30           = (k2_tarski @ X1 @ X0))),
% 3.04/3.30      inference('sup+', [status(thm)], ['7', '8'])).
% 3.04/3.30  thf(t94_xboole_1, axiom,
% 3.04/3.30    (![A:$i,B:$i]:
% 3.04/3.30     ( ( k2_xboole_0 @ A @ B ) =
% 3.04/3.30       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 3.04/3.30  thf('10', plain,
% 3.04/3.30      (![X7 : $i, X8 : $i]:
% 3.04/3.30         ((k2_xboole_0 @ X7 @ X8)
% 3.04/3.30           = (k5_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ (k3_xboole_0 @ X7 @ X8)))),
% 3.04/3.30      inference('cnf', [status(esa)], [t94_xboole_1])).
% 3.04/3.30  thf(t91_xboole_1, axiom,
% 3.04/3.30    (![A:$i,B:$i,C:$i]:
% 3.04/3.30     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 3.04/3.30       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 3.04/3.30  thf('11', plain,
% 3.04/3.30      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.04/3.30         ((k5_xboole_0 @ (k5_xboole_0 @ X4 @ X5) @ X6)
% 3.04/3.30           = (k5_xboole_0 @ X4 @ (k5_xboole_0 @ X5 @ X6)))),
% 3.04/3.30      inference('cnf', [status(esa)], [t91_xboole_1])).
% 3.04/3.30  thf('12', plain,
% 3.04/3.30      (![X7 : $i, X8 : $i]:
% 3.04/3.30         ((k2_xboole_0 @ X7 @ X8)
% 3.04/3.30           = (k5_xboole_0 @ X7 @ (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X7 @ X8))))),
% 3.04/3.30      inference('demod', [status(thm)], ['10', '11'])).
% 3.04/3.30  thf('13', plain,
% 3.04/3.30      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.04/3.30         ((k5_xboole_0 @ (k5_xboole_0 @ X4 @ X5) @ X6)
% 3.04/3.30           = (k5_xboole_0 @ X4 @ (k5_xboole_0 @ X5 @ X6)))),
% 3.04/3.30      inference('cnf', [status(esa)], [t91_xboole_1])).
% 3.04/3.30  thf(commutativity_k5_xboole_0, axiom,
% 3.04/3.30    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 3.04/3.30  thf('14', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 3.04/3.30      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 3.04/3.30  thf('15', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.04/3.30         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 3.04/3.30           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 3.04/3.30      inference('sup+', [status(thm)], ['13', '14'])).
% 3.04/3.30  thf('16', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i]:
% 3.04/3.30         ((k2_xboole_0 @ X1 @ X0)
% 3.04/3.30           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 3.04/3.30      inference('sup+', [status(thm)], ['12', '15'])).
% 3.04/3.30  thf('17', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 3.04/3.30      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 3.04/3.30  thf(t100_xboole_1, axiom,
% 3.04/3.30    (![A:$i,B:$i]:
% 3.04/3.30     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 3.04/3.30  thf('18', plain,
% 3.04/3.30      (![X2 : $i, X3 : $i]:
% 3.04/3.30         ((k4_xboole_0 @ X2 @ X3)
% 3.04/3.30           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 3.04/3.30      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.04/3.30  thf('19', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i]:
% 3.04/3.30         ((k2_xboole_0 @ X1 @ X0)
% 3.04/3.30           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.04/3.30      inference('demod', [status(thm)], ['16', '17', '18'])).
% 3.04/3.30  thf(t98_xboole_1, axiom,
% 3.04/3.30    (![A:$i,B:$i]:
% 3.04/3.30     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 3.04/3.30  thf('20', plain,
% 3.04/3.30      (![X9 : $i, X10 : $i]:
% 3.04/3.30         ((k2_xboole_0 @ X9 @ X10)
% 3.04/3.30           = (k5_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9)))),
% 3.04/3.30      inference('cnf', [status(esa)], [t98_xboole_1])).
% 3.04/3.30  thf('21', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 3.04/3.30      inference('sup+', [status(thm)], ['19', '20'])).
% 3.04/3.30  thf('22', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i]:
% 3.04/3.30         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 3.04/3.30           = (k2_tarski @ X1 @ X0))),
% 3.04/3.30      inference('sup+', [status(thm)], ['9', '21'])).
% 3.04/3.30  thf('23', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i]:
% 3.04/3.30         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 3.04/3.30           = (k2_tarski @ X1 @ X0))),
% 3.04/3.30      inference('sup+', [status(thm)], ['7', '8'])).
% 3.04/3.30  thf('24', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 3.04/3.30      inference('sup+', [status(thm)], ['22', '23'])).
% 3.04/3.30  thf('25', plain,
% 3.04/3.30      (![X41 : $i, X42 : $i]:
% 3.04/3.30         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 3.04/3.30      inference('cnf', [status(esa)], [t70_enumset1])).
% 3.04/3.30  thf('26', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i]:
% 3.04/3.30         ((k1_enumset1 @ X0 @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 3.04/3.30      inference('sup+', [status(thm)], ['24', '25'])).
% 3.04/3.30  thf('27', plain,
% 3.04/3.30      (![X41 : $i, X42 : $i]:
% 3.04/3.30         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 3.04/3.30      inference('cnf', [status(esa)], [t70_enumset1])).
% 3.04/3.30  thf('28', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i]:
% 3.04/3.30         ((k1_enumset1 @ X0 @ X0 @ X1) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 3.04/3.30      inference('sup+', [status(thm)], ['26', '27'])).
% 3.04/3.30  thf('29', plain,
% 3.04/3.30      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 3.04/3.30         ((k2_enumset1 @ X28 @ X29 @ X30 @ X31)
% 3.04/3.30           = (k2_xboole_0 @ (k1_enumset1 @ X28 @ X29 @ X30) @ (k1_tarski @ X31)))),
% 3.04/3.30      inference('cnf', [status(esa)], [t46_enumset1])).
% 3.04/3.30  thf('30', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.04/3.30         ((k2_enumset1 @ X0 @ X0 @ X1 @ X2)
% 3.04/3.30           = (k2_xboole_0 @ (k1_enumset1 @ X1 @ X1 @ X0) @ (k1_tarski @ X2)))),
% 3.04/3.30      inference('sup+', [status(thm)], ['28', '29'])).
% 3.04/3.30  thf('31', plain,
% 3.04/3.30      (![X43 : $i, X44 : $i, X45 : $i]:
% 3.04/3.30         ((k2_enumset1 @ X43 @ X43 @ X44 @ X45)
% 3.04/3.30           = (k1_enumset1 @ X43 @ X44 @ X45))),
% 3.04/3.30      inference('cnf', [status(esa)], [t71_enumset1])).
% 3.04/3.30  thf('32', plain,
% 3.04/3.30      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 3.04/3.30         ((k2_enumset1 @ X28 @ X29 @ X30 @ X31)
% 3.04/3.30           = (k2_xboole_0 @ (k1_enumset1 @ X28 @ X29 @ X30) @ (k1_tarski @ X31)))),
% 3.04/3.30      inference('cnf', [status(esa)], [t46_enumset1])).
% 3.04/3.30  thf('33', plain,
% 3.04/3.30      (![X43 : $i, X44 : $i, X45 : $i]:
% 3.04/3.30         ((k2_enumset1 @ X43 @ X43 @ X44 @ X45)
% 3.04/3.30           = (k1_enumset1 @ X43 @ X44 @ X45))),
% 3.04/3.30      inference('cnf', [status(esa)], [t71_enumset1])).
% 3.04/3.30  thf('34', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.04/3.30         ((k1_enumset1 @ X0 @ X1 @ X2) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 3.04/3.30      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 3.04/3.30  thf('35', plain,
% 3.04/3.30      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 3.04/3.30         != (k1_enumset1 @ sk_B @ sk_A @ sk_C))),
% 3.04/3.30      inference('demod', [status(thm)], ['0', '34'])).
% 3.04/3.30  thf(t107_enumset1, axiom,
% 3.04/3.30    (![A:$i,B:$i,C:$i,D:$i]:
% 3.04/3.30     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ D @ C @ B ) ))).
% 3.04/3.30  thf('36', plain,
% 3.04/3.30      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 3.04/3.30         ((k2_enumset1 @ X16 @ X19 @ X18 @ X17)
% 3.04/3.30           = (k2_enumset1 @ X16 @ X17 @ X18 @ X19))),
% 3.04/3.30      inference('cnf', [status(esa)], [t107_enumset1])).
% 3.04/3.30  thf('37', plain,
% 3.04/3.30      (![X43 : $i, X44 : $i, X45 : $i]:
% 3.04/3.30         ((k2_enumset1 @ X43 @ X43 @ X44 @ X45)
% 3.04/3.30           = (k1_enumset1 @ X43 @ X44 @ X45))),
% 3.04/3.30      inference('cnf', [status(esa)], [t71_enumset1])).
% 3.04/3.30  thf('38', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.04/3.30         ((k2_enumset1 @ X0 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 3.04/3.30      inference('sup+', [status(thm)], ['36', '37'])).
% 3.04/3.30  thf(t125_enumset1, axiom,
% 3.04/3.30    (![A:$i,B:$i,C:$i,D:$i]:
% 3.04/3.30     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ C @ B @ A ) ))).
% 3.04/3.30  thf('39', plain,
% 3.04/3.30      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 3.04/3.30         ((k2_enumset1 @ X27 @ X26 @ X25 @ X24)
% 3.04/3.30           = (k2_enumset1 @ X24 @ X25 @ X26 @ X27))),
% 3.04/3.30      inference('cnf', [status(esa)], [t125_enumset1])).
% 3.04/3.30  thf('40', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.04/3.30         ((k2_enumset1 @ X2 @ X1 @ X0 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 3.04/3.30      inference('sup+', [status(thm)], ['38', '39'])).
% 3.04/3.30  thf('41', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.04/3.30         ((k2_enumset1 @ X0 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 3.04/3.30      inference('sup+', [status(thm)], ['36', '37'])).
% 3.04/3.30  thf('42', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.04/3.30         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 3.04/3.30      inference('sup+', [status(thm)], ['40', '41'])).
% 3.04/3.30  thf('43', plain,
% 3.04/3.30      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 3.04/3.30         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 3.04/3.30      inference('demod', [status(thm)], ['35', '42'])).
% 3.04/3.30  thf('44', plain,
% 3.04/3.30      (![X41 : $i, X42 : $i]:
% 3.04/3.30         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 3.04/3.30      inference('cnf', [status(esa)], [t70_enumset1])).
% 3.04/3.30  thf(l57_enumset1, axiom,
% 3.04/3.30    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 3.04/3.30     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 3.04/3.30       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ))).
% 3.04/3.30  thf('45', plain,
% 3.04/3.30      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 3.04/3.30         ((k3_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15)
% 3.04/3.30           = (k2_xboole_0 @ (k1_enumset1 @ X11 @ X12 @ X13) @ 
% 3.04/3.30              (k2_tarski @ X14 @ X15)))),
% 3.04/3.30      inference('cnf', [status(esa)], [l57_enumset1])).
% 3.04/3.30  thf('46', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.04/3.30         ((k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2)
% 3.04/3.30           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 3.04/3.30      inference('sup+', [status(thm)], ['44', '45'])).
% 3.04/3.30  thf(t72_enumset1, axiom,
% 3.04/3.30    (![A:$i,B:$i,C:$i,D:$i]:
% 3.04/3.30     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 3.04/3.30  thf('47', plain,
% 3.04/3.30      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 3.04/3.30         ((k3_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49)
% 3.04/3.30           = (k2_enumset1 @ X46 @ X47 @ X48 @ X49))),
% 3.04/3.30      inference('cnf', [status(esa)], [t72_enumset1])).
% 3.04/3.30  thf('48', plain,
% 3.04/3.30      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 3.04/3.30         ((k2_enumset1 @ X27 @ X26 @ X25 @ X24)
% 3.04/3.30           = (k2_enumset1 @ X24 @ X25 @ X26 @ X27))),
% 3.04/3.30      inference('cnf', [status(esa)], [t125_enumset1])).
% 3.04/3.30  thf('49', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.04/3.30         ((k2_enumset1 @ X0 @ X1 @ X2 @ X3)
% 3.04/3.30           = (k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0))),
% 3.04/3.30      inference('sup+', [status(thm)], ['47', '48'])).
% 3.04/3.30  thf('50', plain,
% 3.04/3.30      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 3.04/3.30         ((k2_enumset1 @ X27 @ X26 @ X25 @ X24)
% 3.04/3.30           = (k2_enumset1 @ X24 @ X25 @ X26 @ X27))),
% 3.04/3.30      inference('cnf', [status(esa)], [t125_enumset1])).
% 3.04/3.30  thf('51', plain,
% 3.04/3.30      (![X43 : $i, X44 : $i, X45 : $i]:
% 3.04/3.30         ((k2_enumset1 @ X43 @ X43 @ X44 @ X45)
% 3.04/3.30           = (k1_enumset1 @ X43 @ X44 @ X45))),
% 3.04/3.30      inference('cnf', [status(esa)], [t71_enumset1])).
% 3.04/3.30  thf('52', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.04/3.30         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 3.04/3.30      inference('sup+', [status(thm)], ['50', '51'])).
% 3.04/3.30  thf('53', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.04/3.30         ((k2_enumset1 @ X0 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 3.04/3.30      inference('sup+', [status(thm)], ['36', '37'])).
% 3.04/3.30  thf('54', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i]:
% 3.04/3.30         ((k1_enumset1 @ X0 @ X1 @ X0) = (k1_enumset1 @ X0 @ X0 @ X1))),
% 3.04/3.30      inference('sup+', [status(thm)], ['52', '53'])).
% 3.04/3.30  thf('55', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i]:
% 3.04/3.30         ((k1_enumset1 @ X0 @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 3.04/3.30      inference('sup+', [status(thm)], ['24', '25'])).
% 3.04/3.30  thf('56', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i]:
% 3.04/3.30         ((k1_enumset1 @ X0 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 3.04/3.30      inference('sup+', [status(thm)], ['54', '55'])).
% 3.04/3.30  thf('57', plain,
% 3.04/3.30      (![X41 : $i, X42 : $i]:
% 3.04/3.30         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 3.04/3.30      inference('cnf', [status(esa)], [t70_enumset1])).
% 3.04/3.30  thf('58', plain,
% 3.04/3.30      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 3.04/3.30         ((k2_enumset1 @ X28 @ X29 @ X30 @ X31)
% 3.04/3.30           = (k2_xboole_0 @ (k1_enumset1 @ X28 @ X29 @ X30) @ (k1_tarski @ X31)))),
% 3.04/3.30      inference('cnf', [status(esa)], [t46_enumset1])).
% 3.04/3.30  thf('59', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 3.04/3.30      inference('sup+', [status(thm)], ['19', '20'])).
% 3.04/3.30  thf('60', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.04/3.30         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_enumset1 @ X3 @ X2 @ X1))
% 3.04/3.30           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 3.04/3.30      inference('sup+', [status(thm)], ['58', '59'])).
% 3.04/3.30  thf('61', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.04/3.30         ((k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0))
% 3.04/3.30           = (k2_enumset1 @ X1 @ X1 @ X0 @ X2))),
% 3.04/3.30      inference('sup+', [status(thm)], ['57', '60'])).
% 3.04/3.30  thf('62', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.04/3.30         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 3.04/3.30      inference('sup+', [status(thm)], ['50', '51'])).
% 3.04/3.30  thf('63', plain,
% 3.04/3.30      (![X43 : $i, X44 : $i, X45 : $i]:
% 3.04/3.30         ((k2_enumset1 @ X43 @ X43 @ X44 @ X45)
% 3.04/3.30           = (k1_enumset1 @ X43 @ X44 @ X45))),
% 3.04/3.30      inference('cnf', [status(esa)], [t71_enumset1])).
% 3.04/3.30  thf('64', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i]:
% 3.04/3.30         ((k1_enumset1 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X1))),
% 3.04/3.30      inference('sup+', [status(thm)], ['62', '63'])).
% 3.04/3.30  thf('65', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.04/3.30         ((k1_enumset1 @ X0 @ X1 @ X2) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 3.04/3.30      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 3.04/3.30  thf('66', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i]:
% 3.04/3.30         ((k1_enumset1 @ X1 @ X0 @ X0) = (k1_enumset1 @ X1 @ X0 @ X1))),
% 3.04/3.30      inference('sup+', [status(thm)], ['64', '65'])).
% 3.04/3.30  thf('67', plain,
% 3.04/3.30      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 3.04/3.30         ((k2_enumset1 @ X28 @ X29 @ X30 @ X31)
% 3.04/3.30           = (k2_xboole_0 @ (k1_enumset1 @ X28 @ X29 @ X30) @ (k1_tarski @ X31)))),
% 3.04/3.30      inference('cnf', [status(esa)], [t46_enumset1])).
% 3.04/3.30  thf('68', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.04/3.30         ((k2_enumset1 @ X1 @ X0 @ X1 @ X2)
% 3.04/3.30           = (k2_xboole_0 @ (k1_enumset1 @ X1 @ X0 @ X0) @ (k1_tarski @ X2)))),
% 3.04/3.30      inference('sup+', [status(thm)], ['66', '67'])).
% 3.04/3.30  thf(t113_enumset1, axiom,
% 3.04/3.30    (![A:$i,B:$i,C:$i,D:$i]:
% 3.04/3.30     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ D @ C @ A ) ))).
% 3.04/3.30  thf('69', plain,
% 3.04/3.30      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 3.04/3.30         ((k2_enumset1 @ X23 @ X20 @ X22 @ X21)
% 3.04/3.30           = (k2_enumset1 @ X20 @ X21 @ X22 @ X23))),
% 3.04/3.30      inference('cnf', [status(esa)], [t113_enumset1])).
% 3.04/3.30  thf('70', plain,
% 3.04/3.30      (![X43 : $i, X44 : $i, X45 : $i]:
% 3.04/3.30         ((k2_enumset1 @ X43 @ X43 @ X44 @ X45)
% 3.04/3.30           = (k1_enumset1 @ X43 @ X44 @ X45))),
% 3.04/3.30      inference('cnf', [status(esa)], [t71_enumset1])).
% 3.04/3.30  thf('71', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.04/3.30         ((k2_enumset1 @ X2 @ X0 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 3.04/3.30      inference('sup+', [status(thm)], ['69', '70'])).
% 3.04/3.30  thf('72', plain,
% 3.04/3.30      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 3.04/3.30         ((k2_enumset1 @ X27 @ X26 @ X25 @ X24)
% 3.04/3.30           = (k2_enumset1 @ X24 @ X25 @ X26 @ X27))),
% 3.04/3.30      inference('cnf', [status(esa)], [t125_enumset1])).
% 3.04/3.30  thf('73', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.04/3.30         ((k2_enumset1 @ X2 @ X1 @ X2 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 3.04/3.30      inference('sup+', [status(thm)], ['71', '72'])).
% 3.04/3.30  thf('74', plain,
% 3.04/3.30      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 3.04/3.30         ((k2_enumset1 @ X28 @ X29 @ X30 @ X31)
% 3.04/3.30           = (k2_xboole_0 @ (k1_enumset1 @ X28 @ X29 @ X30) @ (k1_tarski @ X31)))),
% 3.04/3.30      inference('cnf', [status(esa)], [t46_enumset1])).
% 3.04/3.30  thf('75', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.04/3.30         ((k1_enumset1 @ X1 @ X0 @ X2) = (k2_enumset1 @ X1 @ X0 @ X0 @ X2))),
% 3.04/3.30      inference('demod', [status(thm)], ['68', '73', '74'])).
% 3.04/3.30  thf('76', plain,
% 3.04/3.30      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 3.04/3.30         ((k2_enumset1 @ X16 @ X19 @ X18 @ X17)
% 3.04/3.30           = (k2_enumset1 @ X16 @ X17 @ X18 @ X19))),
% 3.04/3.30      inference('cnf', [status(esa)], [t107_enumset1])).
% 3.04/3.30  thf('77', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.04/3.30         ((k2_enumset1 @ X2 @ X0 @ X1 @ X1) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 3.04/3.30      inference('sup+', [status(thm)], ['75', '76'])).
% 3.04/3.30  thf('78', plain,
% 3.04/3.30      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 3.04/3.30         ((k2_enumset1 @ X27 @ X26 @ X25 @ X24)
% 3.04/3.30           = (k2_enumset1 @ X24 @ X25 @ X26 @ X27))),
% 3.04/3.30      inference('cnf', [status(esa)], [t125_enumset1])).
% 3.04/3.30  thf('79', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.04/3.30         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 3.04/3.30      inference('sup+', [status(thm)], ['77', '78'])).
% 3.04/3.30  thf('80', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.04/3.30         ((k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0))
% 3.04/3.30           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 3.04/3.30      inference('demod', [status(thm)], ['61', '79'])).
% 3.04/3.30  thf('81', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.04/3.30         ((k2_xboole_0 @ (k1_tarski @ X2) @ (k1_enumset1 @ X0 @ X1 @ X0))
% 3.04/3.30           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 3.04/3.30      inference('sup+', [status(thm)], ['56', '80'])).
% 3.04/3.30  thf('82', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.04/3.30         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_enumset1 @ X3 @ X2 @ X1))
% 3.04/3.30           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 3.04/3.30      inference('sup+', [status(thm)], ['58', '59'])).
% 3.04/3.30  thf('83', plain,
% 3.04/3.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.04/3.30         ((k2_enumset1 @ X0 @ X1 @ X0 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 3.04/3.30      inference('demod', [status(thm)], ['81', '82'])).
% 3.04/3.30  thf('84', plain,
% 3.04/3.30      (((k1_enumset1 @ sk_B @ sk_C @ sk_A)
% 3.04/3.30         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 3.04/3.30      inference('demod', [status(thm)], ['43', '46', '49', '83'])).
% 3.04/3.30  thf('85', plain, ($false), inference('simplify', [status(thm)], ['84'])).
% 3.04/3.30  
% 3.04/3.30  % SZS output end Refutation
% 3.04/3.30  
% 3.04/3.31  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

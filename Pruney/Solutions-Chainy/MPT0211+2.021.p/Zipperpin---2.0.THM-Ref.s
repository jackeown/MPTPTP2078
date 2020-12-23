%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.U2gZaf8dYD

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:32 EST 2020

% Result     : Theorem 48.76s
% Output     : Refutation 48.76s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 422 expanded)
%              Number of leaves         :   20 ( 153 expanded)
%              Depth                    :   15
%              Number of atoms          : 1332 (4560 expanded)
%              Number of equality atoms :  114 ( 411 expanded)
%              Maximal formula depth    :   15 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

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

thf(t113_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ D @ C @ A ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k2_enumset1 @ X17 @ X14 @ X16 @ X15 )
      = ( k2_enumset1 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t113_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('2',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X43 @ X43 @ X44 @ X45 )
      = ( k1_enumset1 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t104_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ B @ D ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X8 @ X7 @ X9 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t104_enumset1])).

thf('5',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X43 @ X43 @ X44 @ X45 )
      = ( k1_enumset1 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('8',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k2_enumset1 @ X22 @ X23 @ X24 @ X25 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X22 @ X23 @ X24 ) @ ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X0 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k2_enumset1 @ X17 @ X14 @ X16 @ X15 )
      = ( k2_enumset1 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t113_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k2_enumset1 @ X22 @ X23 @ X24 @ X25 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X22 @ X23 @ X24 ) @ ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','12','13','14'])).

thf('16',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_tarski @ sk_C @ sk_A ) )
 != ( k1_enumset1 @ sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['0','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','12','13','14'])).

thf(t107_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ D @ C @ B ) ) )).

thf('18',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X13 @ X12 @ X11 )
      = ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('25',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_tarski @ sk_C @ sk_A ) )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['16','23','24'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('26',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( k3_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49 )
      = ( k2_enumset1 @ X46 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X13 @ X12 @ X11 )
      = ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('30',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X43 @ X43 @ X44 @ X45 )
      = ( k1_enumset1 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('34',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','35'])).

thf('37',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( k3_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49 )
      = ( k2_enumset1 @ X46 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t54_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_tarski @ E @ F ) ) ) )).

thf('38',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k4_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X26 @ X27 @ X28 @ X29 ) @ ( k2_tarski @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t54_enumset1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X5 @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X1 @ X0 @ X1 @ X1 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('42',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X13 @ X12 @ X11 )
      = ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('43',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X8 @ X7 @ X9 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t104_enumset1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X1 @ X0 @ X2 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k4_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X26 @ X27 @ X28 @ X29 ) @ ( k2_tarski @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t54_enumset1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X3 @ X0 @ X2 @ X1 @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X5 @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X0 @ X1 @ X2 @ X2 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X43 @ X43 @ X44 @ X45 )
      = ( k1_enumset1 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('49',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k4_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X26 @ X27 @ X28 @ X29 ) @ ( k2_tarski @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t54_enumset1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X2 @ X2 @ X1 @ X0 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('51',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( k4_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 @ X54 )
      = ( k3_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X2 @ X1 @ X0 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X0 @ X1 @ X2 @ X2 @ X4 @ X3 )
      = ( k3_enumset1 @ X2 @ X1 @ X0 @ X4 @ X3 ) ) ),
    inference(demod,[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X0 @ X1 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['40','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('56',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X13 @ X12 @ X11 )
      = ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('57',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k4_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X26 @ X27 @ X28 @ X29 ) @ ( k2_tarski @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t54_enumset1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X3 @ X0 @ X1 @ X2 @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X5 @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X2 @ X0 @ X2 @ X1 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','12','13','14'])).

thf('61',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('66',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k2_enumset1 @ X22 @ X23 @ X24 @ X25 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X22 @ X23 @ X24 ) @ ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X43 @ X43 @ X44 @ X45 )
      = ( k1_enumset1 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X0 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['64','69'])).

thf('71',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k2_enumset1 @ X22 @ X23 @ X24 @ X25 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X22 @ X23 @ X24 ) @ ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k2_enumset1 @ X1 @ X0 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k2_enumset1 @ X17 @ X14 @ X16 @ X15 )
      = ( k2_enumset1 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t113_enumset1])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X1 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k2_enumset1 @ X17 @ X14 @ X16 @ X15 )
      = ( k2_enumset1 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t113_enumset1])).

thf('76',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k4_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X26 @ X27 @ X28 @ X29 ) @ ( k2_tarski @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t54_enumset1])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X0 @ X3 @ X1 @ X2 @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X5 @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X1 @ X0 @ X1 @ X2 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['74','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X2 @ X1 @ X0 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X1 @ X0 @ X1 @ X2 @ X4 @ X3 )
      = ( k3_enumset1 @ X2 @ X1 @ X0 @ X4 @ X3 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('82',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X8 @ X7 @ X9 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t104_enumset1])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X2 @ X0 @ X1 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k4_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X26 @ X27 @ X28 @ X29 ) @ ( k2_tarski @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t54_enumset1])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X2 @ X2 @ X0 @ X1 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( k4_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 @ X54 )
      = ( k3_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X2 @ X0 @ X1 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X1 @ X2 @ X0 @ X4 @ X3 )
      = ( k3_enumset1 @ X2 @ X0 @ X1 @ X4 @ X3 ) ) ),
    inference(demod,[status(thm)],['59','80','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','12','13','14'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k2_enumset1 @ X22 @ X23 @ X24 @ X25 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X22 @ X23 @ X24 ) @ ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( k3_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49 )
      = ( k2_enumset1 @ X46 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('97',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k2_enumset1 @ X17 @ X14 @ X16 @ X15 )
      = ( k2_enumset1 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t113_enumset1])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X0 @ X1 @ X3 ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X1 @ X2 @ X1 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['95','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','12','13','14'])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('102',plain,(
    ( k1_enumset1 @ sk_B @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['25','54','88','99','100','101'])).

thf('103',plain,(
    $false ),
    inference(simplify,[status(thm)],['102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.U2gZaf8dYD
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:32:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 48.76/48.97  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 48.76/48.97  % Solved by: fo/fo7.sh
% 48.76/48.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 48.76/48.97  % done 22412 iterations in 48.499s
% 48.76/48.97  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 48.76/48.97  % SZS output start Refutation
% 48.76/48.97  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 48.76/48.97  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 48.76/48.97  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 48.76/48.97  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 48.76/48.97  thf(sk_C_type, type, sk_C: $i).
% 48.76/48.97  thf(sk_B_type, type, sk_B: $i).
% 48.76/48.97  thf(sk_A_type, type, sk_A: $i).
% 48.76/48.97  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 48.76/48.97  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 48.76/48.97  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 48.76/48.97  thf(t137_enumset1, conjecture,
% 48.76/48.97    (![A:$i,B:$i,C:$i]:
% 48.76/48.97     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 48.76/48.97       ( k1_enumset1 @ A @ B @ C ) ))).
% 48.76/48.97  thf(zf_stmt_0, negated_conjecture,
% 48.76/48.97    (~( ![A:$i,B:$i,C:$i]:
% 48.76/48.97        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 48.76/48.97          ( k1_enumset1 @ A @ B @ C ) ) )),
% 48.76/48.97    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 48.76/48.97  thf('0', plain,
% 48.76/48.97      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 48.76/48.97         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 48.76/48.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 48.76/48.97  thf(t113_enumset1, axiom,
% 48.76/48.97    (![A:$i,B:$i,C:$i,D:$i]:
% 48.76/48.97     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ D @ C @ A ) ))).
% 48.76/48.97  thf('1', plain,
% 48.76/48.97      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X17 @ X14 @ X16 @ X15)
% 48.76/48.97           = (k2_enumset1 @ X14 @ X15 @ X16 @ X17))),
% 48.76/48.97      inference('cnf', [status(esa)], [t113_enumset1])).
% 48.76/48.97  thf(t71_enumset1, axiom,
% 48.76/48.97    (![A:$i,B:$i,C:$i]:
% 48.76/48.97     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 48.76/48.97  thf('2', plain,
% 48.76/48.97      (![X43 : $i, X44 : $i, X45 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X43 @ X43 @ X44 @ X45)
% 48.76/48.97           = (k1_enumset1 @ X43 @ X44 @ X45))),
% 48.76/48.97      inference('cnf', [status(esa)], [t71_enumset1])).
% 48.76/48.97  thf('3', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X2 @ X0 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 48.76/48.97      inference('sup+', [status(thm)], ['1', '2'])).
% 48.76/48.97  thf(t104_enumset1, axiom,
% 48.76/48.97    (![A:$i,B:$i,C:$i,D:$i]:
% 48.76/48.97     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ B @ D ) ))).
% 48.76/48.97  thf('4', plain,
% 48.76/48.97      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X6 @ X8 @ X7 @ X9) = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 48.76/48.97      inference('cnf', [status(esa)], [t104_enumset1])).
% 48.76/48.97  thf('5', plain,
% 48.76/48.97      (![X43 : $i, X44 : $i, X45 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X43 @ X43 @ X44 @ X45)
% 48.76/48.97           = (k1_enumset1 @ X43 @ X44 @ X45))),
% 48.76/48.97      inference('cnf', [status(esa)], [t71_enumset1])).
% 48.76/48.97  thf('6', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 48.76/48.97      inference('sup+', [status(thm)], ['4', '5'])).
% 48.76/48.97  thf('7', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i]:
% 48.76/48.97         ((k1_enumset1 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X1))),
% 48.76/48.97      inference('sup+', [status(thm)], ['3', '6'])).
% 48.76/48.97  thf(t46_enumset1, axiom,
% 48.76/48.97    (![A:$i,B:$i,C:$i,D:$i]:
% 48.76/48.97     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 48.76/48.97       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 48.76/48.97  thf('8', plain,
% 48.76/48.97      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X22 @ X23 @ X24 @ X25)
% 48.76/48.97           = (k2_xboole_0 @ (k1_enumset1 @ X22 @ X23 @ X24) @ (k1_tarski @ X25)))),
% 48.76/48.97      inference('cnf', [status(esa)], [t46_enumset1])).
% 48.76/48.97  thf('9', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X0 @ X1 @ X1 @ X2)
% 48.76/48.97           = (k2_xboole_0 @ (k1_enumset1 @ X1 @ X0 @ X0) @ (k1_tarski @ X2)))),
% 48.76/48.97      inference('sup+', [status(thm)], ['7', '8'])).
% 48.76/48.97  thf('10', plain,
% 48.76/48.97      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X17 @ X14 @ X16 @ X15)
% 48.76/48.97           = (k2_enumset1 @ X14 @ X15 @ X16 @ X17))),
% 48.76/48.97      inference('cnf', [status(esa)], [t113_enumset1])).
% 48.76/48.97  thf('11', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 48.76/48.97      inference('sup+', [status(thm)], ['4', '5'])).
% 48.76/48.97  thf('12', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 48.76/48.97      inference('sup+', [status(thm)], ['10', '11'])).
% 48.76/48.97  thf('13', plain,
% 48.76/48.97      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X22 @ X23 @ X24 @ X25)
% 48.76/48.97           = (k2_xboole_0 @ (k1_enumset1 @ X22 @ X23 @ X24) @ (k1_tarski @ X25)))),
% 48.76/48.97      inference('cnf', [status(esa)], [t46_enumset1])).
% 48.76/48.97  thf('14', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 48.76/48.97      inference('sup+', [status(thm)], ['10', '11'])).
% 48.76/48.97  thf('15', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.76/48.97         ((k1_enumset1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 48.76/48.97      inference('demod', [status(thm)], ['9', '12', '13', '14'])).
% 48.76/48.97  thf('16', plain,
% 48.76/48.97      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 48.76/48.97         != (k1_enumset1 @ sk_C @ sk_B @ sk_A))),
% 48.76/48.97      inference('demod', [status(thm)], ['0', '15'])).
% 48.76/48.97  thf('17', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.76/48.97         ((k1_enumset1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 48.76/48.97      inference('demod', [status(thm)], ['9', '12', '13', '14'])).
% 48.76/48.97  thf(t107_enumset1, axiom,
% 48.76/48.97    (![A:$i,B:$i,C:$i,D:$i]:
% 48.76/48.97     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ D @ C @ B ) ))).
% 48.76/48.97  thf('18', plain,
% 48.76/48.97      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X10 @ X13 @ X12 @ X11)
% 48.76/48.97           = (k2_enumset1 @ X10 @ X11 @ X12 @ X13))),
% 48.76/48.97      inference('cnf', [status(esa)], [t107_enumset1])).
% 48.76/48.97  thf('19', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 48.76/48.97      inference('sup+', [status(thm)], ['4', '5'])).
% 48.76/48.97  thf('20', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 48.76/48.97      inference('sup+', [status(thm)], ['18', '19'])).
% 48.76/48.97  thf('21', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 48.76/48.97      inference('sup+', [status(thm)], ['4', '5'])).
% 48.76/48.97  thf('22', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.76/48.97         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 48.76/48.97      inference('sup+', [status(thm)], ['20', '21'])).
% 48.76/48.97  thf('23', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.76/48.97         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 48.76/48.97      inference('sup+', [status(thm)], ['17', '22'])).
% 48.76/48.97  thf('24', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.76/48.97         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 48.76/48.97      inference('sup+', [status(thm)], ['20', '21'])).
% 48.76/48.97  thf('25', plain,
% 48.76/48.97      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 48.76/48.97         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 48.76/48.97      inference('demod', [status(thm)], ['16', '23', '24'])).
% 48.76/48.97  thf(t72_enumset1, axiom,
% 48.76/48.97    (![A:$i,B:$i,C:$i,D:$i]:
% 48.76/48.97     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 48.76/48.97  thf('26', plain,
% 48.76/48.97      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 48.76/48.97         ((k3_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49)
% 48.76/48.97           = (k2_enumset1 @ X46 @ X47 @ X48 @ X49))),
% 48.76/48.97      inference('cnf', [status(esa)], [t72_enumset1])).
% 48.76/48.97  thf('27', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 48.76/48.97      inference('sup+', [status(thm)], ['4', '5'])).
% 48.76/48.97  thf('28', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.76/48.97         ((k3_enumset1 @ X1 @ X1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 48.76/48.97      inference('sup+', [status(thm)], ['26', '27'])).
% 48.76/48.97  thf('29', plain,
% 48.76/48.97      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X10 @ X13 @ X12 @ X11)
% 48.76/48.97           = (k2_enumset1 @ X10 @ X11 @ X12 @ X13))),
% 48.76/48.97      inference('cnf', [status(esa)], [t107_enumset1])).
% 48.76/48.97  thf('30', plain,
% 48.76/48.97      (![X43 : $i, X44 : $i, X45 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X43 @ X43 @ X44 @ X45)
% 48.76/48.97           = (k1_enumset1 @ X43 @ X44 @ X45))),
% 48.76/48.97      inference('cnf', [status(esa)], [t71_enumset1])).
% 48.76/48.97  thf('31', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X0 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 48.76/48.97      inference('sup+', [status(thm)], ['29', '30'])).
% 48.76/48.97  thf('32', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 48.76/48.97      inference('sup+', [status(thm)], ['4', '5'])).
% 48.76/48.97  thf('33', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i]:
% 48.76/48.97         ((k1_enumset1 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X1))),
% 48.76/48.97      inference('sup+', [status(thm)], ['31', '32'])).
% 48.76/48.97  thf(t70_enumset1, axiom,
% 48.76/48.97    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 48.76/48.97  thf('34', plain,
% 48.76/48.97      (![X41 : $i, X42 : $i]:
% 48.76/48.97         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 48.76/48.97      inference('cnf', [status(esa)], [t70_enumset1])).
% 48.76/48.97  thf('35', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i]:
% 48.76/48.97         ((k1_enumset1 @ X0 @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 48.76/48.97      inference('sup+', [status(thm)], ['33', '34'])).
% 48.76/48.97  thf('36', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i]:
% 48.76/48.97         ((k3_enumset1 @ X0 @ X0 @ X1 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 48.76/48.97      inference('sup+', [status(thm)], ['28', '35'])).
% 48.76/48.97  thf('37', plain,
% 48.76/48.97      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 48.76/48.97         ((k3_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49)
% 48.76/48.97           = (k2_enumset1 @ X46 @ X47 @ X48 @ X49))),
% 48.76/48.97      inference('cnf', [status(esa)], [t72_enumset1])).
% 48.76/48.97  thf(t54_enumset1, axiom,
% 48.76/48.97    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 48.76/48.97     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 48.76/48.97       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_tarski @ E @ F ) ) ))).
% 48.76/48.97  thf('38', plain,
% 48.76/48.97      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 48.76/48.97         ((k4_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31)
% 48.76/48.97           = (k2_xboole_0 @ (k2_enumset1 @ X26 @ X27 @ X28 @ X29) @ 
% 48.76/48.97              (k2_tarski @ X30 @ X31)))),
% 48.76/48.97      inference('cnf', [status(esa)], [t54_enumset1])).
% 48.76/48.97  thf('39', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 48.76/48.97         ((k4_enumset1 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4)
% 48.76/48.97           = (k2_xboole_0 @ (k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0) @ 
% 48.76/48.97              (k2_tarski @ X5 @ X4)))),
% 48.76/48.97      inference('sup+', [status(thm)], ['37', '38'])).
% 48.76/48.97  thf('40', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 48.76/48.97         ((k4_enumset1 @ X1 @ X0 @ X1 @ X1 @ X3 @ X2)
% 48.76/48.97           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 48.76/48.97      inference('sup+', [status(thm)], ['36', '39'])).
% 48.76/48.97  thf('41', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 48.76/48.97      inference('sup+', [status(thm)], ['10', '11'])).
% 48.76/48.97  thf('42', plain,
% 48.76/48.97      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X10 @ X13 @ X12 @ X11)
% 48.76/48.97           = (k2_enumset1 @ X10 @ X11 @ X12 @ X13))),
% 48.76/48.97      inference('cnf', [status(esa)], [t107_enumset1])).
% 48.76/48.97  thf('43', plain,
% 48.76/48.97      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X6 @ X8 @ X7 @ X9) = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 48.76/48.97      inference('cnf', [status(esa)], [t104_enumset1])).
% 48.76/48.97  thf('44', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X3 @ X1 @ X0 @ X2) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 48.76/48.97      inference('sup+', [status(thm)], ['42', '43'])).
% 48.76/48.97  thf('45', plain,
% 48.76/48.97      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 48.76/48.97         ((k4_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31)
% 48.76/48.97           = (k2_xboole_0 @ (k2_enumset1 @ X26 @ X27 @ X28 @ X29) @ 
% 48.76/48.97              (k2_tarski @ X30 @ X31)))),
% 48.76/48.97      inference('cnf', [status(esa)], [t54_enumset1])).
% 48.76/48.97  thf('46', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 48.76/48.97         ((k4_enumset1 @ X3 @ X0 @ X2 @ X1 @ X5 @ X4)
% 48.76/48.97           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 48.76/48.97              (k2_tarski @ X5 @ X4)))),
% 48.76/48.97      inference('sup+', [status(thm)], ['44', '45'])).
% 48.76/48.97  thf('47', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 48.76/48.97         ((k4_enumset1 @ X0 @ X1 @ X2 @ X2 @ X4 @ X3)
% 48.76/48.97           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 48.76/48.97              (k2_tarski @ X4 @ X3)))),
% 48.76/48.97      inference('sup+', [status(thm)], ['41', '46'])).
% 48.76/48.97  thf('48', plain,
% 48.76/48.97      (![X43 : $i, X44 : $i, X45 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X43 @ X43 @ X44 @ X45)
% 48.76/48.97           = (k1_enumset1 @ X43 @ X44 @ X45))),
% 48.76/48.97      inference('cnf', [status(esa)], [t71_enumset1])).
% 48.76/48.97  thf('49', plain,
% 48.76/48.97      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 48.76/48.97         ((k4_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31)
% 48.76/48.97           = (k2_xboole_0 @ (k2_enumset1 @ X26 @ X27 @ X28 @ X29) @ 
% 48.76/48.97              (k2_tarski @ X30 @ X31)))),
% 48.76/48.97      inference('cnf', [status(esa)], [t54_enumset1])).
% 48.76/48.97  thf('50', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 48.76/48.97         ((k4_enumset1 @ X2 @ X2 @ X1 @ X0 @ X4 @ X3)
% 48.76/48.97           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 48.76/48.97              (k2_tarski @ X4 @ X3)))),
% 48.76/48.97      inference('sup+', [status(thm)], ['48', '49'])).
% 48.76/48.97  thf(t73_enumset1, axiom,
% 48.76/48.97    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 48.76/48.97     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 48.76/48.97       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 48.76/48.97  thf('51', plain,
% 48.76/48.97      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 48.76/48.97         ((k4_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 @ X54)
% 48.76/48.97           = (k3_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54))),
% 48.76/48.97      inference('cnf', [status(esa)], [t73_enumset1])).
% 48.76/48.97  thf('52', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 48.76/48.97         ((k3_enumset1 @ X2 @ X1 @ X0 @ X4 @ X3)
% 48.76/48.97           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 48.76/48.97              (k2_tarski @ X4 @ X3)))),
% 48.76/48.97      inference('demod', [status(thm)], ['50', '51'])).
% 48.76/48.97  thf('53', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 48.76/48.97         ((k4_enumset1 @ X0 @ X1 @ X2 @ X2 @ X4 @ X3)
% 48.76/48.97           = (k3_enumset1 @ X2 @ X1 @ X0 @ X4 @ X3))),
% 48.76/48.97      inference('demod', [status(thm)], ['47', '52'])).
% 48.76/48.97  thf('54', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 48.76/48.97         ((k3_enumset1 @ X1 @ X0 @ X1 @ X3 @ X2)
% 48.76/48.97           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 48.76/48.97      inference('demod', [status(thm)], ['40', '53'])).
% 48.76/48.97  thf('55', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 48.76/48.97      inference('sup+', [status(thm)], ['4', '5'])).
% 48.76/48.97  thf('56', plain,
% 48.76/48.97      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X10 @ X13 @ X12 @ X11)
% 48.76/48.97           = (k2_enumset1 @ X10 @ X11 @ X12 @ X13))),
% 48.76/48.97      inference('cnf', [status(esa)], [t107_enumset1])).
% 48.76/48.97  thf('57', plain,
% 48.76/48.97      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 48.76/48.97         ((k4_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31)
% 48.76/48.97           = (k2_xboole_0 @ (k2_enumset1 @ X26 @ X27 @ X28 @ X29) @ 
% 48.76/48.97              (k2_tarski @ X30 @ X31)))),
% 48.76/48.97      inference('cnf', [status(esa)], [t54_enumset1])).
% 48.76/48.97  thf('58', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 48.76/48.97         ((k4_enumset1 @ X3 @ X0 @ X1 @ X2 @ X5 @ X4)
% 48.76/48.97           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 48.76/48.97              (k2_tarski @ X5 @ X4)))),
% 48.76/48.97      inference('sup+', [status(thm)], ['56', '57'])).
% 48.76/48.97  thf('59', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 48.76/48.97         ((k4_enumset1 @ X2 @ X0 @ X2 @ X1 @ X4 @ X3)
% 48.76/48.97           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 48.76/48.97              (k2_tarski @ X4 @ X3)))),
% 48.76/48.97      inference('sup+', [status(thm)], ['55', '58'])).
% 48.76/48.97  thf('60', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.76/48.97         ((k1_enumset1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 48.76/48.97      inference('demod', [status(thm)], ['9', '12', '13', '14'])).
% 48.76/48.97  thf('61', plain,
% 48.76/48.97      (![X41 : $i, X42 : $i]:
% 48.76/48.97         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 48.76/48.97      inference('cnf', [status(esa)], [t70_enumset1])).
% 48.76/48.97  thf('62', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i]:
% 48.76/48.97         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 48.76/48.97      inference('sup+', [status(thm)], ['60', '61'])).
% 48.76/48.97  thf('63', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i]:
% 48.76/48.97         ((k1_enumset1 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X1))),
% 48.76/48.97      inference('sup+', [status(thm)], ['3', '6'])).
% 48.76/48.97  thf('64', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i]:
% 48.76/48.97         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X0))),
% 48.76/48.97      inference('sup+', [status(thm)], ['62', '63'])).
% 48.76/48.97  thf('65', plain,
% 48.76/48.97      (![X41 : $i, X42 : $i]:
% 48.76/48.97         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 48.76/48.97      inference('cnf', [status(esa)], [t70_enumset1])).
% 48.76/48.97  thf('66', plain,
% 48.76/48.97      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X22 @ X23 @ X24 @ X25)
% 48.76/48.97           = (k2_xboole_0 @ (k1_enumset1 @ X22 @ X23 @ X24) @ (k1_tarski @ X25)))),
% 48.76/48.97      inference('cnf', [status(esa)], [t46_enumset1])).
% 48.76/48.97  thf('67', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 48.76/48.97           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 48.76/48.97      inference('sup+', [status(thm)], ['65', '66'])).
% 48.76/48.97  thf('68', plain,
% 48.76/48.97      (![X43 : $i, X44 : $i, X45 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X43 @ X43 @ X44 @ X45)
% 48.76/48.97           = (k1_enumset1 @ X43 @ X44 @ X45))),
% 48.76/48.97      inference('cnf', [status(esa)], [t71_enumset1])).
% 48.76/48.97  thf('69', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.76/48.97         ((k1_enumset1 @ X1 @ X0 @ X2)
% 48.76/48.97           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 48.76/48.97      inference('demod', [status(thm)], ['67', '68'])).
% 48.76/48.97  thf('70', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.76/48.97         ((k1_enumset1 @ X1 @ X0 @ X2)
% 48.76/48.97           = (k2_xboole_0 @ (k1_enumset1 @ X1 @ X0 @ X0) @ (k1_tarski @ X2)))),
% 48.76/48.97      inference('sup+', [status(thm)], ['64', '69'])).
% 48.76/48.97  thf('71', plain,
% 48.76/48.97      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X22 @ X23 @ X24 @ X25)
% 48.76/48.97           = (k2_xboole_0 @ (k1_enumset1 @ X22 @ X23 @ X24) @ (k1_tarski @ X25)))),
% 48.76/48.97      inference('cnf', [status(esa)], [t46_enumset1])).
% 48.76/48.97  thf('72', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.76/48.97         ((k1_enumset1 @ X1 @ X0 @ X2) = (k2_enumset1 @ X1 @ X0 @ X0 @ X2))),
% 48.76/48.97      inference('demod', [status(thm)], ['70', '71'])).
% 48.76/48.97  thf('73', plain,
% 48.76/48.97      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X17 @ X14 @ X16 @ X15)
% 48.76/48.97           = (k2_enumset1 @ X14 @ X15 @ X16 @ X17))),
% 48.76/48.97      inference('cnf', [status(esa)], [t113_enumset1])).
% 48.76/48.97  thf('74', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X0 @ X2 @ X1 @ X1) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 48.76/48.97      inference('sup+', [status(thm)], ['72', '73'])).
% 48.76/48.97  thf('75', plain,
% 48.76/48.97      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X17 @ X14 @ X16 @ X15)
% 48.76/48.97           = (k2_enumset1 @ X14 @ X15 @ X16 @ X17))),
% 48.76/48.97      inference('cnf', [status(esa)], [t113_enumset1])).
% 48.76/48.97  thf('76', plain,
% 48.76/48.97      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 48.76/48.97         ((k4_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31)
% 48.76/48.97           = (k2_xboole_0 @ (k2_enumset1 @ X26 @ X27 @ X28 @ X29) @ 
% 48.76/48.97              (k2_tarski @ X30 @ X31)))),
% 48.76/48.97      inference('cnf', [status(esa)], [t54_enumset1])).
% 48.76/48.97  thf('77', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 48.76/48.97         ((k4_enumset1 @ X0 @ X3 @ X1 @ X2 @ X5 @ X4)
% 48.76/48.97           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 48.76/48.97              (k2_tarski @ X5 @ X4)))),
% 48.76/48.97      inference('sup+', [status(thm)], ['75', '76'])).
% 48.76/48.97  thf('78', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 48.76/48.97         ((k4_enumset1 @ X1 @ X0 @ X1 @ X2 @ X4 @ X3)
% 48.76/48.97           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 48.76/48.97              (k2_tarski @ X4 @ X3)))),
% 48.76/48.97      inference('sup+', [status(thm)], ['74', '77'])).
% 48.76/48.97  thf('79', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 48.76/48.97         ((k3_enumset1 @ X2 @ X1 @ X0 @ X4 @ X3)
% 48.76/48.97           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 48.76/48.97              (k2_tarski @ X4 @ X3)))),
% 48.76/48.97      inference('demod', [status(thm)], ['50', '51'])).
% 48.76/48.97  thf('80', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 48.76/48.97         ((k4_enumset1 @ X1 @ X0 @ X1 @ X2 @ X4 @ X3)
% 48.76/48.97           = (k3_enumset1 @ X2 @ X1 @ X0 @ X4 @ X3))),
% 48.76/48.97      inference('demod', [status(thm)], ['78', '79'])).
% 48.76/48.97  thf('81', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 48.76/48.97      inference('sup+', [status(thm)], ['18', '19'])).
% 48.76/48.97  thf('82', plain,
% 48.76/48.97      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X6 @ X8 @ X7 @ X9) = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 48.76/48.97      inference('cnf', [status(esa)], [t104_enumset1])).
% 48.76/48.97  thf('83', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X2 @ X2 @ X0 @ X1) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 48.76/48.97      inference('sup+', [status(thm)], ['81', '82'])).
% 48.76/48.97  thf('84', plain,
% 48.76/48.97      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 48.76/48.97         ((k4_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31)
% 48.76/48.97           = (k2_xboole_0 @ (k2_enumset1 @ X26 @ X27 @ X28 @ X29) @ 
% 48.76/48.97              (k2_tarski @ X30 @ X31)))),
% 48.76/48.97      inference('cnf', [status(esa)], [t54_enumset1])).
% 48.76/48.97  thf('85', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 48.76/48.97         ((k4_enumset1 @ X2 @ X2 @ X0 @ X1 @ X4 @ X3)
% 48.76/48.97           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 48.76/48.97              (k2_tarski @ X4 @ X3)))),
% 48.76/48.97      inference('sup+', [status(thm)], ['83', '84'])).
% 48.76/48.97  thf('86', plain,
% 48.76/48.97      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 48.76/48.97         ((k4_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 @ X54)
% 48.76/48.97           = (k3_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54))),
% 48.76/48.97      inference('cnf', [status(esa)], [t73_enumset1])).
% 48.76/48.97  thf('87', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 48.76/48.97         ((k3_enumset1 @ X2 @ X0 @ X1 @ X4 @ X3)
% 48.76/48.97           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 48.76/48.97              (k2_tarski @ X4 @ X3)))),
% 48.76/48.97      inference('demod', [status(thm)], ['85', '86'])).
% 48.76/48.97  thf('88', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 48.76/48.97         ((k3_enumset1 @ X1 @ X2 @ X0 @ X4 @ X3)
% 48.76/48.97           = (k3_enumset1 @ X2 @ X0 @ X1 @ X4 @ X3))),
% 48.76/48.97      inference('demod', [status(thm)], ['59', '80', '87'])).
% 48.76/48.97  thf('89', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i]:
% 48.76/48.97         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X0))),
% 48.76/48.97      inference('sup+', [status(thm)], ['62', '63'])).
% 48.76/48.97  thf('90', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.76/48.97         ((k1_enumset1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 48.76/48.97      inference('demod', [status(thm)], ['9', '12', '13', '14'])).
% 48.76/48.97  thf('91', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i]:
% 48.76/48.97         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X0 @ X0 @ X1))),
% 48.76/48.97      inference('sup+', [status(thm)], ['89', '90'])).
% 48.76/48.97  thf('92', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.76/48.97         ((k1_enumset1 @ X1 @ X0 @ X2)
% 48.76/48.97           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 48.76/48.97      inference('demod', [status(thm)], ['67', '68'])).
% 48.76/48.97  thf('93', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.76/48.97         ((k1_enumset1 @ X0 @ X1 @ X2)
% 48.76/48.97           = (k2_xboole_0 @ (k1_enumset1 @ X1 @ X1 @ X0) @ (k1_tarski @ X2)))),
% 48.76/48.97      inference('sup+', [status(thm)], ['91', '92'])).
% 48.76/48.97  thf('94', plain,
% 48.76/48.97      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X22 @ X23 @ X24 @ X25)
% 48.76/48.97           = (k2_xboole_0 @ (k1_enumset1 @ X22 @ X23 @ X24) @ (k1_tarski @ X25)))),
% 48.76/48.97      inference('cnf', [status(esa)], [t46_enumset1])).
% 48.76/48.97  thf('95', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.76/48.97         ((k1_enumset1 @ X0 @ X1 @ X2) = (k2_enumset1 @ X1 @ X1 @ X0 @ X2))),
% 48.76/48.97      inference('demod', [status(thm)], ['93', '94'])).
% 48.76/48.97  thf('96', plain,
% 48.76/48.97      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 48.76/48.97         ((k3_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49)
% 48.76/48.97           = (k2_enumset1 @ X46 @ X47 @ X48 @ X49))),
% 48.76/48.97      inference('cnf', [status(esa)], [t72_enumset1])).
% 48.76/48.97  thf('97', plain,
% 48.76/48.97      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 48.76/48.97         ((k2_enumset1 @ X17 @ X14 @ X16 @ X15)
% 48.76/48.97           = (k2_enumset1 @ X14 @ X15 @ X16 @ X17))),
% 48.76/48.97      inference('cnf', [status(esa)], [t113_enumset1])).
% 48.76/48.97  thf('98', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 48.76/48.97         ((k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0)
% 48.76/48.97           = (k2_enumset1 @ X2 @ X0 @ X1 @ X3))),
% 48.76/48.97      inference('sup+', [status(thm)], ['96', '97'])).
% 48.76/48.97  thf('99', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.76/48.97         ((k3_enumset1 @ X0 @ X0 @ X1 @ X2 @ X1) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 48.76/48.97      inference('sup+', [status(thm)], ['95', '98'])).
% 48.76/48.97  thf('100', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.76/48.97         ((k1_enumset1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 48.76/48.97      inference('demod', [status(thm)], ['9', '12', '13', '14'])).
% 48.76/48.97  thf('101', plain,
% 48.76/48.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 48.76/48.97         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 48.76/48.97      inference('sup+', [status(thm)], ['20', '21'])).
% 48.76/48.97  thf('102', plain,
% 48.76/48.97      (((k1_enumset1 @ sk_B @ sk_C @ sk_A)
% 48.76/48.97         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 48.76/48.97      inference('demod', [status(thm)], ['25', '54', '88', '99', '100', '101'])).
% 48.76/48.97  thf('103', plain, ($false), inference('simplify', [status(thm)], ['102'])).
% 48.76/48.97  
% 48.76/48.97  % SZS output end Refutation
% 48.76/48.97  
% 48.76/48.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

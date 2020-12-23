%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BAupTZ0I9D

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:39 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 247 expanded)
%              Number of leaves         :   17 (  93 expanded)
%              Depth                    :   12
%              Number of atoms          :  748 (2530 expanded)
%              Number of equality atoms :   71 ( 237 expanded)
%              Maximal formula depth    :   12 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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

thf(t111_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ C @ D @ A ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k2_enumset1 @ X14 @ X11 @ X12 @ X13 )
      = ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t111_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_enumset1 @ X22 @ X22 @ X23 @ X24 )
      = ( k1_enumset1 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t107_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ D @ C @ B ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k2_enumset1 @ X7 @ X10 @ X9 @ X8 )
      = ( k2_enumset1 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('5',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_enumset1 @ X22 @ X22 @ X23 @ X24 )
      = ( k1_enumset1 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X15 @ X16 @ X17 ) @ ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X0 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('11',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X15 @ X16 @ X17 ) @ ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('14',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_tarski @ sk_C @ sk_A ) )
 != ( k1_enumset1 @ sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['0','13'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X20 @ X20 @ X21 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(l57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X3 @ X4 ) @ ( k2_tarski @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('18',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_enumset1 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('19',plain,(
    ( k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['14','17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('21',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k2_enumset1 @ X14 @ X11 @ X12 @ X13 )
      = ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t111_enumset1])).

thf('22',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_enumset1 @ X22 @ X22 @ X23 @ X24 )
      = ( k1_enumset1 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('28',plain,(
    ( k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['19','26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('30',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_enumset1 @ X22 @ X22 @ X23 @ X24 )
      = ( k1_enumset1 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X15 @ X16 @ X17 ) @ ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X15 @ X16 @ X17 ) @ ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X1 @ X2 )
      = ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_enumset1 @ X22 @ X22 @ X23 @ X24 )
      = ( k1_enumset1 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X1 @ X2 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k2_enumset1 @ X14 @ X11 @ X12 @ X13 )
      = ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t111_enumset1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('41',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X20 @ X20 @ X21 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('46',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X20 @ X20 @ X21 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X1 )
      = ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X15 @ X16 @ X17 ) @ ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X0 @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k2_enumset1 @ X14 @ X11 @ X12 @ X13 )
      = ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t111_enumset1])).

thf('52',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k2_enumset1 @ X7 @ X10 @ X9 @ X8 )
      = ( k2_enumset1 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X0 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X15 @ X16 @ X17 ) @ ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X1 @ X2 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference(demod,[status(thm)],['50','55','56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('61',plain,(
    ( k1_enumset1 @ sk_B @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['28','39','58','59','60'])).

thf('62',plain,(
    $false ),
    inference(simplify,[status(thm)],['61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BAupTZ0I9D
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:13:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.68/0.86  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.68/0.86  % Solved by: fo/fo7.sh
% 0.68/0.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.86  % done 844 iterations in 0.405s
% 0.68/0.86  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.68/0.86  % SZS output start Refutation
% 0.68/0.86  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.68/0.86  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.86  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.68/0.86  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.68/0.86  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.86  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.68/0.86  thf(sk_C_type, type, sk_C: $i).
% 0.68/0.86  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.68/0.86  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.68/0.86  thf(t137_enumset1, conjecture,
% 0.68/0.86    (![A:$i,B:$i,C:$i]:
% 0.68/0.86     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.68/0.86       ( k1_enumset1 @ A @ B @ C ) ))).
% 0.68/0.86  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.86    (~( ![A:$i,B:$i,C:$i]:
% 0.68/0.86        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.68/0.86          ( k1_enumset1 @ A @ B @ C ) ) )),
% 0.68/0.86    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 0.68/0.86  thf('0', plain,
% 0.68/0.86      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 0.68/0.86         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.68/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.86  thf(t111_enumset1, axiom,
% 0.68/0.86    (![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.86     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ C @ D @ A ) ))).
% 0.68/0.86  thf('1', plain,
% 0.68/0.86      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X14 @ X11 @ X12 @ X13)
% 0.68/0.86           = (k2_enumset1 @ X11 @ X12 @ X13 @ X14))),
% 0.68/0.86      inference('cnf', [status(esa)], [t111_enumset1])).
% 0.68/0.86  thf(t71_enumset1, axiom,
% 0.68/0.86    (![A:$i,B:$i,C:$i]:
% 0.68/0.86     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.68/0.86  thf('2', plain,
% 0.68/0.86      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X22 @ X22 @ X23 @ X24)
% 0.68/0.86           = (k1_enumset1 @ X22 @ X23 @ X24))),
% 0.68/0.86      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.68/0.86  thf('3', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 0.68/0.86      inference('sup+', [status(thm)], ['1', '2'])).
% 0.68/0.86  thf(t107_enumset1, axiom,
% 0.68/0.86    (![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.86     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ D @ C @ B ) ))).
% 0.68/0.86  thf('4', plain,
% 0.68/0.86      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X7 @ X10 @ X9 @ X8)
% 0.68/0.86           = (k2_enumset1 @ X7 @ X8 @ X9 @ X10))),
% 0.68/0.86      inference('cnf', [status(esa)], [t107_enumset1])).
% 0.68/0.86  thf('5', plain,
% 0.68/0.86      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X22 @ X22 @ X23 @ X24)
% 0.68/0.86           = (k1_enumset1 @ X22 @ X23 @ X24))),
% 0.68/0.86      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.68/0.86  thf('6', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X0 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.68/0.86      inference('sup+', [status(thm)], ['4', '5'])).
% 0.68/0.86  thf('7', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]:
% 0.68/0.86         ((k1_enumset1 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X1))),
% 0.68/0.86      inference('sup+', [status(thm)], ['3', '6'])).
% 0.68/0.86  thf(t46_enumset1, axiom,
% 0.68/0.86    (![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.86     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.68/0.86       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.68/0.86  thf('8', plain,
% 0.68/0.86      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X15 @ X16 @ X17 @ X18)
% 0.68/0.86           = (k2_xboole_0 @ (k1_enumset1 @ X15 @ X16 @ X17) @ (k1_tarski @ X18)))),
% 0.68/0.86      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.68/0.86  thf('9', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X0 @ X1 @ X1 @ X2)
% 0.68/0.86           = (k2_xboole_0 @ (k1_enumset1 @ X1 @ X0 @ X0) @ (k1_tarski @ X2)))),
% 0.68/0.86      inference('sup+', [status(thm)], ['7', '8'])).
% 0.68/0.86  thf('10', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 0.68/0.86      inference('sup+', [status(thm)], ['1', '2'])).
% 0.68/0.86  thf('11', plain,
% 0.68/0.86      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X15 @ X16 @ X17 @ X18)
% 0.68/0.86           = (k2_xboole_0 @ (k1_enumset1 @ X15 @ X16 @ X17) @ (k1_tarski @ X18)))),
% 0.68/0.86      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.68/0.86  thf('12', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 0.68/0.86      inference('sup+', [status(thm)], ['1', '2'])).
% 0.68/0.86  thf('13', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.86         ((k1_enumset1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 0.68/0.86      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.68/0.86  thf('14', plain,
% 0.68/0.86      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 0.68/0.86         != (k1_enumset1 @ sk_C @ sk_B @ sk_A))),
% 0.68/0.86      inference('demod', [status(thm)], ['0', '13'])).
% 0.68/0.86  thf(t70_enumset1, axiom,
% 0.68/0.86    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.68/0.86  thf('15', plain,
% 0.68/0.86      (![X20 : $i, X21 : $i]:
% 0.68/0.86         ((k1_enumset1 @ X20 @ X20 @ X21) = (k2_tarski @ X20 @ X21))),
% 0.68/0.86      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.68/0.86  thf(l57_enumset1, axiom,
% 0.68/0.86    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.68/0.86     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.68/0.86       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ))).
% 0.68/0.86  thf('16', plain,
% 0.68/0.86      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.68/0.86         ((k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6)
% 0.68/0.86           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X3 @ X4) @ 
% 0.68/0.86              (k2_tarski @ X5 @ X6)))),
% 0.68/0.86      inference('cnf', [status(esa)], [l57_enumset1])).
% 0.68/0.86  thf('17', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.86         ((k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2)
% 0.68/0.86           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 0.68/0.86      inference('sup+', [status(thm)], ['15', '16'])).
% 0.68/0.86  thf(t72_enumset1, axiom,
% 0.68/0.86    (![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.86     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.68/0.86  thf('18', plain,
% 0.68/0.86      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.68/0.86         ((k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28)
% 0.68/0.86           = (k2_enumset1 @ X25 @ X26 @ X27 @ X28))),
% 0.68/0.86      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.68/0.86  thf('19', plain,
% 0.68/0.86      (((k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A)
% 0.68/0.86         != (k1_enumset1 @ sk_C @ sk_B @ sk_A))),
% 0.68/0.86      inference('demod', [status(thm)], ['14', '17', '18'])).
% 0.68/0.86  thf('20', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.86         ((k1_enumset1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 0.68/0.86      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.68/0.86  thf('21', plain,
% 0.68/0.86      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X14 @ X11 @ X12 @ X13)
% 0.68/0.86           = (k2_enumset1 @ X11 @ X12 @ X13 @ X14))),
% 0.68/0.86      inference('cnf', [status(esa)], [t111_enumset1])).
% 0.68/0.86  thf('22', plain,
% 0.68/0.86      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X22 @ X22 @ X23 @ X24)
% 0.68/0.86           = (k1_enumset1 @ X22 @ X23 @ X24))),
% 0.68/0.86      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.68/0.86  thf('23', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X0 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 0.68/0.86      inference('sup+', [status(thm)], ['21', '22'])).
% 0.68/0.86  thf('24', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X0 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.68/0.86      inference('sup+', [status(thm)], ['4', '5'])).
% 0.68/0.86  thf('25', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.86         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 0.68/0.86      inference('sup+', [status(thm)], ['23', '24'])).
% 0.68/0.86  thf('26', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.86         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 0.68/0.86      inference('sup+', [status(thm)], ['20', '25'])).
% 0.68/0.86  thf('27', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.86         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 0.68/0.86      inference('sup+', [status(thm)], ['23', '24'])).
% 0.68/0.86  thf('28', plain,
% 0.68/0.86      (((k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A)
% 0.68/0.86         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 0.68/0.86      inference('demod', [status(thm)], ['19', '26', '27'])).
% 0.68/0.86  thf('29', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 0.68/0.86      inference('sup+', [status(thm)], ['1', '2'])).
% 0.68/0.86  thf('30', plain,
% 0.68/0.86      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X22 @ X22 @ X23 @ X24)
% 0.68/0.86           = (k1_enumset1 @ X22 @ X23 @ X24))),
% 0.68/0.86      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.68/0.86  thf('31', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]:
% 0.68/0.86         ((k1_enumset1 @ X0 @ X1 @ X0) = (k1_enumset1 @ X0 @ X0 @ X1))),
% 0.68/0.86      inference('sup+', [status(thm)], ['29', '30'])).
% 0.68/0.86  thf('32', plain,
% 0.68/0.86      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X15 @ X16 @ X17 @ X18)
% 0.68/0.86           = (k2_xboole_0 @ (k1_enumset1 @ X15 @ X16 @ X17) @ (k1_tarski @ X18)))),
% 0.68/0.86      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.68/0.86  thf('33', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X1 @ X0 @ X1 @ X2)
% 0.68/0.86           = (k2_xboole_0 @ (k1_enumset1 @ X1 @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.68/0.86      inference('sup+', [status(thm)], ['31', '32'])).
% 0.68/0.86  thf('34', plain,
% 0.68/0.86      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X15 @ X16 @ X17 @ X18)
% 0.68/0.86           = (k2_xboole_0 @ (k1_enumset1 @ X15 @ X16 @ X17) @ (k1_tarski @ X18)))),
% 0.68/0.86      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.68/0.86  thf('35', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X1 @ X0 @ X1 @ X2) = (k2_enumset1 @ X1 @ X1 @ X0 @ X2))),
% 0.68/0.86      inference('demod', [status(thm)], ['33', '34'])).
% 0.68/0.86  thf('36', plain,
% 0.68/0.86      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X22 @ X22 @ X23 @ X24)
% 0.68/0.86           = (k1_enumset1 @ X22 @ X23 @ X24))),
% 0.68/0.86      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.68/0.86  thf('37', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X1 @ X0 @ X1 @ X2) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 0.68/0.86      inference('demod', [status(thm)], ['35', '36'])).
% 0.68/0.86  thf('38', plain,
% 0.68/0.86      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X14 @ X11 @ X12 @ X13)
% 0.68/0.86           = (k2_enumset1 @ X11 @ X12 @ X13 @ X14))),
% 0.68/0.86      inference('cnf', [status(esa)], [t111_enumset1])).
% 0.68/0.86  thf('39', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X0 @ X2 @ X1 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.68/0.86      inference('sup+', [status(thm)], ['37', '38'])).
% 0.68/0.86  thf('40', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.86         ((k1_enumset1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 0.68/0.86      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.68/0.86  thf('41', plain,
% 0.68/0.86      (![X20 : $i, X21 : $i]:
% 0.68/0.86         ((k1_enumset1 @ X20 @ X20 @ X21) = (k2_tarski @ X20 @ X21))),
% 0.68/0.86      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.68/0.86  thf('42', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]:
% 0.68/0.86         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.68/0.86      inference('sup+', [status(thm)], ['40', '41'])).
% 0.68/0.86  thf('43', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]:
% 0.68/0.86         ((k1_enumset1 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X1))),
% 0.68/0.86      inference('sup+', [status(thm)], ['3', '6'])).
% 0.68/0.86  thf('44', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]:
% 0.68/0.86         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X0))),
% 0.68/0.86      inference('sup+', [status(thm)], ['42', '43'])).
% 0.68/0.86  thf('45', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]:
% 0.68/0.86         ((k1_enumset1 @ X0 @ X1 @ X0) = (k1_enumset1 @ X0 @ X0 @ X1))),
% 0.68/0.86      inference('sup+', [status(thm)], ['29', '30'])).
% 0.68/0.86  thf('46', plain,
% 0.68/0.86      (![X20 : $i, X21 : $i]:
% 0.68/0.86         ((k1_enumset1 @ X20 @ X20 @ X21) = (k2_tarski @ X20 @ X21))),
% 0.68/0.86      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.68/0.86  thf('47', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]:
% 0.68/0.86         ((k1_enumset1 @ X0 @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.68/0.86      inference('sup+', [status(thm)], ['45', '46'])).
% 0.68/0.86  thf('48', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i]:
% 0.68/0.86         ((k1_enumset1 @ X1 @ X0 @ X1) = (k1_enumset1 @ X1 @ X0 @ X0))),
% 0.68/0.86      inference('sup+', [status(thm)], ['44', '47'])).
% 0.68/0.86  thf('49', plain,
% 0.68/0.86      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X15 @ X16 @ X17 @ X18)
% 0.68/0.86           = (k2_xboole_0 @ (k1_enumset1 @ X15 @ X16 @ X17) @ (k1_tarski @ X18)))),
% 0.68/0.86      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.68/0.86  thf('50', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X0 @ X1 @ X1 @ X2)
% 0.68/0.86           = (k2_xboole_0 @ (k1_enumset1 @ X0 @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.68/0.86      inference('sup+', [status(thm)], ['48', '49'])).
% 0.68/0.86  thf('51', plain,
% 0.68/0.86      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X14 @ X11 @ X12 @ X13)
% 0.68/0.86           = (k2_enumset1 @ X11 @ X12 @ X13 @ X14))),
% 0.68/0.86      inference('cnf', [status(esa)], [t111_enumset1])).
% 0.68/0.86  thf('52', plain,
% 0.68/0.86      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X7 @ X10 @ X9 @ X8)
% 0.68/0.86           = (k2_enumset1 @ X7 @ X8 @ X9 @ X10))),
% 0.68/0.86      inference('cnf', [status(esa)], [t107_enumset1])).
% 0.68/0.86  thf('53', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X2 @ X3 @ X0 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.68/0.86      inference('sup+', [status(thm)], ['51', '52'])).
% 0.68/0.86  thf('54', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X0 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 0.68/0.86      inference('sup+', [status(thm)], ['21', '22'])).
% 0.68/0.86  thf('55', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 0.68/0.86      inference('sup+', [status(thm)], ['53', '54'])).
% 0.68/0.86  thf('56', plain,
% 0.68/0.86      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X15 @ X16 @ X17 @ X18)
% 0.68/0.86           = (k2_xboole_0 @ (k1_enumset1 @ X15 @ X16 @ X17) @ (k1_tarski @ X18)))),
% 0.68/0.86      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.68/0.86  thf('57', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.86         ((k2_enumset1 @ X1 @ X0 @ X1 @ X2) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 0.68/0.86      inference('demod', [status(thm)], ['35', '36'])).
% 0.68/0.86  thf('58', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.86         ((k1_enumset1 @ X1 @ X0 @ X2) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.68/0.86      inference('demod', [status(thm)], ['50', '55', '56', '57'])).
% 0.68/0.86  thf('59', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.86         ((k1_enumset1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 0.68/0.86      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.68/0.86  thf('60', plain,
% 0.68/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.86         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 0.68/0.86      inference('sup+', [status(thm)], ['23', '24'])).
% 0.68/0.86  thf('61', plain,
% 0.68/0.86      (((k1_enumset1 @ sk_B @ sk_C @ sk_A)
% 0.68/0.86         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 0.68/0.86      inference('demod', [status(thm)], ['28', '39', '58', '59', '60'])).
% 0.68/0.86  thf('62', plain, ($false), inference('simplify', [status(thm)], ['61'])).
% 0.68/0.86  
% 0.68/0.86  % SZS output end Refutation
% 0.68/0.86  
% 0.68/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

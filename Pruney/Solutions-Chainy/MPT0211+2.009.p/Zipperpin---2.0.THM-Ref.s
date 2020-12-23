%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jvOdAtoTfX

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:31 EST 2020

% Result     : Theorem 6.73s
% Output     : Refutation 6.73s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 347 expanded)
%              Number of leaves         :   15 ( 122 expanded)
%              Depth                    :   13
%              Number of atoms          :  697 (3100 expanded)
%              Number of equality atoms :   69 ( 338 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

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
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k2_enumset1 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_xboole_0 @ ( k2_tarski @ X7 @ X8 ) @ ( k2_tarski @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('2',plain,(
    ( k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X14: $i] :
      ( ( k2_tarski @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k1_enumset1 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k2_tarski @ X11 @ X12 ) @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_enumset1 @ X15 @ X15 @ X16 )
      = ( k2_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k1_enumset1 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k2_tarski @ X11 @ X12 ) @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k1_enumset1 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k2_tarski @ X11 @ X12 ) @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ( k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['2','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k1_enumset1 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k2_tarski @ X11 @ X12 ) @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X0 @ X1 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ( k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['16','27'])).

thf('29',plain,(
    ! [X14: $i] :
      ( ( k2_tarski @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k1_enumset1 @ X0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X0 @ X2 ) @ X1 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X0 @ X2 ) @ X1 )
      = ( k2_xboole_0 @ X1 @ ( k2_tarski @ X2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X3 @ X0 ) @ ( k2_tarski @ X1 @ X2 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k2_enumset1 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_xboole_0 @ ( k2_tarski @ X7 @ X8 ) @ ( k2_tarski @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X0 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('55',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k1_enumset1 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k2_tarski @ X11 @ X12 ) @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X2 @ X1 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X0 @ X1 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('60',plain,(
    ( k1_enumset1 @ sk_B @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['28','53','58','59'])).

thf('61',plain,(
    $false ),
    inference(simplify,[status(thm)],['60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jvOdAtoTfX
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:08:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 6.73/6.93  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.73/6.93  % Solved by: fo/fo7.sh
% 6.73/6.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.73/6.93  % done 2944 iterations in 6.485s
% 6.73/6.93  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.73/6.93  % SZS output start Refutation
% 6.73/6.93  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 6.73/6.93  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 6.73/6.93  thf(sk_A_type, type, sk_A: $i).
% 6.73/6.93  thf(sk_C_type, type, sk_C: $i).
% 6.73/6.93  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 6.73/6.93  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 6.73/6.93  thf(sk_B_type, type, sk_B: $i).
% 6.73/6.93  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 6.73/6.93  thf(t137_enumset1, conjecture,
% 6.73/6.93    (![A:$i,B:$i,C:$i]:
% 6.73/6.93     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 6.73/6.93       ( k1_enumset1 @ A @ B @ C ) ))).
% 6.73/6.93  thf(zf_stmt_0, negated_conjecture,
% 6.73/6.93    (~( ![A:$i,B:$i,C:$i]:
% 6.73/6.93        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 6.73/6.93          ( k1_enumset1 @ A @ B @ C ) ) )),
% 6.73/6.93    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 6.73/6.93  thf('0', plain,
% 6.73/6.93      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 6.73/6.93         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 6.73/6.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/6.93  thf(l53_enumset1, axiom,
% 6.73/6.93    (![A:$i,B:$i,C:$i,D:$i]:
% 6.73/6.93     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 6.73/6.93       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 6.73/6.93  thf('1', plain,
% 6.73/6.93      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 6.73/6.93         ((k2_enumset1 @ X7 @ X8 @ X9 @ X10)
% 6.73/6.93           = (k2_xboole_0 @ (k2_tarski @ X7 @ X8) @ (k2_tarski @ X9 @ X10)))),
% 6.73/6.93      inference('cnf', [status(esa)], [l53_enumset1])).
% 6.73/6.93  thf('2', plain,
% 6.73/6.93      (((k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A)
% 6.73/6.93         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 6.73/6.93      inference('demod', [status(thm)], ['0', '1'])).
% 6.73/6.93  thf(t69_enumset1, axiom,
% 6.73/6.93    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 6.73/6.93  thf('3', plain, (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 6.73/6.93      inference('cnf', [status(esa)], [t69_enumset1])).
% 6.73/6.93  thf(t43_enumset1, axiom,
% 6.73/6.93    (![A:$i,B:$i,C:$i]:
% 6.73/6.93     ( ( k1_enumset1 @ A @ B @ C ) =
% 6.73/6.93       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 6.73/6.93  thf('4', plain,
% 6.73/6.93      (![X11 : $i, X12 : $i, X13 : $i]:
% 6.73/6.93         ((k1_enumset1 @ X11 @ X12 @ X13)
% 6.73/6.93           = (k2_xboole_0 @ (k2_tarski @ X11 @ X12) @ (k1_tarski @ X13)))),
% 6.73/6.93      inference('cnf', [status(esa)], [t43_enumset1])).
% 6.73/6.93  thf('5', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i]:
% 6.73/6.93         ((k1_enumset1 @ X0 @ X0 @ X1)
% 6.73/6.93           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 6.73/6.93      inference('sup+', [status(thm)], ['3', '4'])).
% 6.73/6.93  thf(t70_enumset1, axiom,
% 6.73/6.93    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 6.73/6.93  thf('6', plain,
% 6.73/6.93      (![X15 : $i, X16 : $i]:
% 6.73/6.93         ((k1_enumset1 @ X15 @ X15 @ X16) = (k2_tarski @ X15 @ X16))),
% 6.73/6.93      inference('cnf', [status(esa)], [t70_enumset1])).
% 6.73/6.93  thf('7', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i]:
% 6.73/6.93         ((k2_tarski @ X0 @ X1)
% 6.73/6.93           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 6.73/6.93      inference('demod', [status(thm)], ['5', '6'])).
% 6.73/6.93  thf(commutativity_k2_xboole_0, axiom,
% 6.73/6.93    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 6.73/6.93  thf('8', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 6.73/6.93      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 6.73/6.93  thf('9', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i]:
% 6.73/6.93         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 6.73/6.93           = (k2_tarski @ X1 @ X0))),
% 6.73/6.93      inference('sup+', [status(thm)], ['7', '8'])).
% 6.73/6.93  thf('10', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i]:
% 6.73/6.93         ((k2_tarski @ X0 @ X1)
% 6.73/6.93           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 6.73/6.93      inference('demod', [status(thm)], ['5', '6'])).
% 6.73/6.93  thf('11', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i]: ((k2_tarski @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 6.73/6.93      inference('sup+', [status(thm)], ['9', '10'])).
% 6.73/6.93  thf('12', plain,
% 6.73/6.93      (![X11 : $i, X12 : $i, X13 : $i]:
% 6.73/6.93         ((k1_enumset1 @ X11 @ X12 @ X13)
% 6.73/6.93           = (k2_xboole_0 @ (k2_tarski @ X11 @ X12) @ (k1_tarski @ X13)))),
% 6.73/6.93      inference('cnf', [status(esa)], [t43_enumset1])).
% 6.73/6.93  thf('13', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.73/6.93         ((k1_enumset1 @ X0 @ X1 @ X2)
% 6.73/6.93           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 6.73/6.93      inference('sup+', [status(thm)], ['11', '12'])).
% 6.73/6.93  thf('14', plain,
% 6.73/6.93      (![X11 : $i, X12 : $i, X13 : $i]:
% 6.73/6.93         ((k1_enumset1 @ X11 @ X12 @ X13)
% 6.73/6.93           = (k2_xboole_0 @ (k2_tarski @ X11 @ X12) @ (k1_tarski @ X13)))),
% 6.73/6.93      inference('cnf', [status(esa)], [t43_enumset1])).
% 6.73/6.93  thf('15', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.73/6.93         ((k1_enumset1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 6.73/6.93      inference('sup+', [status(thm)], ['13', '14'])).
% 6.73/6.93  thf('16', plain,
% 6.73/6.93      (((k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A)
% 6.73/6.93         != (k1_enumset1 @ sk_B @ sk_A @ sk_C))),
% 6.73/6.93      inference('demod', [status(thm)], ['2', '15'])).
% 6.73/6.93  thf('17', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i]:
% 6.73/6.93         ((k2_tarski @ X0 @ X1)
% 6.73/6.93           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 6.73/6.93      inference('demod', [status(thm)], ['5', '6'])).
% 6.73/6.93  thf('18', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i]:
% 6.73/6.93         ((k2_tarski @ X0 @ X1)
% 6.73/6.93           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 6.73/6.93      inference('demod', [status(thm)], ['5', '6'])).
% 6.73/6.93  thf(t4_xboole_1, axiom,
% 6.73/6.93    (![A:$i,B:$i,C:$i]:
% 6.73/6.93     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 6.73/6.93       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 6.73/6.93  thf('19', plain,
% 6.73/6.93      (![X2 : $i, X3 : $i, X4 : $i]:
% 6.73/6.93         ((k2_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ X4)
% 6.73/6.93           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 6.73/6.93      inference('cnf', [status(esa)], [t4_xboole_1])).
% 6.73/6.93  thf('20', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.73/6.93         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 6.73/6.93           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 6.73/6.93              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 6.73/6.93      inference('sup+', [status(thm)], ['18', '19'])).
% 6.73/6.93  thf('21', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.73/6.93         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 6.73/6.93           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 6.73/6.93      inference('sup+', [status(thm)], ['17', '20'])).
% 6.73/6.93  thf('22', plain,
% 6.73/6.93      (![X11 : $i, X12 : $i, X13 : $i]:
% 6.73/6.93         ((k1_enumset1 @ X11 @ X12 @ X13)
% 6.73/6.93           = (k2_xboole_0 @ (k2_tarski @ X11 @ X12) @ (k1_tarski @ X13)))),
% 6.73/6.93      inference('cnf', [status(esa)], [t43_enumset1])).
% 6.73/6.93  thf('23', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 6.73/6.93      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 6.73/6.93  thf('24', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.73/6.93         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1))
% 6.73/6.93           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 6.73/6.93      inference('sup+', [status(thm)], ['22', '23'])).
% 6.73/6.93  thf('25', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.73/6.93         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 6.73/6.93           = (k1_enumset1 @ X1 @ X0 @ X2))),
% 6.73/6.93      inference('demod', [status(thm)], ['21', '24'])).
% 6.73/6.93  thf('26', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.73/6.93         ((k1_enumset1 @ X0 @ X1 @ X2)
% 6.73/6.93           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 6.73/6.93      inference('sup+', [status(thm)], ['11', '12'])).
% 6.73/6.93  thf('27', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.73/6.93         ((k1_enumset1 @ X2 @ X0 @ X1) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 6.73/6.93      inference('sup+', [status(thm)], ['25', '26'])).
% 6.73/6.93  thf('28', plain,
% 6.73/6.93      (((k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A)
% 6.73/6.93         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 6.73/6.93      inference('demod', [status(thm)], ['16', '27'])).
% 6.73/6.93  thf('29', plain,
% 6.73/6.93      (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 6.73/6.93      inference('cnf', [status(esa)], [t69_enumset1])).
% 6.73/6.93  thf('30', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.73/6.93         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 6.73/6.93           = (k1_enumset1 @ X1 @ X0 @ X2))),
% 6.73/6.93      inference('demod', [status(thm)], ['21', '24'])).
% 6.73/6.93  thf('31', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i]:
% 6.73/6.93         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 6.73/6.93           = (k1_enumset1 @ X0 @ X1 @ X0))),
% 6.73/6.93      inference('sup+', [status(thm)], ['29', '30'])).
% 6.73/6.93  thf('32', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i]:
% 6.73/6.93         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 6.73/6.93           = (k2_tarski @ X1 @ X0))),
% 6.73/6.93      inference('sup+', [status(thm)], ['7', '8'])).
% 6.73/6.93  thf('33', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i]:
% 6.73/6.93         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X0))),
% 6.73/6.93      inference('demod', [status(thm)], ['31', '32'])).
% 6.73/6.93  thf('34', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.73/6.93         ((k1_enumset1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 6.73/6.93      inference('sup+', [status(thm)], ['13', '14'])).
% 6.73/6.93  thf('35', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i]:
% 6.73/6.93         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 6.73/6.93      inference('sup+', [status(thm)], ['33', '34'])).
% 6.73/6.93  thf('36', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 6.73/6.93      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 6.73/6.93  thf('37', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.73/6.93         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 6.73/6.93           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 6.73/6.93              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 6.73/6.93      inference('sup+', [status(thm)], ['18', '19'])).
% 6.73/6.93  thf('38', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.73/6.93         ((k2_xboole_0 @ (k2_tarski @ X0 @ X2) @ X1)
% 6.73/6.93           = (k2_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ X2) @ X1) @ 
% 6.73/6.93              (k1_tarski @ X0)))),
% 6.73/6.93      inference('sup+', [status(thm)], ['36', '37'])).
% 6.73/6.93  thf('39', plain,
% 6.73/6.93      (![X2 : $i, X3 : $i, X4 : $i]:
% 6.73/6.93         ((k2_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ X4)
% 6.73/6.93           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 6.73/6.93      inference('cnf', [status(esa)], [t4_xboole_1])).
% 6.73/6.93  thf('40', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 6.73/6.93      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 6.73/6.93  thf('41', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.73/6.93         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1))
% 6.73/6.93           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 6.73/6.93      inference('sup+', [status(thm)], ['39', '40'])).
% 6.73/6.93  thf('42', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 6.73/6.93      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 6.73/6.93  thf('43', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.73/6.93         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X2) @ X1)
% 6.73/6.93           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 6.73/6.93      inference('sup+', [status(thm)], ['41', '42'])).
% 6.73/6.93  thf('44', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i]:
% 6.73/6.93         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 6.73/6.93           = (k2_tarski @ X1 @ X0))),
% 6.73/6.93      inference('sup+', [status(thm)], ['7', '8'])).
% 6.73/6.93  thf('45', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.73/6.93         ((k2_xboole_0 @ (k2_tarski @ X0 @ X2) @ X1)
% 6.73/6.93           = (k2_xboole_0 @ X1 @ (k2_tarski @ X2 @ X0)))),
% 6.73/6.93      inference('demod', [status(thm)], ['38', '43', '44'])).
% 6.73/6.93  thf('46', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.73/6.93         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 6.73/6.93           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 6.73/6.93              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 6.73/6.93      inference('sup+', [status(thm)], ['18', '19'])).
% 6.73/6.93  thf('47', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.73/6.93         ((k2_xboole_0 @ (k2_tarski @ X3 @ X0) @ (k2_tarski @ X1 @ X2))
% 6.73/6.93           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 6.73/6.93              (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))))),
% 6.73/6.93      inference('sup+', [status(thm)], ['45', '46'])).
% 6.73/6.93  thf('48', plain,
% 6.73/6.93      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 6.73/6.93         ((k2_enumset1 @ X7 @ X8 @ X9 @ X10)
% 6.73/6.93           = (k2_xboole_0 @ (k2_tarski @ X7 @ X8) @ (k2_tarski @ X9 @ X10)))),
% 6.73/6.93      inference('cnf', [status(esa)], [l53_enumset1])).
% 6.73/6.93  thf('49', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.73/6.93         ((k1_enumset1 @ X0 @ X1 @ X2)
% 6.73/6.93           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 6.73/6.93      inference('sup+', [status(thm)], ['11', '12'])).
% 6.73/6.93  thf('50', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.73/6.93         ((k2_enumset1 @ X3 @ X0 @ X1 @ X2)
% 6.73/6.93           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X1 @ X2 @ X0)))),
% 6.73/6.93      inference('demod', [status(thm)], ['47', '48', '49'])).
% 6.73/6.93  thf('51', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.73/6.93         ((k2_enumset1 @ X2 @ X0 @ X1 @ X0)
% 6.73/6.93           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 6.73/6.93      inference('sup+', [status(thm)], ['35', '50'])).
% 6.73/6.93  thf('52', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.73/6.93         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1))
% 6.73/6.93           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 6.73/6.93      inference('sup+', [status(thm)], ['22', '23'])).
% 6.73/6.93  thf('53', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.73/6.93         ((k2_enumset1 @ X2 @ X0 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 6.73/6.93      inference('demod', [status(thm)], ['51', '52'])).
% 6.73/6.93  thf('54', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.73/6.93         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 6.73/6.93           = (k1_enumset1 @ X1 @ X0 @ X2))),
% 6.73/6.93      inference('demod', [status(thm)], ['21', '24'])).
% 6.73/6.93  thf('55', plain,
% 6.73/6.93      (![X11 : $i, X12 : $i, X13 : $i]:
% 6.73/6.93         ((k1_enumset1 @ X11 @ X12 @ X13)
% 6.73/6.93           = (k2_xboole_0 @ (k2_tarski @ X11 @ X12) @ (k1_tarski @ X13)))),
% 6.73/6.93      inference('cnf', [status(esa)], [t43_enumset1])).
% 6.73/6.93  thf('56', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.73/6.93         ((k1_enumset1 @ X0 @ X2 @ X1) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 6.73/6.93      inference('sup+', [status(thm)], ['54', '55'])).
% 6.73/6.93  thf('57', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.73/6.93         ((k1_enumset1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 6.73/6.93      inference('sup+', [status(thm)], ['13', '14'])).
% 6.73/6.93  thf('58', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.73/6.93         ((k1_enumset1 @ X0 @ X1 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 6.73/6.93      inference('sup+', [status(thm)], ['56', '57'])).
% 6.73/6.93  thf('59', plain,
% 6.73/6.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.73/6.93         ((k1_enumset1 @ X2 @ X0 @ X1) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 6.73/6.93      inference('sup+', [status(thm)], ['25', '26'])).
% 6.73/6.93  thf('60', plain,
% 6.73/6.93      (((k1_enumset1 @ sk_B @ sk_C @ sk_A)
% 6.73/6.93         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 6.73/6.93      inference('demod', [status(thm)], ['28', '53', '58', '59'])).
% 6.73/6.93  thf('61', plain, ($false), inference('simplify', [status(thm)], ['60'])).
% 6.73/6.93  
% 6.73/6.93  % SZS output end Refutation
% 6.73/6.93  
% 6.73/6.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

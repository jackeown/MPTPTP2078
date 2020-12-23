%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Qd5lObjT4g

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:50 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 985 expanded)
%              Number of leaves         :   21 ( 353 expanded)
%              Depth                    :   20
%              Number of atoms          :  885 (8569 expanded)
%              Number of equality atoms :  108 ( 977 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t49_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t49_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
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

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['0','9'])).

thf('11',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('12',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('22',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('28',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('29',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['22','23','26','27','28'])).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('31',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('32',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','35'])).

thf('37',plain,
    ( sk_B
    = ( k5_xboole_0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['29','36'])).

thf('38',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('39',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('40',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('42',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['37','38','39','40','41'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('43',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('44',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['37','38','39','40','41'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('47',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('49',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['37','38','39','40','41'])).

thf('51',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('52',plain,
    ( sk_B
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('54',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('56',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['54','55'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('57',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('58',plain,(
    ! [X46: $i,X47: $i] :
      ( ( X47 != X46 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X47 ) @ ( k1_tarski @ X46 ) )
       != ( k1_tarski @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('59',plain,(
    ! [X46: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X46 ) @ ( k1_tarski @ X46 ) )
     != ( k1_tarski @ X46 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) )
     != ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_A ) @ k1_xboole_0 )
 != ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['56','60'])).

thf('62',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('63',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['54','55'])).

thf('64',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('65',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('68',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('70',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('71',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('78',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['69','79'])).

thf('81',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('84',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['86','89'])).

thf('91',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['54','55'])).

thf('92',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['61','62','63','90','91'])).

thf('93',plain,(
    $false ),
    inference(simplify,[status(thm)],['92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Qd5lObjT4g
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:32:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.71  % Solved by: fo/fo7.sh
% 0.46/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.71  % done 461 iterations in 0.260s
% 0.46/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.71  % SZS output start Refutation
% 0.46/0.71  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.71  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.71  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.71  thf(t49_zfmisc_1, conjecture,
% 0.46/0.71    (![A:$i,B:$i]:
% 0.46/0.71     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.46/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.71    (~( ![A:$i,B:$i]:
% 0.46/0.71        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ) )),
% 0.46/0.71    inference('cnf.neg', [status(esa)], [t49_zfmisc_1])).
% 0.46/0.71  thf('0', plain,
% 0.46/0.71      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf(commutativity_k5_xboole_0, axiom,
% 0.46/0.71    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.46/0.71  thf('1', plain,
% 0.46/0.71      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.46/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.71  thf(t94_xboole_1, axiom,
% 0.46/0.71    (![A:$i,B:$i]:
% 0.46/0.71     ( ( k2_xboole_0 @ A @ B ) =
% 0.46/0.71       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.71  thf('2', plain,
% 0.46/0.71      (![X14 : $i, X15 : $i]:
% 0.46/0.71         ((k2_xboole_0 @ X14 @ X15)
% 0.46/0.71           = (k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ 
% 0.46/0.71              (k3_xboole_0 @ X14 @ X15)))),
% 0.46/0.71      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.46/0.71  thf('3', plain,
% 0.46/0.71      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.46/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.71  thf('4', plain,
% 0.46/0.71      (![X14 : $i, X15 : $i]:
% 0.46/0.71         ((k2_xboole_0 @ X14 @ X15)
% 0.46/0.71           = (k5_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ 
% 0.46/0.71              (k5_xboole_0 @ X14 @ X15)))),
% 0.46/0.71      inference('demod', [status(thm)], ['2', '3'])).
% 0.46/0.71  thf('5', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]:
% 0.46/0.71         ((k2_xboole_0 @ X0 @ X1)
% 0.46/0.71           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.71      inference('sup+', [status(thm)], ['1', '4'])).
% 0.46/0.71  thf(commutativity_k3_xboole_0, axiom,
% 0.46/0.71    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.46/0.71  thf('6', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.71  thf('7', plain,
% 0.46/0.71      (![X14 : $i, X15 : $i]:
% 0.46/0.71         ((k2_xboole_0 @ X14 @ X15)
% 0.46/0.71           = (k5_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ 
% 0.46/0.71              (k5_xboole_0 @ X14 @ X15)))),
% 0.46/0.71      inference('demod', [status(thm)], ['2', '3'])).
% 0.46/0.71  thf('8', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]:
% 0.46/0.71         ((k2_xboole_0 @ X0 @ X1)
% 0.46/0.71           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X0 @ X1)))),
% 0.46/0.71      inference('sup+', [status(thm)], ['6', '7'])).
% 0.46/0.71  thf('9', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['5', '8'])).
% 0.46/0.71  thf('10', plain,
% 0.46/0.71      (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.46/0.71      inference('demod', [status(thm)], ['0', '9'])).
% 0.46/0.71  thf('11', plain,
% 0.46/0.71      (![X14 : $i, X15 : $i]:
% 0.46/0.71         ((k2_xboole_0 @ X14 @ X15)
% 0.46/0.71           = (k5_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ 
% 0.46/0.71              (k5_xboole_0 @ X14 @ X15)))),
% 0.46/0.71      inference('demod', [status(thm)], ['2', '3'])).
% 0.46/0.71  thf('12', plain,
% 0.46/0.71      (![X14 : $i, X15 : $i]:
% 0.46/0.71         ((k2_xboole_0 @ X14 @ X15)
% 0.46/0.71           = (k5_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ 
% 0.46/0.71              (k5_xboole_0 @ X14 @ X15)))),
% 0.46/0.71      inference('demod', [status(thm)], ['2', '3'])).
% 0.46/0.71  thf('13', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]:
% 0.46/0.71         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.46/0.71           = (k5_xboole_0 @ 
% 0.46/0.71              (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)) @ 
% 0.46/0.71              (k2_xboole_0 @ X1 @ X0)))),
% 0.46/0.71      inference('sup+', [status(thm)], ['11', '12'])).
% 0.46/0.71  thf('14', plain,
% 0.46/0.71      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.46/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.71  thf('15', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]:
% 0.46/0.71         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.46/0.71           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.46/0.71              (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))))),
% 0.46/0.71      inference('demod', [status(thm)], ['13', '14'])).
% 0.46/0.71  thf('16', plain,
% 0.46/0.71      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.71         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.46/0.71         = (k5_xboole_0 @ k1_xboole_0 @ 
% 0.46/0.71            (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.71             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.46/0.71      inference('sup+', [status(thm)], ['10', '15'])).
% 0.46/0.71  thf('17', plain,
% 0.46/0.71      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.46/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.71  thf(t5_boole, axiom,
% 0.46/0.71    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.71  thf('18', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.46/0.71      inference('cnf', [status(esa)], [t5_boole])).
% 0.46/0.71  thf('19', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['17', '18'])).
% 0.46/0.71  thf('20', plain,
% 0.46/0.71      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.71         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.46/0.71         = (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.71            (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.46/0.71      inference('demod', [status(thm)], ['16', '19'])).
% 0.46/0.71  thf('21', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]:
% 0.46/0.71         ((k2_xboole_0 @ X0 @ X1)
% 0.46/0.71           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.71      inference('sup+', [status(thm)], ['1', '4'])).
% 0.46/0.71  thf('22', plain,
% 0.46/0.71      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.71         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.46/0.71         = (k5_xboole_0 @ 
% 0.46/0.71            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.71             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.46/0.71            (k5_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.71             (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.46/0.71      inference('sup+', [status(thm)], ['20', '21'])).
% 0.46/0.71  thf(t91_xboole_1, axiom,
% 0.46/0.71    (![A:$i,B:$i,C:$i]:
% 0.46/0.71     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.46/0.71       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.46/0.71  thf('23', plain,
% 0.46/0.71      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.71         ((k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12)
% 0.46/0.71           = (k5_xboole_0 @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.46/0.71      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.71  thf('24', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.71  thf(t100_xboole_1, axiom,
% 0.46/0.71    (![A:$i,B:$i]:
% 0.46/0.71     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.71  thf('25', plain,
% 0.46/0.71      (![X5 : $i, X6 : $i]:
% 0.46/0.71         ((k4_xboole_0 @ X5 @ X6)
% 0.46/0.71           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.46/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.71  thf('26', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]:
% 0.46/0.71         ((k4_xboole_0 @ X0 @ X1)
% 0.46/0.71           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.46/0.71      inference('sup+', [status(thm)], ['24', '25'])).
% 0.46/0.71  thf('27', plain,
% 0.46/0.71      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.46/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.71  thf('28', plain,
% 0.46/0.71      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.71         ((k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12)
% 0.46/0.71           = (k5_xboole_0 @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.46/0.71      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.71  thf('29', plain,
% 0.46/0.71      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.71         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.46/0.71         = (k5_xboole_0 @ sk_B @ 
% 0.46/0.71            (k5_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.46/0.71             (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.71              (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))))),
% 0.46/0.71      inference('demod', [status(thm)], ['22', '23', '26', '27', '28'])).
% 0.46/0.71  thf('30', plain,
% 0.46/0.71      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.46/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.71  thf(t92_xboole_1, axiom,
% 0.46/0.71    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.46/0.71  thf('31', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.46/0.71      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.46/0.71  thf('32', plain,
% 0.46/0.71      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.71         ((k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12)
% 0.46/0.71           = (k5_xboole_0 @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.46/0.71      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.71  thf('33', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]:
% 0.46/0.71         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.71           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.71      inference('sup+', [status(thm)], ['31', '32'])).
% 0.46/0.71  thf('34', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['17', '18'])).
% 0.46/0.71  thf('35', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]:
% 0.46/0.71         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.71      inference('demod', [status(thm)], ['33', '34'])).
% 0.46/0.71  thf('36', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]:
% 0.46/0.71         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.71      inference('sup+', [status(thm)], ['30', '35'])).
% 0.46/0.71  thf('37', plain,
% 0.46/0.71      (((sk_B)
% 0.46/0.71         = (k5_xboole_0 @ 
% 0.46/0.71            (k5_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.46/0.71             (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.71              (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))) @ 
% 0.46/0.71            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.71             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.46/0.71      inference('sup+', [status(thm)], ['29', '36'])).
% 0.46/0.71  thf('38', plain,
% 0.46/0.71      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.71         ((k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12)
% 0.46/0.71           = (k5_xboole_0 @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.46/0.71      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.71  thf('39', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.46/0.71      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.46/0.71  thf('40', plain,
% 0.46/0.71      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.46/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.71  thf('41', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['17', '18'])).
% 0.46/0.71  thf('42', plain, (((sk_B) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.46/0.71      inference('demod', [status(thm)], ['37', '38', '39', '40', '41'])).
% 0.46/0.71  thf(t48_xboole_1, axiom,
% 0.46/0.71    (![A:$i,B:$i]:
% 0.46/0.71     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.71  thf('43', plain,
% 0.46/0.71      (![X7 : $i, X8 : $i]:
% 0.46/0.71         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.46/0.71           = (k3_xboole_0 @ X7 @ X8))),
% 0.46/0.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.71  thf('44', plain,
% 0.46/0.71      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.46/0.71         = (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.46/0.71      inference('sup+', [status(thm)], ['42', '43'])).
% 0.46/0.71  thf('45', plain, (((sk_B) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.46/0.71      inference('demod', [status(thm)], ['37', '38', '39', '40', '41'])).
% 0.46/0.71  thf('46', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.71  thf('47', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.46/0.71      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.46/0.71  thf('48', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]:
% 0.46/0.71         ((k4_xboole_0 @ X0 @ X1)
% 0.46/0.71           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.46/0.71      inference('sup+', [status(thm)], ['24', '25'])).
% 0.46/0.71  thf('49', plain,
% 0.46/0.71      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.46/0.71         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.46/0.71      inference('sup+', [status(thm)], ['47', '48'])).
% 0.46/0.71  thf('50', plain, (((sk_B) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.46/0.71      inference('demod', [status(thm)], ['37', '38', '39', '40', '41'])).
% 0.46/0.71  thf('51', plain,
% 0.46/0.71      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.46/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.71  thf('52', plain, (((sk_B) = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.46/0.71      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.46/0.71  thf('53', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]:
% 0.46/0.71         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.71      inference('demod', [status(thm)], ['33', '34'])).
% 0.46/0.71  thf('54', plain, (((k1_tarski @ sk_A) = (k5_xboole_0 @ sk_B @ sk_B))),
% 0.46/0.71      inference('sup+', [status(thm)], ['52', '53'])).
% 0.46/0.71  thf('55', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.46/0.71      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.46/0.71  thf('56', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.46/0.71      inference('demod', [status(thm)], ['54', '55'])).
% 0.46/0.71  thf(t69_enumset1, axiom,
% 0.46/0.71    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.46/0.71  thf('57', plain,
% 0.46/0.71      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.46/0.71      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.71  thf(t20_zfmisc_1, axiom,
% 0.46/0.71    (![A:$i,B:$i]:
% 0.46/0.71     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.46/0.71         ( k1_tarski @ A ) ) <=>
% 0.46/0.71       ( ( A ) != ( B ) ) ))).
% 0.46/0.71  thf('58', plain,
% 0.46/0.71      (![X46 : $i, X47 : $i]:
% 0.46/0.71         (((X47) != (X46))
% 0.46/0.71          | ((k4_xboole_0 @ (k1_tarski @ X47) @ (k1_tarski @ X46))
% 0.46/0.71              != (k1_tarski @ X47)))),
% 0.46/0.71      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.46/0.71  thf('59', plain,
% 0.46/0.71      (![X46 : $i]:
% 0.46/0.71         ((k4_xboole_0 @ (k1_tarski @ X46) @ (k1_tarski @ X46))
% 0.46/0.71           != (k1_tarski @ X46))),
% 0.46/0.71      inference('simplify', [status(thm)], ['58'])).
% 0.46/0.71  thf('60', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0))
% 0.46/0.71           != (k1_tarski @ X0))),
% 0.46/0.71      inference('sup-', [status(thm)], ['57', '59'])).
% 0.46/0.71  thf('61', plain,
% 0.46/0.71      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_A) @ k1_xboole_0)
% 0.46/0.71         != (k1_tarski @ sk_A))),
% 0.46/0.71      inference('sup-', [status(thm)], ['56', '60'])).
% 0.46/0.71  thf('62', plain,
% 0.46/0.71      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.46/0.71      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.71  thf('63', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.46/0.71      inference('demod', [status(thm)], ['54', '55'])).
% 0.46/0.71  thf('64', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.46/0.71      inference('cnf', [status(esa)], [t5_boole])).
% 0.46/0.71  thf('65', plain,
% 0.46/0.71      (![X14 : $i, X15 : $i]:
% 0.46/0.71         ((k2_xboole_0 @ X14 @ X15)
% 0.46/0.71           = (k5_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ 
% 0.46/0.71              (k5_xboole_0 @ X14 @ X15)))),
% 0.46/0.71      inference('demod', [status(thm)], ['2', '3'])).
% 0.46/0.71  thf('66', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 0.46/0.71           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['64', '65'])).
% 0.46/0.71  thf('67', plain,
% 0.46/0.71      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.46/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.71  thf('68', plain,
% 0.46/0.71      (![X5 : $i, X6 : $i]:
% 0.46/0.71         ((k4_xboole_0 @ X5 @ X6)
% 0.46/0.71           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.46/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.71  thf('69', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.71      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.46/0.71  thf(idempotence_k3_xboole_0, axiom,
% 0.46/0.71    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.46/0.71  thf('70', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 0.46/0.71      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.46/0.71  thf('71', plain,
% 0.46/0.71      (![X5 : $i, X6 : $i]:
% 0.46/0.71         ((k4_xboole_0 @ X5 @ X6)
% 0.46/0.71           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.46/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.71  thf('72', plain,
% 0.46/0.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['70', '71'])).
% 0.46/0.71  thf('73', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.46/0.71      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.46/0.71  thf('74', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['72', '73'])).
% 0.46/0.71  thf('75', plain,
% 0.46/0.71      (![X7 : $i, X8 : $i]:
% 0.46/0.71         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.46/0.71           = (k3_xboole_0 @ X7 @ X8))),
% 0.46/0.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.71  thf('76', plain,
% 0.46/0.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['74', '75'])).
% 0.46/0.71  thf('77', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.71      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.46/0.71  thf('78', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 0.46/0.71      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.46/0.71  thf('79', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.71      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.46/0.71  thf('80', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.71      inference('demod', [status(thm)], ['69', '79'])).
% 0.46/0.71  thf('81', plain,
% 0.46/0.71      (![X7 : $i, X8 : $i]:
% 0.46/0.71         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.46/0.71           = (k3_xboole_0 @ X7 @ X8))),
% 0.46/0.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.71  thf('82', plain,
% 0.46/0.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['80', '81'])).
% 0.46/0.71  thf('83', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['72', '73'])).
% 0.46/0.71  thf('84', plain,
% 0.46/0.71      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.71      inference('demod', [status(thm)], ['82', '83'])).
% 0.46/0.71  thf('85', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.71  thf('86', plain,
% 0.46/0.71      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['84', '85'])).
% 0.46/0.71  thf('87', plain,
% 0.46/0.71      (![X5 : $i, X6 : $i]:
% 0.46/0.71         ((k4_xboole_0 @ X5 @ X6)
% 0.46/0.71           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.46/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.71  thf('88', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['17', '18'])).
% 0.46/0.71  thf('89', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['87', '88'])).
% 0.46/0.71  thf('90', plain,
% 0.46/0.71      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['86', '89'])).
% 0.46/0.71  thf('91', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.46/0.71      inference('demod', [status(thm)], ['54', '55'])).
% 0.46/0.71  thf('92', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.46/0.71      inference('demod', [status(thm)], ['61', '62', '63', '90', '91'])).
% 0.46/0.71  thf('93', plain, ($false), inference('simplify', [status(thm)], ['92'])).
% 0.46/0.71  
% 0.46/0.71  % SZS output end Refutation
% 0.46/0.71  
% 0.46/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

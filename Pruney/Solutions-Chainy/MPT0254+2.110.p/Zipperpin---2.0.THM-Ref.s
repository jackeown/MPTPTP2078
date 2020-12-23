%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ilgwQcsuZU

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:50 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 238 expanded)
%              Number of leaves         :   19 (  85 expanded)
%              Depth                    :   16
%              Number of atoms          :  695 (1715 expanded)
%              Number of equality atoms :   97 ( 231 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf('11',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['0','9'])).

thf('12',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['12','15','18'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('20',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('21',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('24',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','26'])).

thf('28',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','27'])).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('31',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['28','29','30'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('33',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('34',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('35',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','40'])).

thf('42',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['0','9'])).

thf('43',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('51',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('58',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('61',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['56','62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['49','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['46','69'])).

thf('71',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['10','43','76'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('78',plain,(
    ! [X46: $i,X47: $i] :
      ( ( X47 != X46 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X47 ) @ ( k1_tarski @ X46 ) )
       != ( k1_tarski @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('79',plain,(
    ! [X46: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X46 ) @ ( k1_tarski @ X46 ) )
     != ( k1_tarski @ X46 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('81',plain,(
    ! [X46: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X46 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['77','81'])).

thf('83',plain,(
    $false ),
    inference(simplify,[status(thm)],['82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ilgwQcsuZU
% 0.17/0.37  % Computer   : n002.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 17:34:22 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.17/0.38  % Python version: Python 3.6.8
% 0.17/0.38  % Running in FO mode
% 0.48/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.48/0.69  % Solved by: fo/fo7.sh
% 0.48/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.69  % done 364 iterations in 0.198s
% 0.48/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.48/0.69  % SZS output start Refutation
% 0.48/0.69  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.48/0.69  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.48/0.69  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.48/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.48/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.48/0.69  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.48/0.69  thf(t49_zfmisc_1, conjecture,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.48/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.69    (~( ![A:$i,B:$i]:
% 0.48/0.69        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ) )),
% 0.48/0.69    inference('cnf.neg', [status(esa)], [t49_zfmisc_1])).
% 0.48/0.69  thf('0', plain,
% 0.48/0.69      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf(commutativity_k5_xboole_0, axiom,
% 0.48/0.69    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.48/0.69  thf('1', plain,
% 0.48/0.69      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.48/0.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.48/0.69  thf(t94_xboole_1, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( k2_xboole_0 @ A @ B ) =
% 0.48/0.69       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.48/0.69  thf('2', plain,
% 0.48/0.69      (![X14 : $i, X15 : $i]:
% 0.48/0.69         ((k2_xboole_0 @ X14 @ X15)
% 0.48/0.69           = (k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ 
% 0.48/0.69              (k3_xboole_0 @ X14 @ X15)))),
% 0.48/0.69      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.48/0.69  thf('3', plain,
% 0.48/0.69      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.48/0.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.48/0.69  thf('4', plain,
% 0.48/0.69      (![X14 : $i, X15 : $i]:
% 0.48/0.69         ((k2_xboole_0 @ X14 @ X15)
% 0.48/0.69           = (k5_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ 
% 0.48/0.69              (k5_xboole_0 @ X14 @ X15)))),
% 0.48/0.69      inference('demod', [status(thm)], ['2', '3'])).
% 0.48/0.69  thf('5', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         ((k2_xboole_0 @ X0 @ X1)
% 0.48/0.69           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.48/0.69      inference('sup+', [status(thm)], ['1', '4'])).
% 0.48/0.69  thf(commutativity_k3_xboole_0, axiom,
% 0.48/0.69    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.48/0.69  thf('6', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.48/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.48/0.69  thf('7', plain,
% 0.48/0.69      (![X14 : $i, X15 : $i]:
% 0.48/0.69         ((k2_xboole_0 @ X14 @ X15)
% 0.48/0.69           = (k5_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ 
% 0.48/0.69              (k5_xboole_0 @ X14 @ X15)))),
% 0.48/0.69      inference('demod', [status(thm)], ['2', '3'])).
% 0.48/0.69  thf('8', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         ((k2_xboole_0 @ X0 @ X1)
% 0.48/0.69           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X0 @ X1)))),
% 0.48/0.69      inference('sup+', [status(thm)], ['6', '7'])).
% 0.48/0.69  thf('9', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 0.48/0.69      inference('sup+', [status(thm)], ['5', '8'])).
% 0.48/0.69  thf('10', plain,
% 0.48/0.69      (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.48/0.69      inference('demod', [status(thm)], ['0', '9'])).
% 0.48/0.69  thf('11', plain,
% 0.48/0.69      (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.48/0.69      inference('demod', [status(thm)], ['0', '9'])).
% 0.48/0.69  thf('12', plain,
% 0.48/0.69      (![X14 : $i, X15 : $i]:
% 0.48/0.69         ((k2_xboole_0 @ X14 @ X15)
% 0.48/0.69           = (k5_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ 
% 0.48/0.69              (k5_xboole_0 @ X14 @ X15)))),
% 0.48/0.69      inference('demod', [status(thm)], ['2', '3'])).
% 0.48/0.69  thf(t91_xboole_1, axiom,
% 0.48/0.69    (![A:$i,B:$i,C:$i]:
% 0.48/0.69     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.48/0.69       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.48/0.69  thf('13', plain,
% 0.48/0.69      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.48/0.69         ((k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12)
% 0.48/0.69           = (k5_xboole_0 @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.48/0.69      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.48/0.69  thf('14', plain,
% 0.48/0.69      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.48/0.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.48/0.69  thf('15', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.69         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.48/0.69           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.48/0.69      inference('sup+', [status(thm)], ['13', '14'])).
% 0.48/0.69  thf('16', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.48/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.48/0.69  thf(t100_xboole_1, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.48/0.69  thf('17', plain,
% 0.48/0.69      (![X5 : $i, X6 : $i]:
% 0.48/0.69         ((k4_xboole_0 @ X5 @ X6)
% 0.48/0.69           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.48/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.48/0.69  thf('18', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         ((k4_xboole_0 @ X0 @ X1)
% 0.48/0.69           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.48/0.69      inference('sup+', [status(thm)], ['16', '17'])).
% 0.48/0.69  thf('19', plain,
% 0.48/0.69      (![X14 : $i, X15 : $i]:
% 0.48/0.69         ((k2_xboole_0 @ X14 @ X15)
% 0.48/0.69           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.48/0.69      inference('demod', [status(thm)], ['12', '15', '18'])).
% 0.48/0.69  thf(t92_xboole_1, axiom,
% 0.48/0.69    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.48/0.69  thf('20', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.48/0.69      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.48/0.69  thf('21', plain,
% 0.48/0.69      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.48/0.69         ((k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12)
% 0.48/0.69           = (k5_xboole_0 @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.48/0.69      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.48/0.69  thf('22', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.48/0.69           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.48/0.69      inference('sup+', [status(thm)], ['20', '21'])).
% 0.48/0.69  thf('23', plain,
% 0.48/0.69      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.48/0.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.48/0.69  thf(t5_boole, axiom,
% 0.48/0.69    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.48/0.69  thf('24', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.48/0.69      inference('cnf', [status(esa)], [t5_boole])).
% 0.48/0.69  thf('25', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.48/0.69      inference('sup+', [status(thm)], ['23', '24'])).
% 0.48/0.69  thf('26', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.48/0.69      inference('demod', [status(thm)], ['22', '25'])).
% 0.48/0.69  thf('27', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         ((k4_xboole_0 @ X0 @ X1)
% 0.48/0.69           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.48/0.69      inference('sup+', [status(thm)], ['19', '26'])).
% 0.48/0.69  thf('28', plain,
% 0.48/0.69      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.48/0.69         = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.48/0.69      inference('sup+', [status(thm)], ['11', '27'])).
% 0.48/0.69  thf('29', plain,
% 0.48/0.69      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.48/0.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.48/0.69  thf('30', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.48/0.69      inference('sup+', [status(thm)], ['23', '24'])).
% 0.48/0.69  thf('31', plain, (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B))),
% 0.48/0.69      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.48/0.69  thf(t39_xboole_1, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.48/0.69  thf('32', plain,
% 0.48/0.69      (![X7 : $i, X8 : $i]:
% 0.48/0.69         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 0.48/0.69           = (k2_xboole_0 @ X7 @ X8))),
% 0.48/0.69      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.48/0.69  thf('33', plain,
% 0.48/0.69      (((k2_xboole_0 @ sk_B @ sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.48/0.69      inference('sup+', [status(thm)], ['31', '32'])).
% 0.48/0.69  thf(idempotence_k3_xboole_0, axiom,
% 0.48/0.69    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.48/0.69  thf('34', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 0.48/0.69      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.48/0.69  thf('35', plain,
% 0.48/0.69      (![X14 : $i, X15 : $i]:
% 0.48/0.69         ((k2_xboole_0 @ X14 @ X15)
% 0.48/0.69           = (k5_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ 
% 0.48/0.69              (k5_xboole_0 @ X14 @ X15)))),
% 0.48/0.69      inference('demod', [status(thm)], ['2', '3'])).
% 0.48/0.69  thf('36', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((k2_xboole_0 @ X0 @ X0)
% 0.48/0.69           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.48/0.69      inference('sup+', [status(thm)], ['34', '35'])).
% 0.48/0.69  thf('37', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.48/0.69      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.48/0.69  thf('38', plain,
% 0.48/0.69      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.48/0.69      inference('demod', [status(thm)], ['36', '37'])).
% 0.48/0.69  thf('39', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.48/0.69      inference('cnf', [status(esa)], [t5_boole])).
% 0.48/0.69  thf('40', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.48/0.69      inference('demod', [status(thm)], ['38', '39'])).
% 0.48/0.69  thf('41', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.48/0.69      inference('demod', [status(thm)], ['33', '40'])).
% 0.48/0.69  thf('42', plain,
% 0.48/0.69      (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.48/0.69      inference('demod', [status(thm)], ['0', '9'])).
% 0.48/0.69  thf('43', plain, (((sk_B) = (k1_xboole_0))),
% 0.48/0.69      inference('sup+', [status(thm)], ['41', '42'])).
% 0.48/0.69  thf('44', plain,
% 0.48/0.69      (![X5 : $i, X6 : $i]:
% 0.48/0.69         ((k4_xboole_0 @ X5 @ X6)
% 0.48/0.69           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.48/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.48/0.69  thf('45', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.48/0.69      inference('sup+', [status(thm)], ['23', '24'])).
% 0.48/0.69  thf('46', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.48/0.69      inference('sup+', [status(thm)], ['44', '45'])).
% 0.48/0.69  thf('47', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.48/0.69      inference('sup+', [status(thm)], ['44', '45'])).
% 0.48/0.69  thf('48', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         ((k4_xboole_0 @ X0 @ X1)
% 0.48/0.69           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.48/0.69      inference('sup+', [status(thm)], ['16', '17'])).
% 0.48/0.69  thf('49', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.48/0.69           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.48/0.69      inference('sup+', [status(thm)], ['47', '48'])).
% 0.48/0.69  thf('50', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 0.48/0.69      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.48/0.69  thf('51', plain,
% 0.48/0.69      (![X5 : $i, X6 : $i]:
% 0.48/0.69         ((k4_xboole_0 @ X5 @ X6)
% 0.48/0.69           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.48/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.48/0.69  thf('52', plain,
% 0.48/0.69      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.48/0.69      inference('sup+', [status(thm)], ['50', '51'])).
% 0.48/0.69  thf('53', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.48/0.69      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.48/0.69  thf('54', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.48/0.69      inference('sup+', [status(thm)], ['52', '53'])).
% 0.48/0.69  thf('55', plain,
% 0.48/0.69      (![X7 : $i, X8 : $i]:
% 0.48/0.69         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 0.48/0.69           = (k2_xboole_0 @ X7 @ X8))),
% 0.48/0.69      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.48/0.69  thf('56', plain,
% 0.48/0.69      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 0.48/0.69      inference('sup+', [status(thm)], ['54', '55'])).
% 0.48/0.69  thf('57', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.48/0.69      inference('cnf', [status(esa)], [t5_boole])).
% 0.48/0.69  thf('58', plain,
% 0.48/0.69      (![X14 : $i, X15 : $i]:
% 0.48/0.69         ((k2_xboole_0 @ X14 @ X15)
% 0.48/0.69           = (k5_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ 
% 0.48/0.69              (k5_xboole_0 @ X14 @ X15)))),
% 0.48/0.69      inference('demod', [status(thm)], ['2', '3'])).
% 0.48/0.69  thf('59', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 0.48/0.69           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X0))),
% 0.48/0.69      inference('sup+', [status(thm)], ['57', '58'])).
% 0.48/0.69  thf('60', plain,
% 0.48/0.69      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.48/0.69      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.48/0.69  thf('61', plain,
% 0.48/0.69      (![X5 : $i, X6 : $i]:
% 0.48/0.69         ((k4_xboole_0 @ X5 @ X6)
% 0.48/0.69           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.48/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.48/0.69  thf('62', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.48/0.69      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.48/0.69  thf('63', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.48/0.69      inference('demod', [status(thm)], ['38', '39'])).
% 0.48/0.69  thf('64', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.48/0.69      inference('demod', [status(thm)], ['56', '62', '63'])).
% 0.48/0.69  thf('65', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((X0) = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.48/0.69      inference('demod', [status(thm)], ['49', '64'])).
% 0.48/0.69  thf('66', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.48/0.69      inference('demod', [status(thm)], ['22', '25'])).
% 0.48/0.69  thf('67', plain,
% 0.48/0.69      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.48/0.69      inference('sup+', [status(thm)], ['65', '66'])).
% 0.48/0.69  thf('68', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.48/0.69      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.48/0.69  thf('69', plain,
% 0.48/0.69      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.48/0.69      inference('demod', [status(thm)], ['67', '68'])).
% 0.48/0.69  thf('70', plain,
% 0.48/0.69      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.48/0.69      inference('demod', [status(thm)], ['46', '69'])).
% 0.48/0.69  thf('71', plain,
% 0.48/0.69      (![X14 : $i, X15 : $i]:
% 0.48/0.69         ((k2_xboole_0 @ X14 @ X15)
% 0.48/0.69           = (k5_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ 
% 0.48/0.69              (k5_xboole_0 @ X14 @ X15)))),
% 0.48/0.69      inference('demod', [status(thm)], ['2', '3'])).
% 0.48/0.69  thf('72', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.48/0.69           = (k5_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.48/0.69      inference('sup+', [status(thm)], ['70', '71'])).
% 0.48/0.69  thf('73', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.48/0.69      inference('sup+', [status(thm)], ['23', '24'])).
% 0.48/0.69  thf('74', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.48/0.69      inference('demod', [status(thm)], ['72', '73'])).
% 0.48/0.69  thf('75', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.48/0.69      inference('sup+', [status(thm)], ['23', '24'])).
% 0.48/0.69  thf('76', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.48/0.69      inference('sup+', [status(thm)], ['74', '75'])).
% 0.48/0.69  thf('77', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.48/0.69      inference('demod', [status(thm)], ['10', '43', '76'])).
% 0.48/0.69  thf(t20_zfmisc_1, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.48/0.69         ( k1_tarski @ A ) ) <=>
% 0.48/0.69       ( ( A ) != ( B ) ) ))).
% 0.48/0.69  thf('78', plain,
% 0.48/0.69      (![X46 : $i, X47 : $i]:
% 0.48/0.69         (((X47) != (X46))
% 0.48/0.69          | ((k4_xboole_0 @ (k1_tarski @ X47) @ (k1_tarski @ X46))
% 0.48/0.69              != (k1_tarski @ X47)))),
% 0.48/0.69      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.48/0.69  thf('79', plain,
% 0.48/0.69      (![X46 : $i]:
% 0.48/0.69         ((k4_xboole_0 @ (k1_tarski @ X46) @ (k1_tarski @ X46))
% 0.48/0.69           != (k1_tarski @ X46))),
% 0.48/0.69      inference('simplify', [status(thm)], ['78'])).
% 0.48/0.69  thf('80', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.48/0.69      inference('sup+', [status(thm)], ['52', '53'])).
% 0.48/0.69  thf('81', plain, (![X46 : $i]: ((k1_xboole_0) != (k1_tarski @ X46))),
% 0.48/0.69      inference('demod', [status(thm)], ['79', '80'])).
% 0.48/0.69  thf('82', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.48/0.69      inference('sup-', [status(thm)], ['77', '81'])).
% 0.48/0.69  thf('83', plain, ($false), inference('simplify', [status(thm)], ['82'])).
% 0.48/0.69  
% 0.48/0.69  % SZS output end Refutation
% 0.48/0.69  
% 0.48/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

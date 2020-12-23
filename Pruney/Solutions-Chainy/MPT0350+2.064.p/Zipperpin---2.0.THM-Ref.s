%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.h4Xab0KbpQ

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:54 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 263 expanded)
%              Number of leaves         :   35 (  97 expanded)
%              Depth                    :   18
%              Number of atoms          :  962 (1945 expanded)
%              Number of equality atoms :   99 ( 200 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t25_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
          = ( k2_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X54 @ X55 )
      | ( r2_hidden @ X54 @ X55 )
      | ( v1_xboole_0 @ X55 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X60: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('4',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['2','3'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('5',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( r2_hidden @ X50 @ X49 )
      | ( r1_tarski @ X50 @ X48 )
      | ( X49
       != ( k1_zfmisc_1 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('6',plain,(
    ! [X48: $i,X50: $i] :
      ( ( r1_tarski @ X50 @ X48 )
      | ~ ( r2_hidden @ X50 @ ( k1_zfmisc_1 @ X48 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['4','6'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X58: $i,X59: $i] :
      ( ( ( k3_subset_1 @ X58 @ X59 )
        = ( k4_xboole_0 @ X58 @ X59 ) )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('16',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('18',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','16','17'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('19',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('23',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['18','25'])).

thf('27',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','16','17'])).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( sk_B
    = ( k5_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('34',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X6 @ X8 ) @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['31','39'])).

thf('41',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('42',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X6 @ X8 ) @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('52',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['40','55'])).

thf('57',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('62',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['62','67'])).

thf('69',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('71',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('73',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('74',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X52 @ X53 ) )
      = ( k2_xboole_0 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('75',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('76',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X18 @ X19 ) )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['72','76'])).

thf('78',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['71','79'])).

thf('81',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
    = sk_A ),
    inference('sup+',[status(thm)],['26','80'])).

thf('82',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('83',plain,(
    ! [X57: $i] :
      ( ( k2_subset_1 @ X57 )
      = X57 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('84',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('86',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('87',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( r1_tarski @ X47 @ X48 )
      | ( r2_hidden @ X47 @ X49 )
      | ( X49
       != ( k1_zfmisc_1 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('89',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r2_hidden @ X47 @ ( k1_zfmisc_1 @ X48 ) )
      | ~ ( r1_tarski @ X47 @ X48 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    r2_hidden @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['87','89'])).

thf('91',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( r2_hidden @ X54 @ X55 )
      | ( m1_subset_1 @ X54 @ X55 )
      | ( v1_xboole_0 @ X55 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('92',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X60: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('94',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('96',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ X62 ) )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ X62 ) )
      | ( ( k4_subset_1 @ X62 @ X61 @ X63 )
        = ( k2_xboole_0 @ X61 @ X63 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('97',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X52 @ X53 ) )
      = ( k2_xboole_0 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('98',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ X62 ) )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ X62 ) )
      | ( ( k4_subset_1 @ X62 @ X61 @ X63 )
        = ( k3_tarski @ ( k2_tarski @ X61 @ X63 ) ) ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['94','99'])).

thf('101',plain,(
    ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
 != sk_A ),
    inference(demod,[status(thm)],['84','100'])).

thf('102',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['81','101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.h4Xab0KbpQ
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:58:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.65/1.87  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.65/1.87  % Solved by: fo/fo7.sh
% 1.65/1.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.65/1.87  % done 2723 iterations in 1.409s
% 1.65/1.87  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.65/1.87  % SZS output start Refutation
% 1.65/1.87  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.65/1.87  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.65/1.87  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.65/1.87  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.65/1.87  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.65/1.87  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.65/1.87  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.65/1.87  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.65/1.87  thf(sk_B_type, type, sk_B: $i).
% 1.65/1.87  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.65/1.87  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.65/1.87  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.65/1.87  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.65/1.87  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.65/1.87  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.65/1.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.65/1.87  thf(sk_A_type, type, sk_A: $i).
% 1.65/1.87  thf(t25_subset_1, conjecture,
% 1.65/1.87    (![A:$i,B:$i]:
% 1.65/1.87     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.65/1.87       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 1.65/1.87         ( k2_subset_1 @ A ) ) ))).
% 1.65/1.87  thf(zf_stmt_0, negated_conjecture,
% 1.65/1.87    (~( ![A:$i,B:$i]:
% 1.65/1.87        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.65/1.87          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 1.65/1.87            ( k2_subset_1 @ A ) ) ) )),
% 1.65/1.87    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 1.65/1.87  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf(d2_subset_1, axiom,
% 1.65/1.87    (![A:$i,B:$i]:
% 1.65/1.87     ( ( ( v1_xboole_0 @ A ) =>
% 1.65/1.87         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.65/1.87       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.65/1.87         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.65/1.87  thf('1', plain,
% 1.65/1.87      (![X54 : $i, X55 : $i]:
% 1.65/1.87         (~ (m1_subset_1 @ X54 @ X55)
% 1.65/1.87          | (r2_hidden @ X54 @ X55)
% 1.65/1.87          | (v1_xboole_0 @ X55))),
% 1.65/1.87      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.65/1.87  thf('2', plain,
% 1.65/1.87      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 1.65/1.87        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 1.65/1.87      inference('sup-', [status(thm)], ['0', '1'])).
% 1.65/1.87  thf(fc1_subset_1, axiom,
% 1.65/1.87    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.65/1.87  thf('3', plain, (![X60 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X60))),
% 1.65/1.87      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.65/1.87  thf('4', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.65/1.87      inference('clc', [status(thm)], ['2', '3'])).
% 1.65/1.87  thf(d1_zfmisc_1, axiom,
% 1.65/1.87    (![A:$i,B:$i]:
% 1.65/1.87     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 1.65/1.87       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 1.65/1.87  thf('5', plain,
% 1.65/1.87      (![X48 : $i, X49 : $i, X50 : $i]:
% 1.65/1.87         (~ (r2_hidden @ X50 @ X49)
% 1.65/1.87          | (r1_tarski @ X50 @ X48)
% 1.65/1.87          | ((X49) != (k1_zfmisc_1 @ X48)))),
% 1.65/1.87      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.65/1.87  thf('6', plain,
% 1.65/1.87      (![X48 : $i, X50 : $i]:
% 1.65/1.87         ((r1_tarski @ X50 @ X48) | ~ (r2_hidden @ X50 @ (k1_zfmisc_1 @ X48)))),
% 1.65/1.87      inference('simplify', [status(thm)], ['5'])).
% 1.65/1.87  thf('7', plain, ((r1_tarski @ sk_B @ sk_A)),
% 1.65/1.87      inference('sup-', [status(thm)], ['4', '6'])).
% 1.65/1.87  thf(t28_xboole_1, axiom,
% 1.65/1.87    (![A:$i,B:$i]:
% 1.65/1.87     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.65/1.87  thf('8', plain,
% 1.65/1.87      (![X9 : $i, X10 : $i]:
% 1.65/1.87         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 1.65/1.87      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.65/1.87  thf('9', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 1.65/1.87      inference('sup-', [status(thm)], ['7', '8'])).
% 1.65/1.87  thf(commutativity_k3_xboole_0, axiom,
% 1.65/1.87    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.65/1.87  thf('10', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.65/1.87      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.65/1.87  thf(t100_xboole_1, axiom,
% 1.65/1.87    (![A:$i,B:$i]:
% 1.65/1.87     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.65/1.87  thf('11', plain,
% 1.65/1.87      (![X4 : $i, X5 : $i]:
% 1.65/1.87         ((k4_xboole_0 @ X4 @ X5)
% 1.65/1.87           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.65/1.87      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.65/1.87  thf('12', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         ((k4_xboole_0 @ X0 @ X1)
% 1.65/1.87           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.65/1.87      inference('sup+', [status(thm)], ['10', '11'])).
% 1.65/1.87  thf('13', plain,
% 1.65/1.87      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 1.65/1.87      inference('sup+', [status(thm)], ['9', '12'])).
% 1.65/1.87  thf('14', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf(d5_subset_1, axiom,
% 1.65/1.87    (![A:$i,B:$i]:
% 1.65/1.87     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.65/1.87       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.65/1.87  thf('15', plain,
% 1.65/1.87      (![X58 : $i, X59 : $i]:
% 1.65/1.87         (((k3_subset_1 @ X58 @ X59) = (k4_xboole_0 @ X58 @ X59))
% 1.65/1.87          | ~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ X58)))),
% 1.65/1.87      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.65/1.87  thf('16', plain,
% 1.65/1.87      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 1.65/1.87      inference('sup-', [status(thm)], ['14', '15'])).
% 1.65/1.87  thf(commutativity_k5_xboole_0, axiom,
% 1.65/1.87    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.65/1.87  thf('17', plain,
% 1.65/1.87      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.65/1.87      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.65/1.87  thf('18', plain,
% 1.65/1.87      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_B @ sk_A))),
% 1.65/1.87      inference('demod', [status(thm)], ['13', '16', '17'])).
% 1.65/1.87  thf(t92_xboole_1, axiom,
% 1.65/1.87    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.65/1.87  thf('19', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ X17) = (k1_xboole_0))),
% 1.65/1.87      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.65/1.87  thf(t91_xboole_1, axiom,
% 1.65/1.87    (![A:$i,B:$i,C:$i]:
% 1.65/1.87     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.65/1.87       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.65/1.87  thf('20', plain,
% 1.65/1.87      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.65/1.87         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 1.65/1.87           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 1.65/1.87      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.65/1.87  thf('21', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.65/1.87           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.65/1.87      inference('sup+', [status(thm)], ['19', '20'])).
% 1.65/1.87  thf('22', plain,
% 1.65/1.87      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.65/1.87      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.65/1.87  thf(t5_boole, axiom,
% 1.65/1.87    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.65/1.87  thf('23', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 1.65/1.87      inference('cnf', [status(esa)], [t5_boole])).
% 1.65/1.87  thf('24', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.65/1.87      inference('sup+', [status(thm)], ['22', '23'])).
% 1.65/1.87  thf('25', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.65/1.87      inference('demod', [status(thm)], ['21', '24'])).
% 1.65/1.87  thf('26', plain,
% 1.65/1.87      (((sk_A) = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 1.65/1.87      inference('sup+', [status(thm)], ['18', '25'])).
% 1.65/1.87  thf('27', plain,
% 1.65/1.87      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_B @ sk_A))),
% 1.65/1.87      inference('demod', [status(thm)], ['13', '16', '17'])).
% 1.65/1.87  thf('28', plain,
% 1.65/1.87      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.65/1.87      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.65/1.87  thf('29', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.65/1.87      inference('demod', [status(thm)], ['21', '24'])).
% 1.65/1.87  thf('30', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.65/1.87      inference('sup+', [status(thm)], ['28', '29'])).
% 1.65/1.87  thf('31', plain,
% 1.65/1.87      (((sk_B) = (k5_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 1.65/1.87      inference('sup+', [status(thm)], ['27', '30'])).
% 1.65/1.87  thf('32', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 1.65/1.87      inference('sup-', [status(thm)], ['7', '8'])).
% 1.65/1.87  thf('33', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.65/1.87      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.65/1.87  thf(t112_xboole_1, axiom,
% 1.65/1.87    (![A:$i,B:$i,C:$i]:
% 1.65/1.87     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 1.65/1.87       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 1.65/1.87  thf('34', plain,
% 1.65/1.87      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.65/1.87         ((k5_xboole_0 @ (k3_xboole_0 @ X6 @ X8) @ (k3_xboole_0 @ X7 @ X8))
% 1.65/1.87           = (k3_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8))),
% 1.65/1.87      inference('cnf', [status(esa)], [t112_xboole_1])).
% 1.65/1.87  thf('35', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.87         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X2 @ X1))
% 1.65/1.87           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X2) @ X1))),
% 1.65/1.87      inference('sup+', [status(thm)], ['33', '34'])).
% 1.65/1.87  thf('36', plain,
% 1.65/1.87      (![X0 : $i]:
% 1.65/1.87         ((k5_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_B))
% 1.65/1.87           = (k3_xboole_0 @ (k5_xboole_0 @ sk_A @ X0) @ sk_B))),
% 1.65/1.87      inference('sup+', [status(thm)], ['32', '35'])).
% 1.65/1.87  thf('37', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         ((k4_xboole_0 @ X0 @ X1)
% 1.65/1.87           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.65/1.87      inference('sup+', [status(thm)], ['10', '11'])).
% 1.65/1.87  thf('38', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.65/1.87      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.65/1.87  thf('39', plain,
% 1.65/1.87      (![X0 : $i]:
% 1.65/1.87         ((k4_xboole_0 @ sk_B @ X0)
% 1.65/1.87           = (k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ X0)))),
% 1.65/1.87      inference('demod', [status(thm)], ['36', '37', '38'])).
% 1.65/1.87  thf('40', plain,
% 1.65/1.87      (((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 1.65/1.87         = (k3_xboole_0 @ sk_B @ sk_B))),
% 1.65/1.87      inference('sup+', [status(thm)], ['31', '39'])).
% 1.65/1.87  thf('41', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ X17) = (k1_xboole_0))),
% 1.65/1.87      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.65/1.87  thf('42', plain,
% 1.65/1.87      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.65/1.87         ((k5_xboole_0 @ (k3_xboole_0 @ X6 @ X8) @ (k3_xboole_0 @ X7 @ X8))
% 1.65/1.87           = (k3_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8))),
% 1.65/1.87      inference('cnf', [status(esa)], [t112_xboole_1])).
% 1.65/1.87  thf('43', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         ((k1_xboole_0) = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0))),
% 1.65/1.87      inference('sup+', [status(thm)], ['41', '42'])).
% 1.65/1.87  thf('44', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ X17) = (k1_xboole_0))),
% 1.65/1.87      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.65/1.87  thf('45', plain,
% 1.65/1.87      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 1.65/1.87      inference('demod', [status(thm)], ['43', '44'])).
% 1.65/1.87  thf('46', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.65/1.87      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.65/1.87  thf('47', plain,
% 1.65/1.87      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.65/1.87      inference('sup+', [status(thm)], ['45', '46'])).
% 1.65/1.87  thf('48', plain,
% 1.65/1.87      (![X4 : $i, X5 : $i]:
% 1.65/1.87         ((k4_xboole_0 @ X4 @ X5)
% 1.65/1.87           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.65/1.87      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.65/1.87  thf('49', plain,
% 1.65/1.87      (![X0 : $i]:
% 1.65/1.87         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.65/1.87      inference('sup+', [status(thm)], ['47', '48'])).
% 1.65/1.87  thf('50', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 1.65/1.87      inference('cnf', [status(esa)], [t5_boole])).
% 1.65/1.87  thf('51', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.65/1.87      inference('sup+', [status(thm)], ['49', '50'])).
% 1.65/1.87  thf(t36_xboole_1, axiom,
% 1.65/1.87    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.65/1.87  thf('52', plain,
% 1.65/1.87      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 1.65/1.87      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.65/1.87  thf('53', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.65/1.87      inference('sup+', [status(thm)], ['51', '52'])).
% 1.65/1.87  thf('54', plain,
% 1.65/1.87      (![X9 : $i, X10 : $i]:
% 1.65/1.87         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 1.65/1.87      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.65/1.87  thf('55', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.65/1.87      inference('sup-', [status(thm)], ['53', '54'])).
% 1.65/1.87  thf('56', plain,
% 1.65/1.87      (((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 1.65/1.87      inference('demod', [status(thm)], ['40', '55'])).
% 1.65/1.87  thf('57', plain,
% 1.65/1.87      (![X4 : $i, X5 : $i]:
% 1.65/1.87         ((k4_xboole_0 @ X4 @ X5)
% 1.65/1.87           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.65/1.87      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.65/1.87  thf('58', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.65/1.87      inference('demod', [status(thm)], ['21', '24'])).
% 1.65/1.87  thf('59', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         ((k3_xboole_0 @ X1 @ X0)
% 1.65/1.87           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.65/1.87      inference('sup+', [status(thm)], ['57', '58'])).
% 1.65/1.87  thf('60', plain,
% 1.65/1.87      (((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 1.65/1.87         = (k5_xboole_0 @ sk_B @ sk_B))),
% 1.65/1.87      inference('sup+', [status(thm)], ['56', '59'])).
% 1.65/1.87  thf('61', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ X17) = (k1_xboole_0))),
% 1.65/1.87      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.65/1.87  thf('62', plain,
% 1.65/1.87      (((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 1.65/1.87      inference('demod', [status(thm)], ['60', '61'])).
% 1.65/1.87  thf('63', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         ((k4_xboole_0 @ X0 @ X1)
% 1.65/1.87           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.65/1.87      inference('sup+', [status(thm)], ['10', '11'])).
% 1.65/1.87  thf('64', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.65/1.87      inference('sup+', [status(thm)], ['28', '29'])).
% 1.65/1.87  thf('65', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         ((X1)
% 1.65/1.87           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 1.65/1.87      inference('sup+', [status(thm)], ['63', '64'])).
% 1.65/1.87  thf('66', plain,
% 1.65/1.87      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.65/1.87      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.65/1.87  thf('67', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         ((X1)
% 1.65/1.87           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 1.65/1.87      inference('demod', [status(thm)], ['65', '66'])).
% 1.65/1.87  thf('68', plain,
% 1.65/1.87      (((k3_subset_1 @ sk_A @ sk_B)
% 1.65/1.87         = (k5_xboole_0 @ (k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B) @ 
% 1.65/1.87            k1_xboole_0))),
% 1.65/1.87      inference('sup+', [status(thm)], ['62', '67'])).
% 1.65/1.87  thf('69', plain,
% 1.65/1.87      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.65/1.87      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.65/1.87  thf('70', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.65/1.87      inference('sup+', [status(thm)], ['22', '23'])).
% 1.65/1.87  thf('71', plain,
% 1.65/1.87      (((k3_subset_1 @ sk_A @ sk_B)
% 1.65/1.87         = (k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 1.65/1.87      inference('demod', [status(thm)], ['68', '69', '70'])).
% 1.65/1.87  thf('72', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.65/1.87      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.65/1.87  thf(t94_xboole_1, axiom,
% 1.65/1.87    (![A:$i,B:$i]:
% 1.65/1.87     ( ( k2_xboole_0 @ A @ B ) =
% 1.65/1.87       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.65/1.87  thf('73', plain,
% 1.65/1.87      (![X18 : $i, X19 : $i]:
% 1.65/1.87         ((k2_xboole_0 @ X18 @ X19)
% 1.65/1.87           = (k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ 
% 1.65/1.87              (k3_xboole_0 @ X18 @ X19)))),
% 1.65/1.87      inference('cnf', [status(esa)], [t94_xboole_1])).
% 1.65/1.87  thf(l51_zfmisc_1, axiom,
% 1.65/1.87    (![A:$i,B:$i]:
% 1.65/1.87     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.65/1.87  thf('74', plain,
% 1.65/1.87      (![X52 : $i, X53 : $i]:
% 1.65/1.87         ((k3_tarski @ (k2_tarski @ X52 @ X53)) = (k2_xboole_0 @ X52 @ X53))),
% 1.65/1.87      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.65/1.87  thf('75', plain,
% 1.65/1.87      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.65/1.87         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 1.65/1.87           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 1.65/1.87      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.65/1.87  thf('76', plain,
% 1.65/1.87      (![X18 : $i, X19 : $i]:
% 1.65/1.87         ((k3_tarski @ (k2_tarski @ X18 @ X19))
% 1.65/1.87           = (k5_xboole_0 @ X18 @ 
% 1.65/1.87              (k5_xboole_0 @ X19 @ (k3_xboole_0 @ X18 @ X19))))),
% 1.65/1.87      inference('demod', [status(thm)], ['73', '74', '75'])).
% 1.65/1.87  thf('77', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         ((k3_tarski @ (k2_tarski @ X0 @ X1))
% 1.65/1.87           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 1.65/1.87      inference('sup+', [status(thm)], ['72', '76'])).
% 1.65/1.87  thf('78', plain,
% 1.65/1.87      (![X4 : $i, X5 : $i]:
% 1.65/1.87         ((k4_xboole_0 @ X4 @ X5)
% 1.65/1.87           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.65/1.87      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.65/1.87  thf('79', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         ((k3_tarski @ (k2_tarski @ X0 @ X1))
% 1.65/1.87           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.65/1.87      inference('demod', [status(thm)], ['77', '78'])).
% 1.65/1.87  thf('80', plain,
% 1.65/1.87      (((k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 1.65/1.87         = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 1.65/1.87      inference('sup+', [status(thm)], ['71', '79'])).
% 1.65/1.87  thf('81', plain,
% 1.65/1.87      (((k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) = (sk_A))),
% 1.65/1.87      inference('sup+', [status(thm)], ['26', '80'])).
% 1.65/1.87  thf('82', plain,
% 1.65/1.87      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 1.65/1.87         != (k2_subset_1 @ sk_A))),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.65/1.87  thf('83', plain, (![X57 : $i]: ((k2_subset_1 @ X57) = (X57))),
% 1.65/1.87      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.65/1.87  thf('84', plain,
% 1.65/1.87      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 1.65/1.87      inference('demod', [status(thm)], ['82', '83'])).
% 1.65/1.87  thf('85', plain,
% 1.65/1.87      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 1.65/1.87      inference('sup-', [status(thm)], ['14', '15'])).
% 1.65/1.87  thf('86', plain,
% 1.65/1.87      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 1.65/1.87      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.65/1.87  thf('87', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A)),
% 1.65/1.87      inference('sup+', [status(thm)], ['85', '86'])).
% 1.65/1.87  thf('88', plain,
% 1.65/1.87      (![X47 : $i, X48 : $i, X49 : $i]:
% 1.65/1.87         (~ (r1_tarski @ X47 @ X48)
% 1.65/1.87          | (r2_hidden @ X47 @ X49)
% 1.65/1.87          | ((X49) != (k1_zfmisc_1 @ X48)))),
% 1.65/1.87      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.65/1.87  thf('89', plain,
% 1.65/1.87      (![X47 : $i, X48 : $i]:
% 1.65/1.87         ((r2_hidden @ X47 @ (k1_zfmisc_1 @ X48)) | ~ (r1_tarski @ X47 @ X48))),
% 1.65/1.87      inference('simplify', [status(thm)], ['88'])).
% 1.65/1.87  thf('90', plain,
% 1.65/1.87      ((r2_hidden @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 1.65/1.87      inference('sup-', [status(thm)], ['87', '89'])).
% 1.65/1.87  thf('91', plain,
% 1.65/1.87      (![X54 : $i, X55 : $i]:
% 1.65/1.87         (~ (r2_hidden @ X54 @ X55)
% 1.65/1.87          | (m1_subset_1 @ X54 @ X55)
% 1.65/1.87          | (v1_xboole_0 @ X55))),
% 1.65/1.87      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.65/1.87  thf('92', plain,
% 1.65/1.87      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 1.65/1.87        | (m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 1.65/1.87      inference('sup-', [status(thm)], ['90', '91'])).
% 1.65/1.87  thf('93', plain, (![X60 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X60))),
% 1.65/1.87      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.65/1.87  thf('94', plain,
% 1.65/1.87      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 1.65/1.87      inference('clc', [status(thm)], ['92', '93'])).
% 1.65/1.87  thf('95', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf(redefinition_k4_subset_1, axiom,
% 1.65/1.87    (![A:$i,B:$i,C:$i]:
% 1.65/1.87     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.65/1.87         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.65/1.87       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.65/1.87  thf('96', plain,
% 1.65/1.87      (![X61 : $i, X62 : $i, X63 : $i]:
% 1.65/1.87         (~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ X62))
% 1.65/1.87          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ X62))
% 1.65/1.87          | ((k4_subset_1 @ X62 @ X61 @ X63) = (k2_xboole_0 @ X61 @ X63)))),
% 1.65/1.87      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.65/1.87  thf('97', plain,
% 1.65/1.87      (![X52 : $i, X53 : $i]:
% 1.65/1.87         ((k3_tarski @ (k2_tarski @ X52 @ X53)) = (k2_xboole_0 @ X52 @ X53))),
% 1.65/1.87      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.65/1.87  thf('98', plain,
% 1.65/1.87      (![X61 : $i, X62 : $i, X63 : $i]:
% 1.65/1.87         (~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ X62))
% 1.65/1.87          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ X62))
% 1.65/1.87          | ((k4_subset_1 @ X62 @ X61 @ X63)
% 1.65/1.87              = (k3_tarski @ (k2_tarski @ X61 @ X63))))),
% 1.65/1.87      inference('demod', [status(thm)], ['96', '97'])).
% 1.65/1.87  thf('99', plain,
% 1.65/1.87      (![X0 : $i]:
% 1.65/1.87         (((k4_subset_1 @ sk_A @ sk_B @ X0)
% 1.65/1.87            = (k3_tarski @ (k2_tarski @ sk_B @ X0)))
% 1.65/1.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 1.65/1.87      inference('sup-', [status(thm)], ['95', '98'])).
% 1.65/1.87  thf('100', plain,
% 1.65/1.87      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 1.65/1.87         = (k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 1.65/1.87      inference('sup-', [status(thm)], ['94', '99'])).
% 1.65/1.87  thf('101', plain,
% 1.65/1.87      (((k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 1.65/1.87         != (sk_A))),
% 1.65/1.87      inference('demod', [status(thm)], ['84', '100'])).
% 1.65/1.87  thf('102', plain, ($false),
% 1.65/1.87      inference('simplify_reflect-', [status(thm)], ['81', '101'])).
% 1.65/1.87  
% 1.65/1.87  % SZS output end Refutation
% 1.65/1.87  
% 1.65/1.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

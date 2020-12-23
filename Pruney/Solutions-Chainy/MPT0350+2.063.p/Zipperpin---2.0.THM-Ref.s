%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BHwoWTz8tD

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:54 EST 2020

% Result     : Theorem 1.89s
% Output     : Refutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 332 expanded)
%              Number of leaves         :   37 ( 120 expanded)
%              Depth                    :   18
%              Number of atoms          :  970 (2439 expanded)
%              Number of equality atoms :  101 ( 272 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ! [X58: $i,X59: $i] :
      ( ~ ( m1_subset_1 @ X58 @ X59 )
      | ( r2_hidden @ X58 @ X59 )
      | ( v1_xboole_0 @ X59 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X64: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X64 ) ) ),
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
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( r2_hidden @ X54 @ X53 )
      | ( r1_tarski @ X54 @ X52 )
      | ( X53
       != ( k1_zfmisc_1 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('6',plain,(
    ! [X52: $i,X54: $i] :
      ( ( r1_tarski @ X54 @ X52 )
      | ~ ( r2_hidden @ X54 @ ( k1_zfmisc_1 @ X52 ) ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
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
    ! [X62: $i,X63: $i] :
      ( ( ( k3_subset_1 @ X62 @ X63 )
        = ( k4_xboole_0 @ X62 @ X63 ) )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ X62 ) ) ) ),
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

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('19',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('20',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('23',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X56: $i,X57: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X56 @ X57 ) )
      = ( k2_xboole_0 @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('25',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) )
      = X10 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('27',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('28',plain,(
    ! [X56: $i,X57: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X56 @ X57 ) )
      = ( k2_xboole_0 @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('29',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k3_tarski @ ( k2_tarski @ X16 @ X17 ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','30'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('32',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('35',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['18','37'])).

thf('39',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','16','17'])).

thf('40',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,
    ( sk_B
    = ( k5_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('44',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('46',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X7 @ X9 ) @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['43','51'])).

thf('53',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('54',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','30'])).

thf('60',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['60','65'])).

thf('67',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('69',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('71',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('72',plain,(
    ! [X56: $i,X57: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X56 @ X57 ) )
      = ( k2_xboole_0 @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('73',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('74',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X22 @ X23 ) )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['70','74'])).

thf('76',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['69','77'])).

thf('79',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
    = sk_A ),
    inference('sup+',[status(thm)],['38','78'])).

thf('80',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('81',plain,(
    ! [X61: $i] :
      ( ( k2_subset_1 @ X61 )
      = X61 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('82',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('84',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('85',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( r1_tarski @ X51 @ X52 )
      | ( r2_hidden @ X51 @ X53 )
      | ( X53
       != ( k1_zfmisc_1 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('87',plain,(
    ! [X51: $i,X52: $i] :
      ( ( r2_hidden @ X51 @ ( k1_zfmisc_1 @ X52 ) )
      | ~ ( r1_tarski @ X51 @ X52 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    r2_hidden @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['85','87'])).

thf('89',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( r2_hidden @ X58 @ X59 )
      | ( m1_subset_1 @ X58 @ X59 )
      | ( v1_xboole_0 @ X59 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('90',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X64: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('92',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('94',plain,(
    ! [X65: $i,X66: $i,X67: $i] :
      ( ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ X66 ) )
      | ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ X66 ) )
      | ( ( k4_subset_1 @ X66 @ X65 @ X67 )
        = ( k2_xboole_0 @ X65 @ X67 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('95',plain,(
    ! [X56: $i,X57: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X56 @ X57 ) )
      = ( k2_xboole_0 @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('96',plain,(
    ! [X65: $i,X66: $i,X67: $i] :
      ( ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ X66 ) )
      | ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ X66 ) )
      | ( ( k4_subset_1 @ X66 @ X65 @ X67 )
        = ( k3_tarski @ ( k2_tarski @ X65 @ X67 ) ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['92','97'])).

thf('99',plain,(
    ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
 != sk_A ),
    inference(demod,[status(thm)],['82','98'])).

thf('100',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['79','99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BHwoWTz8tD
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:44:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.89/2.11  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.89/2.11  % Solved by: fo/fo7.sh
% 1.89/2.11  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.89/2.11  % done 2550 iterations in 1.653s
% 1.89/2.11  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.89/2.11  % SZS output start Refutation
% 1.89/2.11  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.89/2.11  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.89/2.11  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.89/2.11  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.89/2.11  thf(sk_A_type, type, sk_A: $i).
% 1.89/2.11  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.89/2.11  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.89/2.11  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.89/2.11  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.89/2.11  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.89/2.11  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.89/2.11  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.89/2.11  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.89/2.11  thf(sk_B_type, type, sk_B: $i).
% 1.89/2.11  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.89/2.11  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.89/2.11  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.89/2.11  thf(t25_subset_1, conjecture,
% 1.89/2.11    (![A:$i,B:$i]:
% 1.89/2.11     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.89/2.11       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 1.89/2.11         ( k2_subset_1 @ A ) ) ))).
% 1.89/2.11  thf(zf_stmt_0, negated_conjecture,
% 1.89/2.11    (~( ![A:$i,B:$i]:
% 1.89/2.11        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.89/2.11          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 1.89/2.11            ( k2_subset_1 @ A ) ) ) )),
% 1.89/2.11    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 1.89/2.11  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.89/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.11  thf(d2_subset_1, axiom,
% 1.89/2.11    (![A:$i,B:$i]:
% 1.89/2.11     ( ( ( v1_xboole_0 @ A ) =>
% 1.89/2.11         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.89/2.11       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.89/2.11         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.89/2.11  thf('1', plain,
% 1.89/2.11      (![X58 : $i, X59 : $i]:
% 1.89/2.11         (~ (m1_subset_1 @ X58 @ X59)
% 1.89/2.11          | (r2_hidden @ X58 @ X59)
% 1.89/2.11          | (v1_xboole_0 @ X59))),
% 1.89/2.11      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.89/2.11  thf('2', plain,
% 1.89/2.11      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 1.89/2.11        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 1.89/2.11      inference('sup-', [status(thm)], ['0', '1'])).
% 1.89/2.11  thf(fc1_subset_1, axiom,
% 1.89/2.11    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.89/2.11  thf('3', plain, (![X64 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X64))),
% 1.89/2.11      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.89/2.11  thf('4', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.89/2.11      inference('clc', [status(thm)], ['2', '3'])).
% 1.89/2.11  thf(d1_zfmisc_1, axiom,
% 1.89/2.11    (![A:$i,B:$i]:
% 1.89/2.11     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 1.89/2.11       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 1.89/2.11  thf('5', plain,
% 1.89/2.11      (![X52 : $i, X53 : $i, X54 : $i]:
% 1.89/2.11         (~ (r2_hidden @ X54 @ X53)
% 1.89/2.11          | (r1_tarski @ X54 @ X52)
% 1.89/2.11          | ((X53) != (k1_zfmisc_1 @ X52)))),
% 1.89/2.11      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.89/2.11  thf('6', plain,
% 1.89/2.11      (![X52 : $i, X54 : $i]:
% 1.89/2.11         ((r1_tarski @ X54 @ X52) | ~ (r2_hidden @ X54 @ (k1_zfmisc_1 @ X52)))),
% 1.89/2.11      inference('simplify', [status(thm)], ['5'])).
% 1.89/2.11  thf('7', plain, ((r1_tarski @ sk_B @ sk_A)),
% 1.89/2.11      inference('sup-', [status(thm)], ['4', '6'])).
% 1.89/2.11  thf(t28_xboole_1, axiom,
% 1.89/2.11    (![A:$i,B:$i]:
% 1.89/2.11     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.89/2.11  thf('8', plain,
% 1.89/2.11      (![X12 : $i, X13 : $i]:
% 1.89/2.11         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 1.89/2.11      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.89/2.11  thf('9', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 1.89/2.11      inference('sup-', [status(thm)], ['7', '8'])).
% 1.89/2.11  thf(commutativity_k3_xboole_0, axiom,
% 1.89/2.11    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.89/2.11  thf('10', plain,
% 1.89/2.11      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.89/2.11      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.89/2.11  thf(t100_xboole_1, axiom,
% 1.89/2.11    (![A:$i,B:$i]:
% 1.89/2.11     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.89/2.11  thf('11', plain,
% 1.89/2.11      (![X5 : $i, X6 : $i]:
% 1.89/2.11         ((k4_xboole_0 @ X5 @ X6)
% 1.89/2.11           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.89/2.11      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.89/2.11  thf('12', plain,
% 1.89/2.11      (![X0 : $i, X1 : $i]:
% 1.89/2.11         ((k4_xboole_0 @ X0 @ X1)
% 1.89/2.11           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.89/2.11      inference('sup+', [status(thm)], ['10', '11'])).
% 1.89/2.11  thf('13', plain,
% 1.89/2.11      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 1.89/2.11      inference('sup+', [status(thm)], ['9', '12'])).
% 1.89/2.11  thf('14', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.89/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.11  thf(d5_subset_1, axiom,
% 1.89/2.11    (![A:$i,B:$i]:
% 1.89/2.11     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.89/2.11       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.89/2.11  thf('15', plain,
% 1.89/2.11      (![X62 : $i, X63 : $i]:
% 1.89/2.11         (((k3_subset_1 @ X62 @ X63) = (k4_xboole_0 @ X62 @ X63))
% 1.89/2.11          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ X62)))),
% 1.89/2.11      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.89/2.11  thf('16', plain,
% 1.89/2.11      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 1.89/2.11      inference('sup-', [status(thm)], ['14', '15'])).
% 1.89/2.11  thf(commutativity_k5_xboole_0, axiom,
% 1.89/2.11    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.89/2.11  thf('17', plain,
% 1.89/2.11      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.89/2.11      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.89/2.11  thf('18', plain,
% 1.89/2.11      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_B @ sk_A))),
% 1.89/2.11      inference('demod', [status(thm)], ['13', '16', '17'])).
% 1.89/2.11  thf(idempotence_k3_xboole_0, axiom,
% 1.89/2.11    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.89/2.11  thf('19', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 1.89/2.11      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.89/2.11  thf('20', plain,
% 1.89/2.11      (![X5 : $i, X6 : $i]:
% 1.89/2.11         ((k4_xboole_0 @ X5 @ X6)
% 1.89/2.11           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.89/2.11      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.89/2.11  thf('21', plain,
% 1.89/2.11      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.89/2.11      inference('sup+', [status(thm)], ['19', '20'])).
% 1.89/2.11  thf('22', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 1.89/2.11      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.89/2.11  thf(t22_xboole_1, axiom,
% 1.89/2.11    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 1.89/2.11  thf('23', plain,
% 1.89/2.11      (![X10 : $i, X11 : $i]:
% 1.89/2.11         ((k2_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)) = (X10))),
% 1.89/2.11      inference('cnf', [status(esa)], [t22_xboole_1])).
% 1.89/2.11  thf(l51_zfmisc_1, axiom,
% 1.89/2.11    (![A:$i,B:$i]:
% 1.89/2.11     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.89/2.11  thf('24', plain,
% 1.89/2.11      (![X56 : $i, X57 : $i]:
% 1.89/2.11         ((k3_tarski @ (k2_tarski @ X56 @ X57)) = (k2_xboole_0 @ X56 @ X57))),
% 1.89/2.11      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.89/2.11  thf('25', plain,
% 1.89/2.11      (![X10 : $i, X11 : $i]:
% 1.89/2.11         ((k3_tarski @ (k2_tarski @ X10 @ (k3_xboole_0 @ X10 @ X11))) = (X10))),
% 1.89/2.11      inference('demod', [status(thm)], ['23', '24'])).
% 1.89/2.11  thf('26', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 1.89/2.11      inference('sup+', [status(thm)], ['22', '25'])).
% 1.89/2.11  thf(t46_xboole_1, axiom,
% 1.89/2.11    (![A:$i,B:$i]:
% 1.89/2.11     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 1.89/2.11  thf('27', plain,
% 1.89/2.11      (![X16 : $i, X17 : $i]:
% 1.89/2.11         ((k4_xboole_0 @ X16 @ (k2_xboole_0 @ X16 @ X17)) = (k1_xboole_0))),
% 1.89/2.11      inference('cnf', [status(esa)], [t46_xboole_1])).
% 1.89/2.11  thf('28', plain,
% 1.89/2.11      (![X56 : $i, X57 : $i]:
% 1.89/2.11         ((k3_tarski @ (k2_tarski @ X56 @ X57)) = (k2_xboole_0 @ X56 @ X57))),
% 1.89/2.11      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.89/2.11  thf('29', plain,
% 1.89/2.11      (![X16 : $i, X17 : $i]:
% 1.89/2.11         ((k4_xboole_0 @ X16 @ (k3_tarski @ (k2_tarski @ X16 @ X17)))
% 1.89/2.11           = (k1_xboole_0))),
% 1.89/2.11      inference('demod', [status(thm)], ['27', '28'])).
% 1.89/2.11  thf('30', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.89/2.11      inference('sup+', [status(thm)], ['26', '29'])).
% 1.89/2.11  thf('31', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 1.89/2.11      inference('demod', [status(thm)], ['21', '30'])).
% 1.89/2.11  thf(t91_xboole_1, axiom,
% 1.89/2.11    (![A:$i,B:$i,C:$i]:
% 1.89/2.11     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.89/2.11       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.89/2.11  thf('32', plain,
% 1.89/2.11      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.89/2.11         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 1.89/2.11           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 1.89/2.11      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.89/2.11  thf('33', plain,
% 1.89/2.11      (![X0 : $i, X1 : $i]:
% 1.89/2.11         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.89/2.11           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.89/2.11      inference('sup+', [status(thm)], ['31', '32'])).
% 1.89/2.11  thf('34', plain,
% 1.89/2.11      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.89/2.11      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.89/2.11  thf(t5_boole, axiom,
% 1.89/2.11    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.89/2.11  thf('35', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 1.89/2.11      inference('cnf', [status(esa)], [t5_boole])).
% 1.89/2.11  thf('36', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.89/2.11      inference('sup+', [status(thm)], ['34', '35'])).
% 1.89/2.11  thf('37', plain,
% 1.89/2.11      (![X0 : $i, X1 : $i]:
% 1.89/2.11         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.89/2.11      inference('demod', [status(thm)], ['33', '36'])).
% 1.89/2.11  thf('38', plain,
% 1.89/2.11      (((sk_A) = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 1.89/2.11      inference('sup+', [status(thm)], ['18', '37'])).
% 1.89/2.11  thf('39', plain,
% 1.89/2.11      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_B @ sk_A))),
% 1.89/2.11      inference('demod', [status(thm)], ['13', '16', '17'])).
% 1.89/2.11  thf('40', plain,
% 1.89/2.11      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.89/2.11      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.89/2.11  thf('41', plain,
% 1.89/2.11      (![X0 : $i, X1 : $i]:
% 1.89/2.11         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.89/2.11      inference('demod', [status(thm)], ['33', '36'])).
% 1.89/2.11  thf('42', plain,
% 1.89/2.11      (![X0 : $i, X1 : $i]:
% 1.89/2.11         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.89/2.11      inference('sup+', [status(thm)], ['40', '41'])).
% 1.89/2.11  thf('43', plain,
% 1.89/2.11      (((sk_B) = (k5_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 1.89/2.11      inference('sup+', [status(thm)], ['39', '42'])).
% 1.89/2.11  thf('44', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 1.89/2.11      inference('sup-', [status(thm)], ['7', '8'])).
% 1.89/2.11  thf('45', plain,
% 1.89/2.11      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.89/2.11      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.89/2.11  thf(t112_xboole_1, axiom,
% 1.89/2.11    (![A:$i,B:$i,C:$i]:
% 1.89/2.11     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 1.89/2.11       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 1.89/2.11  thf('46', plain,
% 1.89/2.11      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.89/2.11         ((k5_xboole_0 @ (k3_xboole_0 @ X7 @ X9) @ (k3_xboole_0 @ X8 @ X9))
% 1.89/2.11           = (k3_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9))),
% 1.89/2.11      inference('cnf', [status(esa)], [t112_xboole_1])).
% 1.89/2.11  thf('47', plain,
% 1.89/2.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.89/2.11         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X2 @ X1))
% 1.89/2.11           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X2) @ X1))),
% 1.89/2.11      inference('sup+', [status(thm)], ['45', '46'])).
% 1.89/2.11  thf('48', plain,
% 1.89/2.11      (![X0 : $i]:
% 1.89/2.11         ((k5_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_B))
% 1.89/2.11           = (k3_xboole_0 @ (k5_xboole_0 @ sk_A @ X0) @ sk_B))),
% 1.89/2.11      inference('sup+', [status(thm)], ['44', '47'])).
% 1.89/2.11  thf('49', plain,
% 1.89/2.11      (![X0 : $i, X1 : $i]:
% 1.89/2.11         ((k4_xboole_0 @ X0 @ X1)
% 1.89/2.11           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.89/2.11      inference('sup+', [status(thm)], ['10', '11'])).
% 1.89/2.11  thf('50', plain,
% 1.89/2.11      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.89/2.11      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.89/2.11  thf('51', plain,
% 1.89/2.11      (![X0 : $i]:
% 1.89/2.11         ((k4_xboole_0 @ sk_B @ X0)
% 1.89/2.11           = (k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ X0)))),
% 1.89/2.11      inference('demod', [status(thm)], ['48', '49', '50'])).
% 1.89/2.11  thf('52', plain,
% 1.89/2.11      (((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 1.89/2.11         = (k3_xboole_0 @ sk_B @ sk_B))),
% 1.89/2.11      inference('sup+', [status(thm)], ['43', '51'])).
% 1.89/2.11  thf('53', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 1.89/2.11      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.89/2.11  thf('54', plain,
% 1.89/2.11      (((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 1.89/2.11      inference('demod', [status(thm)], ['52', '53'])).
% 1.89/2.11  thf('55', plain,
% 1.89/2.11      (![X5 : $i, X6 : $i]:
% 1.89/2.11         ((k4_xboole_0 @ X5 @ X6)
% 1.89/2.11           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.89/2.11      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.89/2.11  thf('56', plain,
% 1.89/2.11      (![X0 : $i, X1 : $i]:
% 1.89/2.11         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.89/2.11      inference('demod', [status(thm)], ['33', '36'])).
% 1.89/2.11  thf('57', plain,
% 1.89/2.11      (![X0 : $i, X1 : $i]:
% 1.89/2.11         ((k3_xboole_0 @ X1 @ X0)
% 1.89/2.11           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.89/2.11      inference('sup+', [status(thm)], ['55', '56'])).
% 1.89/2.11  thf('58', plain,
% 1.89/2.11      (((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 1.89/2.11         = (k5_xboole_0 @ sk_B @ sk_B))),
% 1.89/2.11      inference('sup+', [status(thm)], ['54', '57'])).
% 1.89/2.11  thf('59', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 1.89/2.11      inference('demod', [status(thm)], ['21', '30'])).
% 1.89/2.11  thf('60', plain,
% 1.89/2.11      (((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 1.89/2.11      inference('demod', [status(thm)], ['58', '59'])).
% 1.89/2.11  thf('61', plain,
% 1.89/2.11      (![X0 : $i, X1 : $i]:
% 1.89/2.11         ((k4_xboole_0 @ X0 @ X1)
% 1.89/2.11           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.89/2.11      inference('sup+', [status(thm)], ['10', '11'])).
% 1.89/2.11  thf('62', plain,
% 1.89/2.11      (![X0 : $i, X1 : $i]:
% 1.89/2.11         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.89/2.11      inference('sup+', [status(thm)], ['40', '41'])).
% 1.89/2.11  thf('63', plain,
% 1.89/2.11      (![X0 : $i, X1 : $i]:
% 1.89/2.11         ((X1)
% 1.89/2.11           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 1.89/2.11      inference('sup+', [status(thm)], ['61', '62'])).
% 1.89/2.11  thf('64', plain,
% 1.89/2.11      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.89/2.11      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.89/2.11  thf('65', plain,
% 1.89/2.11      (![X0 : $i, X1 : $i]:
% 1.89/2.11         ((X1)
% 1.89/2.11           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 1.89/2.11      inference('demod', [status(thm)], ['63', '64'])).
% 1.89/2.11  thf('66', plain,
% 1.89/2.11      (((k3_subset_1 @ sk_A @ sk_B)
% 1.89/2.11         = (k5_xboole_0 @ (k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B) @ 
% 1.89/2.11            k1_xboole_0))),
% 1.89/2.11      inference('sup+', [status(thm)], ['60', '65'])).
% 1.89/2.11  thf('67', plain,
% 1.89/2.11      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.89/2.11      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.89/2.11  thf('68', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.89/2.11      inference('sup+', [status(thm)], ['34', '35'])).
% 1.89/2.11  thf('69', plain,
% 1.89/2.11      (((k3_subset_1 @ sk_A @ sk_B)
% 1.89/2.11         = (k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 1.89/2.11      inference('demod', [status(thm)], ['66', '67', '68'])).
% 1.89/2.11  thf('70', plain,
% 1.89/2.11      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.89/2.11      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.89/2.11  thf(t94_xboole_1, axiom,
% 1.89/2.11    (![A:$i,B:$i]:
% 1.89/2.11     ( ( k2_xboole_0 @ A @ B ) =
% 1.89/2.11       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.89/2.11  thf('71', plain,
% 1.89/2.11      (![X22 : $i, X23 : $i]:
% 1.89/2.11         ((k2_xboole_0 @ X22 @ X23)
% 1.89/2.11           = (k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ 
% 1.89/2.11              (k3_xboole_0 @ X22 @ X23)))),
% 1.89/2.11      inference('cnf', [status(esa)], [t94_xboole_1])).
% 1.89/2.11  thf('72', plain,
% 1.89/2.11      (![X56 : $i, X57 : $i]:
% 1.89/2.11         ((k3_tarski @ (k2_tarski @ X56 @ X57)) = (k2_xboole_0 @ X56 @ X57))),
% 1.89/2.11      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.89/2.11  thf('73', plain,
% 1.89/2.11      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.89/2.11         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 1.89/2.11           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 1.89/2.11      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.89/2.11  thf('74', plain,
% 1.89/2.11      (![X22 : $i, X23 : $i]:
% 1.89/2.11         ((k3_tarski @ (k2_tarski @ X22 @ X23))
% 1.89/2.11           = (k5_xboole_0 @ X22 @ 
% 1.89/2.11              (k5_xboole_0 @ X23 @ (k3_xboole_0 @ X22 @ X23))))),
% 1.89/2.11      inference('demod', [status(thm)], ['71', '72', '73'])).
% 1.89/2.11  thf('75', plain,
% 1.89/2.11      (![X0 : $i, X1 : $i]:
% 1.89/2.11         ((k3_tarski @ (k2_tarski @ X0 @ X1))
% 1.89/2.11           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 1.89/2.11      inference('sup+', [status(thm)], ['70', '74'])).
% 1.89/2.11  thf('76', plain,
% 1.89/2.11      (![X5 : $i, X6 : $i]:
% 1.89/2.11         ((k4_xboole_0 @ X5 @ X6)
% 1.89/2.11           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.89/2.11      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.89/2.11  thf('77', plain,
% 1.89/2.11      (![X0 : $i, X1 : $i]:
% 1.89/2.11         ((k3_tarski @ (k2_tarski @ X0 @ X1))
% 1.89/2.11           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.89/2.11      inference('demod', [status(thm)], ['75', '76'])).
% 1.89/2.11  thf('78', plain,
% 1.89/2.11      (((k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 1.89/2.11         = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 1.89/2.11      inference('sup+', [status(thm)], ['69', '77'])).
% 1.89/2.11  thf('79', plain,
% 1.89/2.11      (((k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) = (sk_A))),
% 1.89/2.11      inference('sup+', [status(thm)], ['38', '78'])).
% 1.89/2.11  thf('80', plain,
% 1.89/2.11      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 1.89/2.11         != (k2_subset_1 @ sk_A))),
% 1.89/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.11  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.89/2.11  thf('81', plain, (![X61 : $i]: ((k2_subset_1 @ X61) = (X61))),
% 1.89/2.11      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.89/2.11  thf('82', plain,
% 1.89/2.11      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 1.89/2.11      inference('demod', [status(thm)], ['80', '81'])).
% 1.89/2.11  thf('83', plain,
% 1.89/2.11      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 1.89/2.11      inference('sup-', [status(thm)], ['14', '15'])).
% 1.89/2.11  thf(t36_xboole_1, axiom,
% 1.89/2.11    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.89/2.11  thf('84', plain,
% 1.89/2.11      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 1.89/2.11      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.89/2.11  thf('85', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A)),
% 1.89/2.11      inference('sup+', [status(thm)], ['83', '84'])).
% 1.89/2.11  thf('86', plain,
% 1.89/2.11      (![X51 : $i, X52 : $i, X53 : $i]:
% 1.89/2.11         (~ (r1_tarski @ X51 @ X52)
% 1.89/2.11          | (r2_hidden @ X51 @ X53)
% 1.89/2.11          | ((X53) != (k1_zfmisc_1 @ X52)))),
% 1.89/2.11      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.89/2.11  thf('87', plain,
% 1.89/2.11      (![X51 : $i, X52 : $i]:
% 1.89/2.11         ((r2_hidden @ X51 @ (k1_zfmisc_1 @ X52)) | ~ (r1_tarski @ X51 @ X52))),
% 1.89/2.11      inference('simplify', [status(thm)], ['86'])).
% 1.89/2.11  thf('88', plain,
% 1.89/2.11      ((r2_hidden @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 1.89/2.11      inference('sup-', [status(thm)], ['85', '87'])).
% 1.89/2.11  thf('89', plain,
% 1.89/2.11      (![X58 : $i, X59 : $i]:
% 1.89/2.11         (~ (r2_hidden @ X58 @ X59)
% 1.89/2.11          | (m1_subset_1 @ X58 @ X59)
% 1.89/2.11          | (v1_xboole_0 @ X59))),
% 1.89/2.11      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.89/2.11  thf('90', plain,
% 1.89/2.11      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 1.89/2.11        | (m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 1.89/2.11      inference('sup-', [status(thm)], ['88', '89'])).
% 1.89/2.11  thf('91', plain, (![X64 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X64))),
% 1.89/2.11      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.89/2.11  thf('92', plain,
% 1.89/2.11      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 1.89/2.11      inference('clc', [status(thm)], ['90', '91'])).
% 1.89/2.11  thf('93', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.89/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.89/2.11  thf(redefinition_k4_subset_1, axiom,
% 1.89/2.11    (![A:$i,B:$i,C:$i]:
% 1.89/2.11     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.89/2.11         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.89/2.11       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.89/2.11  thf('94', plain,
% 1.89/2.11      (![X65 : $i, X66 : $i, X67 : $i]:
% 1.89/2.11         (~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ X66))
% 1.89/2.11          | ~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ X66))
% 1.89/2.11          | ((k4_subset_1 @ X66 @ X65 @ X67) = (k2_xboole_0 @ X65 @ X67)))),
% 1.89/2.11      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.89/2.11  thf('95', plain,
% 1.89/2.11      (![X56 : $i, X57 : $i]:
% 1.89/2.11         ((k3_tarski @ (k2_tarski @ X56 @ X57)) = (k2_xboole_0 @ X56 @ X57))),
% 1.89/2.11      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.89/2.11  thf('96', plain,
% 1.89/2.11      (![X65 : $i, X66 : $i, X67 : $i]:
% 1.89/2.11         (~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ X66))
% 1.89/2.11          | ~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ X66))
% 1.89/2.11          | ((k4_subset_1 @ X66 @ X65 @ X67)
% 1.89/2.11              = (k3_tarski @ (k2_tarski @ X65 @ X67))))),
% 1.89/2.11      inference('demod', [status(thm)], ['94', '95'])).
% 1.89/2.11  thf('97', plain,
% 1.89/2.11      (![X0 : $i]:
% 1.89/2.11         (((k4_subset_1 @ sk_A @ sk_B @ X0)
% 1.89/2.11            = (k3_tarski @ (k2_tarski @ sk_B @ X0)))
% 1.89/2.11          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 1.89/2.11      inference('sup-', [status(thm)], ['93', '96'])).
% 1.89/2.11  thf('98', plain,
% 1.89/2.11      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 1.89/2.11         = (k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 1.89/2.11      inference('sup-', [status(thm)], ['92', '97'])).
% 1.89/2.11  thf('99', plain,
% 1.89/2.11      (((k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 1.89/2.11         != (sk_A))),
% 1.89/2.11      inference('demod', [status(thm)], ['82', '98'])).
% 1.89/2.11  thf('100', plain, ($false),
% 1.89/2.11      inference('simplify_reflect-', [status(thm)], ['79', '99'])).
% 1.89/2.11  
% 1.89/2.11  % SZS output end Refutation
% 1.89/2.11  
% 1.97/2.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

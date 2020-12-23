%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pFAi1d5gyr

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:33 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 387 expanded)
%              Number of leaves         :   28 ( 120 expanded)
%              Depth                    :   16
%              Number of atoms          :  739 (3112 expanded)
%              Number of equality atoms :   85 ( 341 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t39_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
      <=> ( B
          = ( k2_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
        <=> ( B
            = ( k2_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_subset_1])).

thf('0',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      = ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('7',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('10',plain,(
    ! [X26: $i] :
      ( ( k2_subset_1 @ X26 )
      = X26 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('11',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('16',plain,
    ( ( ( k3_subset_1 @ sk_A @ sk_A )
      = ( k4_xboole_0 @ sk_A @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('23',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k3_subset_1 @ sk_A @ sk_A )
      = k1_xboole_0 )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','24'])).

thf('26',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('27',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf('28',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('30',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_A ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('33',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','34'])).

thf('36',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sat_resolution*',[status(thm)],['9','35','36'])).

thf('38',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['7','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('41',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('43',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','41','42'])).

thf('44',plain,(
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

thf('45',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ X24 )
      | ( r2_hidden @ X23 @ X24 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('47',plain,(
    ! [X29: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('48',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['46','47'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('49',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ( r1_tarski @ X21 @ X19 )
      | ( X20
       != ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('50',plain,(
    ! [X19: $i,X21: $i] :
      ( ( r1_tarski @ X21 @ X19 )
      | ~ ( r2_hidden @ X21 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('53',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('55',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('57',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('58',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('59',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('60',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('63',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','65'])).

thf('67',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['57','66'])).

thf('68',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['43','67'])).

thf('69',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('70',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_A )
    | ( sk_B
      = ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['48','50'])).

thf('74',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['43','67'])).

thf('75',plain,(
    sk_B = sk_A ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['8'])).

thf('77',plain,(
    ! [X26: $i] :
      ( ( k2_subset_1 @ X26 )
      = X26 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('78',plain,
    ( ( sk_B != sk_A )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    sk_B
 != ( k2_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['9','35'])).

thf('80',plain,(
    sk_B != sk_A ),
    inference(simpl_trail,[status(thm)],['78','79'])).

thf('81',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['75','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pFAi1d5gyr
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:41:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.23/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.23/0.55  % Solved by: fo/fo7.sh
% 0.23/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.55  % done 230 iterations in 0.081s
% 0.23/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.23/0.55  % SZS output start Refutation
% 0.23/0.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.23/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.23/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.55  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.23/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.55  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.23/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.23/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.55  thf(t39_subset_1, conjecture,
% 0.23/0.55    (![A:$i,B:$i]:
% 0.23/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.55       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.23/0.55         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 0.23/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.55    (~( ![A:$i,B:$i]:
% 0.23/0.55        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.55          ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.23/0.55            ( ( B ) = ( k2_subset_1 @ A ) ) ) ) )),
% 0.23/0.55    inference('cnf.neg', [status(esa)], [t39_subset_1])).
% 0.23/0.55  thf('0', plain,
% 0.23/0.55      ((((sk_B) = (k2_subset_1 @ sk_A))
% 0.23/0.55        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('1', plain,
% 0.23/0.55      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.23/0.55         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.23/0.55      inference('split', [status(esa)], ['0'])).
% 0.23/0.55  thf(t28_xboole_1, axiom,
% 0.23/0.55    (![A:$i,B:$i]:
% 0.23/0.55     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.23/0.55  thf('2', plain,
% 0.23/0.55      (![X9 : $i, X10 : $i]:
% 0.23/0.55         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.23/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.23/0.55  thf('3', plain,
% 0.23/0.55      ((((k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)
% 0.23/0.55          = (k3_subset_1 @ sk_A @ sk_B)))
% 0.23/0.55         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.23/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.55  thf(commutativity_k3_xboole_0, axiom,
% 0.23/0.55    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.23/0.55  thf('4', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.23/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.23/0.55  thf('5', plain,
% 0.23/0.55      ((((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.23/0.55          = (k3_subset_1 @ sk_A @ sk_B)))
% 0.23/0.55         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.23/0.55      inference('demod', [status(thm)], ['3', '4'])).
% 0.23/0.55  thf(t100_xboole_1, axiom,
% 0.23/0.55    (![A:$i,B:$i]:
% 0.23/0.55     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.23/0.55  thf('6', plain,
% 0.23/0.55      (![X7 : $i, X8 : $i]:
% 0.23/0.55         ((k4_xboole_0 @ X7 @ X8)
% 0.23/0.55           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.23/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.23/0.55  thf('7', plain,
% 0.23/0.55      ((((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.23/0.55          = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))
% 0.23/0.55         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.23/0.55      inference('sup+', [status(thm)], ['5', '6'])).
% 0.23/0.55  thf('8', plain,
% 0.23/0.55      ((((sk_B) != (k2_subset_1 @ sk_A))
% 0.23/0.55        | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('9', plain,
% 0.23/0.55      (~ (((sk_B) = (k2_subset_1 @ sk_A))) | 
% 0.23/0.55       ~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.23/0.55      inference('split', [status(esa)], ['8'])).
% 0.23/0.55  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.23/0.55  thf('10', plain, (![X26 : $i]: ((k2_subset_1 @ X26) = (X26))),
% 0.23/0.55      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.23/0.55  thf('11', plain,
% 0.23/0.55      ((((sk_B) = (k2_subset_1 @ sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.23/0.55      inference('split', [status(esa)], ['0'])).
% 0.23/0.55  thf('12', plain,
% 0.23/0.55      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.23/0.55      inference('sup+', [status(thm)], ['10', '11'])).
% 0.23/0.55  thf('13', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('14', plain,
% 0.23/0.55      (((m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ sk_A)))
% 0.23/0.55         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.23/0.55      inference('sup+', [status(thm)], ['12', '13'])).
% 0.23/0.55  thf(d5_subset_1, axiom,
% 0.23/0.55    (![A:$i,B:$i]:
% 0.23/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.55       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.23/0.55  thf('15', plain,
% 0.23/0.55      (![X27 : $i, X28 : $i]:
% 0.23/0.55         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 0.23/0.55          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 0.23/0.55      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.23/0.55  thf('16', plain,
% 0.23/0.55      ((((k3_subset_1 @ sk_A @ sk_A) = (k4_xboole_0 @ sk_A @ sk_A)))
% 0.23/0.55         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.23/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.23/0.55  thf(d10_xboole_0, axiom,
% 0.23/0.55    (![A:$i,B:$i]:
% 0.23/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.23/0.55  thf('17', plain,
% 0.23/0.55      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.23/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.23/0.55  thf('18', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.23/0.55      inference('simplify', [status(thm)], ['17'])).
% 0.23/0.55  thf('19', plain,
% 0.23/0.55      (![X9 : $i, X10 : $i]:
% 0.23/0.55         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.23/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.23/0.55  thf('20', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.23/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.23/0.55  thf('21', plain,
% 0.23/0.55      (![X7 : $i, X8 : $i]:
% 0.23/0.55         ((k4_xboole_0 @ X7 @ X8)
% 0.23/0.55           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.23/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.23/0.55  thf('22', plain,
% 0.23/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.23/0.55      inference('sup+', [status(thm)], ['20', '21'])).
% 0.23/0.55  thf(t92_xboole_1, axiom,
% 0.23/0.55    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.23/0.55  thf('23', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ X17) = (k1_xboole_0))),
% 0.23/0.55      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.23/0.55  thf('24', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.23/0.55      inference('sup+', [status(thm)], ['22', '23'])).
% 0.23/0.55  thf('25', plain,
% 0.23/0.55      ((((k3_subset_1 @ sk_A @ sk_A) = (k1_xboole_0)))
% 0.23/0.55         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.23/0.55      inference('demod', [status(thm)], ['16', '24'])).
% 0.23/0.55  thf('26', plain,
% 0.23/0.55      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.23/0.55      inference('sup+', [status(thm)], ['10', '11'])).
% 0.23/0.55  thf('27', plain,
% 0.23/0.55      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.23/0.55         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.23/0.55      inference('split', [status(esa)], ['8'])).
% 0.23/0.55  thf('28', plain,
% 0.23/0.55      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A))
% 0.23/0.55         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.23/0.55             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.23/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.23/0.55  thf('29', plain,
% 0.23/0.55      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.23/0.55      inference('sup+', [status(thm)], ['10', '11'])).
% 0.23/0.55  thf('30', plain,
% 0.23/0.55      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_A) @ sk_A))
% 0.23/0.55         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.23/0.55             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.23/0.55      inference('demod', [status(thm)], ['28', '29'])).
% 0.23/0.55  thf('31', plain,
% 0.23/0.55      ((~ (r1_tarski @ k1_xboole_0 @ sk_A))
% 0.23/0.55         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.23/0.55             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.23/0.55      inference('sup-', [status(thm)], ['25', '30'])).
% 0.23/0.55  thf('32', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.23/0.55      inference('sup+', [status(thm)], ['22', '23'])).
% 0.23/0.55  thf(t36_xboole_1, axiom,
% 0.23/0.55    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.23/0.55  thf('33', plain,
% 0.23/0.55      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.23/0.55      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.23/0.55  thf('34', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.23/0.55      inference('sup+', [status(thm)], ['32', '33'])).
% 0.23/0.55  thf('35', plain,
% 0.23/0.55      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.23/0.55       ~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.23/0.55      inference('demod', [status(thm)], ['31', '34'])).
% 0.23/0.55  thf('36', plain,
% 0.23/0.55      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.23/0.55       (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.23/0.55      inference('split', [status(esa)], ['0'])).
% 0.23/0.55  thf('37', plain, (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.23/0.55      inference('sat_resolution*', [status(thm)], ['9', '35', '36'])).
% 0.23/0.55  thf('38', plain,
% 0.23/0.55      (((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.23/0.55         = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.23/0.55      inference('simpl_trail', [status(thm)], ['7', '37'])).
% 0.23/0.55  thf('39', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('40', plain,
% 0.23/0.55      (![X27 : $i, X28 : $i]:
% 0.23/0.55         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 0.23/0.55          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 0.23/0.55      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.23/0.55  thf('41', plain,
% 0.23/0.55      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.23/0.55      inference('sup-', [status(thm)], ['39', '40'])).
% 0.23/0.55  thf('42', plain,
% 0.23/0.55      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.23/0.55      inference('sup-', [status(thm)], ['39', '40'])).
% 0.23/0.55  thf('43', plain,
% 0.23/0.55      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.23/0.55         = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.23/0.55      inference('demod', [status(thm)], ['38', '41', '42'])).
% 0.23/0.55  thf('44', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf(d2_subset_1, axiom,
% 0.23/0.55    (![A:$i,B:$i]:
% 0.23/0.55     ( ( ( v1_xboole_0 @ A ) =>
% 0.23/0.55         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.23/0.55       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.23/0.55         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.23/0.55  thf('45', plain,
% 0.23/0.55      (![X23 : $i, X24 : $i]:
% 0.23/0.55         (~ (m1_subset_1 @ X23 @ X24)
% 0.23/0.55          | (r2_hidden @ X23 @ X24)
% 0.23/0.55          | (v1_xboole_0 @ X24))),
% 0.23/0.55      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.23/0.55  thf('46', plain,
% 0.23/0.55      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.23/0.55        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.23/0.55      inference('sup-', [status(thm)], ['44', '45'])).
% 0.23/0.55  thf(fc1_subset_1, axiom,
% 0.23/0.55    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.23/0.55  thf('47', plain, (![X29 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X29))),
% 0.23/0.55      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.23/0.55  thf('48', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.55      inference('clc', [status(thm)], ['46', '47'])).
% 0.23/0.55  thf(d1_zfmisc_1, axiom,
% 0.23/0.55    (![A:$i,B:$i]:
% 0.23/0.55     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.23/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.23/0.55  thf('49', plain,
% 0.23/0.55      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.23/0.55         (~ (r2_hidden @ X21 @ X20)
% 0.23/0.55          | (r1_tarski @ X21 @ X19)
% 0.23/0.55          | ((X20) != (k1_zfmisc_1 @ X19)))),
% 0.23/0.55      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.23/0.55  thf('50', plain,
% 0.23/0.55      (![X19 : $i, X21 : $i]:
% 0.23/0.55         ((r1_tarski @ X21 @ X19) | ~ (r2_hidden @ X21 @ (k1_zfmisc_1 @ X19)))),
% 0.23/0.55      inference('simplify', [status(thm)], ['49'])).
% 0.23/0.55  thf('51', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.23/0.55      inference('sup-', [status(thm)], ['48', '50'])).
% 0.23/0.55  thf('52', plain,
% 0.23/0.55      (![X9 : $i, X10 : $i]:
% 0.23/0.55         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.23/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.23/0.55  thf('53', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.23/0.55      inference('sup-', [status(thm)], ['51', '52'])).
% 0.23/0.55  thf('54', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.23/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.23/0.55  thf('55', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.23/0.55      inference('demod', [status(thm)], ['53', '54'])).
% 0.23/0.55  thf('56', plain,
% 0.23/0.55      (![X7 : $i, X8 : $i]:
% 0.23/0.55         ((k4_xboole_0 @ X7 @ X8)
% 0.23/0.55           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.23/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.23/0.55  thf('57', plain,
% 0.23/0.55      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.23/0.55      inference('sup+', [status(thm)], ['55', '56'])).
% 0.23/0.55  thf(commutativity_k5_xboole_0, axiom,
% 0.23/0.55    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.23/0.55  thf('58', plain,
% 0.23/0.55      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.23/0.55      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.23/0.55  thf('59', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ X17) = (k1_xboole_0))),
% 0.23/0.55      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.23/0.55  thf(t91_xboole_1, axiom,
% 0.23/0.55    (![A:$i,B:$i,C:$i]:
% 0.23/0.55     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.23/0.55       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.23/0.55  thf('60', plain,
% 0.23/0.55      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.23/0.55         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 0.23/0.55           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 0.23/0.55      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.23/0.55  thf('61', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i]:
% 0.23/0.55         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.23/0.55           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.23/0.55      inference('sup+', [status(thm)], ['59', '60'])).
% 0.23/0.55  thf('62', plain,
% 0.23/0.55      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.23/0.55      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.23/0.55  thf(t5_boole, axiom,
% 0.23/0.55    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.23/0.55  thf('63', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.23/0.55      inference('cnf', [status(esa)], [t5_boole])).
% 0.23/0.55  thf('64', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.23/0.55      inference('sup+', [status(thm)], ['62', '63'])).
% 0.23/0.55  thf('65', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i]:
% 0.23/0.55         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.23/0.55      inference('demod', [status(thm)], ['61', '64'])).
% 0.23/0.55  thf('66', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i]:
% 0.23/0.55         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.23/0.55      inference('sup+', [status(thm)], ['58', '65'])).
% 0.23/0.55  thf('67', plain,
% 0.23/0.55      (((sk_A) = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.23/0.55      inference('sup+', [status(thm)], ['57', '66'])).
% 0.23/0.55  thf('68', plain,
% 0.23/0.55      (((sk_A) = (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.23/0.55      inference('sup+', [status(thm)], ['43', '67'])).
% 0.23/0.55  thf('69', plain,
% 0.23/0.55      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.23/0.55      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.23/0.55  thf('70', plain,
% 0.23/0.55      (![X4 : $i, X6 : $i]:
% 0.23/0.55         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.23/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.23/0.55  thf('71', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i]:
% 0.23/0.55         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.23/0.55          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.23/0.55      inference('sup-', [status(thm)], ['69', '70'])).
% 0.23/0.55  thf('72', plain,
% 0.23/0.55      ((~ (r1_tarski @ sk_B @ sk_A)
% 0.23/0.55        | ((sk_B) = (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))))),
% 0.23/0.55      inference('sup-', [status(thm)], ['68', '71'])).
% 0.23/0.55  thf('73', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.23/0.55      inference('sup-', [status(thm)], ['48', '50'])).
% 0.23/0.55  thf('74', plain,
% 0.23/0.55      (((sk_A) = (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.23/0.55      inference('sup+', [status(thm)], ['43', '67'])).
% 0.23/0.55  thf('75', plain, (((sk_B) = (sk_A))),
% 0.23/0.55      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.23/0.55  thf('76', plain,
% 0.23/0.55      ((((sk_B) != (k2_subset_1 @ sk_A)))
% 0.23/0.55         <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.23/0.55      inference('split', [status(esa)], ['8'])).
% 0.23/0.55  thf('77', plain, (![X26 : $i]: ((k2_subset_1 @ X26) = (X26))),
% 0.23/0.55      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.23/0.55  thf('78', plain,
% 0.23/0.55      ((((sk_B) != (sk_A))) <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.23/0.55      inference('demod', [status(thm)], ['76', '77'])).
% 0.23/0.55  thf('79', plain, (~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.23/0.55      inference('sat_resolution*', [status(thm)], ['9', '35'])).
% 0.23/0.55  thf('80', plain, (((sk_B) != (sk_A))),
% 0.23/0.55      inference('simpl_trail', [status(thm)], ['78', '79'])).
% 0.23/0.55  thf('81', plain, ($false),
% 0.23/0.55      inference('simplify_reflect-', [status(thm)], ['75', '80'])).
% 0.23/0.55  
% 0.23/0.55  % SZS output end Refutation
% 0.23/0.55  
% 0.23/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

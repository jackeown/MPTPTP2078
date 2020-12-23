%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lCSJ0Hv6ZV

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:34 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 415 expanded)
%              Number of leaves         :   28 ( 132 expanded)
%              Depth                    :   23
%              Number of atoms          : 1049 (3249 expanded)
%              Number of equality atoms :  116 ( 371 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

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

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X16 @ X17 )
      | ( r2_hidden @ X16 @ X18 )
      | ( X18
       != ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r2_hidden @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,
    ( ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('7',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
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

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('20',plain,(
    ! [X24: $i] :
      ( ( k2_subset_1 @ X24 )
      = X24 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('21',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k4_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('26',plain,
    ( ( ( k3_subset_1 @ sk_A @ sk_A )
      = ( k4_xboole_0 @ sk_A @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k3_subset_1 @ sk_A @ sk_A )
      = k1_xboole_0 )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['19','26'])).

thf('28',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('29',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('30',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('32',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_A ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('35',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sat_resolution*',[status(thm)],['6','35','36'])).

thf('38',plain,(
    r2_hidden @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['4','37'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('39',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ( m1_subset_1 @ X21 @ X22 )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B ) )
    | ( m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('41',plain,(
    ! [X27: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('42',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k4_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('44',plain,
    ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('46',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
    = ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('49',plain,
    ( ( ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('51',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      = ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sat_resolution*',[status(thm)],['6','35','36'])).

thf('53',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['46','53'])).

thf('55',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('56',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('57',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('59',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('60',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','62'])).

thf('64',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['54','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ X22 )
      | ( r2_hidden @ X21 @ X22 )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('67',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X27: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('69',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X18 )
      | ( r1_tarski @ X19 @ X17 )
      | ( X18
       != ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('71',plain,(
    ! [X17: $i,X19: $i] :
      ( ( r1_tarski @ X19 @ X17 )
      | ~ ( r2_hidden @ X19 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['69','71'])).

thf('73',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('74',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('76',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('78',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k4_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('81',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','61'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['82','85'])).

thf('87',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['64','86'])).

thf('88',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('89',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','62'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('98',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['96','99'])).

thf('101',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['87','102'])).

thf('104',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( sk_A
    = ( k5_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['103','108'])).

thf('110',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['74','75'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('112',plain,(
    sk_A = sk_B ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('114',plain,(
    ! [X24: $i] :
      ( ( k2_subset_1 @ X24 )
      = X24 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('115',plain,
    ( ( sk_B != sk_A )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    sk_B
 != ( k2_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['6','35'])).

thf('117',plain,(
    sk_B != sk_A ),
    inference(simpl_trail,[status(thm)],['115','116'])).

thf('118',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['112','117'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lCSJ0Hv6ZV
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:58:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.39/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.57  % Solved by: fo/fo7.sh
% 0.39/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.57  % done 250 iterations in 0.111s
% 0.39/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.57  % SZS output start Refutation
% 0.39/0.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.39/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.57  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.39/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.57  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.39/0.57  thf(t39_subset_1, conjecture,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.57       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.39/0.57         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 0.39/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.57    (~( ![A:$i,B:$i]:
% 0.39/0.57        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.57          ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.39/0.57            ( ( B ) = ( k2_subset_1 @ A ) ) ) ) )),
% 0.39/0.57    inference('cnf.neg', [status(esa)], [t39_subset_1])).
% 0.39/0.57  thf('0', plain,
% 0.39/0.57      ((((sk_B) = (k2_subset_1 @ sk_A))
% 0.39/0.57        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('1', plain,
% 0.39/0.57      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.39/0.57         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.39/0.57      inference('split', [status(esa)], ['0'])).
% 0.39/0.57  thf(d1_zfmisc_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.39/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.39/0.57  thf('2', plain,
% 0.39/0.57      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.39/0.57         (~ (r1_tarski @ X16 @ X17)
% 0.39/0.57          | (r2_hidden @ X16 @ X18)
% 0.39/0.57          | ((X18) != (k1_zfmisc_1 @ X17)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.39/0.57  thf('3', plain,
% 0.39/0.57      (![X16 : $i, X17 : $i]:
% 0.39/0.57         ((r2_hidden @ X16 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X16 @ X17))),
% 0.39/0.57      inference('simplify', [status(thm)], ['2'])).
% 0.39/0.57  thf('4', plain,
% 0.39/0.57      (((r2_hidden @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.39/0.57         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['1', '3'])).
% 0.39/0.57  thf('5', plain,
% 0.39/0.57      ((((sk_B) != (k2_subset_1 @ sk_A))
% 0.39/0.57        | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('6', plain,
% 0.39/0.57      (~ (((sk_B) = (k2_subset_1 @ sk_A))) | 
% 0.39/0.57       ~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.39/0.57      inference('split', [status(esa)], ['5'])).
% 0.39/0.57  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.39/0.57  thf('7', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.39/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.39/0.57  thf(t28_xboole_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.39/0.57  thf('8', plain,
% 0.39/0.57      (![X6 : $i, X7 : $i]:
% 0.39/0.57         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.39/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.39/0.57  thf('9', plain,
% 0.39/0.57      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.39/0.57  thf(commutativity_k3_xboole_0, axiom,
% 0.39/0.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.39/0.57  thf('10', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.39/0.57  thf('11', plain,
% 0.39/0.57      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['9', '10'])).
% 0.39/0.57  thf(t100_xboole_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.39/0.57  thf('12', plain,
% 0.39/0.57      (![X4 : $i, X5 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X4 @ X5)
% 0.39/0.57           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.39/0.57  thf('13', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['11', '12'])).
% 0.39/0.57  thf(t5_boole, axiom,
% 0.39/0.57    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.39/0.57  thf('14', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.39/0.57      inference('cnf', [status(esa)], [t5_boole])).
% 0.39/0.57  thf('15', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['13', '14'])).
% 0.39/0.57  thf(t48_xboole_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.39/0.57  thf('16', plain,
% 0.39/0.57      (![X9 : $i, X10 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.39/0.57           = (k3_xboole_0 @ X9 @ X10))),
% 0.39/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.57  thf('17', plain,
% 0.39/0.57      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['15', '16'])).
% 0.39/0.57  thf('18', plain,
% 0.39/0.57      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['9', '10'])).
% 0.39/0.57  thf('19', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.39/0.57      inference('demod', [status(thm)], ['17', '18'])).
% 0.39/0.57  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.39/0.57  thf('20', plain, (![X24 : $i]: ((k2_subset_1 @ X24) = (X24))),
% 0.39/0.57      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.39/0.57  thf('21', plain,
% 0.39/0.57      ((((sk_B) = (k2_subset_1 @ sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.39/0.57      inference('split', [status(esa)], ['0'])).
% 0.39/0.57  thf('22', plain,
% 0.39/0.57      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.39/0.57      inference('sup+', [status(thm)], ['20', '21'])).
% 0.39/0.57  thf('23', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('24', plain,
% 0.39/0.57      (((m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ sk_A)))
% 0.39/0.57         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.39/0.57      inference('sup+', [status(thm)], ['22', '23'])).
% 0.39/0.57  thf(d5_subset_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.57       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.39/0.57  thf('25', plain,
% 0.39/0.57      (![X25 : $i, X26 : $i]:
% 0.39/0.57         (((k3_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))
% 0.39/0.57          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.39/0.57  thf('26', plain,
% 0.39/0.57      ((((k3_subset_1 @ sk_A @ sk_A) = (k4_xboole_0 @ sk_A @ sk_A)))
% 0.39/0.57         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['24', '25'])).
% 0.39/0.57  thf('27', plain,
% 0.39/0.57      ((((k3_subset_1 @ sk_A @ sk_A) = (k1_xboole_0)))
% 0.39/0.57         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.39/0.57      inference('sup+', [status(thm)], ['19', '26'])).
% 0.39/0.57  thf('28', plain,
% 0.39/0.57      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.39/0.57      inference('sup+', [status(thm)], ['20', '21'])).
% 0.39/0.57  thf('29', plain,
% 0.39/0.57      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.39/0.57         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.39/0.57      inference('split', [status(esa)], ['5'])).
% 0.39/0.57  thf('30', plain,
% 0.39/0.57      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A))
% 0.39/0.57         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.39/0.57             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['28', '29'])).
% 0.39/0.57  thf('31', plain,
% 0.39/0.57      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.39/0.57      inference('sup+', [status(thm)], ['20', '21'])).
% 0.39/0.57  thf('32', plain,
% 0.39/0.57      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_A) @ sk_A))
% 0.39/0.57         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.39/0.57             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.39/0.57      inference('demod', [status(thm)], ['30', '31'])).
% 0.39/0.57  thf('33', plain,
% 0.39/0.57      ((~ (r1_tarski @ k1_xboole_0 @ sk_A))
% 0.39/0.57         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.39/0.57             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['27', '32'])).
% 0.39/0.57  thf('34', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.39/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.39/0.57  thf('35', plain,
% 0.39/0.57      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.39/0.57       ~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.39/0.57      inference('demod', [status(thm)], ['33', '34'])).
% 0.39/0.57  thf('36', plain,
% 0.39/0.57      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.39/0.57       (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.39/0.57      inference('split', [status(esa)], ['0'])).
% 0.39/0.57  thf('37', plain, (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.39/0.57      inference('sat_resolution*', [status(thm)], ['6', '35', '36'])).
% 0.39/0.57  thf('38', plain,
% 0.39/0.57      ((r2_hidden @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 0.39/0.57      inference('simpl_trail', [status(thm)], ['4', '37'])).
% 0.39/0.57  thf(d2_subset_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ( v1_xboole_0 @ A ) =>
% 0.39/0.57         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.39/0.57       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.39/0.57         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.39/0.57  thf('39', plain,
% 0.39/0.57      (![X21 : $i, X22 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X21 @ X22)
% 0.39/0.57          | (m1_subset_1 @ X21 @ X22)
% 0.39/0.57          | (v1_xboole_0 @ X22))),
% 0.39/0.57      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.39/0.57  thf('40', plain,
% 0.39/0.57      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_B))
% 0.39/0.57        | (m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['38', '39'])).
% 0.39/0.57  thf(fc1_subset_1, axiom,
% 0.39/0.57    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.39/0.57  thf('41', plain, (![X27 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X27))),
% 0.39/0.57      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.39/0.57  thf('42', plain,
% 0.39/0.57      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 0.39/0.57      inference('clc', [status(thm)], ['40', '41'])).
% 0.39/0.57  thf('43', plain,
% 0.39/0.57      (![X25 : $i, X26 : $i]:
% 0.39/0.57         (((k3_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))
% 0.39/0.57          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.39/0.57  thf('44', plain,
% 0.39/0.57      (((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.39/0.57         = (k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['42', '43'])).
% 0.39/0.57  thf('45', plain,
% 0.39/0.57      (![X9 : $i, X10 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.39/0.57           = (k3_xboole_0 @ X9 @ X10))),
% 0.39/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.57  thf('46', plain,
% 0.39/0.57      (((k4_xboole_0 @ sk_B @ 
% 0.39/0.57         (k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.39/0.57         = (k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['44', '45'])).
% 0.39/0.57  thf('47', plain,
% 0.39/0.57      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.39/0.57         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.39/0.57      inference('split', [status(esa)], ['0'])).
% 0.39/0.57  thf('48', plain,
% 0.39/0.57      (![X6 : $i, X7 : $i]:
% 0.39/0.57         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.39/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.39/0.57  thf('49', plain,
% 0.39/0.57      ((((k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)
% 0.39/0.57          = (k3_subset_1 @ sk_A @ sk_B)))
% 0.39/0.57         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['47', '48'])).
% 0.39/0.57  thf('50', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.39/0.57  thf('51', plain,
% 0.39/0.57      ((((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.39/0.57          = (k3_subset_1 @ sk_A @ sk_B)))
% 0.39/0.57         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.39/0.57      inference('demod', [status(thm)], ['49', '50'])).
% 0.39/0.57  thf('52', plain, (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.39/0.57      inference('sat_resolution*', [status(thm)], ['6', '35', '36'])).
% 0.39/0.57  thf('53', plain,
% 0.39/0.57      (((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.39/0.57         = (k3_subset_1 @ sk_A @ sk_B))),
% 0.39/0.57      inference('simpl_trail', [status(thm)], ['51', '52'])).
% 0.39/0.57  thf('54', plain,
% 0.39/0.57      (((k4_xboole_0 @ sk_B @ 
% 0.39/0.57         (k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.39/0.57         = (k3_subset_1 @ sk_A @ sk_B))),
% 0.39/0.57      inference('demod', [status(thm)], ['46', '53'])).
% 0.39/0.57  thf('55', plain,
% 0.39/0.57      (![X4 : $i, X5 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X4 @ X5)
% 0.39/0.57           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.39/0.57  thf(t92_xboole_1, axiom,
% 0.39/0.57    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.39/0.57  thf('56', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.39/0.57  thf(t91_xboole_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.39/0.57       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.39/0.57  thf('57', plain,
% 0.39/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.39/0.57         ((k5_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ X14)
% 0.39/0.57           = (k5_xboole_0 @ X12 @ (k5_xboole_0 @ X13 @ X14)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.39/0.57  thf('58', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.39/0.57           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['56', '57'])).
% 0.39/0.57  thf(commutativity_k5_xboole_0, axiom,
% 0.39/0.57    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.39/0.57  thf('59', plain,
% 0.39/0.57      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.39/0.57      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.39/0.57  thf('60', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.39/0.57      inference('cnf', [status(esa)], [t5_boole])).
% 0.39/0.57  thf('61', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['59', '60'])).
% 0.39/0.57  thf('62', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.39/0.57      inference('demod', [status(thm)], ['58', '61'])).
% 0.39/0.57  thf('63', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((k3_xboole_0 @ X1 @ X0)
% 0.39/0.57           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['55', '62'])).
% 0.39/0.57  thf('64', plain,
% 0.39/0.57      (((k3_xboole_0 @ sk_B @ 
% 0.39/0.57         (k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.39/0.57         = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['54', '63'])).
% 0.39/0.57  thf('65', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('66', plain,
% 0.39/0.57      (![X21 : $i, X22 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X21 @ X22)
% 0.39/0.57          | (r2_hidden @ X21 @ X22)
% 0.39/0.57          | (v1_xboole_0 @ X22))),
% 0.39/0.57      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.39/0.57  thf('67', plain,
% 0.39/0.57      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.39/0.57        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['65', '66'])).
% 0.39/0.57  thf('68', plain, (![X27 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X27))),
% 0.39/0.57      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.39/0.57  thf('69', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.57      inference('clc', [status(thm)], ['67', '68'])).
% 0.39/0.57  thf('70', plain,
% 0.39/0.57      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X19 @ X18)
% 0.39/0.57          | (r1_tarski @ X19 @ X17)
% 0.39/0.57          | ((X18) != (k1_zfmisc_1 @ X17)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.39/0.57  thf('71', plain,
% 0.39/0.57      (![X17 : $i, X19 : $i]:
% 0.39/0.57         ((r1_tarski @ X19 @ X17) | ~ (r2_hidden @ X19 @ (k1_zfmisc_1 @ X17)))),
% 0.39/0.57      inference('simplify', [status(thm)], ['70'])).
% 0.39/0.57  thf('72', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.39/0.57      inference('sup-', [status(thm)], ['69', '71'])).
% 0.39/0.57  thf('73', plain,
% 0.39/0.57      (![X6 : $i, X7 : $i]:
% 0.39/0.57         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.39/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.39/0.57  thf('74', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.39/0.57      inference('sup-', [status(thm)], ['72', '73'])).
% 0.39/0.57  thf('75', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.39/0.57  thf('76', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.39/0.57      inference('demod', [status(thm)], ['74', '75'])).
% 0.39/0.57  thf('77', plain,
% 0.39/0.57      (![X4 : $i, X5 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X4 @ X5)
% 0.39/0.57           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.39/0.57  thf('78', plain,
% 0.39/0.57      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.57      inference('sup+', [status(thm)], ['76', '77'])).
% 0.39/0.57  thf('79', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('80', plain,
% 0.39/0.57      (![X25 : $i, X26 : $i]:
% 0.39/0.57         (((k3_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))
% 0.39/0.57          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.39/0.57  thf('81', plain,
% 0.39/0.57      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.57      inference('sup-', [status(thm)], ['79', '80'])).
% 0.39/0.57  thf('82', plain,
% 0.39/0.57      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.57      inference('demod', [status(thm)], ['78', '81'])).
% 0.39/0.57  thf('83', plain,
% 0.39/0.57      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.39/0.57      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.39/0.57  thf('84', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.39/0.57      inference('demod', [status(thm)], ['58', '61'])).
% 0.39/0.57  thf('85', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['83', '84'])).
% 0.39/0.57  thf('86', plain,
% 0.39/0.57      (((sk_A) = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['82', '85'])).
% 0.39/0.57  thf('87', plain,
% 0.39/0.57      (((k3_xboole_0 @ sk_B @ 
% 0.39/0.57         (k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) = (sk_A))),
% 0.39/0.57      inference('demod', [status(thm)], ['64', '86'])).
% 0.39/0.57  thf('88', plain,
% 0.39/0.57      (![X9 : $i, X10 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.39/0.57           = (k3_xboole_0 @ X9 @ X10))),
% 0.39/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.57  thf('89', plain,
% 0.39/0.57      (![X9 : $i, X10 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.39/0.57           = (k3_xboole_0 @ X9 @ X10))),
% 0.39/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.57  thf('90', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.39/0.57           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['88', '89'])).
% 0.39/0.57  thf('91', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((k3_xboole_0 @ X1 @ X0)
% 0.39/0.57           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['55', '62'])).
% 0.39/0.57  thf('92', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.39/0.57           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.39/0.57      inference('sup+', [status(thm)], ['90', '91'])).
% 0.39/0.57  thf('93', plain,
% 0.39/0.57      (![X4 : $i, X5 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X4 @ X5)
% 0.39/0.57           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.39/0.57  thf('94', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.39/0.57           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.39/0.57      inference('demod', [status(thm)], ['92', '93'])).
% 0.39/0.57  thf('95', plain,
% 0.39/0.57      (![X9 : $i, X10 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.39/0.57           = (k3_xboole_0 @ X9 @ X10))),
% 0.39/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.57  thf('96', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.39/0.57           = (k3_xboole_0 @ X1 @ X0))),
% 0.39/0.57      inference('demod', [status(thm)], ['94', '95'])).
% 0.39/0.57  thf('97', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.39/0.57  thf('98', plain,
% 0.39/0.57      (![X4 : $i, X5 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X4 @ X5)
% 0.39/0.57           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.39/0.57  thf('99', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X0 @ X1)
% 0.39/0.57           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['97', '98'])).
% 0.39/0.57  thf('100', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 0.39/0.57           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['96', '99'])).
% 0.39/0.57  thf('101', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.39/0.57  thf('102', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 0.39/0.57      inference('demod', [status(thm)], ['100', '101'])).
% 0.39/0.57  thf('103', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['87', '102'])).
% 0.39/0.57  thf('104', plain,
% 0.39/0.57      (![X4 : $i, X5 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X4 @ X5)
% 0.39/0.57           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.39/0.57  thf('105', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['83', '84'])).
% 0.39/0.57  thf('106', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((X1)
% 0.39/0.57           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['104', '105'])).
% 0.39/0.57  thf('107', plain,
% 0.39/0.57      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.39/0.57      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.39/0.57  thf('108', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((X1)
% 0.39/0.57           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.39/0.57      inference('demod', [status(thm)], ['106', '107'])).
% 0.39/0.57  thf('109', plain,
% 0.39/0.57      (((sk_A) = (k5_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['103', '108'])).
% 0.39/0.57  thf('110', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.39/0.57      inference('demod', [status(thm)], ['74', '75'])).
% 0.39/0.57  thf('111', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['59', '60'])).
% 0.39/0.57  thf('112', plain, (((sk_A) = (sk_B))),
% 0.39/0.57      inference('demod', [status(thm)], ['109', '110', '111'])).
% 0.39/0.57  thf('113', plain,
% 0.39/0.57      ((((sk_B) != (k2_subset_1 @ sk_A)))
% 0.39/0.57         <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.39/0.57      inference('split', [status(esa)], ['5'])).
% 0.39/0.57  thf('114', plain, (![X24 : $i]: ((k2_subset_1 @ X24) = (X24))),
% 0.39/0.57      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.39/0.57  thf('115', plain,
% 0.39/0.57      ((((sk_B) != (sk_A))) <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.39/0.57      inference('demod', [status(thm)], ['113', '114'])).
% 0.39/0.57  thf('116', plain, (~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.39/0.57      inference('sat_resolution*', [status(thm)], ['6', '35'])).
% 0.39/0.57  thf('117', plain, (((sk_B) != (sk_A))),
% 0.39/0.57      inference('simpl_trail', [status(thm)], ['115', '116'])).
% 0.39/0.57  thf('118', plain, ($false),
% 0.39/0.57      inference('simplify_reflect-', [status(thm)], ['112', '117'])).
% 0.39/0.57  
% 0.39/0.57  % SZS output end Refutation
% 0.39/0.57  
% 0.39/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

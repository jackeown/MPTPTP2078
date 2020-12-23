%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fsMdIlKNgd

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 239 expanded)
%              Number of leaves         :   31 (  77 expanded)
%              Depth                    :   21
%              Number of atoms          :  704 (1898 expanded)
%              Number of equality atoms :   78 ( 210 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ X25 )
      | ( r2_hidden @ X24 @ X25 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X30: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X30 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X22 @ X21 )
      | ( r1_tarski @ X22 @ X20 )
      | ( X21
       != ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('6',plain,(
    ! [X20: $i,X22: $i] :
      ( ( r1_tarski @ X22 @ X20 )
      | ~ ( r2_hidden @ X22 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
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

thf('11',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('16',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['18'])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('20',plain,(
    ! [X27: $i] :
      ( ( k2_subset_1 @ X27 )
      = X27 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('21',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['12'])).

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

thf('25',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ X25 )
      | ( r2_hidden @ X24 @ X25 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('26',plain,
    ( ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r2_hidden @ sk_A @ ( k1_zfmisc_1 @ sk_A ) ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X30: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('28',plain,
    ( ( r2_hidden @ sk_A @ ( k1_zfmisc_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X20: $i,X22: $i] :
      ( ( r1_tarski @ X22 @ X20 )
      | ~ ( r2_hidden @ X22 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('30',plain,
    ( ( r1_tarski @ sk_A @ sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('32',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_A )
      = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('33',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('34',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_A )
      = ( k5_xboole_0 @ sk_A @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('35',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('36',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_A )
      = k1_xboole_0 )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('38',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('39',plain,
    ( ( ( k3_subset_1 @ sk_A @ sk_A )
      = ( k4_xboole_0 @ sk_A @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('41',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['18'])).

thf('42',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('44',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_A ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_A ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','45'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('47',plain,(
    ! [X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ X9 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('48',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['12'])).

thf('50',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sat_resolution*',[status(thm)],['19','48','49'])).

thf('51',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B ),
    inference(simpl_trail,[status(thm)],['17','50'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('52',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('53',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('56',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('57',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('59',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('60',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

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
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
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
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','65'])).

thf('67',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['57','66'])).

thf('68',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('70',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    sk_B = sk_A ),
    inference('sup+',[status(thm)],['11','70'])).

thf('72',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['18'])).

thf('73',plain,(
    ! [X27: $i] :
      ( ( k2_subset_1 @ X27 )
      = X27 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('74',plain,
    ( ( sk_B != sk_A )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    sk_B
 != ( k2_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['19','48'])).

thf('76',plain,(
    sk_B != sk_A ),
    inference(simpl_trail,[status(thm)],['74','75'])).

thf('77',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['71','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fsMdIlKNgd
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:00:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 193 iterations in 0.083s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(t39_subset_1, conjecture,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.20/0.53         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i]:
% 0.20/0.53        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53          ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.20/0.53            ( ( B ) = ( k2_subset_1 @ A ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t39_subset_1])).
% 0.20/0.53  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(d2_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( v1_xboole_0 @ A ) =>
% 0.20/0.53         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.20/0.53       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.53         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (![X24 : $i, X25 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X24 @ X25)
% 0.20/0.53          | (r2_hidden @ X24 @ X25)
% 0.20/0.53          | (v1_xboole_0 @ X25))),
% 0.20/0.53      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.53        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.53  thf(fc1_subset_1, axiom,
% 0.20/0.53    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.53  thf('3', plain, (![X30 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X30))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.53  thf('4', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.53      inference('clc', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf(d1_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.20/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X22 @ X21)
% 0.20/0.53          | (r1_tarski @ X22 @ X20)
% 0.20/0.53          | ((X21) != (k1_zfmisc_1 @ X20)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (![X20 : $i, X22 : $i]:
% 0.20/0.53         ((r1_tarski @ X22 @ X20) | ~ (r2_hidden @ X22 @ (k1_zfmisc_1 @ X20)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.53  thf('7', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.20/0.53      inference('sup-', [status(thm)], ['4', '6'])).
% 0.20/0.53  thf(t28_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X7 : $i, X8 : $i]:
% 0.20/0.53         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.20/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.53  thf('9', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.53  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.53  thf('11', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      ((((sk_B) = (k2_subset_1 @ sk_A))
% 0.20/0.53        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.20/0.53         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.53      inference('split', [status(esa)], ['12'])).
% 0.20/0.53  thf('14', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(d5_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X28 : $i, X29 : $i]:
% 0.20/0.53         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 0.20/0.53          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B))
% 0.20/0.53         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['13', '16'])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      ((((sk_B) != (k2_subset_1 @ sk_A))
% 0.20/0.53        | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (~ (((sk_B) = (k2_subset_1 @ sk_A))) | 
% 0.20/0.53       ~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.53      inference('split', [status(esa)], ['18'])).
% 0.20/0.53  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.53  thf('20', plain, (![X27 : $i]: ((k2_subset_1 @ X27) = (X27))),
% 0.20/0.53      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      ((((sk_B) = (k2_subset_1 @ sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.53      inference('split', [status(esa)], ['12'])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf('23', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      (((m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ sk_A)))
% 0.20/0.53         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['22', '23'])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X24 : $i, X25 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X24 @ X25)
% 0.20/0.53          | (r2_hidden @ X24 @ X25)
% 0.20/0.53          | (v1_xboole_0 @ X25))),
% 0.20/0.53      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      ((((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.53         | (r2_hidden @ sk_A @ (k1_zfmisc_1 @ sk_A))))
% 0.20/0.53         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.53  thf('27', plain, (![X30 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X30))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (((r2_hidden @ sk_A @ (k1_zfmisc_1 @ sk_A)))
% 0.20/0.53         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.53      inference('clc', [status(thm)], ['26', '27'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (![X20 : $i, X22 : $i]:
% 0.20/0.53         ((r1_tarski @ X22 @ X20) | ~ (r2_hidden @ X22 @ (k1_zfmisc_1 @ X20)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (((r1_tarski @ sk_A @ sk_A)) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      (![X7 : $i, X8 : $i]:
% 0.20/0.53         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.20/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      ((((k3_xboole_0 @ sk_A @ sk_A) = (sk_A)))
% 0.20/0.53         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.53  thf(t100_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      (![X5 : $i, X6 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X5 @ X6)
% 0.20/0.53           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      ((((k4_xboole_0 @ sk_A @ sk_A) = (k5_xboole_0 @ sk_A @ sk_A)))
% 0.20/0.53         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['32', '33'])).
% 0.20/0.53  thf(t92_xboole_1, axiom,
% 0.20/0.53    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.53  thf('35', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      ((((k4_xboole_0 @ sk_A @ sk_A) = (k1_xboole_0)))
% 0.20/0.53         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.53      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (((m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ sk_A)))
% 0.20/0.53         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['22', '23'])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      (![X28 : $i, X29 : $i]:
% 0.20/0.53         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 0.20/0.53          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      ((((k3_subset_1 @ sk_A @ sk_A) = (k4_xboole_0 @ sk_A @ sk_A)))
% 0.20/0.53         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.20/0.53         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.53      inference('split', [status(esa)], ['18'])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A))
% 0.20/0.53         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.20/0.53             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_A) @ sk_A))
% 0.20/0.53         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.20/0.53             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.53      inference('demod', [status(thm)], ['42', '43'])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      ((~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_A) @ sk_A))
% 0.20/0.53         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.20/0.53             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['39', '44'])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      ((~ (r1_tarski @ k1_xboole_0 @ sk_A))
% 0.20/0.53         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.20/0.53             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['36', '45'])).
% 0.20/0.53  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.53  thf('47', plain, (![X9 : $i]: (r1_tarski @ k1_xboole_0 @ X9)),
% 0.20/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.20/0.53       ~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['46', '47'])).
% 0.20/0.53  thf('49', plain,
% 0.20/0.53      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.20/0.53       (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.20/0.53      inference('split', [status(esa)], ['12'])).
% 0.20/0.53  thf('50', plain, (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['19', '48', '49'])).
% 0.20/0.53  thf('51', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B)),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['17', '50'])).
% 0.20/0.53  thf(t79_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.20/0.53  thf('52', plain,
% 0.20/0.53      (![X13 : $i, X14 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X14)),
% 0.20/0.53      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.20/0.53  thf(t69_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.53       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.20/0.53  thf('53', plain,
% 0.20/0.53      (![X11 : $i, X12 : $i]:
% 0.20/0.53         (~ (r1_xboole_0 @ X11 @ X12)
% 0.20/0.53          | ~ (r1_tarski @ X11 @ X12)
% 0.20/0.53          | (v1_xboole_0 @ X11))),
% 0.20/0.53      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.20/0.53  thf('54', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((v1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))
% 0.20/0.53          | ~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.53  thf('55', plain, ((v1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['51', '54'])).
% 0.20/0.53  thf(l13_xboole_0, axiom,
% 0.20/0.53    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.53  thf('56', plain,
% 0.20/0.53      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.20/0.53      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.53  thf('57', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.53  thf('58', plain,
% 0.20/0.53      (![X5 : $i, X6 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X5 @ X6)
% 0.20/0.53           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.53  thf('59', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.53  thf(t91_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.53       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.20/0.53  thf('60', plain,
% 0.20/0.53      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.53         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 0.20/0.53           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.20/0.53  thf('61', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.20/0.53           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['59', '60'])).
% 0.20/0.53  thf(commutativity_k5_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.20/0.53  thf('62', plain,
% 0.20/0.53      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.20/0.53      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.20/0.53  thf(t5_boole, axiom,
% 0.20/0.53    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.53  thf('63', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.53  thf('64', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['62', '63'])).
% 0.20/0.53  thf('65', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['61', '64'])).
% 0.20/0.53  thf('66', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k3_xboole_0 @ X1 @ X0)
% 0.20/0.53           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['58', '65'])).
% 0.20/0.53  thf('67', plain,
% 0.20/0.53      (((k3_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['57', '66'])).
% 0.20/0.53  thf('68', plain,
% 0.20/0.53      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.20/0.53      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.20/0.53  thf('69', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['62', '63'])).
% 0.20/0.53  thf('70', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.20/0.53  thf('71', plain, (((sk_B) = (sk_A))),
% 0.20/0.53      inference('sup+', [status(thm)], ['11', '70'])).
% 0.20/0.53  thf('72', plain,
% 0.20/0.53      ((((sk_B) != (k2_subset_1 @ sk_A)))
% 0.20/0.53         <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.53      inference('split', [status(esa)], ['18'])).
% 0.20/0.53  thf('73', plain, (![X27 : $i]: ((k2_subset_1 @ X27) = (X27))),
% 0.20/0.53      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.53  thf('74', plain,
% 0.20/0.53      ((((sk_B) != (sk_A))) <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.53      inference('demod', [status(thm)], ['72', '73'])).
% 0.20/0.53  thf('75', plain, (~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['19', '48'])).
% 0.20/0.53  thf('76', plain, (((sk_B) != (sk_A))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['74', '75'])).
% 0.20/0.53  thf('77', plain, ($false),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['71', '76'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

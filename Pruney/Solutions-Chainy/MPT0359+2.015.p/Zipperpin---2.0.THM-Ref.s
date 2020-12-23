%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jvI4bVXU5U

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:33 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 527 expanded)
%              Number of leaves         :   33 ( 164 expanded)
%              Depth                    :   19
%              Number of atoms          :  961 (4318 expanded)
%              Number of equality atoms :   92 ( 430 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('0',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

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

thf('1',plain,(
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

thf('2',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ X23 )
      | ( r2_hidden @ X22 @ X23 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X29: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('5',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['3','4'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X20 @ X19 )
      | ( r1_tarski @ X20 @ X18 )
      | ( X19
       != ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('7',plain,(
    ! [X18: $i,X20: $i] :
      ( ( r1_tarski @ X20 @ X18 )
      | ~ ( r2_hidden @ X20 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['5','7'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['10','11'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 )
      = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B )
    = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','16'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('21',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['17','18','19','22'])).

thf('24',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ( r2_hidden @ X17 @ X19 )
      | ( X19
       != ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('27',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r2_hidden @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ( m1_subset_1 @ X22 @ X23 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('30',plain,
    ( ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B ) )
      | ( m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X29: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('32',plain,
    ( ( m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('34',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('35',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('37',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['37'])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('39',plain,(
    ! [X26: $i] :
      ( ( k2_subset_1 @ X26 )
      = X26 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('40',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['24'])).

thf('41',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('43',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['37'])).

thf('44',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_A ) @ sk_B )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('47',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('48',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = ( k5_xboole_0 @ sk_A @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('50',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('51',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_A )
      = k1_xboole_0 )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('53',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('54',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','51','52','53'])).

thf('55',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['24'])).

thf('56',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sat_resolution*',[status(thm)],['38','54','55'])).

thf('57',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['36','56'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('58',plain,(
    ! [X25: $i] :
      ( ( k1_subset_1 @ X25 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('59',plain,(
    ! [X30: $i] :
      ( ( k2_subset_1 @ X30 )
      = ( k3_subset_1 @ X30 @ ( k1_subset_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf('60',plain,(
    ! [X26: $i] :
      ( ( k2_subset_1 @ X26 )
      = X26 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('61',plain,(
    ! [X30: $i] :
      ( X30
      = ( k3_subset_1 @ X30 @ ( k1_subset_1 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['58','61'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('63',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X32 @ X31 ) @ ( k3_subset_1 @ X32 @ X33 ) )
      | ( r1_tarski @ X33 @ X31 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ X1 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('65',plain,(
    ! [X34: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['57','66'])).

thf('68',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['36','56'])).

thf('69',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('70',plain,
    ( ( k3_subset_1 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 )
    | ~ ( r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['67','70'])).

thf('72',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['17','18','19','22'])).

thf('73',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('74',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['24'])).

thf('75',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('76',plain,
    ( ( ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('78',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      = ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('80',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['73','80'])).

thf('82',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('83',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sat_resolution*',[status(thm)],['38','54','55'])).

thf('85',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference('sup+',[status(thm)],['72','85'])).

thf('87',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['5','7'])).

thf('88',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['71','86','87'])).

thf('89',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('90',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('95',plain,(
    sk_B = sk_A ),
    inference(demod,[status(thm)],['23','92','93','94'])).

thf('96',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['37'])).

thf('97',plain,(
    ! [X26: $i] :
      ( ( k2_subset_1 @ X26 )
      = X26 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('98',plain,
    ( ( sk_B != sk_A )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    sk_B
 != ( k2_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['38','54'])).

thf('100',plain,(
    sk_B != sk_A ),
    inference(simpl_trail,[status(thm)],['98','99'])).

thf('101',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['95','100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jvI4bVXU5U
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:26:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.47/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.65  % Solved by: fo/fo7.sh
% 0.47/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.65  % done 558 iterations in 0.187s
% 0.47/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.65  % SZS output start Refutation
% 0.47/0.65  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.47/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.65  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.47/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.65  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.47/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.65  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.47/0.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.47/0.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.65  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.47/0.65  thf(t92_xboole_1, axiom,
% 0.47/0.65    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.47/0.65  thf('0', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.47/0.65      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.47/0.65  thf(t39_subset_1, conjecture,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.47/0.65       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.47/0.65         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 0.47/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.65    (~( ![A:$i,B:$i]:
% 0.47/0.65        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.47/0.65          ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.47/0.65            ( ( B ) = ( k2_subset_1 @ A ) ) ) ) )),
% 0.47/0.65    inference('cnf.neg', [status(esa)], [t39_subset_1])).
% 0.47/0.65  thf('1', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(d2_subset_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( ( v1_xboole_0 @ A ) =>
% 0.47/0.65         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.47/0.65       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.47/0.65         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.47/0.65  thf('2', plain,
% 0.47/0.65      (![X22 : $i, X23 : $i]:
% 0.47/0.65         (~ (m1_subset_1 @ X22 @ X23)
% 0.47/0.65          | (r2_hidden @ X22 @ X23)
% 0.47/0.65          | (v1_xboole_0 @ X23))),
% 0.47/0.65      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.47/0.65  thf('3', plain,
% 0.47/0.65      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.47/0.65        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['1', '2'])).
% 0.47/0.65  thf(fc1_subset_1, axiom,
% 0.47/0.65    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.47/0.65  thf('4', plain, (![X29 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X29))),
% 0.47/0.65      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.47/0.65  thf('5', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.47/0.65      inference('clc', [status(thm)], ['3', '4'])).
% 0.47/0.65  thf(d1_zfmisc_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.47/0.65       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.47/0.65  thf('6', plain,
% 0.47/0.65      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.47/0.65         (~ (r2_hidden @ X20 @ X19)
% 0.47/0.65          | (r1_tarski @ X20 @ X18)
% 0.47/0.65          | ((X19) != (k1_zfmisc_1 @ X18)))),
% 0.47/0.65      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.47/0.65  thf('7', plain,
% 0.47/0.65      (![X18 : $i, X20 : $i]:
% 0.47/0.65         ((r1_tarski @ X20 @ X18) | ~ (r2_hidden @ X20 @ (k1_zfmisc_1 @ X18)))),
% 0.47/0.65      inference('simplify', [status(thm)], ['6'])).
% 0.47/0.65  thf('8', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.47/0.65      inference('sup-', [status(thm)], ['5', '7'])).
% 0.47/0.65  thf(t28_xboole_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.47/0.65  thf('9', plain,
% 0.47/0.65      (![X9 : $i, X10 : $i]:
% 0.47/0.65         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.47/0.65      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.47/0.65  thf('10', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.47/0.65      inference('sup-', [status(thm)], ['8', '9'])).
% 0.47/0.65  thf(commutativity_k3_xboole_0, axiom,
% 0.47/0.65    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.47/0.65  thf('11', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.47/0.65      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.47/0.65  thf('12', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.47/0.65      inference('demod', [status(thm)], ['10', '11'])).
% 0.47/0.65  thf(t100_xboole_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.47/0.65  thf('13', plain,
% 0.47/0.65      (![X7 : $i, X8 : $i]:
% 0.47/0.65         ((k4_xboole_0 @ X7 @ X8)
% 0.47/0.65           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.47/0.65      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.47/0.65  thf('14', plain,
% 0.47/0.65      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.47/0.65      inference('sup+', [status(thm)], ['12', '13'])).
% 0.47/0.65  thf(t91_xboole_1, axiom,
% 0.47/0.65    (![A:$i,B:$i,C:$i]:
% 0.47/0.65     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.47/0.65       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.47/0.65  thf('15', plain,
% 0.47/0.65      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.47/0.65         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.47/0.65           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.47/0.65      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.47/0.65  thf('16', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((k5_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ X0)
% 0.47/0.65           = (k5_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ X0)))),
% 0.47/0.65      inference('sup+', [status(thm)], ['14', '15'])).
% 0.47/0.65  thf('17', plain,
% 0.47/0.65      (((k5_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B)
% 0.47/0.65         = (k5_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.47/0.65      inference('sup+', [status(thm)], ['0', '16'])).
% 0.47/0.65  thf(commutativity_k5_xboole_0, axiom,
% 0.47/0.65    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.47/0.65  thf('18', plain,
% 0.47/0.65      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.47/0.65      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.47/0.65  thf('19', plain,
% 0.47/0.65      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.47/0.65      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.47/0.65  thf('20', plain,
% 0.47/0.65      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.47/0.65      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.47/0.65  thf(t5_boole, axiom,
% 0.47/0.65    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.47/0.65  thf('21', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.47/0.65      inference('cnf', [status(esa)], [t5_boole])).
% 0.47/0.65  thf('22', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.47/0.65      inference('sup+', [status(thm)], ['20', '21'])).
% 0.47/0.65  thf('23', plain,
% 0.47/0.65      (((k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 0.47/0.65      inference('demod', [status(thm)], ['17', '18', '19', '22'])).
% 0.47/0.65  thf('24', plain,
% 0.47/0.65      ((((sk_B) = (k2_subset_1 @ sk_A))
% 0.47/0.65        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('25', plain,
% 0.47/0.65      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.47/0.65         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.47/0.65      inference('split', [status(esa)], ['24'])).
% 0.47/0.65  thf('26', plain,
% 0.47/0.65      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.47/0.65         (~ (r1_tarski @ X17 @ X18)
% 0.47/0.65          | (r2_hidden @ X17 @ X19)
% 0.47/0.65          | ((X19) != (k1_zfmisc_1 @ X18)))),
% 0.47/0.65      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.47/0.65  thf('27', plain,
% 0.47/0.65      (![X17 : $i, X18 : $i]:
% 0.47/0.65         ((r2_hidden @ X17 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X17 @ X18))),
% 0.47/0.65      inference('simplify', [status(thm)], ['26'])).
% 0.47/0.65  thf('28', plain,
% 0.47/0.65      (((r2_hidden @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.47/0.65         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['25', '27'])).
% 0.47/0.65  thf('29', plain,
% 0.47/0.65      (![X22 : $i, X23 : $i]:
% 0.47/0.65         (~ (r2_hidden @ X22 @ X23)
% 0.47/0.65          | (m1_subset_1 @ X22 @ X23)
% 0.47/0.65          | (v1_xboole_0 @ X23))),
% 0.47/0.65      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.47/0.65  thf('30', plain,
% 0.47/0.65      ((((v1_xboole_0 @ (k1_zfmisc_1 @ sk_B))
% 0.47/0.65         | (m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))))
% 0.47/0.65         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['28', '29'])).
% 0.47/0.65  thf('31', plain, (![X29 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X29))),
% 0.47/0.65      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.47/0.65  thf('32', plain,
% 0.47/0.65      (((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.47/0.65         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.47/0.65      inference('clc', [status(thm)], ['30', '31'])).
% 0.47/0.66  thf('33', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(d5_subset_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.47/0.66       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.47/0.66  thf('34', plain,
% 0.47/0.66      (![X27 : $i, X28 : $i]:
% 0.47/0.66         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 0.47/0.66          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 0.47/0.66      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.47/0.66  thf('35', plain,
% 0.47/0.66      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.47/0.66      inference('sup-', [status(thm)], ['33', '34'])).
% 0.47/0.66  thf('36', plain,
% 0.47/0.66      (((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.47/0.66         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.47/0.66      inference('demod', [status(thm)], ['32', '35'])).
% 0.47/0.66  thf('37', plain,
% 0.47/0.66      ((((sk_B) != (k2_subset_1 @ sk_A))
% 0.47/0.66        | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('38', plain,
% 0.47/0.66      (~ (((sk_B) = (k2_subset_1 @ sk_A))) | 
% 0.47/0.66       ~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.47/0.66      inference('split', [status(esa)], ['37'])).
% 0.47/0.66  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.47/0.66  thf('39', plain, (![X26 : $i]: ((k2_subset_1 @ X26) = (X26))),
% 0.47/0.66      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.47/0.66  thf('40', plain,
% 0.47/0.66      ((((sk_B) = (k2_subset_1 @ sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.47/0.66      inference('split', [status(esa)], ['24'])).
% 0.47/0.66  thf('41', plain,
% 0.47/0.66      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.47/0.66      inference('sup+', [status(thm)], ['39', '40'])).
% 0.47/0.66  thf('42', plain,
% 0.47/0.66      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.47/0.66      inference('sup-', [status(thm)], ['33', '34'])).
% 0.47/0.66  thf('43', plain,
% 0.47/0.66      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.47/0.66         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.47/0.66      inference('split', [status(esa)], ['37'])).
% 0.47/0.66  thf('44', plain,
% 0.47/0.66      ((~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B))
% 0.47/0.66         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['42', '43'])).
% 0.47/0.66  thf('45', plain,
% 0.47/0.66      ((~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_A) @ sk_B))
% 0.47/0.66         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.47/0.66             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['41', '44'])).
% 0.47/0.66  thf('46', plain,
% 0.47/0.66      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.47/0.66      inference('sup+', [status(thm)], ['39', '40'])).
% 0.47/0.66  thf('47', plain,
% 0.47/0.66      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.47/0.66      inference('sup+', [status(thm)], ['12', '13'])).
% 0.47/0.66  thf('48', plain,
% 0.47/0.66      ((((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_A)))
% 0.47/0.66         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.47/0.66      inference('sup+', [status(thm)], ['46', '47'])).
% 0.47/0.66  thf('49', plain,
% 0.47/0.66      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.47/0.66      inference('sup+', [status(thm)], ['39', '40'])).
% 0.47/0.66  thf('50', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.47/0.66      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.47/0.66  thf('51', plain,
% 0.47/0.66      ((((k4_xboole_0 @ sk_A @ sk_A) = (k1_xboole_0)))
% 0.47/0.66         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.47/0.66      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.47/0.66  thf('52', plain,
% 0.47/0.66      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.47/0.66      inference('sup+', [status(thm)], ['39', '40'])).
% 0.47/0.66  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.47/0.66  thf('53', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.47/0.66      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.47/0.66  thf('54', plain,
% 0.47/0.66      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.47/0.66       ~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.47/0.66      inference('demod', [status(thm)], ['45', '51', '52', '53'])).
% 0.47/0.66  thf('55', plain,
% 0.47/0.66      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.47/0.66       (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.47/0.66      inference('split', [status(esa)], ['24'])).
% 0.47/0.66  thf('56', plain, (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.47/0.66      inference('sat_resolution*', [status(thm)], ['38', '54', '55'])).
% 0.47/0.66  thf('57', plain,
% 0.47/0.66      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 0.47/0.66      inference('simpl_trail', [status(thm)], ['36', '56'])).
% 0.47/0.66  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.47/0.66  thf('58', plain, (![X25 : $i]: ((k1_subset_1 @ X25) = (k1_xboole_0))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.47/0.66  thf(t22_subset_1, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.47/0.66  thf('59', plain,
% 0.47/0.66      (![X30 : $i]:
% 0.47/0.66         ((k2_subset_1 @ X30) = (k3_subset_1 @ X30 @ (k1_subset_1 @ X30)))),
% 0.47/0.66      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.47/0.66  thf('60', plain, (![X26 : $i]: ((k2_subset_1 @ X26) = (X26))),
% 0.47/0.66      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.47/0.66  thf('61', plain,
% 0.47/0.66      (![X30 : $i]: ((X30) = (k3_subset_1 @ X30 @ (k1_subset_1 @ X30)))),
% 0.47/0.66      inference('demod', [status(thm)], ['59', '60'])).
% 0.47/0.66  thf('62', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.47/0.66      inference('sup+', [status(thm)], ['58', '61'])).
% 0.47/0.66  thf(t31_subset_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.47/0.66       ( ![C:$i]:
% 0.47/0.66         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.47/0.66           ( ( r1_tarski @ B @ C ) <=>
% 0.47/0.66             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.47/0.66  thf('63', plain,
% 0.47/0.66      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.47/0.66         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 0.47/0.66          | ~ (r1_tarski @ (k3_subset_1 @ X32 @ X31) @ 
% 0.47/0.66               (k3_subset_1 @ X32 @ X33))
% 0.47/0.66          | (r1_tarski @ X33 @ X31)
% 0.47/0.66          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32)))),
% 0.47/0.66      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.47/0.66  thf('64', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (~ (r1_tarski @ X0 @ (k3_subset_1 @ X0 @ X1))
% 0.47/0.66          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.47/0.66          | (r1_tarski @ X1 @ k1_xboole_0)
% 0.47/0.66          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['62', '63'])).
% 0.47/0.66  thf(t4_subset_1, axiom,
% 0.47/0.66    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.47/0.66  thf('65', plain,
% 0.47/0.66      (![X34 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X34))),
% 0.47/0.66      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.47/0.66  thf('66', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (~ (r1_tarski @ X0 @ (k3_subset_1 @ X0 @ X1))
% 0.47/0.66          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.47/0.66          | (r1_tarski @ X1 @ k1_xboole_0))),
% 0.47/0.66      inference('demod', [status(thm)], ['64', '65'])).
% 0.47/0.66  thf('67', plain,
% 0.47/0.66      (((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0)
% 0.47/0.66        | ~ (r1_tarski @ sk_B @ 
% 0.47/0.66             (k3_subset_1 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['57', '66'])).
% 0.47/0.66  thf('68', plain,
% 0.47/0.66      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 0.47/0.66      inference('simpl_trail', [status(thm)], ['36', '56'])).
% 0.47/0.66  thf('69', plain,
% 0.47/0.66      (![X27 : $i, X28 : $i]:
% 0.47/0.66         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 0.47/0.66          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 0.47/0.66      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.47/0.66  thf('70', plain,
% 0.47/0.66      (((k3_subset_1 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.47/0.66         = (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['68', '69'])).
% 0.47/0.66  thf('71', plain,
% 0.47/0.66      (((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0)
% 0.47/0.66        | ~ (r1_tarski @ sk_B @ 
% 0.47/0.66             (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))))),
% 0.47/0.66      inference('demod', [status(thm)], ['67', '70'])).
% 0.47/0.66  thf('72', plain,
% 0.47/0.66      (((k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 0.47/0.66      inference('demod', [status(thm)], ['17', '18', '19', '22'])).
% 0.47/0.66  thf('73', plain,
% 0.47/0.66      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.47/0.66      inference('sup-', [status(thm)], ['33', '34'])).
% 0.47/0.66  thf('74', plain,
% 0.47/0.66      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.47/0.66         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.47/0.66      inference('split', [status(esa)], ['24'])).
% 0.47/0.66  thf('75', plain,
% 0.47/0.66      (![X9 : $i, X10 : $i]:
% 0.47/0.66         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.47/0.66      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.47/0.66  thf('76', plain,
% 0.47/0.66      ((((k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)
% 0.47/0.66          = (k3_subset_1 @ sk_A @ sk_B)))
% 0.47/0.66         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['74', '75'])).
% 0.47/0.66  thf('77', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.47/0.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.47/0.66  thf('78', plain,
% 0.47/0.66      ((((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.47/0.66          = (k3_subset_1 @ sk_A @ sk_B)))
% 0.47/0.66         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.47/0.66      inference('demod', [status(thm)], ['76', '77'])).
% 0.47/0.66  thf('79', plain,
% 0.47/0.66      (![X7 : $i, X8 : $i]:
% 0.47/0.66         ((k4_xboole_0 @ X7 @ X8)
% 0.47/0.66           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.47/0.66      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.47/0.66  thf('80', plain,
% 0.47/0.66      ((((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.47/0.66          = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))
% 0.47/0.66         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.47/0.66      inference('sup+', [status(thm)], ['78', '79'])).
% 0.47/0.66  thf('81', plain,
% 0.47/0.66      ((((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.47/0.66          = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))))
% 0.47/0.66         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.47/0.66      inference('sup+', [status(thm)], ['73', '80'])).
% 0.47/0.66  thf('82', plain,
% 0.47/0.66      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.47/0.66      inference('sup-', [status(thm)], ['33', '34'])).
% 0.47/0.66  thf('83', plain,
% 0.47/0.66      ((((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.47/0.66          = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))))
% 0.47/0.66         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.47/0.66      inference('demod', [status(thm)], ['81', '82'])).
% 0.47/0.66  thf('84', plain, (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.47/0.66      inference('sat_resolution*', [status(thm)], ['38', '54', '55'])).
% 0.47/0.66  thf('85', plain,
% 0.47/0.66      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.47/0.66         = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.47/0.66      inference('simpl_trail', [status(thm)], ['83', '84'])).
% 0.47/0.66  thf('86', plain,
% 0.47/0.66      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 0.47/0.66      inference('sup+', [status(thm)], ['72', '85'])).
% 0.47/0.66  thf('87', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.47/0.66      inference('sup-', [status(thm)], ['5', '7'])).
% 0.47/0.66  thf('88', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0)),
% 0.47/0.66      inference('demod', [status(thm)], ['71', '86', '87'])).
% 0.47/0.66  thf('89', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.47/0.66      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.47/0.66  thf(d10_xboole_0, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.66  thf('90', plain,
% 0.47/0.66      (![X4 : $i, X6 : $i]:
% 0.47/0.66         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.47/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.66  thf('91', plain,
% 0.47/0.66      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['89', '90'])).
% 0.47/0.66  thf('92', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['88', '91'])).
% 0.47/0.66  thf('93', plain,
% 0.47/0.66      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.47/0.66      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.47/0.66  thf('94', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.47/0.66      inference('sup+', [status(thm)], ['20', '21'])).
% 0.47/0.66  thf('95', plain, (((sk_B) = (sk_A))),
% 0.47/0.66      inference('demod', [status(thm)], ['23', '92', '93', '94'])).
% 0.47/0.66  thf('96', plain,
% 0.47/0.66      ((((sk_B) != (k2_subset_1 @ sk_A)))
% 0.47/0.66         <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.47/0.66      inference('split', [status(esa)], ['37'])).
% 0.47/0.66  thf('97', plain, (![X26 : $i]: ((k2_subset_1 @ X26) = (X26))),
% 0.47/0.66      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.47/0.66  thf('98', plain,
% 0.47/0.66      ((((sk_B) != (sk_A))) <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.47/0.66      inference('demod', [status(thm)], ['96', '97'])).
% 0.47/0.66  thf('99', plain, (~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.47/0.66      inference('sat_resolution*', [status(thm)], ['38', '54'])).
% 0.47/0.66  thf('100', plain, (((sk_B) != (sk_A))),
% 0.47/0.66      inference('simpl_trail', [status(thm)], ['98', '99'])).
% 0.47/0.66  thf('101', plain, ($false),
% 0.47/0.66      inference('simplify_reflect-', [status(thm)], ['95', '100'])).
% 0.47/0.66  
% 0.47/0.66  % SZS output end Refutation
% 0.47/0.66  
% 0.47/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

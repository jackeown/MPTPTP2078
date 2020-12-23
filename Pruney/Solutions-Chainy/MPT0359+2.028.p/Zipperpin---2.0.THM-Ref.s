%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UXkk1SptmI

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:35 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 317 expanded)
%              Number of leaves         :   33 ( 103 expanded)
%              Depth                    :   16
%              Number of atoms          :  881 (2500 expanded)
%              Number of equality atoms :   83 ( 243 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('1',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k3_subset_1 @ X40 @ ( k3_subset_1 @ X40 @ X39 ) )
        = X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
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

thf('4',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ X32 )
      | ( r2_hidden @ X31 @ X32 )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('6',plain,(
    ! [X38: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('7',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('8',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X29 @ X28 )
      | ( r1_tarski @ X29 @ X27 )
      | ( X28
       != ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('9',plain,(
    ! [X27: $i,X29: $i] :
      ( ( r1_tarski @ X29 @ X27 )
      | ~ ( r2_hidden @ X29 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['7','9'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('11',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('14',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['12','13'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('16',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X36 @ X37 )
        = ( k4_xboole_0 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('19',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('21',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X8 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('22',plain,(
    ! [X42: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('23',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X36 @ X37 )
        = ( k4_xboole_0 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('25',plain,(
    ! [X41: $i] :
      ( ( k2_subset_1 @ X41 )
      = ( k3_subset_1 @ X41 @ ( k1_subset_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('26',plain,(
    ! [X35: $i] :
      ( ( k2_subset_1 @ X35 )
      = X35 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('27',plain,(
    ! [X34: $i] :
      ( ( k1_subset_1 @ X34 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('28',plain,(
    ! [X41: $i] :
      ( X41
      = ( k3_subset_1 @ X41 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','28'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('30',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ~ ( r2_hidden @ X16 @ X14 )
      | ( X15
       != ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('31',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['21','33'])).

thf('35',plain,(
    ! [X42: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('36',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ X32 )
      | ( r2_hidden @ X31 @ X32 )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X38: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X27: $i,X29: $i] :
      ( ( r1_tarski @ X29 @ X27 )
      | ~ ( r2_hidden @ X29 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['34','45'])).

thf('47',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['47'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('49',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['53'])).

thf('55',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('56',plain,(
    ! [X18: $i] :
      ( ( k3_xboole_0 @ X18 @ X18 )
      = X18 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('57',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ( r2_hidden @ X16 @ X13 )
      | ( X15
       != ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('60',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( r2_hidden @ X16 @ X13 )
      | ~ ( r2_hidden @ X16 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('63',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['55','65'])).

thf('67',plain,(
    ! [X35: $i] :
      ( ( k2_subset_1 @ X35 )
      = X35 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('68',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['47'])).

thf('69',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X36 @ X37 )
        = ( k4_xboole_0 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('73',plain,
    ( ( ( k3_subset_1 @ sk_A @ sk_A )
      = ( k4_xboole_0 @ sk_A @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('75',plain,
    ( ( ( k3_subset_1 @ sk_A @ sk_A )
      = ( k5_xboole_0 @ sk_A @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('77',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['53'])).

thf('78',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('80',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_A ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_A ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['75','80'])).

thf('82',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','81'])).

thf('83',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['47'])).

thf('84',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sat_resolution*',[status(thm)],['54','82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['52','84'])).

thf('86',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('87',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['85','88'])).

thf('90',plain,
    ( ( k5_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['46','89'])).

thf('91',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','90'])).

thf('92',plain,(
    ! [X41: $i] :
      ( X41
      = ( k3_subset_1 @ X41 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('93',plain,(
    sk_A = sk_B ),
    inference(demod,[status(thm)],['2','91','92'])).

thf('94',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['53'])).

thf('95',plain,(
    ! [X35: $i] :
      ( ( k2_subset_1 @ X35 )
      = X35 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('96',plain,
    ( ( sk_B != sk_A )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    sk_B
 != ( k2_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['54','82'])).

thf('98',plain,(
    sk_B != sk_A ),
    inference(simpl_trail,[status(thm)],['96','97'])).

thf('99',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['93','98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UXkk1SptmI
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:11:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.63  % Solved by: fo/fo7.sh
% 0.46/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.63  % done 384 iterations in 0.182s
% 0.46/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.63  % SZS output start Refutation
% 0.46/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.63  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.63  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.63  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.46/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.63  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.46/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.63  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.46/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.63  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.46/0.63  thf(t39_subset_1, conjecture,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.63       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.46/0.63         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 0.46/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.63    (~( ![A:$i,B:$i]:
% 0.46/0.63        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.63          ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.46/0.63            ( ( B ) = ( k2_subset_1 @ A ) ) ) ) )),
% 0.46/0.63    inference('cnf.neg', [status(esa)], [t39_subset_1])).
% 0.46/0.63  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(involutiveness_k3_subset_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.63       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.46/0.63  thf('1', plain,
% 0.46/0.63      (![X39 : $i, X40 : $i]:
% 0.46/0.63         (((k3_subset_1 @ X40 @ (k3_subset_1 @ X40 @ X39)) = (X39))
% 0.46/0.63          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40)))),
% 0.46/0.63      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.46/0.63  thf('2', plain,
% 0.46/0.63      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.63  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(d2_subset_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( ( v1_xboole_0 @ A ) =>
% 0.46/0.63         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.46/0.63       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.63         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.46/0.63  thf('4', plain,
% 0.46/0.63      (![X31 : $i, X32 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X31 @ X32)
% 0.46/0.63          | (r2_hidden @ X31 @ X32)
% 0.46/0.63          | (v1_xboole_0 @ X32))),
% 0.46/0.63      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.46/0.63  thf('5', plain,
% 0.46/0.63      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.46/0.63        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.63  thf(fc1_subset_1, axiom,
% 0.46/0.63    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.46/0.63  thf('6', plain, (![X38 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X38))),
% 0.46/0.63      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.46/0.63  thf('7', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.63      inference('clc', [status(thm)], ['5', '6'])).
% 0.46/0.63  thf(d1_zfmisc_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.46/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.46/0.63  thf('8', plain,
% 0.46/0.63      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.46/0.63         (~ (r2_hidden @ X29 @ X28)
% 0.46/0.63          | (r1_tarski @ X29 @ X27)
% 0.46/0.63          | ((X28) != (k1_zfmisc_1 @ X27)))),
% 0.46/0.63      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.46/0.63  thf('9', plain,
% 0.46/0.63      (![X27 : $i, X29 : $i]:
% 0.46/0.63         ((r1_tarski @ X29 @ X27) | ~ (r2_hidden @ X29 @ (k1_zfmisc_1 @ X27)))),
% 0.46/0.63      inference('simplify', [status(thm)], ['8'])).
% 0.46/0.63  thf('10', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.46/0.63      inference('sup-', [status(thm)], ['7', '9'])).
% 0.46/0.63  thf(t28_xboole_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.46/0.63  thf('11', plain,
% 0.46/0.63      (![X23 : $i, X24 : $i]:
% 0.46/0.63         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 0.46/0.63      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.63  thf('12', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.63  thf(commutativity_k3_xboole_0, axiom,
% 0.46/0.63    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.46/0.63  thf('13', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.63  thf('14', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['12', '13'])).
% 0.46/0.63  thf(t100_xboole_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.63  thf('15', plain,
% 0.46/0.63      (![X21 : $i, X22 : $i]:
% 0.46/0.63         ((k4_xboole_0 @ X21 @ X22)
% 0.46/0.63           = (k5_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22)))),
% 0.46/0.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.63  thf('16', plain,
% 0.46/0.63      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.46/0.63      inference('sup+', [status(thm)], ['14', '15'])).
% 0.46/0.63  thf('17', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(d5_subset_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.63       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.46/0.63  thf('18', plain,
% 0.46/0.63      (![X36 : $i, X37 : $i]:
% 0.46/0.63         (((k3_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))
% 0.46/0.63          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 0.46/0.63      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.46/0.63  thf('19', plain,
% 0.46/0.63      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['17', '18'])).
% 0.46/0.63  thf('20', plain,
% 0.46/0.63      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.46/0.63      inference('sup+', [status(thm)], ['16', '19'])).
% 0.46/0.63  thf(d4_xboole_0, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.46/0.63       ( ![D:$i]:
% 0.46/0.63         ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.63           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.46/0.63  thf('21', plain,
% 0.46/0.63      (![X7 : $i, X8 : $i, X11 : $i]:
% 0.46/0.63         (((X11) = (k3_xboole_0 @ X7 @ X8))
% 0.46/0.63          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X8)
% 0.46/0.63          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 0.46/0.63      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.46/0.63  thf(t4_subset_1, axiom,
% 0.46/0.63    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.46/0.63  thf('22', plain,
% 0.46/0.63      (![X42 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X42))),
% 0.46/0.63      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.63  thf('23', plain,
% 0.46/0.63      (![X36 : $i, X37 : $i]:
% 0.46/0.63         (((k3_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))
% 0.46/0.63          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 0.46/0.63      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.46/0.63  thf('24', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['22', '23'])).
% 0.46/0.63  thf(t22_subset_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.46/0.63  thf('25', plain,
% 0.46/0.63      (![X41 : $i]:
% 0.46/0.63         ((k2_subset_1 @ X41) = (k3_subset_1 @ X41 @ (k1_subset_1 @ X41)))),
% 0.46/0.63      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.46/0.63  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.46/0.63  thf('26', plain, (![X35 : $i]: ((k2_subset_1 @ X35) = (X35))),
% 0.46/0.63      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.46/0.63  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.46/0.63  thf('27', plain, (![X34 : $i]: ((k1_subset_1 @ X34) = (k1_xboole_0))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.46/0.63  thf('28', plain, (![X41 : $i]: ((X41) = (k3_subset_1 @ X41 @ k1_xboole_0))),
% 0.46/0.63      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.46/0.63  thf('29', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.63      inference('demod', [status(thm)], ['24', '28'])).
% 0.46/0.63  thf(d5_xboole_0, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.46/0.63       ( ![D:$i]:
% 0.46/0.63         ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.63           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.46/0.63  thf('30', plain,
% 0.46/0.63      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.46/0.63         (~ (r2_hidden @ X16 @ X15)
% 0.46/0.63          | ~ (r2_hidden @ X16 @ X14)
% 0.46/0.63          | ((X15) != (k4_xboole_0 @ X13 @ X14)))),
% 0.46/0.63      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.46/0.63  thf('31', plain,
% 0.46/0.63      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.46/0.63         (~ (r2_hidden @ X16 @ X14)
% 0.46/0.63          | ~ (r2_hidden @ X16 @ (k4_xboole_0 @ X13 @ X14)))),
% 0.46/0.63      inference('simplify', [status(thm)], ['30'])).
% 0.46/0.63  thf('32', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['29', '31'])).
% 0.46/0.63  thf('33', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.46/0.63      inference('condensation', [status(thm)], ['32'])).
% 0.46/0.63  thf('34', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 0.46/0.63          | ((X1) = (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['21', '33'])).
% 0.46/0.63  thf('35', plain,
% 0.46/0.63      (![X42 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X42))),
% 0.46/0.63      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.63  thf('36', plain,
% 0.46/0.63      (![X31 : $i, X32 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X31 @ X32)
% 0.46/0.63          | (r2_hidden @ X31 @ X32)
% 0.46/0.63          | (v1_xboole_0 @ X32))),
% 0.46/0.63      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.46/0.63  thf('37', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.46/0.63          | (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.63  thf('38', plain, (![X38 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X38))),
% 0.46/0.63      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.46/0.63  thf('39', plain,
% 0.46/0.63      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.46/0.63      inference('clc', [status(thm)], ['37', '38'])).
% 0.46/0.63  thf('40', plain,
% 0.46/0.63      (![X27 : $i, X29 : $i]:
% 0.46/0.63         ((r1_tarski @ X29 @ X27) | ~ (r2_hidden @ X29 @ (k1_zfmisc_1 @ X27)))),
% 0.46/0.63      inference('simplify', [status(thm)], ['8'])).
% 0.46/0.63  thf('41', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.46/0.63      inference('sup-', [status(thm)], ['39', '40'])).
% 0.46/0.63  thf('42', plain,
% 0.46/0.63      (![X23 : $i, X24 : $i]:
% 0.46/0.63         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 0.46/0.63      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.63  thf('43', plain,
% 0.46/0.63      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['41', '42'])).
% 0.46/0.63  thf('44', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.63  thf('45', plain,
% 0.46/0.63      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.63      inference('sup+', [status(thm)], ['43', '44'])).
% 0.46/0.63  thf('46', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 0.46/0.63          | ((X1) = (k1_xboole_0)))),
% 0.46/0.63      inference('demod', [status(thm)], ['34', '45'])).
% 0.46/0.63  thf('47', plain,
% 0.46/0.63      ((((sk_B) = (k2_subset_1 @ sk_A))
% 0.46/0.63        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('48', plain,
% 0.46/0.63      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.46/0.63         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.46/0.63      inference('split', [status(esa)], ['47'])).
% 0.46/0.63  thf(d3_tarski, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( r1_tarski @ A @ B ) <=>
% 0.46/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.46/0.63  thf('49', plain,
% 0.46/0.63      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.63         (~ (r2_hidden @ X2 @ X3)
% 0.46/0.63          | (r2_hidden @ X2 @ X4)
% 0.46/0.63          | ~ (r1_tarski @ X3 @ X4))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.63  thf('50', plain,
% 0.46/0.63      ((![X0 : $i]:
% 0.46/0.63          ((r2_hidden @ X0 @ sk_B)
% 0.46/0.63           | ~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B))))
% 0.46/0.63         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['48', '49'])).
% 0.46/0.63  thf('51', plain,
% 0.46/0.63      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.46/0.63      inference('sup+', [status(thm)], ['16', '19'])).
% 0.46/0.63  thf('52', plain,
% 0.46/0.63      ((![X0 : $i]:
% 0.46/0.63          ((r2_hidden @ X0 @ sk_B)
% 0.46/0.63           | ~ (r2_hidden @ X0 @ (k5_xboole_0 @ sk_A @ sk_B))))
% 0.46/0.63         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.46/0.63      inference('demod', [status(thm)], ['50', '51'])).
% 0.46/0.63  thf('53', plain,
% 0.46/0.63      ((((sk_B) != (k2_subset_1 @ sk_A))
% 0.46/0.63        | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('54', plain,
% 0.46/0.63      (~ (((sk_B) = (k2_subset_1 @ sk_A))) | 
% 0.46/0.63       ~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.46/0.63      inference('split', [status(esa)], ['53'])).
% 0.46/0.63  thf('55', plain,
% 0.46/0.63      (![X3 : $i, X5 : $i]:
% 0.46/0.63         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.63  thf(idempotence_k3_xboole_0, axiom,
% 0.46/0.63    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.46/0.63  thf('56', plain, (![X18 : $i]: ((k3_xboole_0 @ X18 @ X18) = (X18))),
% 0.46/0.63      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.46/0.63  thf('57', plain,
% 0.46/0.63      (![X21 : $i, X22 : $i]:
% 0.46/0.63         ((k4_xboole_0 @ X21 @ X22)
% 0.46/0.63           = (k5_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22)))),
% 0.46/0.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.63  thf('58', plain,
% 0.46/0.63      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.63      inference('sup+', [status(thm)], ['56', '57'])).
% 0.46/0.63  thf('59', plain,
% 0.46/0.63      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.46/0.63         (~ (r2_hidden @ X16 @ X15)
% 0.46/0.63          | (r2_hidden @ X16 @ X13)
% 0.46/0.63          | ((X15) != (k4_xboole_0 @ X13 @ X14)))),
% 0.46/0.63      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.46/0.63  thf('60', plain,
% 0.46/0.63      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.46/0.63         ((r2_hidden @ X16 @ X13)
% 0.46/0.63          | ~ (r2_hidden @ X16 @ (k4_xboole_0 @ X13 @ X14)))),
% 0.46/0.63      inference('simplify', [status(thm)], ['59'])).
% 0.46/0.63  thf('61', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['58', '60'])).
% 0.46/0.63  thf('62', plain,
% 0.46/0.63      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.63      inference('sup+', [status(thm)], ['56', '57'])).
% 0.46/0.63  thf('63', plain,
% 0.46/0.63      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.46/0.63         (~ (r2_hidden @ X16 @ X14)
% 0.46/0.63          | ~ (r2_hidden @ X16 @ (k4_xboole_0 @ X13 @ X14)))),
% 0.46/0.63      inference('simplify', [status(thm)], ['30'])).
% 0.46/0.63  thf('64', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.46/0.63          | ~ (r2_hidden @ X1 @ X0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['62', '63'])).
% 0.46/0.63  thf('65', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.63      inference('clc', [status(thm)], ['61', '64'])).
% 0.46/0.63  thf('66', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X1)),
% 0.46/0.63      inference('sup-', [status(thm)], ['55', '65'])).
% 0.46/0.63  thf('67', plain, (![X35 : $i]: ((k2_subset_1 @ X35) = (X35))),
% 0.46/0.63      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.46/0.63  thf('68', plain,
% 0.46/0.63      ((((sk_B) = (k2_subset_1 @ sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.46/0.63      inference('split', [status(esa)], ['47'])).
% 0.46/0.63  thf('69', plain,
% 0.46/0.63      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.46/0.63      inference('sup+', [status(thm)], ['67', '68'])).
% 0.46/0.63  thf('70', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('71', plain,
% 0.46/0.63      (((m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ sk_A)))
% 0.46/0.63         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.46/0.63      inference('sup+', [status(thm)], ['69', '70'])).
% 0.46/0.63  thf('72', plain,
% 0.46/0.63      (![X36 : $i, X37 : $i]:
% 0.46/0.63         (((k3_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))
% 0.46/0.63          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 0.46/0.63      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.46/0.63  thf('73', plain,
% 0.46/0.63      ((((k3_subset_1 @ sk_A @ sk_A) = (k4_xboole_0 @ sk_A @ sk_A)))
% 0.46/0.63         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['71', '72'])).
% 0.46/0.63  thf('74', plain,
% 0.46/0.63      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.63      inference('sup+', [status(thm)], ['56', '57'])).
% 0.46/0.63  thf('75', plain,
% 0.46/0.63      ((((k3_subset_1 @ sk_A @ sk_A) = (k5_xboole_0 @ sk_A @ sk_A)))
% 0.46/0.63         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.46/0.63      inference('demod', [status(thm)], ['73', '74'])).
% 0.46/0.63  thf('76', plain,
% 0.46/0.63      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.46/0.63      inference('sup+', [status(thm)], ['67', '68'])).
% 0.46/0.63  thf('77', plain,
% 0.46/0.63      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.46/0.63         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.46/0.63      inference('split', [status(esa)], ['53'])).
% 0.46/0.63  thf('78', plain,
% 0.46/0.63      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A))
% 0.46/0.63         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.46/0.63             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['76', '77'])).
% 0.46/0.63  thf('79', plain,
% 0.46/0.63      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.46/0.63      inference('sup+', [status(thm)], ['67', '68'])).
% 0.46/0.63  thf('80', plain,
% 0.46/0.63      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_A) @ sk_A))
% 0.46/0.63         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.46/0.63             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.46/0.63      inference('demod', [status(thm)], ['78', '79'])).
% 0.46/0.63  thf('81', plain,
% 0.46/0.63      ((~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_A) @ sk_A))
% 0.46/0.63         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.46/0.63             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['75', '80'])).
% 0.46/0.63  thf('82', plain,
% 0.46/0.63      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.46/0.63       ~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['66', '81'])).
% 0.46/0.63  thf('83', plain,
% 0.46/0.63      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.46/0.63       (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.46/0.63      inference('split', [status(esa)], ['47'])).
% 0.46/0.63  thf('84', plain, (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.46/0.63      inference('sat_resolution*', [status(thm)], ['54', '82', '83'])).
% 0.46/0.63  thf('85', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((r2_hidden @ X0 @ sk_B)
% 0.46/0.63          | ~ (r2_hidden @ X0 @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 0.46/0.63      inference('simpl_trail', [status(thm)], ['52', '84'])).
% 0.46/0.63  thf('86', plain,
% 0.46/0.63      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.46/0.63      inference('sup+', [status(thm)], ['14', '15'])).
% 0.46/0.63  thf('87', plain,
% 0.46/0.63      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.46/0.63         (~ (r2_hidden @ X16 @ X14)
% 0.46/0.63          | ~ (r2_hidden @ X16 @ (k4_xboole_0 @ X13 @ X14)))),
% 0.46/0.63      inference('simplify', [status(thm)], ['30'])).
% 0.46/0.63  thf('88', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (r2_hidden @ X0 @ (k5_xboole_0 @ sk_A @ sk_B))
% 0.46/0.63          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['86', '87'])).
% 0.46/0.63  thf('89', plain,
% 0.46/0.63      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k5_xboole_0 @ sk_A @ sk_B))),
% 0.46/0.63      inference('clc', [status(thm)], ['85', '88'])).
% 0.46/0.63  thf('90', plain, (((k5_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['46', '89'])).
% 0.46/0.63  thf('91', plain, (((k3_subset_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.46/0.63      inference('demod', [status(thm)], ['20', '90'])).
% 0.46/0.63  thf('92', plain, (![X41 : $i]: ((X41) = (k3_subset_1 @ X41 @ k1_xboole_0))),
% 0.46/0.63      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.46/0.63  thf('93', plain, (((sk_A) = (sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['2', '91', '92'])).
% 0.46/0.63  thf('94', plain,
% 0.46/0.63      ((((sk_B) != (k2_subset_1 @ sk_A)))
% 0.46/0.63         <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.46/0.63      inference('split', [status(esa)], ['53'])).
% 0.46/0.63  thf('95', plain, (![X35 : $i]: ((k2_subset_1 @ X35) = (X35))),
% 0.46/0.63      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.46/0.63  thf('96', plain,
% 0.46/0.63      ((((sk_B) != (sk_A))) <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.46/0.63      inference('demod', [status(thm)], ['94', '95'])).
% 0.46/0.63  thf('97', plain, (~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.46/0.63      inference('sat_resolution*', [status(thm)], ['54', '82'])).
% 0.46/0.63  thf('98', plain, (((sk_B) != (sk_A))),
% 0.46/0.63      inference('simpl_trail', [status(thm)], ['96', '97'])).
% 0.46/0.63  thf('99', plain, ($false),
% 0.46/0.63      inference('simplify_reflect-', [status(thm)], ['93', '98'])).
% 0.46/0.63  
% 0.46/0.63  % SZS output end Refutation
% 0.46/0.63  
% 0.46/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

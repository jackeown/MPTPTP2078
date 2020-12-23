%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RTZwNzFJa0

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:50 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 922 expanded)
%              Number of leaves         :   33 ( 270 expanded)
%              Depth                    :   26
%              Number of atoms          : 1066 (14737 expanded)
%              Number of equality atoms :   89 ( 957 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t77_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( v2_funct_1 @ B )
      <=> ! [C: $i,D: $i] :
            ( ( ( r2_hidden @ C @ A )
              & ( r2_hidden @ D @ A )
              & ( ( k1_funct_1 @ B @ C )
                = ( k1_funct_1 @ B @ D ) ) )
           => ( C = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( ( v2_funct_1 @ B )
        <=> ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ D @ A )
                & ( ( k1_funct_1 @ B @ C )
                  = ( k1_funct_1 @ B @ D ) ) )
             => ( C = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_funct_2])).

thf('0',plain,
    ( ( r2_hidden @ sk_C_2 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_C_2 @ sk_A )
   <= ( r2_hidden @ sk_C_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('5',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
   <= ( r2_hidden @ sk_C_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    ! [X28: $i,X29: $i] :
      ( ( X29 = X28 )
      | ( ( k1_funct_1 @ sk_B_1 @ X29 )
       != ( k1_funct_1 @ sk_B_1 @ X28 ) )
      | ~ ( r2_hidden @ X28 @ sk_A )
      | ~ ( r2_hidden @ X29 @ sk_A )
      | ( v2_funct_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ! [X28: $i,X29: $i] :
        ( ( X29 = X28 )
        | ( ( k1_funct_1 @ sk_B_1 @ X29 )
         != ( k1_funct_1 @ sk_B_1 @ X28 ) )
        | ~ ( r2_hidden @ X28 @ sk_A )
        | ~ ( r2_hidden @ X29 @ sk_A ) ) ),
    inference(split,[status(esa)],['9'])).

thf(d8_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
      <=> ! [B: $i,C: $i] :
            ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
              & ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
              & ( ( k1_funct_1 @ A @ B )
                = ( k1_funct_1 @ A @ C ) ) )
           => ( B = C ) ) ) ) )).

thf('11',plain,(
    ! [X15: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X15 ) @ ( k1_relat_1 @ X15 ) )
      | ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('12',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('14',plain,(
    v4_relat_1 @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v4_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('18',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('19',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['16','19'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_C_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['11','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('25',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_C_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X15: $i] :
      ( ( ( k1_funct_1 @ X15 @ ( sk_B @ X15 ) )
        = ( k1_funct_1 @ X15 @ ( sk_C_1 @ X15 ) ) )
      | ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('28',plain,
    ( ! [X28: $i,X29: $i] :
        ( ( X29 = X28 )
        | ( ( k1_funct_1 @ sk_B_1 @ X29 )
         != ( k1_funct_1 @ sk_B_1 @ X28 ) )
        | ~ ( r2_hidden @ X28 @ sk_A )
        | ~ ( r2_hidden @ X29 @ sk_A ) )
   <= ! [X28: $i,X29: $i] :
        ( ( X29 = X28 )
        | ( ( k1_funct_1 @ sk_B_1 @ X29 )
         != ( k1_funct_1 @ sk_B_1 @ X28 ) )
        | ~ ( r2_hidden @ X28 @ sk_A )
        | ~ ( r2_hidden @ X29 @ sk_A ) ) ),
    inference(split,[status(esa)],['9'])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
        | ~ ( v1_relat_1 @ sk_B_1 )
        | ~ ( v1_funct_1 @ sk_B_1 )
        | ( v2_funct_1 @ sk_B_1 )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ ( sk_C_1 @ sk_B_1 ) @ sk_A )
        | ( X0
          = ( sk_C_1 @ sk_B_1 ) ) )
   <= ! [X28: $i,X29: $i] :
        ( ( X29 = X28 )
        | ( ( k1_funct_1 @ sk_B_1 @ X29 )
         != ( k1_funct_1 @ sk_B_1 @ X28 ) )
        | ~ ( r2_hidden @ X28 @ sk_A )
        | ~ ( r2_hidden @ X29 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('31',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
        | ( v2_funct_1 @ sk_B_1 )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ ( sk_C_1 @ sk_B_1 ) @ sk_A )
        | ( X0
          = ( sk_C_1 @ sk_B_1 ) ) )
   <= ! [X28: $i,X29: $i] :
        ( ( X29 = X28 )
        | ( ( k1_funct_1 @ sk_B_1 @ X29 )
         != ( k1_funct_1 @ sk_B_1 @ X28 ) )
        | ~ ( r2_hidden @ X28 @ sk_A )
        | ~ ( r2_hidden @ X29 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ! [X0: $i] :
        ( ( v2_funct_1 @ sk_B_1 )
        | ( X0
          = ( sk_C_1 @ sk_B_1 ) )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( v2_funct_1 @ sk_B_1 )
        | ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) )
   <= ! [X28: $i,X29: $i] :
        ( ( X29 = X28 )
        | ( ( k1_funct_1 @ sk_B_1 @ X29 )
         != ( k1_funct_1 @ sk_B_1 @ X28 ) )
        | ~ ( r2_hidden @ X28 @ sk_A )
        | ~ ( r2_hidden @ X29 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( X0
          = ( sk_C_1 @ sk_B_1 ) )
        | ( v2_funct_1 @ sk_B_1 ) )
   <= ! [X28: $i,X29: $i] :
        ( ( X29 = X28 )
        | ( ( k1_funct_1 @ sk_B_1 @ X29 )
         != ( k1_funct_1 @ sk_B_1 @ X28 ) )
        | ~ ( r2_hidden @ X28 @ sk_A )
        | ~ ( r2_hidden @ X29 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( ( v2_funct_1 @ sk_B_1 )
      | ( ( sk_B @ sk_B_1 )
        = ( sk_C_1 @ sk_B_1 ) )
      | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) )
   <= ! [X28: $i,X29: $i] :
        ( ( X29 = X28 )
        | ( ( k1_funct_1 @ sk_B_1 @ X29 )
         != ( k1_funct_1 @ sk_B_1 @ X28 ) )
        | ~ ( r2_hidden @ X28 @ sk_A )
        | ~ ( r2_hidden @ X29 @ sk_A ) ) ),
    inference(eq_res,[status(thm)],['34'])).

thf('36',plain,(
    ! [X15: $i] :
      ( ( r2_hidden @ ( sk_B @ X15 ) @ ( k1_relat_1 @ X15 ) )
      | ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('40',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ( ( ( sk_B @ sk_B_1 )
        = ( sk_C_1 @ sk_B_1 ) )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ! [X28: $i,X29: $i] :
        ( ( X29 = X28 )
        | ( ( k1_funct_1 @ sk_B_1 @ X29 )
         != ( k1_funct_1 @ sk_B_1 @ X28 ) )
        | ~ ( r2_hidden @ X28 @ sk_A )
        | ~ ( r2_hidden @ X29 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','41'])).

thf('43',plain,
    ( ~ ( v2_funct_1 @ sk_B_1 )
   <= ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('44',plain,
    ( ( ( sk_B @ sk_B_1 )
      = ( sk_C_1 @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X28: $i,X29: $i] :
          ( ( X29 = X28 )
          | ( ( k1_funct_1 @ sk_B_1 @ X29 )
           != ( k1_funct_1 @ sk_B_1 @ X28 ) )
          | ~ ( r2_hidden @ X28 @ sk_A )
          | ~ ( r2_hidden @ X29 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X15: $i] :
      ( ( ( sk_B @ X15 )
       != ( sk_C_1 @ X15 ) )
      | ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('46',plain,
    ( ( ( ( sk_B @ sk_B_1 )
       != ( sk_B @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X28: $i,X29: $i] :
          ( ( X29 = X28 )
          | ( ( k1_funct_1 @ sk_B_1 @ X29 )
           != ( k1_funct_1 @ sk_B_1 @ X28 ) )
          | ~ ( r2_hidden @ X28 @ sk_A )
          | ~ ( r2_hidden @ X29 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('48',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( ( sk_B @ sk_B_1 )
       != ( sk_B @ sk_B_1 ) )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X28: $i,X29: $i] :
          ( ( X29 = X28 )
          | ( ( k1_funct_1 @ sk_B_1 @ X29 )
           != ( k1_funct_1 @ sk_B_1 @ X28 ) )
          | ~ ( r2_hidden @ X28 @ sk_A )
          | ~ ( r2_hidden @ X29 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,
    ( ( v2_funct_1 @ sk_B_1 )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X28: $i,X29: $i] :
          ( ( X29 = X28 )
          | ( ( k1_funct_1 @ sk_B_1 @ X29 )
           != ( k1_funct_1 @ sk_B_1 @ X28 ) )
          | ~ ( r2_hidden @ X28 @ sk_A )
          | ~ ( r2_hidden @ X29 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ~ ( v2_funct_1 @ sk_B_1 )
   <= ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,
    ( ~ ! [X28: $i,X29: $i] :
          ( ( X29 = X28 )
          | ( ( k1_funct_1 @ sk_B_1 @ X29 )
           != ( k1_funct_1 @ sk_B_1 @ X28 ) )
          | ~ ( r2_hidden @ X28 @ sk_A )
          | ~ ( r2_hidden @ X29 @ sk_A ) )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( r2_hidden @ sk_C_2 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('54',plain,(
    r2_hidden @ sk_C_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['10','52','53'])).

thf('55',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['8','54'])).

thf('56',plain,
    ( ( r2_hidden @ sk_C_2 @ sk_A )
   <= ( r2_hidden @ sk_C_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('57',plain,(
    r2_hidden @ sk_C_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['10','52','53'])).

thf('58',plain,(
    r2_hidden @ sk_C_2 @ sk_A ),
    inference(simpl_trail,[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t32_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ D )
          & ( r2_hidden @ C @ A ) )
       => ( ( B = k1_xboole_0 )
          | ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) )
            = C ) ) ) ) )).

thf('60',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ( X26 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ X27 ) @ ( k1_funct_1 @ X27 @ X24 ) )
        = X24 )
      | ~ ( v2_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t32_funct_2])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ( v2_funct_1 @ sk_B_1 )
   <= ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['9'])).

thf('66',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['10','52'])).

thf('67',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(simpl_trail,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('69',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_C_2 ) )
      = sk_C_2 ) ),
    inference('sup-',[status(thm)],['58','68'])).

thf('70',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
   <= ( r2_hidden @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['70'])).

thf('72',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['70'])).

thf('73',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference('sat_resolution*',[status(thm)],['10','52','72'])).

thf('74',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(simpl_trail,[status(thm)],['71','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('76',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_D ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
   <= ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['77'])).

thf('79',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['77'])).

thf('80',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['10','52','79'])).

thf('81',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['78','80'])).

thf('82',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_C_2 ) )
      = sk_D ) ),
    inference(demod,[status(thm)],['76','81'])).

thf('83',plain,
    ( ( sk_C_2 = sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['69','82'])).

thf('84',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C_2 = sk_D ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ( sk_C_2 != sk_D )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( sk_C_2 != sk_D )
   <= ( sk_C_2 != sk_D ) ),
    inference(split,[status(esa)],['85'])).

thf('87',plain,
    ( ( sk_C_2 != sk_D )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['85'])).

thf('88',plain,(
    sk_C_2 != sk_D ),
    inference('sat_resolution*',[status(thm)],['10','52','87'])).

thf('89',plain,(
    sk_C_2 != sk_D ),
    inference(simpl_trail,[status(thm)],['86','88'])).

thf('90',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['84','89'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('91',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('92',plain,(
    $false ),
    inference(demod,[status(thm)],['55','90','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RTZwNzFJa0
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:17:10 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.38/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.63  % Solved by: fo/fo7.sh
% 0.38/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.63  % done 237 iterations in 0.173s
% 0.38/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.63  % SZS output start Refutation
% 0.38/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.63  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.38/0.63  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.63  thf(sk_B_type, type, sk_B: $i > $i).
% 0.38/0.63  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.38/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.63  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.38/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.63  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.38/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.63  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.38/0.63  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.38/0.63  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.38/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.63  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.38/0.63  thf(sk_D_type, type, sk_D: $i).
% 0.38/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.63  thf(t77_funct_2, conjecture,
% 0.38/0.63    (![A:$i,B:$i]:
% 0.38/0.63     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.38/0.63         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.38/0.63       ( ( v2_funct_1 @ B ) <=>
% 0.38/0.63         ( ![C:$i,D:$i]:
% 0.38/0.63           ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.38/0.63               ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.38/0.63             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.38/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.63    (~( ![A:$i,B:$i]:
% 0.38/0.63        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.38/0.63            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.38/0.63          ( ( v2_funct_1 @ B ) <=>
% 0.38/0.63            ( ![C:$i,D:$i]:
% 0.38/0.63              ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.38/0.63                  ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.38/0.63                ( ( C ) = ( D ) ) ) ) ) ) )),
% 0.38/0.63    inference('cnf.neg', [status(esa)], [t77_funct_2])).
% 0.38/0.63  thf('0', plain, (((r2_hidden @ sk_C_2 @ sk_A) | ~ (v2_funct_1 @ sk_B_1))),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('1', plain,
% 0.38/0.63      (((r2_hidden @ sk_C_2 @ sk_A)) <= (((r2_hidden @ sk_C_2 @ sk_A)))),
% 0.38/0.63      inference('split', [status(esa)], ['0'])).
% 0.38/0.63  thf(d10_xboole_0, axiom,
% 0.38/0.63    (![A:$i,B:$i]:
% 0.38/0.63     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.63  thf('2', plain,
% 0.38/0.63      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.38/0.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.63  thf('3', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.38/0.63      inference('simplify', [status(thm)], ['2'])).
% 0.38/0.63  thf(t3_subset, axiom,
% 0.38/0.63    (![A:$i,B:$i]:
% 0.38/0.63     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.63  thf('4', plain,
% 0.38/0.63      (![X7 : $i, X9 : $i]:
% 0.38/0.63         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.38/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.63  thf('5', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.38/0.63      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.63  thf(t5_subset, axiom,
% 0.38/0.63    (![A:$i,B:$i,C:$i]:
% 0.38/0.63     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.38/0.63          ( v1_xboole_0 @ C ) ) ))).
% 0.38/0.63  thf('6', plain,
% 0.38/0.63      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.38/0.63         (~ (r2_hidden @ X10 @ X11)
% 0.38/0.63          | ~ (v1_xboole_0 @ X12)
% 0.38/0.63          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.38/0.63      inference('cnf', [status(esa)], [t5_subset])).
% 0.38/0.63  thf('7', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.38/0.63      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.63  thf('8', plain,
% 0.38/0.63      ((~ (v1_xboole_0 @ sk_A)) <= (((r2_hidden @ sk_C_2 @ sk_A)))),
% 0.38/0.63      inference('sup-', [status(thm)], ['1', '7'])).
% 0.38/0.63  thf('9', plain,
% 0.38/0.63      (![X28 : $i, X29 : $i]:
% 0.38/0.63         (((X29) = (X28))
% 0.38/0.63          | ((k1_funct_1 @ sk_B_1 @ X29) != (k1_funct_1 @ sk_B_1 @ X28))
% 0.38/0.63          | ~ (r2_hidden @ X28 @ sk_A)
% 0.38/0.63          | ~ (r2_hidden @ X29 @ sk_A)
% 0.38/0.63          | (v2_funct_1 @ sk_B_1))),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('10', plain,
% 0.38/0.63      (((v2_funct_1 @ sk_B_1)) | 
% 0.38/0.63       (![X28 : $i, X29 : $i]:
% 0.38/0.63          (((X29) = (X28))
% 0.38/0.63           | ((k1_funct_1 @ sk_B_1 @ X29) != (k1_funct_1 @ sk_B_1 @ X28))
% 0.38/0.63           | ~ (r2_hidden @ X28 @ sk_A)
% 0.38/0.63           | ~ (r2_hidden @ X29 @ sk_A)))),
% 0.38/0.63      inference('split', [status(esa)], ['9'])).
% 0.38/0.63  thf(d8_funct_1, axiom,
% 0.38/0.63    (![A:$i]:
% 0.38/0.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.63       ( ( v2_funct_1 @ A ) <=>
% 0.38/0.63         ( ![B:$i,C:$i]:
% 0.38/0.63           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.38/0.63               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.38/0.63               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.38/0.63             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.38/0.63  thf('11', plain,
% 0.38/0.63      (![X15 : $i]:
% 0.38/0.63         ((r2_hidden @ (sk_C_1 @ X15) @ (k1_relat_1 @ X15))
% 0.38/0.63          | (v2_funct_1 @ X15)
% 0.38/0.63          | ~ (v1_funct_1 @ X15)
% 0.38/0.63          | ~ (v1_relat_1 @ X15))),
% 0.38/0.63      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.38/0.63  thf('12', plain,
% 0.38/0.63      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf(cc2_relset_1, axiom,
% 0.38/0.63    (![A:$i,B:$i,C:$i]:
% 0.38/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.63       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.38/0.63  thf('13', plain,
% 0.38/0.63      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.38/0.63         ((v4_relat_1 @ X21 @ X22)
% 0.38/0.63          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.38/0.63      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.38/0.63  thf('14', plain, ((v4_relat_1 @ sk_B_1 @ sk_A)),
% 0.38/0.63      inference('sup-', [status(thm)], ['12', '13'])).
% 0.38/0.63  thf(d18_relat_1, axiom,
% 0.38/0.63    (![A:$i,B:$i]:
% 0.38/0.63     ( ( v1_relat_1 @ B ) =>
% 0.38/0.63       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.38/0.63  thf('15', plain,
% 0.38/0.63      (![X13 : $i, X14 : $i]:
% 0.38/0.63         (~ (v4_relat_1 @ X13 @ X14)
% 0.38/0.63          | (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 0.38/0.63          | ~ (v1_relat_1 @ X13))),
% 0.38/0.63      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.38/0.63  thf('16', plain,
% 0.38/0.63      ((~ (v1_relat_1 @ sk_B_1) | (r1_tarski @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.38/0.63      inference('sup-', [status(thm)], ['14', '15'])).
% 0.38/0.63  thf('17', plain,
% 0.38/0.63      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf(cc1_relset_1, axiom,
% 0.38/0.63    (![A:$i,B:$i,C:$i]:
% 0.38/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.63       ( v1_relat_1 @ C ) ))).
% 0.38/0.63  thf('18', plain,
% 0.38/0.63      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.38/0.63         ((v1_relat_1 @ X18)
% 0.38/0.63          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.38/0.63      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.38/0.63  thf('19', plain, ((v1_relat_1 @ sk_B_1)),
% 0.38/0.63      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.63  thf('20', plain, ((r1_tarski @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 0.38/0.63      inference('demod', [status(thm)], ['16', '19'])).
% 0.38/0.63  thf(d3_tarski, axiom,
% 0.38/0.63    (![A:$i,B:$i]:
% 0.38/0.63     ( ( r1_tarski @ A @ B ) <=>
% 0.38/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.38/0.63  thf('21', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.63         (~ (r2_hidden @ X0 @ X1)
% 0.38/0.63          | (r2_hidden @ X0 @ X2)
% 0.38/0.63          | ~ (r1_tarski @ X1 @ X2))),
% 0.38/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.63  thf('22', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1)))),
% 0.38/0.63      inference('sup-', [status(thm)], ['20', '21'])).
% 0.38/0.63  thf('23', plain,
% 0.38/0.63      ((~ (v1_relat_1 @ sk_B_1)
% 0.38/0.63        | ~ (v1_funct_1 @ sk_B_1)
% 0.38/0.63        | (v2_funct_1 @ sk_B_1)
% 0.38/0.63        | (r2_hidden @ (sk_C_1 @ sk_B_1) @ sk_A))),
% 0.38/0.63      inference('sup-', [status(thm)], ['11', '22'])).
% 0.38/0.63  thf('24', plain, ((v1_relat_1 @ sk_B_1)),
% 0.38/0.63      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.63  thf('25', plain, ((v1_funct_1 @ sk_B_1)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('26', plain,
% 0.38/0.63      (((v2_funct_1 @ sk_B_1) | (r2_hidden @ (sk_C_1 @ sk_B_1) @ sk_A))),
% 0.38/0.63      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.38/0.63  thf('27', plain,
% 0.38/0.63      (![X15 : $i]:
% 0.38/0.63         (((k1_funct_1 @ X15 @ (sk_B @ X15))
% 0.38/0.63            = (k1_funct_1 @ X15 @ (sk_C_1 @ X15)))
% 0.38/0.63          | (v2_funct_1 @ X15)
% 0.38/0.63          | ~ (v1_funct_1 @ X15)
% 0.38/0.63          | ~ (v1_relat_1 @ X15))),
% 0.38/0.63      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.38/0.63  thf('28', plain,
% 0.38/0.63      ((![X28 : $i, X29 : $i]:
% 0.38/0.63          (((X29) = (X28))
% 0.38/0.63           | ((k1_funct_1 @ sk_B_1 @ X29) != (k1_funct_1 @ sk_B_1 @ X28))
% 0.38/0.63           | ~ (r2_hidden @ X28 @ sk_A)
% 0.38/0.63           | ~ (r2_hidden @ X29 @ sk_A)))
% 0.38/0.63         <= ((![X28 : $i, X29 : $i]:
% 0.38/0.63                (((X29) = (X28))
% 0.38/0.63                 | ((k1_funct_1 @ sk_B_1 @ X29) != (k1_funct_1 @ sk_B_1 @ X28))
% 0.38/0.63                 | ~ (r2_hidden @ X28 @ sk_A)
% 0.38/0.63                 | ~ (r2_hidden @ X29 @ sk_A))))),
% 0.38/0.63      inference('split', [status(esa)], ['9'])).
% 0.38/0.63  thf('29', plain,
% 0.38/0.63      ((![X0 : $i]:
% 0.38/0.63          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.38/0.63             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.38/0.63           | ~ (v1_relat_1 @ sk_B_1)
% 0.38/0.63           | ~ (v1_funct_1 @ sk_B_1)
% 0.38/0.63           | (v2_funct_1 @ sk_B_1)
% 0.38/0.63           | ~ (r2_hidden @ X0 @ sk_A)
% 0.38/0.63           | ~ (r2_hidden @ (sk_C_1 @ sk_B_1) @ sk_A)
% 0.38/0.63           | ((X0) = (sk_C_1 @ sk_B_1))))
% 0.38/0.63         <= ((![X28 : $i, X29 : $i]:
% 0.38/0.63                (((X29) = (X28))
% 0.38/0.63                 | ((k1_funct_1 @ sk_B_1 @ X29) != (k1_funct_1 @ sk_B_1 @ X28))
% 0.38/0.63                 | ~ (r2_hidden @ X28 @ sk_A)
% 0.38/0.63                 | ~ (r2_hidden @ X29 @ sk_A))))),
% 0.38/0.63      inference('sup-', [status(thm)], ['27', '28'])).
% 0.38/0.63  thf('30', plain, ((v1_relat_1 @ sk_B_1)),
% 0.38/0.63      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.63  thf('31', plain, ((v1_funct_1 @ sk_B_1)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('32', plain,
% 0.38/0.63      ((![X0 : $i]:
% 0.38/0.63          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.38/0.63             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.38/0.63           | (v2_funct_1 @ sk_B_1)
% 0.38/0.63           | ~ (r2_hidden @ X0 @ sk_A)
% 0.38/0.63           | ~ (r2_hidden @ (sk_C_1 @ sk_B_1) @ sk_A)
% 0.38/0.63           | ((X0) = (sk_C_1 @ sk_B_1))))
% 0.38/0.63         <= ((![X28 : $i, X29 : $i]:
% 0.38/0.63                (((X29) = (X28))
% 0.38/0.63                 | ((k1_funct_1 @ sk_B_1 @ X29) != (k1_funct_1 @ sk_B_1 @ X28))
% 0.38/0.63                 | ~ (r2_hidden @ X28 @ sk_A)
% 0.38/0.63                 | ~ (r2_hidden @ X29 @ sk_A))))),
% 0.38/0.63      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.38/0.63  thf('33', plain,
% 0.38/0.63      ((![X0 : $i]:
% 0.38/0.63          ((v2_funct_1 @ sk_B_1)
% 0.38/0.63           | ((X0) = (sk_C_1 @ sk_B_1))
% 0.38/0.63           | ~ (r2_hidden @ X0 @ sk_A)
% 0.38/0.63           | (v2_funct_1 @ sk_B_1)
% 0.38/0.63           | ((k1_funct_1 @ sk_B_1 @ X0)
% 0.38/0.63               != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))))
% 0.38/0.63         <= ((![X28 : $i, X29 : $i]:
% 0.38/0.63                (((X29) = (X28))
% 0.38/0.63                 | ((k1_funct_1 @ sk_B_1 @ X29) != (k1_funct_1 @ sk_B_1 @ X28))
% 0.38/0.63                 | ~ (r2_hidden @ X28 @ sk_A)
% 0.38/0.63                 | ~ (r2_hidden @ X29 @ sk_A))))),
% 0.38/0.63      inference('sup-', [status(thm)], ['26', '32'])).
% 0.38/0.63  thf('34', plain,
% 0.38/0.63      ((![X0 : $i]:
% 0.38/0.63          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.38/0.63             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.38/0.63           | ~ (r2_hidden @ X0 @ sk_A)
% 0.38/0.63           | ((X0) = (sk_C_1 @ sk_B_1))
% 0.38/0.63           | (v2_funct_1 @ sk_B_1)))
% 0.38/0.63         <= ((![X28 : $i, X29 : $i]:
% 0.38/0.63                (((X29) = (X28))
% 0.38/0.63                 | ((k1_funct_1 @ sk_B_1 @ X29) != (k1_funct_1 @ sk_B_1 @ X28))
% 0.38/0.63                 | ~ (r2_hidden @ X28 @ sk_A)
% 0.38/0.63                 | ~ (r2_hidden @ X29 @ sk_A))))),
% 0.38/0.63      inference('simplify', [status(thm)], ['33'])).
% 0.38/0.63  thf('35', plain,
% 0.38/0.63      ((((v2_funct_1 @ sk_B_1)
% 0.38/0.63         | ((sk_B @ sk_B_1) = (sk_C_1 @ sk_B_1))
% 0.38/0.63         | ~ (r2_hidden @ (sk_B @ sk_B_1) @ sk_A)))
% 0.38/0.63         <= ((![X28 : $i, X29 : $i]:
% 0.38/0.63                (((X29) = (X28))
% 0.38/0.63                 | ((k1_funct_1 @ sk_B_1 @ X29) != (k1_funct_1 @ sk_B_1 @ X28))
% 0.38/0.63                 | ~ (r2_hidden @ X28 @ sk_A)
% 0.38/0.63                 | ~ (r2_hidden @ X29 @ sk_A))))),
% 0.38/0.63      inference('eq_res', [status(thm)], ['34'])).
% 0.38/0.63  thf('36', plain,
% 0.38/0.63      (![X15 : $i]:
% 0.38/0.63         ((r2_hidden @ (sk_B @ X15) @ (k1_relat_1 @ X15))
% 0.38/0.63          | (v2_funct_1 @ X15)
% 0.38/0.63          | ~ (v1_funct_1 @ X15)
% 0.38/0.63          | ~ (v1_relat_1 @ X15))),
% 0.38/0.63      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.38/0.63  thf('37', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1)))),
% 0.38/0.63      inference('sup-', [status(thm)], ['20', '21'])).
% 0.38/0.63  thf('38', plain,
% 0.38/0.63      ((~ (v1_relat_1 @ sk_B_1)
% 0.38/0.63        | ~ (v1_funct_1 @ sk_B_1)
% 0.38/0.63        | (v2_funct_1 @ sk_B_1)
% 0.38/0.63        | (r2_hidden @ (sk_B @ sk_B_1) @ sk_A))),
% 0.38/0.63      inference('sup-', [status(thm)], ['36', '37'])).
% 0.38/0.63  thf('39', plain, ((v1_relat_1 @ sk_B_1)),
% 0.38/0.63      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.63  thf('40', plain, ((v1_funct_1 @ sk_B_1)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('41', plain,
% 0.38/0.63      (((v2_funct_1 @ sk_B_1) | (r2_hidden @ (sk_B @ sk_B_1) @ sk_A))),
% 0.38/0.63      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.38/0.63  thf('42', plain,
% 0.38/0.63      (((((sk_B @ sk_B_1) = (sk_C_1 @ sk_B_1)) | (v2_funct_1 @ sk_B_1)))
% 0.38/0.63         <= ((![X28 : $i, X29 : $i]:
% 0.38/0.63                (((X29) = (X28))
% 0.38/0.63                 | ((k1_funct_1 @ sk_B_1 @ X29) != (k1_funct_1 @ sk_B_1 @ X28))
% 0.38/0.63                 | ~ (r2_hidden @ X28 @ sk_A)
% 0.38/0.63                 | ~ (r2_hidden @ X29 @ sk_A))))),
% 0.38/0.63      inference('clc', [status(thm)], ['35', '41'])).
% 0.38/0.63  thf('43', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.38/0.63      inference('split', [status(esa)], ['0'])).
% 0.38/0.63  thf('44', plain,
% 0.38/0.63      ((((sk_B @ sk_B_1) = (sk_C_1 @ sk_B_1)))
% 0.38/0.63         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.38/0.63             (![X28 : $i, X29 : $i]:
% 0.38/0.63                (((X29) = (X28))
% 0.38/0.63                 | ((k1_funct_1 @ sk_B_1 @ X29) != (k1_funct_1 @ sk_B_1 @ X28))
% 0.38/0.63                 | ~ (r2_hidden @ X28 @ sk_A)
% 0.38/0.63                 | ~ (r2_hidden @ X29 @ sk_A))))),
% 0.38/0.63      inference('sup-', [status(thm)], ['42', '43'])).
% 0.38/0.63  thf('45', plain,
% 0.38/0.63      (![X15 : $i]:
% 0.38/0.63         (((sk_B @ X15) != (sk_C_1 @ X15))
% 0.38/0.63          | (v2_funct_1 @ X15)
% 0.38/0.63          | ~ (v1_funct_1 @ X15)
% 0.38/0.63          | ~ (v1_relat_1 @ X15))),
% 0.38/0.63      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.38/0.63  thf('46', plain,
% 0.38/0.63      (((((sk_B @ sk_B_1) != (sk_B @ sk_B_1))
% 0.38/0.63         | ~ (v1_relat_1 @ sk_B_1)
% 0.38/0.63         | ~ (v1_funct_1 @ sk_B_1)
% 0.38/0.63         | (v2_funct_1 @ sk_B_1)))
% 0.38/0.63         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.38/0.63             (![X28 : $i, X29 : $i]:
% 0.38/0.63                (((X29) = (X28))
% 0.38/0.63                 | ((k1_funct_1 @ sk_B_1 @ X29) != (k1_funct_1 @ sk_B_1 @ X28))
% 0.38/0.63                 | ~ (r2_hidden @ X28 @ sk_A)
% 0.38/0.63                 | ~ (r2_hidden @ X29 @ sk_A))))),
% 0.38/0.63      inference('sup-', [status(thm)], ['44', '45'])).
% 0.38/0.63  thf('47', plain, ((v1_relat_1 @ sk_B_1)),
% 0.38/0.63      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.63  thf('48', plain, ((v1_funct_1 @ sk_B_1)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('49', plain,
% 0.38/0.63      (((((sk_B @ sk_B_1) != (sk_B @ sk_B_1)) | (v2_funct_1 @ sk_B_1)))
% 0.38/0.63         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.38/0.63             (![X28 : $i, X29 : $i]:
% 0.38/0.63                (((X29) = (X28))
% 0.38/0.63                 | ((k1_funct_1 @ sk_B_1 @ X29) != (k1_funct_1 @ sk_B_1 @ X28))
% 0.38/0.63                 | ~ (r2_hidden @ X28 @ sk_A)
% 0.38/0.63                 | ~ (r2_hidden @ X29 @ sk_A))))),
% 0.38/0.63      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.38/0.63  thf('50', plain,
% 0.38/0.63      (((v2_funct_1 @ sk_B_1))
% 0.38/0.63         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.38/0.63             (![X28 : $i, X29 : $i]:
% 0.38/0.63                (((X29) = (X28))
% 0.38/0.63                 | ((k1_funct_1 @ sk_B_1 @ X29) != (k1_funct_1 @ sk_B_1 @ X28))
% 0.38/0.63                 | ~ (r2_hidden @ X28 @ sk_A)
% 0.38/0.63                 | ~ (r2_hidden @ X29 @ sk_A))))),
% 0.38/0.63      inference('simplify', [status(thm)], ['49'])).
% 0.38/0.63  thf('51', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.38/0.63      inference('split', [status(esa)], ['0'])).
% 0.38/0.63  thf('52', plain,
% 0.38/0.63      (~
% 0.38/0.63       (![X28 : $i, X29 : $i]:
% 0.38/0.63          (((X29) = (X28))
% 0.38/0.63           | ((k1_funct_1 @ sk_B_1 @ X29) != (k1_funct_1 @ sk_B_1 @ X28))
% 0.38/0.63           | ~ (r2_hidden @ X28 @ sk_A)
% 0.38/0.63           | ~ (r2_hidden @ X29 @ sk_A))) | 
% 0.38/0.63       ((v2_funct_1 @ sk_B_1))),
% 0.38/0.63      inference('sup-', [status(thm)], ['50', '51'])).
% 0.38/0.63  thf('53', plain, (((r2_hidden @ sk_C_2 @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.38/0.63      inference('split', [status(esa)], ['0'])).
% 0.38/0.63  thf('54', plain, (((r2_hidden @ sk_C_2 @ sk_A))),
% 0.38/0.63      inference('sat_resolution*', [status(thm)], ['10', '52', '53'])).
% 0.38/0.63  thf('55', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.38/0.63      inference('simpl_trail', [status(thm)], ['8', '54'])).
% 0.38/0.63  thf('56', plain,
% 0.38/0.63      (((r2_hidden @ sk_C_2 @ sk_A)) <= (((r2_hidden @ sk_C_2 @ sk_A)))),
% 0.38/0.63      inference('split', [status(esa)], ['0'])).
% 0.38/0.63  thf('57', plain, (((r2_hidden @ sk_C_2 @ sk_A))),
% 0.38/0.63      inference('sat_resolution*', [status(thm)], ['10', '52', '53'])).
% 0.38/0.63  thf('58', plain, ((r2_hidden @ sk_C_2 @ sk_A)),
% 0.38/0.63      inference('simpl_trail', [status(thm)], ['56', '57'])).
% 0.38/0.63  thf('59', plain,
% 0.38/0.63      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf(t32_funct_2, axiom,
% 0.38/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.63     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.38/0.63         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.63       ( ( ( v2_funct_1 @ D ) & ( r2_hidden @ C @ A ) ) =>
% 0.38/0.63         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.38/0.63           ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) ) =
% 0.38/0.63             ( C ) ) ) ) ))).
% 0.38/0.63  thf('60', plain,
% 0.38/0.63      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.38/0.63         (~ (r2_hidden @ X24 @ X25)
% 0.38/0.63          | ((X26) = (k1_xboole_0))
% 0.38/0.63          | ~ (v1_funct_1 @ X27)
% 0.38/0.63          | ~ (v1_funct_2 @ X27 @ X25 @ X26)
% 0.38/0.63          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.38/0.63          | ((k1_funct_1 @ (k2_funct_1 @ X27) @ (k1_funct_1 @ X27 @ X24))
% 0.38/0.63              = (X24))
% 0.38/0.63          | ~ (v2_funct_1 @ X27))),
% 0.38/0.63      inference('cnf', [status(esa)], [t32_funct_2])).
% 0.38/0.63  thf('61', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         (~ (v2_funct_1 @ sk_B_1)
% 0.38/0.63          | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.38/0.63              = (X0))
% 0.38/0.63          | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.38/0.63          | ~ (v1_funct_1 @ sk_B_1)
% 0.38/0.63          | ((sk_A) = (k1_xboole_0))
% 0.38/0.63          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.38/0.63      inference('sup-', [status(thm)], ['59', '60'])).
% 0.38/0.63  thf('62', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('63', plain, ((v1_funct_1 @ sk_B_1)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('64', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         (~ (v2_funct_1 @ sk_B_1)
% 0.38/0.63          | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.38/0.63              = (X0))
% 0.38/0.63          | ((sk_A) = (k1_xboole_0))
% 0.38/0.63          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.38/0.63      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.38/0.63  thf('65', plain, (((v2_funct_1 @ sk_B_1)) <= (((v2_funct_1 @ sk_B_1)))),
% 0.38/0.63      inference('split', [status(esa)], ['9'])).
% 0.38/0.63  thf('66', plain, (((v2_funct_1 @ sk_B_1))),
% 0.38/0.63      inference('sat_resolution*', [status(thm)], ['10', '52'])).
% 0.38/0.63  thf('67', plain, ((v2_funct_1 @ sk_B_1)),
% 0.38/0.63      inference('simpl_trail', [status(thm)], ['65', '66'])).
% 0.38/0.63  thf('68', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         (((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.38/0.63            = (X0))
% 0.38/0.63          | ((sk_A) = (k1_xboole_0))
% 0.38/0.63          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.38/0.63      inference('demod', [status(thm)], ['64', '67'])).
% 0.38/0.63  thf('69', plain,
% 0.38/0.63      ((((sk_A) = (k1_xboole_0))
% 0.38/0.63        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_C_2))
% 0.38/0.63            = (sk_C_2)))),
% 0.38/0.63      inference('sup-', [status(thm)], ['58', '68'])).
% 0.38/0.63  thf('70', plain, (((r2_hidden @ sk_D @ sk_A) | ~ (v2_funct_1 @ sk_B_1))),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('71', plain,
% 0.38/0.63      (((r2_hidden @ sk_D @ sk_A)) <= (((r2_hidden @ sk_D @ sk_A)))),
% 0.38/0.63      inference('split', [status(esa)], ['70'])).
% 0.38/0.63  thf('72', plain, (((r2_hidden @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.38/0.63      inference('split', [status(esa)], ['70'])).
% 0.38/0.63  thf('73', plain, (((r2_hidden @ sk_D @ sk_A))),
% 0.38/0.63      inference('sat_resolution*', [status(thm)], ['10', '52', '72'])).
% 0.38/0.63  thf('74', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.38/0.63      inference('simpl_trail', [status(thm)], ['71', '73'])).
% 0.38/0.63  thf('75', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         (((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.38/0.63            = (X0))
% 0.38/0.63          | ((sk_A) = (k1_xboole_0))
% 0.38/0.63          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.38/0.63      inference('demod', [status(thm)], ['64', '67'])).
% 0.38/0.63  thf('76', plain,
% 0.38/0.63      ((((sk_A) = (k1_xboole_0))
% 0.38/0.63        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_D))
% 0.38/0.63            = (sk_D)))),
% 0.38/0.63      inference('sup-', [status(thm)], ['74', '75'])).
% 0.38/0.63  thf('77', plain,
% 0.38/0.63      ((((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D))
% 0.38/0.63        | ~ (v2_funct_1 @ sk_B_1))),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('78', plain,
% 0.38/0.63      ((((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D)))
% 0.38/0.63         <= ((((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D))))),
% 0.38/0.63      inference('split', [status(esa)], ['77'])).
% 0.38/0.63  thf('79', plain,
% 0.38/0.63      ((((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D))) | 
% 0.38/0.63       ~ ((v2_funct_1 @ sk_B_1))),
% 0.38/0.63      inference('split', [status(esa)], ['77'])).
% 0.38/0.63  thf('80', plain,
% 0.38/0.63      ((((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D)))),
% 0.38/0.63      inference('sat_resolution*', [status(thm)], ['10', '52', '79'])).
% 0.38/0.63  thf('81', plain,
% 0.38/0.63      (((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D))),
% 0.38/0.63      inference('simpl_trail', [status(thm)], ['78', '80'])).
% 0.38/0.63  thf('82', plain,
% 0.38/0.63      ((((sk_A) = (k1_xboole_0))
% 0.38/0.63        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_C_2))
% 0.38/0.63            = (sk_D)))),
% 0.38/0.63      inference('demod', [status(thm)], ['76', '81'])).
% 0.38/0.63  thf('83', plain,
% 0.38/0.63      ((((sk_C_2) = (sk_D))
% 0.38/0.63        | ((sk_A) = (k1_xboole_0))
% 0.38/0.63        | ((sk_A) = (k1_xboole_0)))),
% 0.38/0.63      inference('sup+', [status(thm)], ['69', '82'])).
% 0.38/0.63  thf('84', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_C_2) = (sk_D)))),
% 0.38/0.63      inference('simplify', [status(thm)], ['83'])).
% 0.38/0.63  thf('85', plain, ((((sk_C_2) != (sk_D)) | ~ (v2_funct_1 @ sk_B_1))),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('86', plain, ((((sk_C_2) != (sk_D))) <= (~ (((sk_C_2) = (sk_D))))),
% 0.38/0.63      inference('split', [status(esa)], ['85'])).
% 0.38/0.63  thf('87', plain, (~ (((sk_C_2) = (sk_D))) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.38/0.63      inference('split', [status(esa)], ['85'])).
% 0.38/0.63  thf('88', plain, (~ (((sk_C_2) = (sk_D)))),
% 0.38/0.63      inference('sat_resolution*', [status(thm)], ['10', '52', '87'])).
% 0.38/0.63  thf('89', plain, (((sk_C_2) != (sk_D))),
% 0.38/0.63      inference('simpl_trail', [status(thm)], ['86', '88'])).
% 0.38/0.63  thf('90', plain, (((sk_A) = (k1_xboole_0))),
% 0.38/0.63      inference('simplify_reflect-', [status(thm)], ['84', '89'])).
% 0.38/0.63  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.38/0.63  thf('91', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.63      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.38/0.63  thf('92', plain, ($false),
% 0.38/0.63      inference('demod', [status(thm)], ['55', '90', '91'])).
% 0.38/0.63  
% 0.38/0.63  % SZS output end Refutation
% 0.38/0.63  
% 0.50/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

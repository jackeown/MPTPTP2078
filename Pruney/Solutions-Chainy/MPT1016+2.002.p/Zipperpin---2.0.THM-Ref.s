%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8N97tT5mvd

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 962 expanded)
%              Number of leaves         :   33 ( 284 expanded)
%              Depth                    :   27
%              Number of atoms          : 1064 (14999 expanded)
%              Number of equality atoms :   87 ( 953 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

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
    ( ( r2_hidden @ sk_C_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_A )
   <= ( r2_hidden @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
   <= ( r2_hidden @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    ! [X27: $i,X28: $i] :
      ( ( X28 = X27 )
      | ( ( k1_funct_1 @ sk_B_1 @ X28 )
       != ( k1_funct_1 @ sk_B_1 @ X27 ) )
      | ~ ( r2_hidden @ X27 @ sk_A )
      | ~ ( r2_hidden @ X28 @ sk_A )
      | ( v2_funct_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ! [X27: $i,X28: $i] :
        ( ( X28 = X27 )
        | ( ( k1_funct_1 @ sk_B_1 @ X28 )
         != ( k1_funct_1 @ sk_B_1 @ X27 ) )
        | ~ ( r2_hidden @ X27 @ sk_A )
        | ~ ( r2_hidden @ X28 @ sk_A ) ) ),
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
    ! [X14: $i] :
      ( ( r2_hidden @ ( sk_C @ X14 ) @ ( k1_relat_1 @ X14 ) )
      | ( v2_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ~ ( v4_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('19',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('23',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_C @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['11','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('27',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_C @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ! [X14: $i] :
      ( ( ( k1_funct_1 @ X14 @ ( sk_B @ X14 ) )
        = ( k1_funct_1 @ X14 @ ( sk_C @ X14 ) ) )
      | ( v2_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('30',plain,
    ( ! [X27: $i,X28: $i] :
        ( ( X28 = X27 )
        | ( ( k1_funct_1 @ sk_B_1 @ X28 )
         != ( k1_funct_1 @ sk_B_1 @ X27 ) )
        | ~ ( r2_hidden @ X27 @ sk_A )
        | ~ ( r2_hidden @ X28 @ sk_A ) )
   <= ! [X27: $i,X28: $i] :
        ( ( X28 = X27 )
        | ( ( k1_funct_1 @ sk_B_1 @ X28 )
         != ( k1_funct_1 @ sk_B_1 @ X27 ) )
        | ~ ( r2_hidden @ X27 @ sk_A )
        | ~ ( r2_hidden @ X28 @ sk_A ) ) ),
    inference(split,[status(esa)],['9'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
        | ~ ( v1_relat_1 @ sk_B_1 )
        | ~ ( v1_funct_1 @ sk_B_1 )
        | ( v2_funct_1 @ sk_B_1 )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ ( sk_C @ sk_B_1 ) @ sk_A )
        | ( X0
          = ( sk_C @ sk_B_1 ) ) )
   <= ! [X27: $i,X28: $i] :
        ( ( X28 = X27 )
        | ( ( k1_funct_1 @ sk_B_1 @ X28 )
         != ( k1_funct_1 @ sk_B_1 @ X27 ) )
        | ~ ( r2_hidden @ X27 @ sk_A )
        | ~ ( r2_hidden @ X28 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('33',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
        | ( v2_funct_1 @ sk_B_1 )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ ( sk_C @ sk_B_1 ) @ sk_A )
        | ( X0
          = ( sk_C @ sk_B_1 ) ) )
   <= ! [X27: $i,X28: $i] :
        ( ( X28 = X27 )
        | ( ( k1_funct_1 @ sk_B_1 @ X28 )
         != ( k1_funct_1 @ sk_B_1 @ X27 ) )
        | ~ ( r2_hidden @ X27 @ sk_A )
        | ~ ( r2_hidden @ X28 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ( v2_funct_1 @ sk_B_1 )
        | ( X0
          = ( sk_C @ sk_B_1 ) )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( v2_funct_1 @ sk_B_1 )
        | ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) )
   <= ! [X27: $i,X28: $i] :
        ( ( X28 = X27 )
        | ( ( k1_funct_1 @ sk_B_1 @ X28 )
         != ( k1_funct_1 @ sk_B_1 @ X27 ) )
        | ~ ( r2_hidden @ X27 @ sk_A )
        | ~ ( r2_hidden @ X28 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( X0
          = ( sk_C @ sk_B_1 ) )
        | ( v2_funct_1 @ sk_B_1 ) )
   <= ! [X27: $i,X28: $i] :
        ( ( X28 = X27 )
        | ( ( k1_funct_1 @ sk_B_1 @ X28 )
         != ( k1_funct_1 @ sk_B_1 @ X27 ) )
        | ~ ( r2_hidden @ X27 @ sk_A )
        | ~ ( r2_hidden @ X28 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( ( v2_funct_1 @ sk_B_1 )
      | ( ( sk_B @ sk_B_1 )
        = ( sk_C @ sk_B_1 ) )
      | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) )
   <= ! [X27: $i,X28: $i] :
        ( ( X28 = X27 )
        | ( ( k1_funct_1 @ sk_B_1 @ X28 )
         != ( k1_funct_1 @ sk_B_1 @ X27 ) )
        | ~ ( r2_hidden @ X27 @ sk_A )
        | ~ ( r2_hidden @ X28 @ sk_A ) ) ),
    inference(eq_res,[status(thm)],['36'])).

thf('38',plain,(
    ! [X14: $i] :
      ( ( r2_hidden @ ( sk_B @ X14 ) @ ( k1_relat_1 @ X14 ) )
      | ( v2_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('42',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ( ( ( sk_B @ sk_B_1 )
        = ( sk_C @ sk_B_1 ) )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ! [X27: $i,X28: $i] :
        ( ( X28 = X27 )
        | ( ( k1_funct_1 @ sk_B_1 @ X28 )
         != ( k1_funct_1 @ sk_B_1 @ X27 ) )
        | ~ ( r2_hidden @ X27 @ sk_A )
        | ~ ( r2_hidden @ X28 @ sk_A ) ) ),
    inference(clc,[status(thm)],['37','43'])).

thf('45',plain,
    ( ~ ( v2_funct_1 @ sk_B_1 )
   <= ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('46',plain,
    ( ( ( sk_B @ sk_B_1 )
      = ( sk_C @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X27: $i,X28: $i] :
          ( ( X28 = X27 )
          | ( ( k1_funct_1 @ sk_B_1 @ X28 )
           != ( k1_funct_1 @ sk_B_1 @ X27 ) )
          | ~ ( r2_hidden @ X27 @ sk_A )
          | ~ ( r2_hidden @ X28 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X14: $i] :
      ( ( ( sk_B @ X14 )
       != ( sk_C @ X14 ) )
      | ( v2_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('48',plain,
    ( ( ( ( sk_B @ sk_B_1 )
       != ( sk_B @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X27: $i,X28: $i] :
          ( ( X28 = X27 )
          | ( ( k1_funct_1 @ sk_B_1 @ X28 )
           != ( k1_funct_1 @ sk_B_1 @ X27 ) )
          | ~ ( r2_hidden @ X27 @ sk_A )
          | ~ ( r2_hidden @ X28 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('50',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( ( ( sk_B @ sk_B_1 )
       != ( sk_B @ sk_B_1 ) )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X27: $i,X28: $i] :
          ( ( X28 = X27 )
          | ( ( k1_funct_1 @ sk_B_1 @ X28 )
           != ( k1_funct_1 @ sk_B_1 @ X27 ) )
          | ~ ( r2_hidden @ X27 @ sk_A )
          | ~ ( r2_hidden @ X28 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ( v2_funct_1 @ sk_B_1 )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X27: $i,X28: $i] :
          ( ( X28 = X27 )
          | ( ( k1_funct_1 @ sk_B_1 @ X28 )
           != ( k1_funct_1 @ sk_B_1 @ X27 ) )
          | ~ ( r2_hidden @ X27 @ sk_A )
          | ~ ( r2_hidden @ X28 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ~ ( v2_funct_1 @ sk_B_1 )
   <= ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('54',plain,
    ( ~ ! [X27: $i,X28: $i] :
          ( ( X28 = X27 )
          | ( ( k1_funct_1 @ sk_B_1 @ X28 )
           != ( k1_funct_1 @ sk_B_1 @ X27 ) )
          | ~ ( r2_hidden @ X27 @ sk_A )
          | ~ ( r2_hidden @ X28 @ sk_A ) )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('56',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['10','54','55'])).

thf('57',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['8','56'])).

thf('58',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_A )
   <= ( r2_hidden @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('59',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['10','54','55'])).

thf('60',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['58','59'])).

thf('61',plain,(
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

thf('62',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X23 @ X24 )
      | ( X25 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ X26 ) @ ( k1_funct_1 @ X26 @ X23 ) )
        = X23 )
      | ~ ( v2_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t32_funct_2])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( v2_funct_1 @ sk_B_1 )
   <= ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['9'])).

thf('65',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['10','54'])).

thf('66',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(simpl_trail,[status(thm)],['64','65'])).

thf('67',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','66','67','68'])).

thf('70',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_C_1 ) )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['60','69'])).

thf('71',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
   <= ( r2_hidden @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['71'])).

thf('73',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['71'])).

thf('74',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference('sat_resolution*',[status(thm)],['10','54','73'])).

thf('75',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(simpl_trail,[status(thm)],['72','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','66','67','68'])).

thf('77',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_D ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
   <= ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['78'])).

thf('80',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['78'])).

thf('81',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['10','54','80'])).

thf('82',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['79','81'])).

thf('83',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_C_1 ) )
      = sk_D ) ),
    inference(demod,[status(thm)],['77','82'])).

thf('84',plain,
    ( ( sk_C_1 = sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['70','83'])).

thf('85',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C_1 = sk_D ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,
    ( ( sk_C_1 != sk_D )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( sk_C_1 != sk_D )
   <= ( sk_C_1 != sk_D ) ),
    inference(split,[status(esa)],['86'])).

thf('88',plain,
    ( ( sk_C_1 != sk_D )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['86'])).

thf('89',plain,(
    sk_C_1 != sk_D ),
    inference('sat_resolution*',[status(thm)],['10','54','88'])).

thf('90',plain,(
    sk_C_1 != sk_D ),
    inference(simpl_trail,[status(thm)],['87','89'])).

thf('91',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['85','90'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('92',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('93',plain,(
    $false ),
    inference(demod,[status(thm)],['57','91','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8N97tT5mvd
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:38:17 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 135 iterations in 0.061s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.52  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.22/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.52  thf(sk_C_type, type, sk_C: $i > $i).
% 0.22/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.52  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.22/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.52  thf(t77_funct_2, conjecture,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.22/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.52       ( ( v2_funct_1 @ B ) <=>
% 0.22/0.52         ( ![C:$i,D:$i]:
% 0.22/0.52           ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.22/0.52               ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.22/0.52             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i,B:$i]:
% 0.22/0.52        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.22/0.52            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.52          ( ( v2_funct_1 @ B ) <=>
% 0.22/0.52            ( ![C:$i,D:$i]:
% 0.22/0.52              ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.22/0.52                  ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.22/0.52                ( ( C ) = ( D ) ) ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t77_funct_2])).
% 0.22/0.52  thf('0', plain, (((r2_hidden @ sk_C_1 @ sk_A) | ~ (v2_funct_1 @ sk_B_1))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      (((r2_hidden @ sk_C_1 @ sk_A)) <= (((r2_hidden @ sk_C_1 @ sk_A)))),
% 0.22/0.52      inference('split', [status(esa)], ['0'])).
% 0.22/0.52  thf(d10_xboole_0, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.22/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.52  thf('3', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.52      inference('simplify', [status(thm)], ['2'])).
% 0.22/0.52  thf(t3_subset, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      (![X6 : $i, X8 : $i]:
% 0.22/0.52         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.22/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.52  thf('5', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.52  thf(t5_subset, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.22/0.52          ( v1_xboole_0 @ C ) ) ))).
% 0.22/0.52  thf('6', plain,
% 0.22/0.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X9 @ X10)
% 0.22/0.52          | ~ (v1_xboole_0 @ X11)
% 0.22/0.52          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t5_subset])).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      ((~ (v1_xboole_0 @ sk_A)) <= (((r2_hidden @ sk_C_1 @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['1', '7'])).
% 0.22/0.52  thf('9', plain,
% 0.22/0.52      (![X27 : $i, X28 : $i]:
% 0.22/0.52         (((X28) = (X27))
% 0.22/0.52          | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.22/0.52          | ~ (r2_hidden @ X27 @ sk_A)
% 0.22/0.52          | ~ (r2_hidden @ X28 @ sk_A)
% 0.22/0.52          | (v2_funct_1 @ sk_B_1))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      (((v2_funct_1 @ sk_B_1)) | 
% 0.22/0.52       (![X27 : $i, X28 : $i]:
% 0.22/0.52          (((X28) = (X27))
% 0.22/0.52           | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.22/0.52           | ~ (r2_hidden @ X27 @ sk_A)
% 0.22/0.52           | ~ (r2_hidden @ X28 @ sk_A)))),
% 0.22/0.52      inference('split', [status(esa)], ['9'])).
% 0.22/0.52  thf(d8_funct_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.52       ( ( v2_funct_1 @ A ) <=>
% 0.22/0.52         ( ![B:$i,C:$i]:
% 0.22/0.52           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.22/0.52               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.22/0.52               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.22/0.52             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      (![X14 : $i]:
% 0.22/0.52         ((r2_hidden @ (sk_C @ X14) @ (k1_relat_1 @ X14))
% 0.22/0.52          | (v2_funct_1 @ X14)
% 0.22/0.52          | ~ (v1_funct_1 @ X14)
% 0.22/0.52          | ~ (v1_relat_1 @ X14))),
% 0.22/0.52      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(cc2_relset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.52       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.52         ((v4_relat_1 @ X20 @ X21)
% 0.22/0.52          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.52  thf('14', plain, ((v4_relat_1 @ sk_B_1 @ sk_A)),
% 0.22/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.52  thf(d18_relat_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ B ) =>
% 0.22/0.52       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      (![X12 : $i, X13 : $i]:
% 0.22/0.52         (~ (v4_relat_1 @ X12 @ X13)
% 0.22/0.52          | (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.22/0.52          | ~ (v1_relat_1 @ X12))),
% 0.22/0.52      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      ((~ (v1_relat_1 @ sk_B_1) | (r1_tarski @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.52  thf('17', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(cc1_relset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.52       ( v1_relat_1 @ C ) ))).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.52         ((v1_relat_1 @ X17)
% 0.22/0.52          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.52  thf('19', plain, ((v1_relat_1 @ sk_B_1)),
% 0.22/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.52  thf('20', plain, ((r1_tarski @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 0.22/0.52      inference('demod', [status(thm)], ['16', '19'])).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      (![X6 : $i, X8 : $i]:
% 0.22/0.52         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.22/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.52  thf('22', plain,
% 0.22/0.52      ((m1_subset_1 @ (k1_relat_1 @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.52  thf(l3_subset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X3 @ X4)
% 0.22/0.52          | (r2_hidden @ X3 @ X5)
% 0.22/0.52          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.22/0.52      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      ((~ (v1_relat_1 @ sk_B_1)
% 0.22/0.52        | ~ (v1_funct_1 @ sk_B_1)
% 0.22/0.52        | (v2_funct_1 @ sk_B_1)
% 0.22/0.52        | (r2_hidden @ (sk_C @ sk_B_1) @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['11', '24'])).
% 0.22/0.52  thf('26', plain, ((v1_relat_1 @ sk_B_1)),
% 0.22/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.52  thf('27', plain, ((v1_funct_1 @ sk_B_1)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('28', plain,
% 0.22/0.52      (((v2_funct_1 @ sk_B_1) | (r2_hidden @ (sk_C @ sk_B_1) @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      (![X14 : $i]:
% 0.22/0.52         (((k1_funct_1 @ X14 @ (sk_B @ X14))
% 0.22/0.52            = (k1_funct_1 @ X14 @ (sk_C @ X14)))
% 0.22/0.52          | (v2_funct_1 @ X14)
% 0.22/0.52          | ~ (v1_funct_1 @ X14)
% 0.22/0.52          | ~ (v1_relat_1 @ X14))),
% 0.22/0.52      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.22/0.52  thf('30', plain,
% 0.22/0.52      ((![X27 : $i, X28 : $i]:
% 0.22/0.52          (((X28) = (X27))
% 0.22/0.52           | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.22/0.52           | ~ (r2_hidden @ X27 @ sk_A)
% 0.22/0.52           | ~ (r2_hidden @ X28 @ sk_A)))
% 0.22/0.52         <= ((![X27 : $i, X28 : $i]:
% 0.22/0.52                (((X28) = (X27))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.22/0.52                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.22/0.52      inference('split', [status(esa)], ['9'])).
% 0.22/0.52  thf('31', plain,
% 0.22/0.52      ((![X0 : $i]:
% 0.22/0.52          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.22/0.52             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.22/0.52           | ~ (v1_relat_1 @ sk_B_1)
% 0.22/0.52           | ~ (v1_funct_1 @ sk_B_1)
% 0.22/0.52           | (v2_funct_1 @ sk_B_1)
% 0.22/0.52           | ~ (r2_hidden @ X0 @ sk_A)
% 0.22/0.52           | ~ (r2_hidden @ (sk_C @ sk_B_1) @ sk_A)
% 0.22/0.52           | ((X0) = (sk_C @ sk_B_1))))
% 0.22/0.52         <= ((![X27 : $i, X28 : $i]:
% 0.22/0.52                (((X28) = (X27))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.22/0.52                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.52  thf('32', plain, ((v1_relat_1 @ sk_B_1)),
% 0.22/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.52  thf('33', plain, ((v1_funct_1 @ sk_B_1)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('34', plain,
% 0.22/0.52      ((![X0 : $i]:
% 0.22/0.52          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.22/0.52             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.22/0.52           | (v2_funct_1 @ sk_B_1)
% 0.22/0.52           | ~ (r2_hidden @ X0 @ sk_A)
% 0.22/0.52           | ~ (r2_hidden @ (sk_C @ sk_B_1) @ sk_A)
% 0.22/0.52           | ((X0) = (sk_C @ sk_B_1))))
% 0.22/0.52         <= ((![X27 : $i, X28 : $i]:
% 0.22/0.52                (((X28) = (X27))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.22/0.52                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.22/0.52      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.22/0.52  thf('35', plain,
% 0.22/0.52      ((![X0 : $i]:
% 0.22/0.52          ((v2_funct_1 @ sk_B_1)
% 0.22/0.52           | ((X0) = (sk_C @ sk_B_1))
% 0.22/0.52           | ~ (r2_hidden @ X0 @ sk_A)
% 0.22/0.52           | (v2_funct_1 @ sk_B_1)
% 0.22/0.52           | ((k1_funct_1 @ sk_B_1 @ X0)
% 0.22/0.52               != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))))
% 0.22/0.52         <= ((![X27 : $i, X28 : $i]:
% 0.22/0.52                (((X28) = (X27))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.22/0.52                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['28', '34'])).
% 0.22/0.52  thf('36', plain,
% 0.22/0.52      ((![X0 : $i]:
% 0.22/0.52          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.22/0.52             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.22/0.52           | ~ (r2_hidden @ X0 @ sk_A)
% 0.22/0.52           | ((X0) = (sk_C @ sk_B_1))
% 0.22/0.52           | (v2_funct_1 @ sk_B_1)))
% 0.22/0.52         <= ((![X27 : $i, X28 : $i]:
% 0.22/0.52                (((X28) = (X27))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.22/0.52                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.22/0.52      inference('simplify', [status(thm)], ['35'])).
% 0.22/0.52  thf('37', plain,
% 0.22/0.52      ((((v2_funct_1 @ sk_B_1)
% 0.22/0.52         | ((sk_B @ sk_B_1) = (sk_C @ sk_B_1))
% 0.22/0.52         | ~ (r2_hidden @ (sk_B @ sk_B_1) @ sk_A)))
% 0.22/0.52         <= ((![X27 : $i, X28 : $i]:
% 0.22/0.52                (((X28) = (X27))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.22/0.52                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.22/0.52      inference('eq_res', [status(thm)], ['36'])).
% 0.22/0.52  thf('38', plain,
% 0.22/0.52      (![X14 : $i]:
% 0.22/0.52         ((r2_hidden @ (sk_B @ X14) @ (k1_relat_1 @ X14))
% 0.22/0.52          | (v2_funct_1 @ X14)
% 0.22/0.52          | ~ (v1_funct_1 @ X14)
% 0.22/0.52          | ~ (v1_relat_1 @ X14))),
% 0.22/0.52      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.22/0.52  thf('39', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.52  thf('40', plain,
% 0.22/0.52      ((~ (v1_relat_1 @ sk_B_1)
% 0.22/0.52        | ~ (v1_funct_1 @ sk_B_1)
% 0.22/0.52        | (v2_funct_1 @ sk_B_1)
% 0.22/0.52        | (r2_hidden @ (sk_B @ sk_B_1) @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['38', '39'])).
% 0.22/0.52  thf('41', plain, ((v1_relat_1 @ sk_B_1)),
% 0.22/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.52  thf('42', plain, ((v1_funct_1 @ sk_B_1)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('43', plain,
% 0.22/0.52      (((v2_funct_1 @ sk_B_1) | (r2_hidden @ (sk_B @ sk_B_1) @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.22/0.52  thf('44', plain,
% 0.22/0.52      (((((sk_B @ sk_B_1) = (sk_C @ sk_B_1)) | (v2_funct_1 @ sk_B_1)))
% 0.22/0.52         <= ((![X27 : $i, X28 : $i]:
% 0.22/0.52                (((X28) = (X27))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.22/0.52                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.22/0.52      inference('clc', [status(thm)], ['37', '43'])).
% 0.22/0.52  thf('45', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.22/0.52      inference('split', [status(esa)], ['0'])).
% 0.22/0.52  thf('46', plain,
% 0.22/0.52      ((((sk_B @ sk_B_1) = (sk_C @ sk_B_1)))
% 0.22/0.52         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.22/0.52             (![X27 : $i, X28 : $i]:
% 0.22/0.52                (((X28) = (X27))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.22/0.52                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['44', '45'])).
% 0.22/0.52  thf('47', plain,
% 0.22/0.52      (![X14 : $i]:
% 0.22/0.52         (((sk_B @ X14) != (sk_C @ X14))
% 0.22/0.52          | (v2_funct_1 @ X14)
% 0.22/0.52          | ~ (v1_funct_1 @ X14)
% 0.22/0.52          | ~ (v1_relat_1 @ X14))),
% 0.22/0.52      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.22/0.52  thf('48', plain,
% 0.22/0.52      (((((sk_B @ sk_B_1) != (sk_B @ sk_B_1))
% 0.22/0.52         | ~ (v1_relat_1 @ sk_B_1)
% 0.22/0.52         | ~ (v1_funct_1 @ sk_B_1)
% 0.22/0.52         | (v2_funct_1 @ sk_B_1)))
% 0.22/0.52         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.22/0.52             (![X27 : $i, X28 : $i]:
% 0.22/0.52                (((X28) = (X27))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.22/0.52                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.52  thf('49', plain, ((v1_relat_1 @ sk_B_1)),
% 0.22/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.52  thf('50', plain, ((v1_funct_1 @ sk_B_1)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('51', plain,
% 0.22/0.52      (((((sk_B @ sk_B_1) != (sk_B @ sk_B_1)) | (v2_funct_1 @ sk_B_1)))
% 0.22/0.52         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.22/0.52             (![X27 : $i, X28 : $i]:
% 0.22/0.52                (((X28) = (X27))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.22/0.52                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.22/0.52      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.22/0.52  thf('52', plain,
% 0.22/0.52      (((v2_funct_1 @ sk_B_1))
% 0.22/0.52         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.22/0.52             (![X27 : $i, X28 : $i]:
% 0.22/0.52                (((X28) = (X27))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.22/0.52                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.22/0.52      inference('simplify', [status(thm)], ['51'])).
% 0.22/0.52  thf('53', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.22/0.52      inference('split', [status(esa)], ['0'])).
% 0.22/0.52  thf('54', plain,
% 0.22/0.52      (~
% 0.22/0.52       (![X27 : $i, X28 : $i]:
% 0.22/0.52          (((X28) = (X27))
% 0.22/0.52           | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.22/0.52           | ~ (r2_hidden @ X27 @ sk_A)
% 0.22/0.52           | ~ (r2_hidden @ X28 @ sk_A))) | 
% 0.22/0.52       ((v2_funct_1 @ sk_B_1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['52', '53'])).
% 0.22/0.52  thf('55', plain, (((r2_hidden @ sk_C_1 @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.22/0.52      inference('split', [status(esa)], ['0'])).
% 0.22/0.52  thf('56', plain, (((r2_hidden @ sk_C_1 @ sk_A))),
% 0.22/0.52      inference('sat_resolution*', [status(thm)], ['10', '54', '55'])).
% 0.22/0.52  thf('57', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.52      inference('simpl_trail', [status(thm)], ['8', '56'])).
% 0.22/0.52  thf('58', plain,
% 0.22/0.52      (((r2_hidden @ sk_C_1 @ sk_A)) <= (((r2_hidden @ sk_C_1 @ sk_A)))),
% 0.22/0.52      inference('split', [status(esa)], ['0'])).
% 0.22/0.52  thf('59', plain, (((r2_hidden @ sk_C_1 @ sk_A))),
% 0.22/0.52      inference('sat_resolution*', [status(thm)], ['10', '54', '55'])).
% 0.22/0.52  thf('60', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.22/0.52      inference('simpl_trail', [status(thm)], ['58', '59'])).
% 0.22/0.52  thf('61', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t32_funct_2, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.52     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.22/0.52         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.52       ( ( ( v2_funct_1 @ D ) & ( r2_hidden @ C @ A ) ) =>
% 0.22/0.52         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.22/0.52           ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) ) =
% 0.22/0.52             ( C ) ) ) ) ))).
% 0.22/0.52  thf('62', plain,
% 0.22/0.52      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X23 @ X24)
% 0.22/0.52          | ((X25) = (k1_xboole_0))
% 0.22/0.52          | ~ (v1_funct_1 @ X26)
% 0.22/0.52          | ~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.22/0.52          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.22/0.52          | ((k1_funct_1 @ (k2_funct_1 @ X26) @ (k1_funct_1 @ X26 @ X23))
% 0.22/0.52              = (X23))
% 0.22/0.52          | ~ (v2_funct_1 @ X26))),
% 0.22/0.52      inference('cnf', [status(esa)], [t32_funct_2])).
% 0.22/0.52  thf('63', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (v2_funct_1 @ sk_B_1)
% 0.22/0.52          | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.22/0.52              = (X0))
% 0.22/0.52          | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.22/0.52          | ~ (v1_funct_1 @ sk_B_1)
% 0.22/0.52          | ((sk_A) = (k1_xboole_0))
% 0.22/0.52          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['61', '62'])).
% 0.22/0.52  thf('64', plain, (((v2_funct_1 @ sk_B_1)) <= (((v2_funct_1 @ sk_B_1)))),
% 0.22/0.52      inference('split', [status(esa)], ['9'])).
% 0.22/0.52  thf('65', plain, (((v2_funct_1 @ sk_B_1))),
% 0.22/0.52      inference('sat_resolution*', [status(thm)], ['10', '54'])).
% 0.22/0.52  thf('66', plain, ((v2_funct_1 @ sk_B_1)),
% 0.22/0.52      inference('simpl_trail', [status(thm)], ['64', '65'])).
% 0.22/0.52  thf('67', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('68', plain, ((v1_funct_1 @ sk_B_1)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('69', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.22/0.52            = (X0))
% 0.22/0.52          | ((sk_A) = (k1_xboole_0))
% 0.22/0.52          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['63', '66', '67', '68'])).
% 0.22/0.52  thf('70', plain,
% 0.22/0.52      ((((sk_A) = (k1_xboole_0))
% 0.22/0.52        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_C_1))
% 0.22/0.52            = (sk_C_1)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['60', '69'])).
% 0.22/0.52  thf('71', plain, (((r2_hidden @ sk_D @ sk_A) | ~ (v2_funct_1 @ sk_B_1))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('72', plain,
% 0.22/0.52      (((r2_hidden @ sk_D @ sk_A)) <= (((r2_hidden @ sk_D @ sk_A)))),
% 0.22/0.52      inference('split', [status(esa)], ['71'])).
% 0.22/0.52  thf('73', plain, (((r2_hidden @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.22/0.52      inference('split', [status(esa)], ['71'])).
% 0.22/0.52  thf('74', plain, (((r2_hidden @ sk_D @ sk_A))),
% 0.22/0.52      inference('sat_resolution*', [status(thm)], ['10', '54', '73'])).
% 0.22/0.52  thf('75', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.22/0.52      inference('simpl_trail', [status(thm)], ['72', '74'])).
% 0.22/0.52  thf('76', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.22/0.52            = (X0))
% 0.22/0.52          | ((sk_A) = (k1_xboole_0))
% 0.22/0.52          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['63', '66', '67', '68'])).
% 0.22/0.52  thf('77', plain,
% 0.22/0.52      ((((sk_A) = (k1_xboole_0))
% 0.22/0.52        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_D))
% 0.22/0.52            = (sk_D)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['75', '76'])).
% 0.22/0.52  thf('78', plain,
% 0.22/0.52      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))
% 0.22/0.52        | ~ (v2_funct_1 @ sk_B_1))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('79', plain,
% 0.22/0.52      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D)))
% 0.22/0.52         <= ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))))),
% 0.22/0.52      inference('split', [status(esa)], ['78'])).
% 0.22/0.52  thf('80', plain,
% 0.22/0.52      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))) | 
% 0.22/0.52       ~ ((v2_funct_1 @ sk_B_1))),
% 0.22/0.52      inference('split', [status(esa)], ['78'])).
% 0.22/0.52  thf('81', plain,
% 0.22/0.52      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D)))),
% 0.22/0.52      inference('sat_resolution*', [status(thm)], ['10', '54', '80'])).
% 0.22/0.52  thf('82', plain,
% 0.22/0.52      (((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))),
% 0.22/0.52      inference('simpl_trail', [status(thm)], ['79', '81'])).
% 0.22/0.52  thf('83', plain,
% 0.22/0.52      ((((sk_A) = (k1_xboole_0))
% 0.22/0.52        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_C_1))
% 0.22/0.52            = (sk_D)))),
% 0.22/0.52      inference('demod', [status(thm)], ['77', '82'])).
% 0.22/0.52  thf('84', plain,
% 0.22/0.52      ((((sk_C_1) = (sk_D))
% 0.22/0.52        | ((sk_A) = (k1_xboole_0))
% 0.22/0.52        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['70', '83'])).
% 0.22/0.52  thf('85', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_C_1) = (sk_D)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['84'])).
% 0.22/0.52  thf('86', plain, ((((sk_C_1) != (sk_D)) | ~ (v2_funct_1 @ sk_B_1))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('87', plain, ((((sk_C_1) != (sk_D))) <= (~ (((sk_C_1) = (sk_D))))),
% 0.22/0.52      inference('split', [status(esa)], ['86'])).
% 0.22/0.52  thf('88', plain, (~ (((sk_C_1) = (sk_D))) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.22/0.52      inference('split', [status(esa)], ['86'])).
% 0.22/0.52  thf('89', plain, (~ (((sk_C_1) = (sk_D)))),
% 0.22/0.52      inference('sat_resolution*', [status(thm)], ['10', '54', '88'])).
% 0.22/0.52  thf('90', plain, (((sk_C_1) != (sk_D))),
% 0.22/0.52      inference('simpl_trail', [status(thm)], ['87', '89'])).
% 0.22/0.52  thf('91', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['85', '90'])).
% 0.22/0.52  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.22/0.52  thf('92', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.52  thf('93', plain, ($false),
% 0.22/0.52      inference('demod', [status(thm)], ['57', '91', '92'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

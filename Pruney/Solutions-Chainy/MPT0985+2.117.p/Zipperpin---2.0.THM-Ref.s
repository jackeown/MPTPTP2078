%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iJWd4QrhpF

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:43 EST 2020

% Result     : Theorem 4.76s
% Output     : Refutation 4.76s
% Verified   : 
% Statistics : Number of formulae       :  272 (23019 expanded)
%              Number of leaves         :   37 (6655 expanded)
%              Depth                    :   27
%              Number of atoms          : 2327 (345739 expanded)
%              Number of equality atoms :  140 (16269 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(t31_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( v2_funct_1 @ C )
            & ( ( k2_relset_1 @ A @ B @ C )
              = B ) )
         => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
            & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
            & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('4',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('13',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('15',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['13','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ sk_C @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( zip_tseitin_0 @ sk_B @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( r1_tarski @ sk_C @ sk_B ) ) ),
    inference(eq_fact,[status(thm)],['21'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ~ ( r1_tarski @ sk_B @ sk_C )
      | ( sk_B = sk_C ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('26',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( sk_B = sk_C )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['24','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('30',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('31',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_B = sk_C )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ( X26
        = ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('35',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('37',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('38',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('40',plain,
    ( ( sk_B = sk_C )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['32','39'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('41',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k1_relat_1 @ X11 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('42',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('43',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('44',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_relat_1 @ X11 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('45',plain,(
    ! [X32: $i] :
      ( ( v1_funct_2 @ X32 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_A )
    | ( sk_B = sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['40','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('55',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('56',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('60',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( sk_B = sk_C ) ),
    inference(demod,[status(thm)],['53','58','59','60','61'])).

thf('63',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('64',plain,
    ( ( sk_B = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['11','64'])).

thf('66',plain,
    ( ( sk_B = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('67',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('68',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('69',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('71',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_B ) )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['66','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('74',plain,
    ( ( ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ ( k2_relat_1 @ sk_B ) @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( sk_B = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('76',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['56','57'])).

thf('77',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( sk_B = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('79',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('80',plain,
    ( ( v1_relat_1 @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( sk_B = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('82',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( v1_funct_1 @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( sk_B = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('85',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v2_funct_1 @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_B @ sk_A )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['74','77','80','83','86'])).

thf('88',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['11','64'])).

thf('89',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('91',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ k1_xboole_0 ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['65','89','90'])).

thf('92',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('93',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('94',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_relat_1 @ X11 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('95',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('96',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('97',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['95','97'])).

thf('99',plain,(
    ! [X32: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('100',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['98','101'])).

thf('103',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('104',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( zip_tseitin_0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['94','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['93','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['92','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ k1_xboole_0 ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['65','89','90'])).

thf('113',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A )
        | ~ ( v1_relat_1 @ k1_xboole_0 )
        | ~ ( v1_funct_1 @ k1_xboole_0 )
        | ~ ( v2_funct_1 @ k1_xboole_0 )
        | ( zip_tseitin_0 @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('115',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('116',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('120',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X15 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relset_1 @ X0 @ X1 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('127',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['118','127'])).

thf('129',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X26
       != ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X25 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('133',plain,(
    ! [X24: $i] :
      ( zip_tseitin_0 @ X24 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('135',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['133','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['131','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('140',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('141',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,
    ( ( v1_funct_1 @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('143',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('144',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,
    ( ( v2_funct_1 @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('146',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('147',plain,
    ( ( v2_funct_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( sk_B = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('149',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_B )
      = sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['148','149'])).

thf('151',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('152',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('153',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('154',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('157',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['150','151','152','155','156'])).

thf('158',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ k1_xboole_0 @ X0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['113','138','141','144','147','157'])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('160',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( X29 != k1_xboole_0 )
      | ( X30 = k1_xboole_0 )
      | ( v1_funct_2 @ X31 @ X30 @ X29 )
      | ( X31 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('162',plain,(
    ! [X30: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X30 @ k1_xboole_0 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('164',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('165',plain,(
    ! [X30: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X30 @ k1_xboole_0 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['162','163','164'])).

thf('166',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ( X26
        = ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0
        = ( k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['118','127'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['169'])).

thf('171',plain,
    ( ! [X0: $i] : ( X0 = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['160','170'])).

thf('172',plain,
    ( ! [X0: $i] : ( X0 = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['160','170'])).

thf('173',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['131','137'])).

thf('174',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['91','171','172','173'])).

thf('175',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('176',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','174','175'])).

thf('177',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','176'])).

thf('178',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k1_relat_1 @ X11 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('179',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['56','57'])).

thf('180',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('181',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('182',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_relat_1 @ X11 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('183',plain,(
    ! [X32: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('184',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['181','184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['180','186'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['187'])).

thf('189',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['179','188'])).

thf('190',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('191',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['189','190','191','192'])).

thf('194',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['178','193'])).

thf('195',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_relat_1 @ X11 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('196',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('197',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('198',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['95','97'])).

thf('199',plain,(
    ! [X32: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('200',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['95','97'])).

thf('202',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('203',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('207',plain,
    ( ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
        | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
        | ( zip_tseitin_0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['200','207'])).

thf('209',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_C )
        | ~ ( v1_funct_1 @ sk_C )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) )
        | ( zip_tseitin_0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
        | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['197','208'])).

thf('210',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('211',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,
    ( ! [X0: $i] :
        ( ( sk_A
          = ( k1_relat_1 @ sk_C ) )
        | ( zip_tseitin_0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
        | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['209','210','211'])).

thf('213',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_C )
        | ~ ( v1_funct_1 @ sk_C )
        | ( zip_tseitin_0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['196','212'])).

thf('214',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('215',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['213','214','215'])).

thf('217',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ ( k2_relat_1 @ sk_C ) @ X0 )
        | ~ ( v1_relat_1 @ sk_C )
        | ~ ( v1_funct_1 @ sk_C )
        | ~ ( v2_funct_1 @ sk_C )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['195','216'])).

thf('218',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['56','57'])).

thf('219',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('220',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ sk_B @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['217','218','219','220','221'])).

thf('223',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('224',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['222','223'])).

thf('225',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('226',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['224','225'])).

thf('227',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','174','175'])).

thf('228',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['226','227'])).

thf('229',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('230',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['194','228','229','230','231'])).

thf('233',plain,(
    $false ),
    inference(demod,[status(thm)],['177','232'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iJWd4QrhpF
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:55:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 4.76/4.95  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.76/4.95  % Solved by: fo/fo7.sh
% 4.76/4.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.76/4.95  % done 4771 iterations in 4.490s
% 4.76/4.95  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.76/4.95  % SZS output start Refutation
% 4.76/4.95  thf(sk_A_type, type, sk_A: $i).
% 4.76/4.95  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.76/4.95  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.76/4.95  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 4.76/4.95  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.76/4.95  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.76/4.95  thf(sk_C_type, type, sk_C: $i).
% 4.76/4.95  thf(sk_B_type, type, sk_B: $i).
% 4.76/4.95  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.76/4.95  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.76/4.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.76/4.95  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 4.76/4.95  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 4.76/4.95  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 4.76/4.95  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.76/4.95  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.76/4.95  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.76/4.95  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 4.76/4.95  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 4.76/4.95  thf(t31_funct_2, conjecture,
% 4.76/4.95    (![A:$i,B:$i,C:$i]:
% 4.76/4.95     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.76/4.95         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.76/4.95       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 4.76/4.95         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 4.76/4.95           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 4.76/4.95           ( m1_subset_1 @
% 4.76/4.95             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 4.76/4.95  thf(zf_stmt_0, negated_conjecture,
% 4.76/4.95    (~( ![A:$i,B:$i,C:$i]:
% 4.76/4.95        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.76/4.95            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.76/4.95          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 4.76/4.95            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 4.76/4.95              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 4.76/4.95              ( m1_subset_1 @
% 4.76/4.95                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 4.76/4.95    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 4.76/4.95  thf('0', plain,
% 4.76/4.95      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.76/4.95        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 4.76/4.95        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.76/4.95             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 4.76/4.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.76/4.95  thf('1', plain,
% 4.76/4.95      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.76/4.95           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 4.76/4.95         <= (~
% 4.76/4.95             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.76/4.95               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 4.76/4.95      inference('split', [status(esa)], ['0'])).
% 4.76/4.95  thf('2', plain,
% 4.76/4.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.76/4.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.76/4.95  thf(cc1_relset_1, axiom,
% 4.76/4.95    (![A:$i,B:$i,C:$i]:
% 4.76/4.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.76/4.95       ( v1_relat_1 @ C ) ))).
% 4.76/4.95  thf('3', plain,
% 4.76/4.95      (![X12 : $i, X13 : $i, X14 : $i]:
% 4.76/4.95         ((v1_relat_1 @ X12)
% 4.76/4.95          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 4.76/4.95      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.76/4.95  thf('4', plain, ((v1_relat_1 @ sk_C)),
% 4.76/4.95      inference('sup-', [status(thm)], ['2', '3'])).
% 4.76/4.95  thf(dt_k2_funct_1, axiom,
% 4.76/4.95    (![A:$i]:
% 4.76/4.95     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.76/4.95       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 4.76/4.95         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 4.76/4.95  thf('5', plain,
% 4.76/4.95      (![X10 : $i]:
% 4.76/4.95         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 4.76/4.95          | ~ (v1_funct_1 @ X10)
% 4.76/4.95          | ~ (v1_relat_1 @ X10))),
% 4.76/4.95      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.76/4.95  thf('6', plain,
% 4.76/4.95      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 4.76/4.95         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 4.76/4.95      inference('split', [status(esa)], ['0'])).
% 4.76/4.95  thf('7', plain,
% 4.76/4.95      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 4.76/4.95         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 4.76/4.95      inference('sup-', [status(thm)], ['5', '6'])).
% 4.76/4.95  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 4.76/4.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.76/4.95  thf('9', plain,
% 4.76/4.95      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 4.76/4.95      inference('demod', [status(thm)], ['7', '8'])).
% 4.76/4.95  thf('10', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.76/4.95      inference('sup-', [status(thm)], ['4', '9'])).
% 4.76/4.95  thf('11', plain,
% 4.76/4.95      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 4.76/4.95         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.76/4.95      inference('split', [status(esa)], ['0'])).
% 4.76/4.95  thf(d1_funct_2, axiom,
% 4.76/4.95    (![A:$i,B:$i,C:$i]:
% 4.76/4.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.76/4.95       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.76/4.95           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 4.76/4.95             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 4.76/4.95         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.76/4.95           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 4.76/4.95             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 4.76/4.95  thf(zf_stmt_1, axiom,
% 4.76/4.95    (![B:$i,A:$i]:
% 4.76/4.95     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.76/4.95       ( zip_tseitin_0 @ B @ A ) ))).
% 4.76/4.95  thf('12', plain,
% 4.76/4.95      (![X24 : $i, X25 : $i]:
% 4.76/4.95         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 4.76/4.95      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.76/4.95  thf('13', plain,
% 4.76/4.95      (![X24 : $i, X25 : $i]:
% 4.76/4.95         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 4.76/4.95      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.76/4.95  thf(t113_zfmisc_1, axiom,
% 4.76/4.95    (![A:$i,B:$i]:
% 4.76/4.95     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 4.76/4.95       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 4.76/4.95  thf('14', plain,
% 4.76/4.95      (![X5 : $i, X6 : $i]:
% 4.76/4.95         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 4.76/4.95      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 4.76/4.95  thf('15', plain,
% 4.76/4.95      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 4.76/4.95      inference('simplify', [status(thm)], ['14'])).
% 4.76/4.95  thf('16', plain,
% 4.76/4.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.76/4.95         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 4.76/4.95      inference('sup+', [status(thm)], ['13', '15'])).
% 4.76/4.95  thf('17', plain,
% 4.76/4.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.76/4.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.76/4.95  thf(t3_subset, axiom,
% 4.76/4.95    (![A:$i,B:$i]:
% 4.76/4.95     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.76/4.95  thf('18', plain,
% 4.76/4.95      (![X7 : $i, X8 : $i]:
% 4.76/4.95         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 4.76/4.95      inference('cnf', [status(esa)], [t3_subset])).
% 4.76/4.95  thf('19', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 4.76/4.95      inference('sup-', [status(thm)], ['17', '18'])).
% 4.76/4.95  thf('20', plain,
% 4.76/4.95      (![X0 : $i]:
% 4.76/4.95         ((r1_tarski @ sk_C @ k1_xboole_0) | (zip_tseitin_0 @ sk_B @ X0))),
% 4.76/4.95      inference('sup+', [status(thm)], ['16', '19'])).
% 4.76/4.95  thf('21', plain,
% 4.76/4.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.76/4.95         ((r1_tarski @ sk_C @ X0)
% 4.76/4.95          | (zip_tseitin_0 @ X0 @ X2)
% 4.76/4.95          | (zip_tseitin_0 @ sk_B @ X1))),
% 4.76/4.95      inference('sup+', [status(thm)], ['12', '20'])).
% 4.76/4.95  thf('22', plain,
% 4.76/4.95      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | (r1_tarski @ sk_C @ sk_B))),
% 4.76/4.95      inference('eq_fact', [status(thm)], ['21'])).
% 4.76/4.95  thf(d10_xboole_0, axiom,
% 4.76/4.95    (![A:$i,B:$i]:
% 4.76/4.95     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.76/4.95  thf('23', plain,
% 4.76/4.95      (![X0 : $i, X2 : $i]:
% 4.76/4.95         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 4.76/4.95      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.76/4.95  thf('24', plain,
% 4.76/4.95      (![X0 : $i]:
% 4.76/4.95         ((zip_tseitin_0 @ sk_B @ X0)
% 4.76/4.95          | ~ (r1_tarski @ sk_B @ sk_C)
% 4.76/4.95          | ((sk_B) = (sk_C)))),
% 4.76/4.95      inference('sup-', [status(thm)], ['22', '23'])).
% 4.76/4.95  thf('25', plain,
% 4.76/4.95      (![X24 : $i, X25 : $i]:
% 4.76/4.95         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 4.76/4.95      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.76/4.95  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 4.76/4.95  thf('26', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 4.76/4.95      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.76/4.95  thf('27', plain,
% 4.76/4.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.76/4.95         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 4.76/4.95      inference('sup+', [status(thm)], ['25', '26'])).
% 4.76/4.95  thf('28', plain,
% 4.76/4.95      (![X0 : $i]: (((sk_B) = (sk_C)) | (zip_tseitin_0 @ sk_B @ X0))),
% 4.76/4.95      inference('clc', [status(thm)], ['24', '27'])).
% 4.76/4.95  thf('29', plain,
% 4.76/4.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.76/4.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.76/4.95  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 4.76/4.95  thf(zf_stmt_3, axiom,
% 4.76/4.95    (![C:$i,B:$i,A:$i]:
% 4.76/4.95     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 4.76/4.95       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 4.76/4.95  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 4.76/4.95  thf(zf_stmt_5, axiom,
% 4.76/4.95    (![A:$i,B:$i,C:$i]:
% 4.76/4.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.76/4.95       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 4.76/4.95         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.76/4.95           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 4.76/4.95             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 4.76/4.95  thf('30', plain,
% 4.76/4.95      (![X29 : $i, X30 : $i, X31 : $i]:
% 4.76/4.95         (~ (zip_tseitin_0 @ X29 @ X30)
% 4.76/4.95          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 4.76/4.95          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 4.76/4.95      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.76/4.95  thf('31', plain,
% 4.76/4.95      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 4.76/4.95      inference('sup-', [status(thm)], ['29', '30'])).
% 4.76/4.95  thf('32', plain,
% 4.76/4.95      ((((sk_B) = (sk_C)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 4.76/4.95      inference('sup-', [status(thm)], ['28', '31'])).
% 4.76/4.95  thf('33', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 4.76/4.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.76/4.95  thf('34', plain,
% 4.76/4.95      (![X26 : $i, X27 : $i, X28 : $i]:
% 4.76/4.95         (~ (v1_funct_2 @ X28 @ X26 @ X27)
% 4.76/4.95          | ((X26) = (k1_relset_1 @ X26 @ X27 @ X28))
% 4.76/4.95          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 4.76/4.95      inference('cnf', [status(esa)], [zf_stmt_3])).
% 4.76/4.95  thf('35', plain,
% 4.76/4.95      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 4.76/4.95        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 4.76/4.95      inference('sup-', [status(thm)], ['33', '34'])).
% 4.76/4.95  thf('36', plain,
% 4.76/4.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.76/4.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.76/4.95  thf(redefinition_k1_relset_1, axiom,
% 4.76/4.95    (![A:$i,B:$i,C:$i]:
% 4.76/4.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.76/4.95       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 4.76/4.95  thf('37', plain,
% 4.76/4.95      (![X18 : $i, X19 : $i, X20 : $i]:
% 4.76/4.95         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 4.76/4.95          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 4.76/4.95      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.76/4.95  thf('38', plain,
% 4.76/4.95      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 4.76/4.95      inference('sup-', [status(thm)], ['36', '37'])).
% 4.76/4.95  thf('39', plain,
% 4.76/4.95      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 4.76/4.95      inference('demod', [status(thm)], ['35', '38'])).
% 4.76/4.95  thf('40', plain, ((((sk_B) = (sk_C)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 4.76/4.96      inference('sup-', [status(thm)], ['32', '39'])).
% 4.76/4.96  thf(t55_funct_1, axiom,
% 4.76/4.96    (![A:$i]:
% 4.76/4.96     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.76/4.96       ( ( v2_funct_1 @ A ) =>
% 4.76/4.96         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 4.76/4.96           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 4.76/4.96  thf('41', plain,
% 4.76/4.96      (![X11 : $i]:
% 4.76/4.96         (~ (v2_funct_1 @ X11)
% 4.76/4.96          | ((k1_relat_1 @ X11) = (k2_relat_1 @ (k2_funct_1 @ X11)))
% 4.76/4.96          | ~ (v1_funct_1 @ X11)
% 4.76/4.96          | ~ (v1_relat_1 @ X11))),
% 4.76/4.96      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.76/4.96  thf('42', plain,
% 4.76/4.96      (![X10 : $i]:
% 4.76/4.96         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 4.76/4.96          | ~ (v1_funct_1 @ X10)
% 4.76/4.96          | ~ (v1_relat_1 @ X10))),
% 4.76/4.96      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.76/4.96  thf('43', plain,
% 4.76/4.96      (![X10 : $i]:
% 4.76/4.96         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 4.76/4.96          | ~ (v1_funct_1 @ X10)
% 4.76/4.96          | ~ (v1_relat_1 @ X10))),
% 4.76/4.96      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.76/4.96  thf('44', plain,
% 4.76/4.96      (![X11 : $i]:
% 4.76/4.96         (~ (v2_funct_1 @ X11)
% 4.76/4.96          | ((k2_relat_1 @ X11) = (k1_relat_1 @ (k2_funct_1 @ X11)))
% 4.76/4.96          | ~ (v1_funct_1 @ X11)
% 4.76/4.96          | ~ (v1_relat_1 @ X11))),
% 4.76/4.96      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.76/4.96  thf(t3_funct_2, axiom,
% 4.76/4.96    (![A:$i]:
% 4.76/4.96     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.76/4.96       ( ( v1_funct_1 @ A ) & 
% 4.76/4.96         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 4.76/4.96         ( m1_subset_1 @
% 4.76/4.96           A @ 
% 4.76/4.96           ( k1_zfmisc_1 @
% 4.76/4.96             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 4.76/4.96  thf('45', plain,
% 4.76/4.96      (![X32 : $i]:
% 4.76/4.96         ((v1_funct_2 @ X32 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))
% 4.76/4.96          | ~ (v1_funct_1 @ X32)
% 4.76/4.96          | ~ (v1_relat_1 @ X32))),
% 4.76/4.96      inference('cnf', [status(esa)], [t3_funct_2])).
% 4.76/4.96  thf('46', plain,
% 4.76/4.96      (![X0 : $i]:
% 4.76/4.96         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 4.76/4.96           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 4.76/4.96          | ~ (v1_relat_1 @ X0)
% 4.76/4.96          | ~ (v1_funct_1 @ X0)
% 4.76/4.96          | ~ (v2_funct_1 @ X0)
% 4.76/4.96          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 4.76/4.96          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 4.76/4.96      inference('sup+', [status(thm)], ['44', '45'])).
% 4.76/4.96  thf('47', plain,
% 4.76/4.96      (![X0 : $i]:
% 4.76/4.96         (~ (v1_relat_1 @ X0)
% 4.76/4.96          | ~ (v1_funct_1 @ X0)
% 4.76/4.96          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 4.76/4.96          | ~ (v2_funct_1 @ X0)
% 4.76/4.96          | ~ (v1_funct_1 @ X0)
% 4.76/4.96          | ~ (v1_relat_1 @ X0)
% 4.76/4.96          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 4.76/4.96             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 4.76/4.96      inference('sup-', [status(thm)], ['43', '46'])).
% 4.76/4.96  thf('48', plain,
% 4.76/4.96      (![X0 : $i]:
% 4.76/4.96         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 4.76/4.96           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 4.76/4.96          | ~ (v2_funct_1 @ X0)
% 4.76/4.96          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 4.76/4.96          | ~ (v1_funct_1 @ X0)
% 4.76/4.96          | ~ (v1_relat_1 @ X0))),
% 4.76/4.96      inference('simplify', [status(thm)], ['47'])).
% 4.76/4.96  thf('49', plain,
% 4.76/4.96      (![X0 : $i]:
% 4.76/4.96         (~ (v1_relat_1 @ X0)
% 4.76/4.96          | ~ (v1_funct_1 @ X0)
% 4.76/4.96          | ~ (v1_relat_1 @ X0)
% 4.76/4.96          | ~ (v1_funct_1 @ X0)
% 4.76/4.96          | ~ (v2_funct_1 @ X0)
% 4.76/4.96          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 4.76/4.96             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 4.76/4.96      inference('sup-', [status(thm)], ['42', '48'])).
% 4.76/4.96  thf('50', plain,
% 4.76/4.96      (![X0 : $i]:
% 4.76/4.96         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 4.76/4.96           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 4.76/4.96          | ~ (v2_funct_1 @ X0)
% 4.76/4.96          | ~ (v1_funct_1 @ X0)
% 4.76/4.96          | ~ (v1_relat_1 @ X0))),
% 4.76/4.96      inference('simplify', [status(thm)], ['49'])).
% 4.76/4.96  thf('51', plain,
% 4.76/4.96      (![X0 : $i]:
% 4.76/4.96         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 4.76/4.96           (k1_relat_1 @ X0))
% 4.76/4.96          | ~ (v1_relat_1 @ X0)
% 4.76/4.96          | ~ (v1_funct_1 @ X0)
% 4.76/4.96          | ~ (v2_funct_1 @ X0)
% 4.76/4.96          | ~ (v1_relat_1 @ X0)
% 4.76/4.96          | ~ (v1_funct_1 @ X0)
% 4.76/4.96          | ~ (v2_funct_1 @ X0))),
% 4.76/4.96      inference('sup+', [status(thm)], ['41', '50'])).
% 4.76/4.96  thf('52', plain,
% 4.76/4.96      (![X0 : $i]:
% 4.76/4.96         (~ (v2_funct_1 @ X0)
% 4.76/4.96          | ~ (v1_funct_1 @ X0)
% 4.76/4.96          | ~ (v1_relat_1 @ X0)
% 4.76/4.96          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 4.76/4.96             (k1_relat_1 @ X0)))),
% 4.76/4.96      inference('simplify', [status(thm)], ['51'])).
% 4.76/4.96  thf('53', plain,
% 4.76/4.96      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_A)
% 4.76/4.96        | ((sk_B) = (sk_C))
% 4.76/4.96        | ~ (v1_relat_1 @ sk_C)
% 4.76/4.96        | ~ (v1_funct_1 @ sk_C)
% 4.76/4.96        | ~ (v2_funct_1 @ sk_C))),
% 4.76/4.96      inference('sup+', [status(thm)], ['40', '52'])).
% 4.76/4.96  thf('54', plain,
% 4.76/4.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.76/4.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.76/4.96  thf(redefinition_k2_relset_1, axiom,
% 4.76/4.96    (![A:$i,B:$i,C:$i]:
% 4.76/4.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.76/4.96       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 4.76/4.96  thf('55', plain,
% 4.76/4.96      (![X21 : $i, X22 : $i, X23 : $i]:
% 4.76/4.96         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 4.76/4.96          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 4.76/4.96      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.76/4.96  thf('56', plain,
% 4.76/4.96      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 4.76/4.96      inference('sup-', [status(thm)], ['54', '55'])).
% 4.76/4.96  thf('57', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 4.76/4.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.76/4.96  thf('58', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 4.76/4.96      inference('sup+', [status(thm)], ['56', '57'])).
% 4.76/4.96  thf('59', plain, ((v1_relat_1 @ sk_C)),
% 4.76/4.96      inference('sup-', [status(thm)], ['2', '3'])).
% 4.76/4.96  thf('60', plain, ((v1_funct_1 @ sk_C)),
% 4.76/4.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.76/4.96  thf('61', plain, ((v2_funct_1 @ sk_C)),
% 4.76/4.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.76/4.96  thf('62', plain,
% 4.76/4.96      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A) | ((sk_B) = (sk_C)))),
% 4.76/4.96      inference('demod', [status(thm)], ['53', '58', '59', '60', '61'])).
% 4.76/4.96  thf('63', plain,
% 4.76/4.96      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 4.76/4.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.76/4.96      inference('split', [status(esa)], ['0'])).
% 4.76/4.96  thf('64', plain,
% 4.76/4.96      ((((sk_B) = (sk_C)))
% 4.76/4.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.76/4.96      inference('sup-', [status(thm)], ['62', '63'])).
% 4.76/4.96  thf('65', plain,
% 4.76/4.96      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_B @ sk_A))
% 4.76/4.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.76/4.96      inference('demod', [status(thm)], ['11', '64'])).
% 4.76/4.96  thf('66', plain,
% 4.76/4.96      ((((sk_B) = (sk_C)))
% 4.76/4.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.76/4.96      inference('sup-', [status(thm)], ['62', '63'])).
% 4.76/4.96  thf('67', plain,
% 4.76/4.96      (![X24 : $i, X25 : $i]:
% 4.76/4.96         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 4.76/4.96      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.76/4.96  thf('68', plain,
% 4.76/4.96      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 4.76/4.96      inference('sup-', [status(thm)], ['29', '30'])).
% 4.76/4.96  thf('69', plain,
% 4.76/4.96      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 4.76/4.96      inference('sup-', [status(thm)], ['67', '68'])).
% 4.76/4.96  thf('70', plain,
% 4.76/4.96      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 4.76/4.96      inference('demod', [status(thm)], ['35', '38'])).
% 4.76/4.96  thf('71', plain,
% 4.76/4.96      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 4.76/4.96      inference('sup-', [status(thm)], ['69', '70'])).
% 4.76/4.96  thf('72', plain,
% 4.76/4.96      (((((sk_A) = (k1_relat_1 @ sk_B)) | ((sk_B) = (k1_xboole_0))))
% 4.76/4.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.76/4.96      inference('sup+', [status(thm)], ['66', '71'])).
% 4.76/4.96  thf('73', plain,
% 4.76/4.96      (![X0 : $i]:
% 4.76/4.96         (~ (v2_funct_1 @ X0)
% 4.76/4.96          | ~ (v1_funct_1 @ X0)
% 4.76/4.96          | ~ (v1_relat_1 @ X0)
% 4.76/4.96          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 4.76/4.96             (k1_relat_1 @ X0)))),
% 4.76/4.96      inference('simplify', [status(thm)], ['51'])).
% 4.76/4.96  thf('74', plain,
% 4.76/4.96      ((((v1_funct_2 @ (k2_funct_1 @ sk_B) @ (k2_relat_1 @ sk_B) @ sk_A)
% 4.76/4.96         | ((sk_B) = (k1_xboole_0))
% 4.76/4.96         | ~ (v1_relat_1 @ sk_B)
% 4.76/4.96         | ~ (v1_funct_1 @ sk_B)
% 4.76/4.96         | ~ (v2_funct_1 @ sk_B)))
% 4.76/4.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.76/4.96      inference('sup+', [status(thm)], ['72', '73'])).
% 4.76/4.96  thf('75', plain,
% 4.76/4.96      ((((sk_B) = (sk_C)))
% 4.76/4.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.76/4.96      inference('sup-', [status(thm)], ['62', '63'])).
% 4.76/4.96  thf('76', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 4.76/4.96      inference('sup+', [status(thm)], ['56', '57'])).
% 4.76/4.96  thf('77', plain,
% 4.76/4.96      ((((k2_relat_1 @ sk_B) = (sk_B)))
% 4.76/4.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.76/4.96      inference('sup+', [status(thm)], ['75', '76'])).
% 4.76/4.96  thf('78', plain,
% 4.76/4.96      ((((sk_B) = (sk_C)))
% 4.76/4.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.76/4.96      inference('sup-', [status(thm)], ['62', '63'])).
% 4.76/4.96  thf('79', plain, ((v1_relat_1 @ sk_C)),
% 4.76/4.96      inference('sup-', [status(thm)], ['2', '3'])).
% 4.76/4.96  thf('80', plain,
% 4.76/4.96      (((v1_relat_1 @ sk_B))
% 4.76/4.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.76/4.96      inference('sup+', [status(thm)], ['78', '79'])).
% 4.76/4.96  thf('81', plain,
% 4.76/4.96      ((((sk_B) = (sk_C)))
% 4.76/4.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.76/4.96      inference('sup-', [status(thm)], ['62', '63'])).
% 4.76/4.96  thf('82', plain, ((v1_funct_1 @ sk_C)),
% 4.76/4.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.76/4.96  thf('83', plain,
% 4.76/4.96      (((v1_funct_1 @ sk_B))
% 4.76/4.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.76/4.96      inference('sup+', [status(thm)], ['81', '82'])).
% 4.76/4.96  thf('84', plain,
% 4.76/4.96      ((((sk_B) = (sk_C)))
% 4.76/4.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.76/4.96      inference('sup-', [status(thm)], ['62', '63'])).
% 4.76/4.96  thf('85', plain, ((v2_funct_1 @ sk_C)),
% 4.76/4.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.76/4.96  thf('86', plain,
% 4.76/4.96      (((v2_funct_1 @ sk_B))
% 4.76/4.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.76/4.96      inference('sup+', [status(thm)], ['84', '85'])).
% 4.76/4.96  thf('87', plain,
% 4.76/4.96      ((((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_B @ sk_A)
% 4.76/4.96         | ((sk_B) = (k1_xboole_0))))
% 4.76/4.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.76/4.96      inference('demod', [status(thm)], ['74', '77', '80', '83', '86'])).
% 4.76/4.96  thf('88', plain,
% 4.76/4.96      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_B @ sk_A))
% 4.76/4.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.76/4.96      inference('demod', [status(thm)], ['11', '64'])).
% 4.76/4.96  thf('89', plain,
% 4.76/4.96      ((((sk_B) = (k1_xboole_0)))
% 4.76/4.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.76/4.96      inference('clc', [status(thm)], ['87', '88'])).
% 4.76/4.96  thf('90', plain,
% 4.76/4.96      ((((sk_B) = (k1_xboole_0)))
% 4.76/4.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.76/4.96      inference('clc', [status(thm)], ['87', '88'])).
% 4.76/4.96  thf('91', plain,
% 4.76/4.96      ((~ (v1_funct_2 @ (k2_funct_1 @ k1_xboole_0) @ k1_xboole_0 @ sk_A))
% 4.76/4.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.76/4.96      inference('demod', [status(thm)], ['65', '89', '90'])).
% 4.76/4.96  thf('92', plain,
% 4.76/4.96      (![X10 : $i]:
% 4.76/4.96         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 4.76/4.96          | ~ (v1_funct_1 @ X10)
% 4.76/4.96          | ~ (v1_relat_1 @ X10))),
% 4.76/4.96      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.76/4.96  thf('93', plain,
% 4.76/4.96      (![X10 : $i]:
% 4.76/4.96         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 4.76/4.96          | ~ (v1_funct_1 @ X10)
% 4.76/4.96          | ~ (v1_relat_1 @ X10))),
% 4.76/4.96      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.76/4.96  thf('94', plain,
% 4.76/4.96      (![X11 : $i]:
% 4.76/4.96         (~ (v2_funct_1 @ X11)
% 4.76/4.96          | ((k2_relat_1 @ X11) = (k1_relat_1 @ (k2_funct_1 @ X11)))
% 4.76/4.96          | ~ (v1_funct_1 @ X11)
% 4.76/4.96          | ~ (v1_relat_1 @ X11))),
% 4.76/4.96      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.76/4.96  thf('95', plain,
% 4.76/4.96      (![X24 : $i, X25 : $i]:
% 4.76/4.96         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 4.76/4.96      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.76/4.96  thf('96', plain,
% 4.76/4.96      (![X5 : $i, X6 : $i]:
% 4.76/4.96         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 4.76/4.96      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 4.76/4.96  thf('97', plain,
% 4.76/4.96      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 4.76/4.96      inference('simplify', [status(thm)], ['96'])).
% 4.76/4.96  thf('98', plain,
% 4.76/4.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.76/4.96         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 4.76/4.96      inference('sup+', [status(thm)], ['95', '97'])).
% 4.76/4.96  thf('99', plain,
% 4.76/4.96      (![X32 : $i]:
% 4.76/4.96         ((m1_subset_1 @ X32 @ 
% 4.76/4.96           (k1_zfmisc_1 @ 
% 4.76/4.96            (k2_zfmisc_1 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))))
% 4.76/4.96          | ~ (v1_funct_1 @ X32)
% 4.76/4.96          | ~ (v1_relat_1 @ X32))),
% 4.76/4.96      inference('cnf', [status(esa)], [t3_funct_2])).
% 4.76/4.96  thf('100', plain,
% 4.76/4.96      (![X7 : $i, X8 : $i]:
% 4.76/4.96         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 4.76/4.96      inference('cnf', [status(esa)], [t3_subset])).
% 4.76/4.96  thf('101', plain,
% 4.76/4.96      (![X0 : $i]:
% 4.76/4.96         (~ (v1_relat_1 @ X0)
% 4.76/4.96          | ~ (v1_funct_1 @ X0)
% 4.76/4.96          | (r1_tarski @ X0 @ 
% 4.76/4.96             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 4.76/4.96      inference('sup-', [status(thm)], ['99', '100'])).
% 4.76/4.96  thf('102', plain,
% 4.76/4.96      (![X0 : $i, X1 : $i]:
% 4.76/4.96         ((r1_tarski @ X0 @ k1_xboole_0)
% 4.76/4.96          | (zip_tseitin_0 @ (k1_relat_1 @ X0) @ X1)
% 4.76/4.96          | ~ (v1_funct_1 @ X0)
% 4.76/4.96          | ~ (v1_relat_1 @ X0))),
% 4.76/4.96      inference('sup+', [status(thm)], ['98', '101'])).
% 4.76/4.96  thf('103', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 4.76/4.96      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.76/4.96  thf('104', plain,
% 4.76/4.96      (![X0 : $i, X2 : $i]:
% 4.76/4.96         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 4.76/4.96      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.76/4.96  thf('105', plain,
% 4.76/4.96      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 4.76/4.96      inference('sup-', [status(thm)], ['103', '104'])).
% 4.76/4.96  thf('106', plain,
% 4.76/4.96      (![X0 : $i, X1 : $i]:
% 4.76/4.96         (~ (v1_relat_1 @ X0)
% 4.76/4.96          | ~ (v1_funct_1 @ X0)
% 4.76/4.96          | (zip_tseitin_0 @ (k1_relat_1 @ X0) @ X1)
% 4.76/4.96          | ((X0) = (k1_xboole_0)))),
% 4.76/4.96      inference('sup-', [status(thm)], ['102', '105'])).
% 4.76/4.96  thf('107', plain,
% 4.76/4.96      (![X0 : $i, X1 : $i]:
% 4.76/4.96         ((zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1)
% 4.76/4.96          | ~ (v1_relat_1 @ X0)
% 4.76/4.96          | ~ (v1_funct_1 @ X0)
% 4.76/4.96          | ~ (v2_funct_1 @ X0)
% 4.76/4.96          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 4.76/4.96          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 4.76/4.96          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 4.76/4.96      inference('sup+', [status(thm)], ['94', '106'])).
% 4.76/4.96  thf('108', plain,
% 4.76/4.96      (![X0 : $i, X1 : $i]:
% 4.76/4.96         (~ (v1_relat_1 @ X0)
% 4.76/4.96          | ~ (v1_funct_1 @ X0)
% 4.76/4.96          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 4.76/4.96          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 4.76/4.96          | ~ (v2_funct_1 @ X0)
% 4.76/4.96          | ~ (v1_funct_1 @ X0)
% 4.76/4.96          | ~ (v1_relat_1 @ X0)
% 4.76/4.96          | (zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1))),
% 4.76/4.96      inference('sup-', [status(thm)], ['93', '107'])).
% 4.76/4.96  thf('109', plain,
% 4.76/4.96      (![X0 : $i, X1 : $i]:
% 4.76/4.96         ((zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1)
% 4.76/4.96          | ~ (v2_funct_1 @ X0)
% 4.76/4.96          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 4.76/4.96          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 4.76/4.96          | ~ (v1_funct_1 @ X0)
% 4.76/4.96          | ~ (v1_relat_1 @ X0))),
% 4.76/4.96      inference('simplify', [status(thm)], ['108'])).
% 4.76/4.96  thf('110', plain,
% 4.76/4.96      (![X0 : $i, X1 : $i]:
% 4.76/4.96         (~ (v1_relat_1 @ X0)
% 4.76/4.96          | ~ (v1_funct_1 @ X0)
% 4.76/4.96          | ~ (v1_relat_1 @ X0)
% 4.76/4.96          | ~ (v1_funct_1 @ X0)
% 4.76/4.96          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 4.76/4.96          | ~ (v2_funct_1 @ X0)
% 4.76/4.96          | (zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1))),
% 4.76/4.96      inference('sup-', [status(thm)], ['92', '109'])).
% 4.76/4.96  thf('111', plain,
% 4.76/4.96      (![X0 : $i, X1 : $i]:
% 4.76/4.96         ((zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1)
% 4.76/4.96          | ~ (v2_funct_1 @ X0)
% 4.76/4.96          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 4.76/4.96          | ~ (v1_funct_1 @ X0)
% 4.76/4.96          | ~ (v1_relat_1 @ X0))),
% 4.76/4.96      inference('simplify', [status(thm)], ['110'])).
% 4.76/4.96  thf('112', plain,
% 4.76/4.96      ((~ (v1_funct_2 @ (k2_funct_1 @ k1_xboole_0) @ k1_xboole_0 @ sk_A))
% 4.76/4.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.76/4.96      inference('demod', [status(thm)], ['65', '89', '90'])).
% 4.76/4.96  thf('113', plain,
% 4.76/4.96      ((![X0 : $i]:
% 4.76/4.96          (~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A)
% 4.76/4.96           | ~ (v1_relat_1 @ k1_xboole_0)
% 4.76/4.96           | ~ (v1_funct_1 @ k1_xboole_0)
% 4.76/4.96           | ~ (v2_funct_1 @ k1_xboole_0)
% 4.76/4.96           | (zip_tseitin_0 @ (k2_relat_1 @ k1_xboole_0) @ X0)))
% 4.76/4.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.76/4.96      inference('sup-', [status(thm)], ['111', '112'])).
% 4.76/4.96  thf('114', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 4.76/4.96      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.76/4.96  thf('115', plain,
% 4.76/4.96      (![X7 : $i, X9 : $i]:
% 4.76/4.96         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 4.76/4.96      inference('cnf', [status(esa)], [t3_subset])).
% 4.76/4.96  thf('116', plain,
% 4.76/4.96      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 4.76/4.96      inference('sup-', [status(thm)], ['114', '115'])).
% 4.76/4.96  thf('117', plain,
% 4.76/4.96      (![X18 : $i, X19 : $i, X20 : $i]:
% 4.76/4.96         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 4.76/4.96          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 4.76/4.96      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.76/4.96  thf('118', plain,
% 4.76/4.96      (![X0 : $i, X1 : $i]:
% 4.76/4.96         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 4.76/4.96      inference('sup-', [status(thm)], ['116', '117'])).
% 4.76/4.96  thf('119', plain,
% 4.76/4.96      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 4.76/4.96      inference('sup-', [status(thm)], ['114', '115'])).
% 4.76/4.96  thf(dt_k1_relset_1, axiom,
% 4.76/4.96    (![A:$i,B:$i,C:$i]:
% 4.76/4.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.76/4.96       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 4.76/4.96  thf('120', plain,
% 4.76/4.96      (![X15 : $i, X16 : $i, X17 : $i]:
% 4.76/4.96         ((m1_subset_1 @ (k1_relset_1 @ X15 @ X16 @ X17) @ (k1_zfmisc_1 @ X15))
% 4.76/4.96          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 4.76/4.96      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 4.76/4.96  thf('121', plain,
% 4.76/4.96      (![X0 : $i, X1 : $i]:
% 4.76/4.96         (m1_subset_1 @ (k1_relset_1 @ X1 @ X0 @ k1_xboole_0) @ 
% 4.76/4.96          (k1_zfmisc_1 @ X1))),
% 4.76/4.96      inference('sup-', [status(thm)], ['119', '120'])).
% 4.76/4.96  thf('122', plain,
% 4.76/4.96      (![X7 : $i, X8 : $i]:
% 4.76/4.96         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 4.76/4.96      inference('cnf', [status(esa)], [t3_subset])).
% 4.76/4.96  thf('123', plain,
% 4.76/4.96      (![X0 : $i, X1 : $i]:
% 4.76/4.96         (r1_tarski @ (k1_relset_1 @ X0 @ X1 @ k1_xboole_0) @ X0)),
% 4.76/4.96      inference('sup-', [status(thm)], ['121', '122'])).
% 4.76/4.96  thf('124', plain,
% 4.76/4.96      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 4.76/4.96      inference('sup-', [status(thm)], ['103', '104'])).
% 4.76/4.96  thf('125', plain,
% 4.76/4.96      (![X0 : $i]:
% 4.76/4.96         ((k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 4.76/4.96      inference('sup-', [status(thm)], ['123', '124'])).
% 4.76/4.96  thf('126', plain,
% 4.76/4.96      (![X0 : $i, X1 : $i]:
% 4.76/4.96         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 4.76/4.96      inference('sup-', [status(thm)], ['116', '117'])).
% 4.76/4.96  thf('127', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.76/4.96      inference('demod', [status(thm)], ['125', '126'])).
% 4.76/4.96  thf('128', plain,
% 4.76/4.96      (![X0 : $i, X1 : $i]:
% 4.76/4.96         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 4.76/4.96      inference('demod', [status(thm)], ['118', '127'])).
% 4.76/4.96  thf('129', plain,
% 4.76/4.96      (![X26 : $i, X27 : $i, X28 : $i]:
% 4.76/4.96         (((X26) != (k1_relset_1 @ X26 @ X27 @ X28))
% 4.76/4.96          | (v1_funct_2 @ X28 @ X26 @ X27)
% 4.76/4.96          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 4.76/4.96      inference('cnf', [status(esa)], [zf_stmt_3])).
% 4.76/4.96  thf('130', plain,
% 4.76/4.96      (![X0 : $i, X1 : $i]:
% 4.76/4.96         (((X1) != (k1_xboole_0))
% 4.76/4.96          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 4.76/4.96          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 4.76/4.96      inference('sup-', [status(thm)], ['128', '129'])).
% 4.76/4.96  thf('131', plain,
% 4.76/4.96      (![X0 : $i]:
% 4.76/4.96         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 4.76/4.96          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 4.76/4.96      inference('simplify', [status(thm)], ['130'])).
% 4.76/4.96  thf('132', plain,
% 4.76/4.96      (![X24 : $i, X25 : $i]:
% 4.76/4.96         ((zip_tseitin_0 @ X24 @ X25) | ((X25) != (k1_xboole_0)))),
% 4.76/4.96      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.76/4.96  thf('133', plain, (![X24 : $i]: (zip_tseitin_0 @ X24 @ k1_xboole_0)),
% 4.76/4.96      inference('simplify', [status(thm)], ['132'])).
% 4.76/4.96  thf('134', plain,
% 4.76/4.96      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 4.76/4.96      inference('sup-', [status(thm)], ['114', '115'])).
% 4.76/4.96  thf('135', plain,
% 4.76/4.96      (![X29 : $i, X30 : $i, X31 : $i]:
% 4.76/4.96         (~ (zip_tseitin_0 @ X29 @ X30)
% 4.76/4.96          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 4.76/4.96          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 4.76/4.96      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.76/4.96  thf('136', plain,
% 4.76/4.96      (![X0 : $i, X1 : $i]:
% 4.76/4.96         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 4.76/4.96      inference('sup-', [status(thm)], ['134', '135'])).
% 4.76/4.96  thf('137', plain,
% 4.76/4.96      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 4.76/4.96      inference('sup-', [status(thm)], ['133', '136'])).
% 4.76/4.96  thf('138', plain,
% 4.76/4.96      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 4.76/4.96      inference('demod', [status(thm)], ['131', '137'])).
% 4.76/4.96  thf('139', plain,
% 4.76/4.96      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 4.76/4.96      inference('sup-', [status(thm)], ['114', '115'])).
% 4.76/4.96  thf('140', plain,
% 4.76/4.96      (![X12 : $i, X13 : $i, X14 : $i]:
% 4.76/4.96         ((v1_relat_1 @ X12)
% 4.76/4.96          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 4.76/4.96      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.76/4.96  thf('141', plain, ((v1_relat_1 @ k1_xboole_0)),
% 4.76/4.96      inference('sup-', [status(thm)], ['139', '140'])).
% 4.76/4.96  thf('142', plain,
% 4.76/4.96      (((v1_funct_1 @ sk_B))
% 4.76/4.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.76/4.96      inference('sup+', [status(thm)], ['81', '82'])).
% 4.76/4.96  thf('143', plain,
% 4.76/4.96      ((((sk_B) = (k1_xboole_0)))
% 4.76/4.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.76/4.96      inference('clc', [status(thm)], ['87', '88'])).
% 4.76/4.96  thf('144', plain,
% 4.76/4.96      (((v1_funct_1 @ k1_xboole_0))
% 4.76/4.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.76/4.96      inference('demod', [status(thm)], ['142', '143'])).
% 4.76/4.96  thf('145', plain,
% 4.76/4.96      (((v2_funct_1 @ sk_B))
% 4.76/4.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.76/4.96      inference('sup+', [status(thm)], ['84', '85'])).
% 4.76/4.96  thf('146', plain,
% 4.76/4.96      ((((sk_B) = (k1_xboole_0)))
% 4.76/4.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.76/4.96      inference('clc', [status(thm)], ['87', '88'])).
% 4.76/4.96  thf('147', plain,
% 4.76/4.96      (((v2_funct_1 @ k1_xboole_0))
% 4.76/4.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.76/4.96      inference('demod', [status(thm)], ['145', '146'])).
% 4.76/4.96  thf('148', plain,
% 4.76/4.96      ((((sk_B) = (sk_C)))
% 4.76/4.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.76/4.96      inference('sup-', [status(thm)], ['62', '63'])).
% 4.76/4.96  thf('149', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 4.76/4.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.76/4.96  thf('150', plain,
% 4.76/4.96      ((((k2_relset_1 @ sk_A @ sk_B @ sk_B) = (sk_B)))
% 4.76/4.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.76/4.96      inference('sup+', [status(thm)], ['148', '149'])).
% 4.76/4.96  thf('151', plain,
% 4.76/4.96      ((((sk_B) = (k1_xboole_0)))
% 4.76/4.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.76/4.96      inference('clc', [status(thm)], ['87', '88'])).
% 4.76/4.96  thf('152', plain,
% 4.76/4.96      ((((sk_B) = (k1_xboole_0)))
% 4.76/4.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.76/4.96      inference('clc', [status(thm)], ['87', '88'])).
% 4.76/4.96  thf('153', plain,
% 4.76/4.96      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 4.76/4.96      inference('sup-', [status(thm)], ['114', '115'])).
% 4.76/4.96  thf('154', plain,
% 4.76/4.96      (![X21 : $i, X22 : $i, X23 : $i]:
% 4.76/4.96         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 4.76/4.96          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 4.76/4.96      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.76/4.96  thf('155', plain,
% 4.76/4.96      (![X0 : $i, X1 : $i]:
% 4.76/4.96         ((k2_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 4.76/4.96      inference('sup-', [status(thm)], ['153', '154'])).
% 4.76/4.96  thf('156', plain,
% 4.76/4.96      ((((sk_B) = (k1_xboole_0)))
% 4.76/4.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.76/4.96      inference('clc', [status(thm)], ['87', '88'])).
% 4.76/4.96  thf('157', plain,
% 4.76/4.96      ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 4.76/4.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.76/4.96      inference('demod', [status(thm)], ['150', '151', '152', '155', '156'])).
% 4.76/4.96  thf('158', plain,
% 4.76/4.96      ((![X0 : $i]: (zip_tseitin_0 @ k1_xboole_0 @ X0))
% 4.76/4.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.76/4.96      inference('demod', [status(thm)],
% 4.76/4.96                ['113', '138', '141', '144', '147', '157'])).
% 4.76/4.96  thf('159', plain,
% 4.76/4.96      (![X0 : $i, X1 : $i]:
% 4.76/4.96         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 4.76/4.96      inference('sup-', [status(thm)], ['134', '135'])).
% 4.76/4.96  thf('160', plain,
% 4.76/4.96      ((![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0))
% 4.76/4.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.76/4.96      inference('sup-', [status(thm)], ['158', '159'])).
% 4.76/4.96  thf('161', plain,
% 4.76/4.96      (![X29 : $i, X30 : $i, X31 : $i]:
% 4.76/4.96         (((X29) != (k1_xboole_0))
% 4.76/4.96          | ((X30) = (k1_xboole_0))
% 4.76/4.96          | (v1_funct_2 @ X31 @ X30 @ X29)
% 4.76/4.96          | ((X31) != (k1_xboole_0))
% 4.76/4.96          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 4.76/4.96      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.76/4.96  thf('162', plain,
% 4.76/4.96      (![X30 : $i]:
% 4.76/4.96         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 4.76/4.96             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ k1_xboole_0)))
% 4.76/4.96          | (v1_funct_2 @ k1_xboole_0 @ X30 @ k1_xboole_0)
% 4.76/4.96          | ((X30) = (k1_xboole_0)))),
% 4.76/4.96      inference('simplify', [status(thm)], ['161'])).
% 4.76/4.96  thf('163', plain,
% 4.76/4.96      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 4.76/4.96      inference('simplify', [status(thm)], ['14'])).
% 4.76/4.96  thf('164', plain,
% 4.76/4.96      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 4.76/4.96      inference('sup-', [status(thm)], ['114', '115'])).
% 4.76/4.96  thf('165', plain,
% 4.76/4.96      (![X30 : $i]:
% 4.76/4.96         ((v1_funct_2 @ k1_xboole_0 @ X30 @ k1_xboole_0)
% 4.76/4.96          | ((X30) = (k1_xboole_0)))),
% 4.76/4.96      inference('demod', [status(thm)], ['162', '163', '164'])).
% 4.76/4.96  thf('166', plain,
% 4.76/4.96      (![X26 : $i, X27 : $i, X28 : $i]:
% 4.76/4.96         (~ (v1_funct_2 @ X28 @ X26 @ X27)
% 4.76/4.96          | ((X26) = (k1_relset_1 @ X26 @ X27 @ X28))
% 4.76/4.96          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 4.76/4.96      inference('cnf', [status(esa)], [zf_stmt_3])).
% 4.76/4.96  thf('167', plain,
% 4.76/4.96      (![X0 : $i]:
% 4.76/4.96         (((X0) = (k1_xboole_0))
% 4.76/4.96          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 4.76/4.96          | ((X0) = (k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0)))),
% 4.76/4.96      inference('sup-', [status(thm)], ['165', '166'])).
% 4.76/4.96  thf('168', plain,
% 4.76/4.96      (![X0 : $i, X1 : $i]:
% 4.76/4.96         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 4.76/4.96      inference('demod', [status(thm)], ['118', '127'])).
% 4.76/4.96  thf('169', plain,
% 4.76/4.96      (![X0 : $i]:
% 4.76/4.96         (((X0) = (k1_xboole_0))
% 4.76/4.96          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 4.76/4.96          | ((X0) = (k1_xboole_0)))),
% 4.76/4.96      inference('demod', [status(thm)], ['167', '168'])).
% 4.76/4.96  thf('170', plain,
% 4.76/4.96      (![X0 : $i]:
% 4.76/4.96         (~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 4.76/4.96          | ((X0) = (k1_xboole_0)))),
% 4.76/4.96      inference('simplify', [status(thm)], ['169'])).
% 4.76/4.96  thf('171', plain,
% 4.76/4.96      ((![X0 : $i]: ((X0) = (k1_xboole_0)))
% 4.76/4.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.76/4.96      inference('sup-', [status(thm)], ['160', '170'])).
% 4.76/4.96  thf('172', plain,
% 4.76/4.96      ((![X0 : $i]: ((X0) = (k1_xboole_0)))
% 4.76/4.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.76/4.96      inference('sup-', [status(thm)], ['160', '170'])).
% 4.76/4.96  thf('173', plain,
% 4.76/4.96      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 4.76/4.96      inference('demod', [status(thm)], ['131', '137'])).
% 4.76/4.96  thf('174', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 4.76/4.96      inference('demod', [status(thm)], ['91', '171', '172', '173'])).
% 4.76/4.96  thf('175', plain,
% 4.76/4.96      (~
% 4.76/4.96       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.76/4.96         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 4.76/4.96       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 4.76/4.96       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.76/4.96      inference('split', [status(esa)], ['0'])).
% 4.76/4.96  thf('176', plain,
% 4.76/4.96      (~
% 4.76/4.96       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.76/4.96         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 4.76/4.96      inference('sat_resolution*', [status(thm)], ['10', '174', '175'])).
% 4.76/4.96  thf('177', plain,
% 4.76/4.96      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.76/4.96          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.76/4.96      inference('simpl_trail', [status(thm)], ['1', '176'])).
% 4.76/4.96  thf('178', plain,
% 4.76/4.96      (![X11 : $i]:
% 4.76/4.96         (~ (v2_funct_1 @ X11)
% 4.76/4.96          | ((k1_relat_1 @ X11) = (k2_relat_1 @ (k2_funct_1 @ X11)))
% 4.76/4.96          | ~ (v1_funct_1 @ X11)
% 4.76/4.96          | ~ (v1_relat_1 @ X11))),
% 4.76/4.96      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.76/4.96  thf('179', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 4.76/4.96      inference('sup+', [status(thm)], ['56', '57'])).
% 4.76/4.96  thf('180', plain,
% 4.76/4.96      (![X10 : $i]:
% 4.76/4.96         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 4.76/4.96          | ~ (v1_funct_1 @ X10)
% 4.76/4.96          | ~ (v1_relat_1 @ X10))),
% 4.76/4.96      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.76/4.96  thf('181', plain,
% 4.76/4.96      (![X10 : $i]:
% 4.76/4.96         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 4.76/4.96          | ~ (v1_funct_1 @ X10)
% 4.76/4.96          | ~ (v1_relat_1 @ X10))),
% 4.76/4.96      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.76/4.96  thf('182', plain,
% 4.76/4.96      (![X11 : $i]:
% 4.76/4.96         (~ (v2_funct_1 @ X11)
% 4.76/4.96          | ((k2_relat_1 @ X11) = (k1_relat_1 @ (k2_funct_1 @ X11)))
% 4.76/4.96          | ~ (v1_funct_1 @ X11)
% 4.76/4.96          | ~ (v1_relat_1 @ X11))),
% 4.76/4.96      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.76/4.96  thf('183', plain,
% 4.76/4.96      (![X32 : $i]:
% 4.76/4.96         ((m1_subset_1 @ X32 @ 
% 4.76/4.96           (k1_zfmisc_1 @ 
% 4.76/4.96            (k2_zfmisc_1 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))))
% 4.76/4.96          | ~ (v1_funct_1 @ X32)
% 4.76/4.96          | ~ (v1_relat_1 @ X32))),
% 4.76/4.96      inference('cnf', [status(esa)], [t3_funct_2])).
% 4.76/4.96  thf('184', plain,
% 4.76/4.96      (![X0 : $i]:
% 4.76/4.96         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 4.76/4.96           (k1_zfmisc_1 @ 
% 4.76/4.96            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 4.76/4.96          | ~ (v1_relat_1 @ X0)
% 4.76/4.96          | ~ (v1_funct_1 @ X0)
% 4.76/4.96          | ~ (v2_funct_1 @ X0)
% 4.76/4.96          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 4.76/4.96          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 4.76/4.96      inference('sup+', [status(thm)], ['182', '183'])).
% 4.76/4.96  thf('185', plain,
% 4.76/4.96      (![X0 : $i]:
% 4.76/4.96         (~ (v1_relat_1 @ X0)
% 4.76/4.96          | ~ (v1_funct_1 @ X0)
% 4.76/4.96          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 4.76/4.96          | ~ (v2_funct_1 @ X0)
% 4.76/4.96          | ~ (v1_funct_1 @ X0)
% 4.76/4.96          | ~ (v1_relat_1 @ X0)
% 4.76/4.96          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 4.76/4.96             (k1_zfmisc_1 @ 
% 4.76/4.96              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 4.76/4.96               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 4.76/4.96      inference('sup-', [status(thm)], ['181', '184'])).
% 4.76/4.96  thf('186', plain,
% 4.76/4.96      (![X0 : $i]:
% 4.76/4.96         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 4.76/4.96           (k1_zfmisc_1 @ 
% 4.76/4.96            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 4.76/4.96          | ~ (v2_funct_1 @ X0)
% 4.76/4.96          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 4.76/4.96          | ~ (v1_funct_1 @ X0)
% 4.76/4.96          | ~ (v1_relat_1 @ X0))),
% 4.76/4.96      inference('simplify', [status(thm)], ['185'])).
% 4.76/4.96  thf('187', plain,
% 4.76/4.96      (![X0 : $i]:
% 4.76/4.96         (~ (v1_relat_1 @ X0)
% 4.76/4.96          | ~ (v1_funct_1 @ X0)
% 4.76/4.96          | ~ (v1_relat_1 @ X0)
% 4.76/4.96          | ~ (v1_funct_1 @ X0)
% 4.76/4.96          | ~ (v2_funct_1 @ X0)
% 4.76/4.96          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 4.76/4.96             (k1_zfmisc_1 @ 
% 4.76/4.96              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 4.76/4.96               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 4.76/4.96      inference('sup-', [status(thm)], ['180', '186'])).
% 4.76/4.96  thf('188', plain,
% 4.76/4.96      (![X0 : $i]:
% 4.76/4.96         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 4.76/4.96           (k1_zfmisc_1 @ 
% 4.76/4.96            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 4.76/4.96          | ~ (v2_funct_1 @ X0)
% 4.76/4.96          | ~ (v1_funct_1 @ X0)
% 4.76/4.96          | ~ (v1_relat_1 @ X0))),
% 4.76/4.96      inference('simplify', [status(thm)], ['187'])).
% 4.76/4.96  thf('189', plain,
% 4.76/4.96      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.76/4.96         (k1_zfmisc_1 @ 
% 4.76/4.96          (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))
% 4.76/4.96        | ~ (v1_relat_1 @ sk_C)
% 4.76/4.96        | ~ (v1_funct_1 @ sk_C)
% 4.76/4.96        | ~ (v2_funct_1 @ sk_C))),
% 4.76/4.96      inference('sup+', [status(thm)], ['179', '188'])).
% 4.76/4.96  thf('190', plain, ((v1_relat_1 @ sk_C)),
% 4.76/4.96      inference('sup-', [status(thm)], ['2', '3'])).
% 4.76/4.96  thf('191', plain, ((v1_funct_1 @ sk_C)),
% 4.76/4.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.76/4.96  thf('192', plain, ((v2_funct_1 @ sk_C)),
% 4.76/4.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.76/4.96  thf('193', plain,
% 4.76/4.96      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.76/4.96        (k1_zfmisc_1 @ 
% 4.76/4.96         (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 4.76/4.96      inference('demod', [status(thm)], ['189', '190', '191', '192'])).
% 4.76/4.96  thf('194', plain,
% 4.76/4.96      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.76/4.96         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C))))
% 4.76/4.96        | ~ (v1_relat_1 @ sk_C)
% 4.76/4.96        | ~ (v1_funct_1 @ sk_C)
% 4.76/4.96        | ~ (v2_funct_1 @ sk_C))),
% 4.76/4.96      inference('sup+', [status(thm)], ['178', '193'])).
% 4.76/4.96  thf('195', plain,
% 4.76/4.96      (![X11 : $i]:
% 4.76/4.96         (~ (v2_funct_1 @ X11)
% 4.76/4.96          | ((k2_relat_1 @ X11) = (k1_relat_1 @ (k2_funct_1 @ X11)))
% 4.76/4.96          | ~ (v1_funct_1 @ X11)
% 4.76/4.96          | ~ (v1_relat_1 @ X11))),
% 4.76/4.96      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.76/4.96  thf('196', plain,
% 4.76/4.96      (![X10 : $i]:
% 4.76/4.96         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 4.76/4.96          | ~ (v1_funct_1 @ X10)
% 4.76/4.96          | ~ (v1_relat_1 @ X10))),
% 4.76/4.96      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.76/4.96  thf('197', plain,
% 4.76/4.96      (![X10 : $i]:
% 4.76/4.96         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 4.76/4.96          | ~ (v1_funct_1 @ X10)
% 4.76/4.96          | ~ (v1_relat_1 @ X10))),
% 4.76/4.96      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.76/4.96  thf('198', plain,
% 4.76/4.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.76/4.96         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 4.76/4.96      inference('sup+', [status(thm)], ['95', '97'])).
% 4.76/4.96  thf('199', plain,
% 4.76/4.96      (![X32 : $i]:
% 4.76/4.96         ((m1_subset_1 @ X32 @ 
% 4.76/4.96           (k1_zfmisc_1 @ 
% 4.76/4.96            (k2_zfmisc_1 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))))
% 4.76/4.96          | ~ (v1_funct_1 @ X32)
% 4.76/4.96          | ~ (v1_relat_1 @ X32))),
% 4.76/4.96      inference('cnf', [status(esa)], [t3_funct_2])).
% 4.76/4.96  thf('200', plain,
% 4.76/4.96      (![X0 : $i, X1 : $i]:
% 4.76/4.96         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 4.76/4.96          | (zip_tseitin_0 @ (k1_relat_1 @ X0) @ X1)
% 4.76/4.96          | ~ (v1_relat_1 @ X0)
% 4.76/4.96          | ~ (v1_funct_1 @ X0))),
% 4.76/4.96      inference('sup+', [status(thm)], ['198', '199'])).
% 4.76/4.96  thf('201', plain,
% 4.76/4.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.76/4.96         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 4.76/4.96      inference('sup+', [status(thm)], ['95', '97'])).
% 4.76/4.96  thf('202', plain,
% 4.76/4.96      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 4.76/4.96      inference('sup-', [status(thm)], ['29', '30'])).
% 4.76/4.96  thf('203', plain,
% 4.76/4.96      (![X0 : $i]:
% 4.76/4.96         (((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0))
% 4.76/4.96          | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 4.76/4.96      inference('sup-', [status(thm)], ['201', '202'])).
% 4.76/4.96  thf('204', plain,
% 4.76/4.96      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 4.76/4.96      inference('demod', [status(thm)], ['35', '38'])).
% 4.76/4.96  thf('205', plain,
% 4.76/4.96      (![X0 : $i]:
% 4.76/4.96         (((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0))
% 4.76/4.96          | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 4.76/4.96      inference('sup-', [status(thm)], ['203', '204'])).
% 4.76/4.96  thf('206', plain,
% 4.76/4.96      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.76/4.96           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 4.76/4.96         <= (~
% 4.76/4.96             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.76/4.96               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 4.76/4.96      inference('split', [status(esa)], ['0'])).
% 4.76/4.96  thf('207', plain,
% 4.76/4.96      (((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ (k1_zfmisc_1 @ k1_xboole_0))
% 4.76/4.96         | ((sk_A) = (k1_relat_1 @ sk_C))))
% 4.76/4.96         <= (~
% 4.76/4.96             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.76/4.96               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 4.76/4.96      inference('sup-', [status(thm)], ['205', '206'])).
% 4.76/4.96  thf('208', plain,
% 4.76/4.96      ((![X0 : $i]:
% 4.76/4.96          (~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.76/4.96           | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 4.76/4.96           | (zip_tseitin_0 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 4.76/4.96           | ((sk_A) = (k1_relat_1 @ sk_C))))
% 4.76/4.96         <= (~
% 4.76/4.96             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.76/4.96               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 4.76/4.96      inference('sup-', [status(thm)], ['200', '207'])).
% 4.76/4.96  thf('209', plain,
% 4.76/4.96      ((![X0 : $i]:
% 4.76/4.96          (~ (v1_relat_1 @ sk_C)
% 4.76/4.96           | ~ (v1_funct_1 @ sk_C)
% 4.76/4.96           | ((sk_A) = (k1_relat_1 @ sk_C))
% 4.76/4.96           | (zip_tseitin_0 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 4.76/4.96           | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))))
% 4.76/4.96         <= (~
% 4.76/4.96             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.76/4.96               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 4.76/4.96      inference('sup-', [status(thm)], ['197', '208'])).
% 4.76/4.96  thf('210', plain, ((v1_relat_1 @ sk_C)),
% 4.76/4.96      inference('sup-', [status(thm)], ['2', '3'])).
% 4.76/4.96  thf('211', plain, ((v1_funct_1 @ sk_C)),
% 4.76/4.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.76/4.96  thf('212', plain,
% 4.76/4.96      ((![X0 : $i]:
% 4.76/4.96          (((sk_A) = (k1_relat_1 @ sk_C))
% 4.76/4.96           | (zip_tseitin_0 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 4.76/4.96           | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))))
% 4.76/4.96         <= (~
% 4.76/4.96             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.76/4.96               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 4.76/4.96      inference('demod', [status(thm)], ['209', '210', '211'])).
% 4.76/4.96  thf('213', plain,
% 4.76/4.96      ((![X0 : $i]:
% 4.76/4.96          (~ (v1_relat_1 @ sk_C)
% 4.76/4.96           | ~ (v1_funct_1 @ sk_C)
% 4.76/4.96           | (zip_tseitin_0 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 4.76/4.96           | ((sk_A) = (k1_relat_1 @ sk_C))))
% 4.76/4.96         <= (~
% 4.76/4.96             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.76/4.96               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 4.76/4.96      inference('sup-', [status(thm)], ['196', '212'])).
% 4.76/4.96  thf('214', plain, ((v1_relat_1 @ sk_C)),
% 4.76/4.96      inference('sup-', [status(thm)], ['2', '3'])).
% 4.76/4.96  thf('215', plain, ((v1_funct_1 @ sk_C)),
% 4.76/4.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.76/4.96  thf('216', plain,
% 4.76/4.96      ((![X0 : $i]:
% 4.76/4.96          ((zip_tseitin_0 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 4.76/4.96           | ((sk_A) = (k1_relat_1 @ sk_C))))
% 4.76/4.96         <= (~
% 4.76/4.96             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.76/4.96               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 4.76/4.96      inference('demod', [status(thm)], ['213', '214', '215'])).
% 4.76/4.96  thf('217', plain,
% 4.76/4.96      ((![X0 : $i]:
% 4.76/4.96          ((zip_tseitin_0 @ (k2_relat_1 @ sk_C) @ X0)
% 4.76/4.96           | ~ (v1_relat_1 @ sk_C)
% 4.76/4.96           | ~ (v1_funct_1 @ sk_C)
% 4.76/4.96           | ~ (v2_funct_1 @ sk_C)
% 4.76/4.96           | ((sk_A) = (k1_relat_1 @ sk_C))))
% 4.76/4.96         <= (~
% 4.76/4.96             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.76/4.96               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 4.76/4.96      inference('sup+', [status(thm)], ['195', '216'])).
% 4.76/4.96  thf('218', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 4.76/4.96      inference('sup+', [status(thm)], ['56', '57'])).
% 4.76/4.96  thf('219', plain, ((v1_relat_1 @ sk_C)),
% 4.76/4.96      inference('sup-', [status(thm)], ['2', '3'])).
% 4.76/4.96  thf('220', plain, ((v1_funct_1 @ sk_C)),
% 4.76/4.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.76/4.96  thf('221', plain, ((v2_funct_1 @ sk_C)),
% 4.76/4.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.76/4.96  thf('222', plain,
% 4.76/4.96      ((![X0 : $i]:
% 4.76/4.96          ((zip_tseitin_0 @ sk_B @ X0) | ((sk_A) = (k1_relat_1 @ sk_C))))
% 4.76/4.96         <= (~
% 4.76/4.96             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.76/4.96               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 4.76/4.96      inference('demod', [status(thm)], ['217', '218', '219', '220', '221'])).
% 4.76/4.96  thf('223', plain,
% 4.76/4.96      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 4.76/4.96      inference('sup-', [status(thm)], ['29', '30'])).
% 4.76/4.96  thf('224', plain,
% 4.76/4.96      (((((sk_A) = (k1_relat_1 @ sk_C)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)))
% 4.76/4.96         <= (~
% 4.76/4.96             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.76/4.96               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 4.76/4.96      inference('sup-', [status(thm)], ['222', '223'])).
% 4.76/4.96  thf('225', plain,
% 4.76/4.96      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 4.76/4.96      inference('demod', [status(thm)], ['35', '38'])).
% 4.76/4.96  thf('226', plain,
% 4.76/4.96      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 4.76/4.96         <= (~
% 4.76/4.96             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.76/4.96               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 4.76/4.96      inference('clc', [status(thm)], ['224', '225'])).
% 4.76/4.96  thf('227', plain,
% 4.76/4.96      (~
% 4.76/4.96       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.76/4.96         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 4.76/4.96      inference('sat_resolution*', [status(thm)], ['10', '174', '175'])).
% 4.76/4.96  thf('228', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 4.76/4.96      inference('simpl_trail', [status(thm)], ['226', '227'])).
% 4.76/4.96  thf('229', plain, ((v1_relat_1 @ sk_C)),
% 4.76/4.96      inference('sup-', [status(thm)], ['2', '3'])).
% 4.76/4.96  thf('230', plain, ((v1_funct_1 @ sk_C)),
% 4.76/4.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.76/4.96  thf('231', plain, ((v2_funct_1 @ sk_C)),
% 4.76/4.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.76/4.96  thf('232', plain,
% 4.76/4.96      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.76/4.96        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.76/4.96      inference('demod', [status(thm)], ['194', '228', '229', '230', '231'])).
% 4.76/4.96  thf('233', plain, ($false), inference('demod', [status(thm)], ['177', '232'])).
% 4.76/4.96  
% 4.76/4.96  % SZS output end Refutation
% 4.76/4.96  
% 4.76/4.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

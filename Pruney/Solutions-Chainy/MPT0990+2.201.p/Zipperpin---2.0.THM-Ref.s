%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pmkPYAAohH

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:29 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :  239 (1334 expanded)
%              Number of leaves         :   43 ( 414 expanded)
%              Depth                    :   29
%              Number of atoms          : 2307 (33362 expanded)
%              Number of equality atoms :  191 (2280 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(t36_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ C )
                = B )
              & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
              & ( v2_funct_1 @ C ) )
           => ( ( A = k1_xboole_0 )
              | ( B = k1_xboole_0 )
              | ( D
                = ( k2_funct_1 @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( ( ( k2_relset_1 @ A @ B @ C )
                  = B )
                & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
                & ( v2_funct_1 @ C ) )
             => ( ( A = k1_xboole_0 )
                | ( B = k1_xboole_0 )
                | ( D
                  = ( k2_funct_1 @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( B = k1_xboole_0 )
          | ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) )
              = ( k6_partfun1 @ A ) )
            & ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C )
              = ( k6_partfun1 @ B ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( X42 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X42 ) ) )
      | ( ( k5_relat_1 @ X43 @ ( k2_funct_1 @ X43 ) )
        = ( k6_partfun1 @ X44 ) )
      | ~ ( v2_funct_1 @ X43 )
      | ( ( k2_relset_1 @ X44 @ X42 @ X43 )
       != X42 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('2',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('8',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X17 @ X18 @ X20 @ X21 @ X16 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('18',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( X11 = X14 )
      | ~ ( r2_relset_1 @ X12 @ X13 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','19'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('21',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('22',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('23',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ ( k6_partfun1 @ B ) )
           => ( ( k2_relset_1 @ A @ B @ C )
              = B ) ) ) ) )).

thf('26',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( r2_relset_1 @ X30 @ X30 @ ( k1_partfun1 @ X30 @ X31 @ X31 @ X30 @ X29 @ X32 ) @ ( k6_partfun1 @ X30 ) )
      | ( ( k2_relset_1 @ X31 @ X30 @ X32 )
        = X30 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('33',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( r2_relset_1 @ X12 @ X13 @ X11 @ X14 )
      | ( X11 != X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('34',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_relset_1 @ X12 @ X13 @ X14 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['31','35','36','37','38'])).

thf('40',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['7','39'])).

thf('41',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('43',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_2 @ D @ A @ B )
        & ( v1_funct_1 @ D ) )
     => ! [E: $i] :
          ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
            & ( v1_funct_2 @ E @ B @ C )
            & ( v1_funct_1 @ E ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ D )
                = B )
              & ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) )
           => ( ( ( v2_funct_1 @ E )
                & ( v2_funct_1 @ D ) )
              | ( ( B != k1_xboole_0 )
                & ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i] :
      ( ( zip_tseitin_1 @ C @ B )
     => ( ( C = k1_xboole_0 )
        & ( B != k1_xboole_0 ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [E: $i,D: $i] :
      ( ( zip_tseitin_0 @ E @ D )
     => ( ( v2_funct_1 @ D )
        & ( v2_funct_1 @ E ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
              & ( ( k2_relset_1 @ A @ B @ D )
                = B ) )
           => ( ( zip_tseitin_1 @ C @ B )
              | ( zip_tseitin_0 @ E @ D ) ) ) ) ) )).

thf('44',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( zip_tseitin_0 @ X37 @ X40 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X41 @ X38 @ X38 @ X39 @ X40 @ X37 ) )
      | ( zip_tseitin_1 @ X39 @ X38 )
      | ( ( k2_relset_1 @ X41 @ X38 @ X40 )
       != X38 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X38 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('50',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('51',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('52',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X7 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['49','52','53','54','55','56'])).

thf('58',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X35 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('60',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X33: $i,X34: $i] :
      ( ( v2_funct_1 @ X34 )
      | ~ ( zip_tseitin_0 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('64',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['41','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('68',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 )
        = ( k5_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['66','71'])).

thf('73',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('75',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf(t64_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) )
              & ( ( k5_relat_1 @ B @ A )
                = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('76',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( X9
        = ( k2_funct_1 @ X10 ) )
      | ( ( k5_relat_1 @ X9 @ X10 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X10 ) ) )
      | ( ( k2_relat_1 @ X9 )
       != ( k1_relat_1 @ X10 ) )
      | ~ ( v2_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('77',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('78',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( X9
        = ( k2_funct_1 @ X10 ) )
      | ( ( k5_relat_1 @ X9 @ X10 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X10 ) ) )
      | ( ( k2_relat_1 @ X9 )
       != ( k1_relat_1 @ X10 ) )
      | ~ ( v2_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('82',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('83',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('84',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('86',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X8 ) @ X8 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('87',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('88',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X8 ) @ X8 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( X42 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X42 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X43 ) @ X43 )
        = ( k6_partfun1 @ X42 ) )
      | ~ ( v2_funct_1 @ X43 )
      | ( ( k2_relset_1 @ X44 @ X42 @ X43 )
       != X42 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('91',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['91','92','93','94','95'])).

thf('97',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['88','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('103',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('105',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['100','105','106','107'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('109',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('110',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('111',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['108','111'])).

thf('113',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('114',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['103','104'])).

thf('117',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['79','84','85','114','115','116'])).

thf('118',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['62','63'])).

thf('119',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k5_relat_1 @ X8 @ ( k2_funct_1 @ X8 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('121',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('122',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k5_relat_1 @ X8 @ ( k2_funct_1 @ X8 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['41','64'])).

thf('124',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['82','83'])).

thf('126',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['62','63'])).

thf('128',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['124','125','126','127'])).

thf('129',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('130',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('132',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    | ( sk_B != sk_B )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['119','132'])).

thf('134',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X8 ) @ X8 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('136',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( X42 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X42 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X43 ) @ X43 )
        = ( k6_partfun1 @ X42 ) )
      | ~ ( v2_funct_1 @ X43 )
      | ( ( k2_relset_1 @ X44 @ X42 @ X43 )
       != X42 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('138',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_D ) @ sk_D )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_D ) @ sk_D )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['138','139','140'])).

thf('142',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_D ) @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['141','142'])).

thf('144',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['31','35','36','37','38'])).

thf('145',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_D ) @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_D ) @ sk_D )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['62','63'])).

thf('148',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_D ) @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,
    ( ( ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['135','148'])).

thf('150',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['82','83'])).

thf('151',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['62','63'])).

thf('153',plain,
    ( ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['149','150','151','152'])).

thf('154',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['134','153'])).

thf('155',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,
    ( ( k5_relat_1 @ sk_D @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['65','155'])).

thf('157',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( X9
        = ( k2_funct_1 @ X10 ) )
      | ( ( k5_relat_1 @ X9 @ X10 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X10 ) ) )
      | ( ( k2_relat_1 @ X9 )
       != ( k1_relat_1 @ X10 ) )
      | ~ ( v2_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('158',plain,
    ( ( ( k6_partfun1 @ sk_B )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_D )
     != ( k1_relat_1 @ sk_C ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('160',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['103','104'])).

thf('161',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['149','150','151','152'])).

thf('164',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('165',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('167',plain,
    ( sk_A
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k5_relat_1 @ X8 @ ( k2_funct_1 @ X8 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('169',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( X42 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X42 ) ) )
      | ( ( k5_relat_1 @ X43 @ ( k2_funct_1 @ X43 ) )
        = ( k6_partfun1 @ X44 ) )
      | ~ ( v2_funct_1 @ X43 )
      | ( ( k2_relset_1 @ X44 @ X42 @ X43 )
       != X42 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('171',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['171','172','173','174','175'])).

thf('177',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['177','178'])).

thf('180',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['168','179'])).

thf('181',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['103','104'])).

thf('182',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['180','181','182','183'])).

thf('185',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('186',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('188',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['82','83'])).

thf('191',plain,
    ( ( ( k6_partfun1 @ sk_B )
     != ( k6_partfun1 @ sk_B ) )
    | ( sk_A != sk_A )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['158','159','160','161','162','167','188','189','190'])).

thf('192',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['191'])).

thf('193',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['192','193'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pmkPYAAohH
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:39:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.38/1.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.38/1.55  % Solved by: fo/fo7.sh
% 1.38/1.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.38/1.55  % done 1397 iterations in 1.074s
% 1.38/1.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.38/1.55  % SZS output start Refutation
% 1.38/1.55  thf(sk_C_type, type, sk_C: $i).
% 1.38/1.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.38/1.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.38/1.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.38/1.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.38/1.55  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.38/1.55  thf(sk_A_type, type, sk_A: $i).
% 1.38/1.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.38/1.55  thf(sk_B_type, type, sk_B: $i).
% 1.38/1.55  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.38/1.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.38/1.55  thf(sk_D_type, type, sk_D: $i).
% 1.38/1.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.38/1.55  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 1.38/1.55  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.38/1.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.38/1.55  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.38/1.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.38/1.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.38/1.55  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.38/1.55  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.38/1.55  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.38/1.55  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.38/1.55  thf(t36_funct_2, conjecture,
% 1.38/1.55    (![A:$i,B:$i,C:$i]:
% 1.38/1.55     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.38/1.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.38/1.55       ( ![D:$i]:
% 1.38/1.55         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.38/1.55             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.38/1.55           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.38/1.55               ( r2_relset_1 @
% 1.38/1.55                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.38/1.55                 ( k6_partfun1 @ A ) ) & 
% 1.38/1.55               ( v2_funct_1 @ C ) ) =>
% 1.38/1.55             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.38/1.55               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.38/1.55  thf(zf_stmt_0, negated_conjecture,
% 1.38/1.55    (~( ![A:$i,B:$i,C:$i]:
% 1.38/1.55        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.38/1.55            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.38/1.55          ( ![D:$i]:
% 1.38/1.55            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.38/1.55                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.38/1.55              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.38/1.55                  ( r2_relset_1 @
% 1.38/1.55                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.38/1.55                    ( k6_partfun1 @ A ) ) & 
% 1.38/1.55                  ( v2_funct_1 @ C ) ) =>
% 1.38/1.55                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.38/1.55                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.38/1.55    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.38/1.55  thf('0', plain,
% 1.38/1.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.38/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.55  thf(t35_funct_2, axiom,
% 1.38/1.55    (![A:$i,B:$i,C:$i]:
% 1.38/1.55     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.38/1.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.38/1.55       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.38/1.55         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.38/1.55           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 1.38/1.55             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 1.38/1.55  thf('1', plain,
% 1.38/1.55      (![X42 : $i, X43 : $i, X44 : $i]:
% 1.38/1.55         (((X42) = (k1_xboole_0))
% 1.38/1.55          | ~ (v1_funct_1 @ X43)
% 1.38/1.55          | ~ (v1_funct_2 @ X43 @ X44 @ X42)
% 1.38/1.55          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X42)))
% 1.38/1.55          | ((k5_relat_1 @ X43 @ (k2_funct_1 @ X43)) = (k6_partfun1 @ X44))
% 1.38/1.55          | ~ (v2_funct_1 @ X43)
% 1.38/1.55          | ((k2_relset_1 @ X44 @ X42 @ X43) != (X42)))),
% 1.38/1.55      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.38/1.55  thf('2', plain,
% 1.38/1.55      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 1.38/1.55        | ~ (v2_funct_1 @ sk_D)
% 1.38/1.55        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.38/1.55        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.38/1.55        | ~ (v1_funct_1 @ sk_D)
% 1.38/1.55        | ((sk_A) = (k1_xboole_0)))),
% 1.38/1.55      inference('sup-', [status(thm)], ['0', '1'])).
% 1.38/1.55  thf('3', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.38/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.55  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 1.38/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.55  thf('5', plain,
% 1.38/1.55      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 1.38/1.55        | ~ (v2_funct_1 @ sk_D)
% 1.38/1.55        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.38/1.55        | ((sk_A) = (k1_xboole_0)))),
% 1.38/1.55      inference('demod', [status(thm)], ['2', '3', '4'])).
% 1.38/1.55  thf('6', plain, (((sk_A) != (k1_xboole_0))),
% 1.38/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.55  thf('7', plain,
% 1.38/1.55      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 1.38/1.55        | ~ (v2_funct_1 @ sk_D)
% 1.38/1.55        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 1.38/1.55      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 1.38/1.55  thf('8', plain,
% 1.38/1.55      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.38/1.55        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.38/1.55        (k6_partfun1 @ sk_A))),
% 1.38/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.55  thf('9', plain,
% 1.38/1.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.38/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.55  thf('10', plain,
% 1.38/1.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.38/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.55  thf(dt_k1_partfun1, axiom,
% 1.38/1.55    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.38/1.55     ( ( ( v1_funct_1 @ E ) & 
% 1.38/1.55         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.38/1.55         ( v1_funct_1 @ F ) & 
% 1.38/1.55         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.38/1.55       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.38/1.55         ( m1_subset_1 @
% 1.38/1.55           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.38/1.55           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.38/1.55  thf('11', plain,
% 1.38/1.55      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.38/1.55         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 1.38/1.55          | ~ (v1_funct_1 @ X16)
% 1.38/1.55          | ~ (v1_funct_1 @ X19)
% 1.38/1.55          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.38/1.55          | (m1_subset_1 @ (k1_partfun1 @ X17 @ X18 @ X20 @ X21 @ X16 @ X19) @ 
% 1.38/1.55             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X21))))),
% 1.38/1.55      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.38/1.55  thf('12', plain,
% 1.38/1.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.55         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.38/1.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.38/1.55          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.38/1.55          | ~ (v1_funct_1 @ X1)
% 1.38/1.55          | ~ (v1_funct_1 @ sk_C))),
% 1.38/1.55      inference('sup-', [status(thm)], ['10', '11'])).
% 1.38/1.55  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 1.38/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.55  thf('14', plain,
% 1.38/1.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.55         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.38/1.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.38/1.55          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.38/1.55          | ~ (v1_funct_1 @ X1))),
% 1.38/1.55      inference('demod', [status(thm)], ['12', '13'])).
% 1.38/1.55  thf('15', plain,
% 1.38/1.55      ((~ (v1_funct_1 @ sk_D)
% 1.38/1.55        | (m1_subset_1 @ 
% 1.38/1.55           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.38/1.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.38/1.55      inference('sup-', [status(thm)], ['9', '14'])).
% 1.38/1.55  thf('16', plain, ((v1_funct_1 @ sk_D)),
% 1.38/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.55  thf('17', plain,
% 1.38/1.55      ((m1_subset_1 @ 
% 1.38/1.55        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.38/1.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.38/1.55      inference('demod', [status(thm)], ['15', '16'])).
% 1.38/1.55  thf(redefinition_r2_relset_1, axiom,
% 1.38/1.55    (![A:$i,B:$i,C:$i,D:$i]:
% 1.38/1.55     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.38/1.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.38/1.55       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.38/1.56  thf('18', plain,
% 1.38/1.56      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 1.38/1.56         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 1.38/1.56          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 1.38/1.56          | ((X11) = (X14))
% 1.38/1.56          | ~ (r2_relset_1 @ X12 @ X13 @ X11 @ X14))),
% 1.38/1.56      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.38/1.56  thf('19', plain,
% 1.38/1.56      (![X0 : $i]:
% 1.38/1.56         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.38/1.56             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 1.38/1.56          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 1.38/1.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.38/1.56      inference('sup-', [status(thm)], ['17', '18'])).
% 1.38/1.56  thf('20', plain,
% 1.38/1.56      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.38/1.56           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.38/1.56        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.38/1.56            = (k6_partfun1 @ sk_A)))),
% 1.38/1.56      inference('sup-', [status(thm)], ['8', '19'])).
% 1.38/1.56  thf(t29_relset_1, axiom,
% 1.38/1.56    (![A:$i]:
% 1.38/1.56     ( m1_subset_1 @
% 1.38/1.56       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.38/1.56  thf('21', plain,
% 1.38/1.56      (![X15 : $i]:
% 1.38/1.56         (m1_subset_1 @ (k6_relat_1 @ X15) @ 
% 1.38/1.56          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X15)))),
% 1.38/1.56      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.38/1.56  thf(redefinition_k6_partfun1, axiom,
% 1.38/1.56    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.38/1.56  thf('22', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 1.38/1.56      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.38/1.56  thf('23', plain,
% 1.38/1.56      (![X15 : $i]:
% 1.38/1.56         (m1_subset_1 @ (k6_partfun1 @ X15) @ 
% 1.38/1.56          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X15)))),
% 1.38/1.56      inference('demod', [status(thm)], ['21', '22'])).
% 1.38/1.56  thf('24', plain,
% 1.38/1.56      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.38/1.56         = (k6_partfun1 @ sk_A))),
% 1.38/1.56      inference('demod', [status(thm)], ['20', '23'])).
% 1.38/1.56  thf('25', plain,
% 1.38/1.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf(t24_funct_2, axiom,
% 1.38/1.56    (![A:$i,B:$i,C:$i]:
% 1.38/1.56     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.38/1.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.38/1.56       ( ![D:$i]:
% 1.38/1.56         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.38/1.56             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.38/1.56           ( ( r2_relset_1 @
% 1.38/1.56               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 1.38/1.56               ( k6_partfun1 @ B ) ) =>
% 1.38/1.56             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 1.38/1.56  thf('26', plain,
% 1.38/1.56      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 1.38/1.56         (~ (v1_funct_1 @ X29)
% 1.38/1.56          | ~ (v1_funct_2 @ X29 @ X30 @ X31)
% 1.38/1.56          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.38/1.56          | ~ (r2_relset_1 @ X30 @ X30 @ 
% 1.38/1.56               (k1_partfun1 @ X30 @ X31 @ X31 @ X30 @ X29 @ X32) @ 
% 1.38/1.56               (k6_partfun1 @ X30))
% 1.38/1.56          | ((k2_relset_1 @ X31 @ X30 @ X32) = (X30))
% 1.38/1.56          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 1.38/1.56          | ~ (v1_funct_2 @ X32 @ X31 @ X30)
% 1.38/1.56          | ~ (v1_funct_1 @ X32))),
% 1.38/1.56      inference('cnf', [status(esa)], [t24_funct_2])).
% 1.38/1.56  thf('27', plain,
% 1.38/1.56      (![X0 : $i]:
% 1.38/1.56         (~ (v1_funct_1 @ X0)
% 1.38/1.56          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.38/1.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.38/1.56          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.38/1.56          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.38/1.56               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.38/1.56               (k6_partfun1 @ sk_A))
% 1.38/1.56          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.38/1.56          | ~ (v1_funct_1 @ sk_C))),
% 1.38/1.56      inference('sup-', [status(thm)], ['25', '26'])).
% 1.38/1.56  thf('28', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('29', plain, ((v1_funct_1 @ sk_C)),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('30', plain,
% 1.38/1.56      (![X0 : $i]:
% 1.38/1.56         (~ (v1_funct_1 @ X0)
% 1.38/1.56          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.38/1.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.38/1.56          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.38/1.56          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.38/1.56               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.38/1.56               (k6_partfun1 @ sk_A)))),
% 1.38/1.56      inference('demod', [status(thm)], ['27', '28', '29'])).
% 1.38/1.56  thf('31', plain,
% 1.38/1.56      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 1.38/1.56           (k6_partfun1 @ sk_A))
% 1.38/1.56        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 1.38/1.56        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.38/1.56        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.38/1.56        | ~ (v1_funct_1 @ sk_D))),
% 1.38/1.56      inference('sup-', [status(thm)], ['24', '30'])).
% 1.38/1.56  thf('32', plain,
% 1.38/1.56      (![X15 : $i]:
% 1.38/1.56         (m1_subset_1 @ (k6_partfun1 @ X15) @ 
% 1.38/1.56          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X15)))),
% 1.38/1.56      inference('demod', [status(thm)], ['21', '22'])).
% 1.38/1.56  thf('33', plain,
% 1.38/1.56      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 1.38/1.56         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 1.38/1.56          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 1.38/1.56          | (r2_relset_1 @ X12 @ X13 @ X11 @ X14)
% 1.38/1.56          | ((X11) != (X14)))),
% 1.38/1.56      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.38/1.56  thf('34', plain,
% 1.38/1.56      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.38/1.56         ((r2_relset_1 @ X12 @ X13 @ X14 @ X14)
% 1.38/1.56          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.38/1.56      inference('simplify', [status(thm)], ['33'])).
% 1.38/1.56  thf('35', plain,
% 1.38/1.56      (![X0 : $i]:
% 1.38/1.56         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 1.38/1.56      inference('sup-', [status(thm)], ['32', '34'])).
% 1.38/1.56  thf('36', plain,
% 1.38/1.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('37', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('38', plain, ((v1_funct_1 @ sk_D)),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('39', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))),
% 1.38/1.56      inference('demod', [status(thm)], ['31', '35', '36', '37', '38'])).
% 1.38/1.56  thf('40', plain,
% 1.38/1.56      ((((sk_A) != (sk_A))
% 1.38/1.56        | ~ (v2_funct_1 @ sk_D)
% 1.38/1.56        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 1.38/1.56      inference('demod', [status(thm)], ['7', '39'])).
% 1.38/1.56  thf('41', plain,
% 1.38/1.56      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.38/1.56        | ~ (v2_funct_1 @ sk_D))),
% 1.38/1.56      inference('simplify', [status(thm)], ['40'])).
% 1.38/1.56  thf('42', plain,
% 1.38/1.56      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.38/1.56         = (k6_partfun1 @ sk_A))),
% 1.38/1.56      inference('demod', [status(thm)], ['20', '23'])).
% 1.38/1.56  thf('43', plain,
% 1.38/1.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf(t30_funct_2, axiom,
% 1.38/1.56    (![A:$i,B:$i,C:$i,D:$i]:
% 1.38/1.56     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.38/1.56         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 1.38/1.56       ( ![E:$i]:
% 1.38/1.56         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 1.38/1.56             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 1.38/1.56           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 1.38/1.56               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 1.38/1.56             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 1.38/1.56               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 1.38/1.56  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 1.38/1.56  thf(zf_stmt_2, axiom,
% 1.38/1.56    (![C:$i,B:$i]:
% 1.38/1.56     ( ( zip_tseitin_1 @ C @ B ) =>
% 1.38/1.56       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 1.38/1.56  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.38/1.56  thf(zf_stmt_4, axiom,
% 1.38/1.56    (![E:$i,D:$i]:
% 1.38/1.56     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 1.38/1.56  thf(zf_stmt_5, axiom,
% 1.38/1.56    (![A:$i,B:$i,C:$i,D:$i]:
% 1.38/1.56     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.38/1.56         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.38/1.56       ( ![E:$i]:
% 1.38/1.56         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.38/1.56             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.38/1.56           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 1.38/1.56               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 1.38/1.56             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 1.38/1.56  thf('44', plain,
% 1.38/1.56      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 1.38/1.56         (~ (v1_funct_1 @ X37)
% 1.38/1.56          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 1.38/1.56          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 1.38/1.56          | (zip_tseitin_0 @ X37 @ X40)
% 1.38/1.56          | ~ (v2_funct_1 @ (k1_partfun1 @ X41 @ X38 @ X38 @ X39 @ X40 @ X37))
% 1.38/1.56          | (zip_tseitin_1 @ X39 @ X38)
% 1.38/1.56          | ((k2_relset_1 @ X41 @ X38 @ X40) != (X38))
% 1.38/1.56          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X38)))
% 1.38/1.56          | ~ (v1_funct_2 @ X40 @ X41 @ X38)
% 1.38/1.56          | ~ (v1_funct_1 @ X40))),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.38/1.56  thf('45', plain,
% 1.38/1.56      (![X0 : $i, X1 : $i]:
% 1.38/1.56         (~ (v1_funct_1 @ X0)
% 1.38/1.56          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.38/1.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.38/1.56          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.38/1.56          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.38/1.56          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.38/1.56          | (zip_tseitin_0 @ sk_D @ X0)
% 1.38/1.56          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.38/1.56          | ~ (v1_funct_1 @ sk_D))),
% 1.38/1.56      inference('sup-', [status(thm)], ['43', '44'])).
% 1.38/1.56  thf('46', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('47', plain, ((v1_funct_1 @ sk_D)),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('48', plain,
% 1.38/1.56      (![X0 : $i, X1 : $i]:
% 1.38/1.56         (~ (v1_funct_1 @ X0)
% 1.38/1.56          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.38/1.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.38/1.56          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.38/1.56          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.38/1.56          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.38/1.56          | (zip_tseitin_0 @ sk_D @ X0))),
% 1.38/1.56      inference('demod', [status(thm)], ['45', '46', '47'])).
% 1.38/1.56  thf('49', plain,
% 1.38/1.56      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 1.38/1.56        | (zip_tseitin_0 @ sk_D @ sk_C)
% 1.38/1.56        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.38/1.56        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.38/1.56        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.38/1.56        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.38/1.56        | ~ (v1_funct_1 @ sk_C))),
% 1.38/1.56      inference('sup-', [status(thm)], ['42', '48'])).
% 1.38/1.56  thf(fc4_funct_1, axiom,
% 1.38/1.56    (![A:$i]:
% 1.38/1.56     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.38/1.56       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.38/1.56  thf('50', plain, (![X7 : $i]: (v2_funct_1 @ (k6_relat_1 @ X7))),
% 1.38/1.56      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.38/1.56  thf('51', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 1.38/1.56      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.38/1.56  thf('52', plain, (![X7 : $i]: (v2_funct_1 @ (k6_partfun1 @ X7))),
% 1.38/1.56      inference('demod', [status(thm)], ['50', '51'])).
% 1.38/1.56  thf('53', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('54', plain,
% 1.38/1.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('55', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('56', plain, ((v1_funct_1 @ sk_C)),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('57', plain,
% 1.38/1.56      (((zip_tseitin_0 @ sk_D @ sk_C)
% 1.38/1.56        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.38/1.56        | ((sk_B) != (sk_B)))),
% 1.38/1.56      inference('demod', [status(thm)], ['49', '52', '53', '54', '55', '56'])).
% 1.38/1.56  thf('58', plain,
% 1.38/1.56      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 1.38/1.56      inference('simplify', [status(thm)], ['57'])).
% 1.38/1.56  thf('59', plain,
% 1.38/1.56      (![X35 : $i, X36 : $i]:
% 1.38/1.56         (((X35) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X35 @ X36))),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.38/1.56  thf('60', plain,
% 1.38/1.56      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 1.38/1.56      inference('sup-', [status(thm)], ['58', '59'])).
% 1.38/1.56  thf('61', plain, (((sk_A) != (k1_xboole_0))),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('62', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 1.38/1.56      inference('simplify_reflect-', [status(thm)], ['60', '61'])).
% 1.38/1.56  thf('63', plain,
% 1.38/1.56      (![X33 : $i, X34 : $i]:
% 1.38/1.56         ((v2_funct_1 @ X34) | ~ (zip_tseitin_0 @ X34 @ X33))),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.38/1.56  thf('64', plain, ((v2_funct_1 @ sk_D)),
% 1.38/1.56      inference('sup-', [status(thm)], ['62', '63'])).
% 1.38/1.56  thf('65', plain,
% 1.38/1.56      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 1.38/1.56      inference('demod', [status(thm)], ['41', '64'])).
% 1.38/1.56  thf('66', plain,
% 1.38/1.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('67', plain,
% 1.38/1.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf(redefinition_k1_partfun1, axiom,
% 1.38/1.56    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.38/1.56     ( ( ( v1_funct_1 @ E ) & 
% 1.38/1.56         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.38/1.56         ( v1_funct_1 @ F ) & 
% 1.38/1.56         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.38/1.56       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.38/1.56  thf('68', plain,
% 1.38/1.56      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.38/1.56         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 1.38/1.56          | ~ (v1_funct_1 @ X22)
% 1.38/1.56          | ~ (v1_funct_1 @ X25)
% 1.38/1.56          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 1.38/1.56          | ((k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25)
% 1.38/1.56              = (k5_relat_1 @ X22 @ X25)))),
% 1.38/1.56      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.38/1.56  thf('69', plain,
% 1.38/1.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.56         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.38/1.56            = (k5_relat_1 @ sk_C @ X0))
% 1.38/1.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.38/1.56          | ~ (v1_funct_1 @ X0)
% 1.38/1.56          | ~ (v1_funct_1 @ sk_C))),
% 1.38/1.56      inference('sup-', [status(thm)], ['67', '68'])).
% 1.38/1.56  thf('70', plain, ((v1_funct_1 @ sk_C)),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('71', plain,
% 1.38/1.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.56         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.38/1.56            = (k5_relat_1 @ sk_C @ X0))
% 1.38/1.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.38/1.56          | ~ (v1_funct_1 @ X0))),
% 1.38/1.56      inference('demod', [status(thm)], ['69', '70'])).
% 1.38/1.56  thf('72', plain,
% 1.38/1.56      ((~ (v1_funct_1 @ sk_D)
% 1.38/1.56        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.38/1.56            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.38/1.56      inference('sup-', [status(thm)], ['66', '71'])).
% 1.38/1.56  thf('73', plain, ((v1_funct_1 @ sk_D)),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('74', plain,
% 1.38/1.56      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.38/1.56         = (k6_partfun1 @ sk_A))),
% 1.38/1.56      inference('demod', [status(thm)], ['20', '23'])).
% 1.38/1.56  thf('75', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 1.38/1.56      inference('demod', [status(thm)], ['72', '73', '74'])).
% 1.38/1.56  thf(t64_funct_1, axiom,
% 1.38/1.56    (![A:$i]:
% 1.38/1.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.38/1.56       ( ![B:$i]:
% 1.38/1.56         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.38/1.56           ( ( ( v2_funct_1 @ A ) & 
% 1.38/1.56               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 1.38/1.56               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 1.38/1.56             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.38/1.56  thf('76', plain,
% 1.38/1.56      (![X9 : $i, X10 : $i]:
% 1.38/1.56         (~ (v1_relat_1 @ X9)
% 1.38/1.56          | ~ (v1_funct_1 @ X9)
% 1.38/1.56          | ((X9) = (k2_funct_1 @ X10))
% 1.38/1.56          | ((k5_relat_1 @ X9 @ X10) != (k6_relat_1 @ (k2_relat_1 @ X10)))
% 1.38/1.56          | ((k2_relat_1 @ X9) != (k1_relat_1 @ X10))
% 1.38/1.56          | ~ (v2_funct_1 @ X10)
% 1.38/1.56          | ~ (v1_funct_1 @ X10)
% 1.38/1.56          | ~ (v1_relat_1 @ X10))),
% 1.38/1.56      inference('cnf', [status(esa)], [t64_funct_1])).
% 1.38/1.56  thf('77', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 1.38/1.56      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.38/1.56  thf('78', plain,
% 1.38/1.56      (![X9 : $i, X10 : $i]:
% 1.38/1.56         (~ (v1_relat_1 @ X9)
% 1.38/1.56          | ~ (v1_funct_1 @ X9)
% 1.38/1.56          | ((X9) = (k2_funct_1 @ X10))
% 1.38/1.56          | ((k5_relat_1 @ X9 @ X10) != (k6_partfun1 @ (k2_relat_1 @ X10)))
% 1.38/1.56          | ((k2_relat_1 @ X9) != (k1_relat_1 @ X10))
% 1.38/1.56          | ~ (v2_funct_1 @ X10)
% 1.38/1.56          | ~ (v1_funct_1 @ X10)
% 1.38/1.56          | ~ (v1_relat_1 @ X10))),
% 1.38/1.56      inference('demod', [status(thm)], ['76', '77'])).
% 1.38/1.56  thf('79', plain,
% 1.38/1.56      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 1.38/1.56        | ~ (v1_relat_1 @ sk_D)
% 1.38/1.56        | ~ (v1_funct_1 @ sk_D)
% 1.38/1.56        | ~ (v2_funct_1 @ sk_D)
% 1.38/1.56        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 1.38/1.56        | ((sk_C) = (k2_funct_1 @ sk_D))
% 1.38/1.56        | ~ (v1_funct_1 @ sk_C)
% 1.38/1.56        | ~ (v1_relat_1 @ sk_C))),
% 1.38/1.56      inference('sup-', [status(thm)], ['75', '78'])).
% 1.38/1.56  thf('80', plain,
% 1.38/1.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf(cc2_relat_1, axiom,
% 1.38/1.56    (![A:$i]:
% 1.38/1.56     ( ( v1_relat_1 @ A ) =>
% 1.38/1.56       ( ![B:$i]:
% 1.38/1.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.38/1.56  thf('81', plain,
% 1.38/1.56      (![X0 : $i, X1 : $i]:
% 1.38/1.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.38/1.56          | (v1_relat_1 @ X0)
% 1.38/1.56          | ~ (v1_relat_1 @ X1))),
% 1.38/1.56      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.38/1.56  thf('82', plain,
% 1.38/1.56      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 1.38/1.56      inference('sup-', [status(thm)], ['80', '81'])).
% 1.38/1.56  thf(fc6_relat_1, axiom,
% 1.38/1.56    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.38/1.56  thf('83', plain,
% 1.38/1.56      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.38/1.56      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.38/1.56  thf('84', plain, ((v1_relat_1 @ sk_D)),
% 1.38/1.56      inference('demod', [status(thm)], ['82', '83'])).
% 1.38/1.56  thf('85', plain, ((v1_funct_1 @ sk_D)),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf(t61_funct_1, axiom,
% 1.38/1.56    (![A:$i]:
% 1.38/1.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.38/1.56       ( ( v2_funct_1 @ A ) =>
% 1.38/1.56         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.38/1.56             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.38/1.56           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.38/1.56             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.38/1.56  thf('86', plain,
% 1.38/1.56      (![X8 : $i]:
% 1.38/1.56         (~ (v2_funct_1 @ X8)
% 1.38/1.56          | ((k5_relat_1 @ (k2_funct_1 @ X8) @ X8)
% 1.38/1.56              = (k6_relat_1 @ (k2_relat_1 @ X8)))
% 1.38/1.56          | ~ (v1_funct_1 @ X8)
% 1.38/1.56          | ~ (v1_relat_1 @ X8))),
% 1.38/1.56      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.38/1.56  thf('87', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 1.38/1.56      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.38/1.56  thf('88', plain,
% 1.38/1.56      (![X8 : $i]:
% 1.38/1.56         (~ (v2_funct_1 @ X8)
% 1.38/1.56          | ((k5_relat_1 @ (k2_funct_1 @ X8) @ X8)
% 1.38/1.56              = (k6_partfun1 @ (k2_relat_1 @ X8)))
% 1.38/1.56          | ~ (v1_funct_1 @ X8)
% 1.38/1.56          | ~ (v1_relat_1 @ X8))),
% 1.38/1.56      inference('demod', [status(thm)], ['86', '87'])).
% 1.38/1.56  thf('89', plain,
% 1.38/1.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('90', plain,
% 1.38/1.56      (![X42 : $i, X43 : $i, X44 : $i]:
% 1.38/1.56         (((X42) = (k1_xboole_0))
% 1.38/1.56          | ~ (v1_funct_1 @ X43)
% 1.38/1.56          | ~ (v1_funct_2 @ X43 @ X44 @ X42)
% 1.38/1.56          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X42)))
% 1.38/1.56          | ((k5_relat_1 @ (k2_funct_1 @ X43) @ X43) = (k6_partfun1 @ X42))
% 1.38/1.56          | ~ (v2_funct_1 @ X43)
% 1.38/1.56          | ((k2_relset_1 @ X44 @ X42 @ X43) != (X42)))),
% 1.38/1.56      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.38/1.56  thf('91', plain,
% 1.38/1.56      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.38/1.56        | ~ (v2_funct_1 @ sk_C)
% 1.38/1.56        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 1.38/1.56        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.38/1.56        | ~ (v1_funct_1 @ sk_C)
% 1.38/1.56        | ((sk_B) = (k1_xboole_0)))),
% 1.38/1.56      inference('sup-', [status(thm)], ['89', '90'])).
% 1.38/1.56  thf('92', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('93', plain, ((v2_funct_1 @ sk_C)),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('94', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('95', plain, ((v1_funct_1 @ sk_C)),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('96', plain,
% 1.38/1.56      ((((sk_B) != (sk_B))
% 1.38/1.56        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 1.38/1.56        | ((sk_B) = (k1_xboole_0)))),
% 1.38/1.56      inference('demod', [status(thm)], ['91', '92', '93', '94', '95'])).
% 1.38/1.56  thf('97', plain,
% 1.38/1.56      ((((sk_B) = (k1_xboole_0))
% 1.38/1.56        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 1.38/1.56      inference('simplify', [status(thm)], ['96'])).
% 1.38/1.56  thf('98', plain, (((sk_B) != (k1_xboole_0))),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('99', plain,
% 1.38/1.56      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 1.38/1.56      inference('simplify_reflect-', [status(thm)], ['97', '98'])).
% 1.38/1.56  thf('100', plain,
% 1.38/1.56      ((((k6_partfun1 @ (k2_relat_1 @ sk_C)) = (k6_partfun1 @ sk_B))
% 1.38/1.56        | ~ (v1_relat_1 @ sk_C)
% 1.38/1.56        | ~ (v1_funct_1 @ sk_C)
% 1.38/1.56        | ~ (v2_funct_1 @ sk_C))),
% 1.38/1.56      inference('sup+', [status(thm)], ['88', '99'])).
% 1.38/1.56  thf('101', plain,
% 1.38/1.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('102', plain,
% 1.38/1.56      (![X0 : $i, X1 : $i]:
% 1.38/1.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.38/1.56          | (v1_relat_1 @ X0)
% 1.38/1.56          | ~ (v1_relat_1 @ X1))),
% 1.38/1.56      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.38/1.56  thf('103', plain,
% 1.38/1.56      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 1.38/1.56      inference('sup-', [status(thm)], ['101', '102'])).
% 1.38/1.56  thf('104', plain,
% 1.38/1.56      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.38/1.56      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.38/1.56  thf('105', plain, ((v1_relat_1 @ sk_C)),
% 1.38/1.56      inference('demod', [status(thm)], ['103', '104'])).
% 1.38/1.56  thf('106', plain, ((v1_funct_1 @ sk_C)),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('107', plain, ((v2_funct_1 @ sk_C)),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('108', plain,
% 1.38/1.56      (((k6_partfun1 @ (k2_relat_1 @ sk_C)) = (k6_partfun1 @ sk_B))),
% 1.38/1.56      inference('demod', [status(thm)], ['100', '105', '106', '107'])).
% 1.38/1.56  thf(t71_relat_1, axiom,
% 1.38/1.56    (![A:$i]:
% 1.38/1.56     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.38/1.56       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.38/1.56  thf('109', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 1.38/1.56      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.38/1.56  thf('110', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 1.38/1.56      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.38/1.56  thf('111', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 1.38/1.56      inference('demod', [status(thm)], ['109', '110'])).
% 1.38/1.56  thf('112', plain,
% 1.38/1.56      (((k1_relat_1 @ (k6_partfun1 @ sk_B)) = (k2_relat_1 @ sk_C))),
% 1.38/1.56      inference('sup+', [status(thm)], ['108', '111'])).
% 1.38/1.56  thf('113', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 1.38/1.56      inference('demod', [status(thm)], ['109', '110'])).
% 1.38/1.56  thf('114', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 1.38/1.56      inference('demod', [status(thm)], ['112', '113'])).
% 1.38/1.56  thf('115', plain, ((v1_funct_1 @ sk_C)),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('116', plain, ((v1_relat_1 @ sk_C)),
% 1.38/1.56      inference('demod', [status(thm)], ['103', '104'])).
% 1.38/1.56  thf('117', plain,
% 1.38/1.56      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 1.38/1.56        | ~ (v2_funct_1 @ sk_D)
% 1.38/1.56        | ((sk_B) != (k1_relat_1 @ sk_D))
% 1.38/1.56        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 1.38/1.56      inference('demod', [status(thm)], ['79', '84', '85', '114', '115', '116'])).
% 1.38/1.56  thf('118', plain, ((v2_funct_1 @ sk_D)),
% 1.38/1.56      inference('sup-', [status(thm)], ['62', '63'])).
% 1.38/1.56  thf('119', plain,
% 1.38/1.56      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 1.38/1.56        | ((sk_B) != (k1_relat_1 @ sk_D))
% 1.38/1.56        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 1.38/1.56      inference('demod', [status(thm)], ['117', '118'])).
% 1.38/1.56  thf('120', plain,
% 1.38/1.56      (![X8 : $i]:
% 1.38/1.56         (~ (v2_funct_1 @ X8)
% 1.38/1.56          | ((k5_relat_1 @ X8 @ (k2_funct_1 @ X8))
% 1.38/1.56              = (k6_relat_1 @ (k1_relat_1 @ X8)))
% 1.38/1.56          | ~ (v1_funct_1 @ X8)
% 1.38/1.56          | ~ (v1_relat_1 @ X8))),
% 1.38/1.56      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.38/1.56  thf('121', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 1.38/1.56      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.38/1.56  thf('122', plain,
% 1.38/1.56      (![X8 : $i]:
% 1.38/1.56         (~ (v2_funct_1 @ X8)
% 1.38/1.56          | ((k5_relat_1 @ X8 @ (k2_funct_1 @ X8))
% 1.38/1.56              = (k6_partfun1 @ (k1_relat_1 @ X8)))
% 1.38/1.56          | ~ (v1_funct_1 @ X8)
% 1.38/1.56          | ~ (v1_relat_1 @ X8))),
% 1.38/1.56      inference('demod', [status(thm)], ['120', '121'])).
% 1.38/1.56  thf('123', plain,
% 1.38/1.56      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 1.38/1.56      inference('demod', [status(thm)], ['41', '64'])).
% 1.38/1.56  thf('124', plain,
% 1.38/1.56      ((((k6_partfun1 @ (k1_relat_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.38/1.56        | ~ (v1_relat_1 @ sk_D)
% 1.38/1.56        | ~ (v1_funct_1 @ sk_D)
% 1.38/1.56        | ~ (v2_funct_1 @ sk_D))),
% 1.38/1.56      inference('sup+', [status(thm)], ['122', '123'])).
% 1.38/1.56  thf('125', plain, ((v1_relat_1 @ sk_D)),
% 1.38/1.56      inference('demod', [status(thm)], ['82', '83'])).
% 1.38/1.56  thf('126', plain, ((v1_funct_1 @ sk_D)),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('127', plain, ((v2_funct_1 @ sk_D)),
% 1.38/1.56      inference('sup-', [status(thm)], ['62', '63'])).
% 1.38/1.56  thf('128', plain,
% 1.38/1.56      (((k6_partfun1 @ (k1_relat_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 1.38/1.56      inference('demod', [status(thm)], ['124', '125', '126', '127'])).
% 1.38/1.56  thf('129', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 1.38/1.56      inference('demod', [status(thm)], ['109', '110'])).
% 1.38/1.56  thf('130', plain,
% 1.38/1.56      (((k1_relat_1 @ (k6_partfun1 @ sk_B)) = (k1_relat_1 @ sk_D))),
% 1.38/1.56      inference('sup+', [status(thm)], ['128', '129'])).
% 1.38/1.56  thf('131', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 1.38/1.56      inference('demod', [status(thm)], ['109', '110'])).
% 1.38/1.56  thf('132', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.38/1.56      inference('demod', [status(thm)], ['130', '131'])).
% 1.38/1.56  thf('133', plain,
% 1.38/1.56      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 1.38/1.56        | ((sk_B) != (sk_B))
% 1.38/1.56        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 1.38/1.56      inference('demod', [status(thm)], ['119', '132'])).
% 1.38/1.56  thf('134', plain,
% 1.38/1.56      ((((sk_C) = (k2_funct_1 @ sk_D))
% 1.38/1.56        | ((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D))))),
% 1.38/1.56      inference('simplify', [status(thm)], ['133'])).
% 1.38/1.56  thf('135', plain,
% 1.38/1.56      (![X8 : $i]:
% 1.38/1.56         (~ (v2_funct_1 @ X8)
% 1.38/1.56          | ((k5_relat_1 @ (k2_funct_1 @ X8) @ X8)
% 1.38/1.56              = (k6_partfun1 @ (k2_relat_1 @ X8)))
% 1.38/1.56          | ~ (v1_funct_1 @ X8)
% 1.38/1.56          | ~ (v1_relat_1 @ X8))),
% 1.38/1.56      inference('demod', [status(thm)], ['86', '87'])).
% 1.38/1.56  thf('136', plain,
% 1.38/1.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('137', plain,
% 1.38/1.56      (![X42 : $i, X43 : $i, X44 : $i]:
% 1.38/1.56         (((X42) = (k1_xboole_0))
% 1.38/1.56          | ~ (v1_funct_1 @ X43)
% 1.38/1.56          | ~ (v1_funct_2 @ X43 @ X44 @ X42)
% 1.38/1.56          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X42)))
% 1.38/1.56          | ((k5_relat_1 @ (k2_funct_1 @ X43) @ X43) = (k6_partfun1 @ X42))
% 1.38/1.56          | ~ (v2_funct_1 @ X43)
% 1.38/1.56          | ((k2_relset_1 @ X44 @ X42 @ X43) != (X42)))),
% 1.38/1.56      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.38/1.56  thf('138', plain,
% 1.38/1.56      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 1.38/1.56        | ~ (v2_funct_1 @ sk_D)
% 1.38/1.56        | ((k5_relat_1 @ (k2_funct_1 @ sk_D) @ sk_D) = (k6_partfun1 @ sk_A))
% 1.38/1.56        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.38/1.56        | ~ (v1_funct_1 @ sk_D)
% 1.38/1.56        | ((sk_A) = (k1_xboole_0)))),
% 1.38/1.56      inference('sup-', [status(thm)], ['136', '137'])).
% 1.38/1.56  thf('139', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('140', plain, ((v1_funct_1 @ sk_D)),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('141', plain,
% 1.38/1.56      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 1.38/1.56        | ~ (v2_funct_1 @ sk_D)
% 1.38/1.56        | ((k5_relat_1 @ (k2_funct_1 @ sk_D) @ sk_D) = (k6_partfun1 @ sk_A))
% 1.38/1.56        | ((sk_A) = (k1_xboole_0)))),
% 1.38/1.56      inference('demod', [status(thm)], ['138', '139', '140'])).
% 1.38/1.56  thf('142', plain, (((sk_A) != (k1_xboole_0))),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('143', plain,
% 1.38/1.56      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 1.38/1.56        | ~ (v2_funct_1 @ sk_D)
% 1.38/1.56        | ((k5_relat_1 @ (k2_funct_1 @ sk_D) @ sk_D) = (k6_partfun1 @ sk_A)))),
% 1.38/1.56      inference('simplify_reflect-', [status(thm)], ['141', '142'])).
% 1.38/1.56  thf('144', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))),
% 1.38/1.56      inference('demod', [status(thm)], ['31', '35', '36', '37', '38'])).
% 1.38/1.56  thf('145', plain,
% 1.38/1.56      ((((sk_A) != (sk_A))
% 1.38/1.56        | ~ (v2_funct_1 @ sk_D)
% 1.38/1.56        | ((k5_relat_1 @ (k2_funct_1 @ sk_D) @ sk_D) = (k6_partfun1 @ sk_A)))),
% 1.38/1.56      inference('demod', [status(thm)], ['143', '144'])).
% 1.38/1.56  thf('146', plain,
% 1.38/1.56      ((((k5_relat_1 @ (k2_funct_1 @ sk_D) @ sk_D) = (k6_partfun1 @ sk_A))
% 1.38/1.56        | ~ (v2_funct_1 @ sk_D))),
% 1.38/1.56      inference('simplify', [status(thm)], ['145'])).
% 1.38/1.56  thf('147', plain, ((v2_funct_1 @ sk_D)),
% 1.38/1.56      inference('sup-', [status(thm)], ['62', '63'])).
% 1.38/1.56  thf('148', plain,
% 1.38/1.56      (((k5_relat_1 @ (k2_funct_1 @ sk_D) @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.38/1.56      inference('demod', [status(thm)], ['146', '147'])).
% 1.38/1.56  thf('149', plain,
% 1.38/1.56      ((((k6_partfun1 @ (k2_relat_1 @ sk_D)) = (k6_partfun1 @ sk_A))
% 1.38/1.56        | ~ (v1_relat_1 @ sk_D)
% 1.38/1.56        | ~ (v1_funct_1 @ sk_D)
% 1.38/1.56        | ~ (v2_funct_1 @ sk_D))),
% 1.38/1.56      inference('sup+', [status(thm)], ['135', '148'])).
% 1.38/1.56  thf('150', plain, ((v1_relat_1 @ sk_D)),
% 1.38/1.56      inference('demod', [status(thm)], ['82', '83'])).
% 1.38/1.56  thf('151', plain, ((v1_funct_1 @ sk_D)),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('152', plain, ((v2_funct_1 @ sk_D)),
% 1.38/1.56      inference('sup-', [status(thm)], ['62', '63'])).
% 1.38/1.56  thf('153', plain,
% 1.38/1.56      (((k6_partfun1 @ (k2_relat_1 @ sk_D)) = (k6_partfun1 @ sk_A))),
% 1.38/1.56      inference('demod', [status(thm)], ['149', '150', '151', '152'])).
% 1.38/1.56  thf('154', plain,
% 1.38/1.56      ((((sk_C) = (k2_funct_1 @ sk_D))
% 1.38/1.56        | ((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A)))),
% 1.38/1.56      inference('demod', [status(thm)], ['134', '153'])).
% 1.38/1.56  thf('155', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.38/1.56      inference('simplify', [status(thm)], ['154'])).
% 1.38/1.56  thf('156', plain, (((k5_relat_1 @ sk_D @ sk_C) = (k6_partfun1 @ sk_B))),
% 1.38/1.56      inference('demod', [status(thm)], ['65', '155'])).
% 1.38/1.56  thf('157', plain,
% 1.38/1.56      (![X9 : $i, X10 : $i]:
% 1.38/1.56         (~ (v1_relat_1 @ X9)
% 1.38/1.56          | ~ (v1_funct_1 @ X9)
% 1.38/1.56          | ((X9) = (k2_funct_1 @ X10))
% 1.38/1.56          | ((k5_relat_1 @ X9 @ X10) != (k6_partfun1 @ (k2_relat_1 @ X10)))
% 1.38/1.56          | ((k2_relat_1 @ X9) != (k1_relat_1 @ X10))
% 1.38/1.56          | ~ (v2_funct_1 @ X10)
% 1.38/1.56          | ~ (v1_funct_1 @ X10)
% 1.38/1.56          | ~ (v1_relat_1 @ X10))),
% 1.38/1.56      inference('demod', [status(thm)], ['76', '77'])).
% 1.38/1.56  thf('158', plain,
% 1.38/1.56      ((((k6_partfun1 @ sk_B) != (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 1.38/1.56        | ~ (v1_relat_1 @ sk_C)
% 1.38/1.56        | ~ (v1_funct_1 @ sk_C)
% 1.38/1.56        | ~ (v2_funct_1 @ sk_C)
% 1.38/1.56        | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ sk_C))
% 1.38/1.56        | ((sk_D) = (k2_funct_1 @ sk_C))
% 1.38/1.56        | ~ (v1_funct_1 @ sk_D)
% 1.38/1.56        | ~ (v1_relat_1 @ sk_D))),
% 1.38/1.56      inference('sup-', [status(thm)], ['156', '157'])).
% 1.38/1.56  thf('159', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 1.38/1.56      inference('demod', [status(thm)], ['112', '113'])).
% 1.38/1.56  thf('160', plain, ((v1_relat_1 @ sk_C)),
% 1.38/1.56      inference('demod', [status(thm)], ['103', '104'])).
% 1.38/1.56  thf('161', plain, ((v1_funct_1 @ sk_C)),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('162', plain, ((v2_funct_1 @ sk_C)),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('163', plain,
% 1.38/1.56      (((k6_partfun1 @ (k2_relat_1 @ sk_D)) = (k6_partfun1 @ sk_A))),
% 1.38/1.56      inference('demod', [status(thm)], ['149', '150', '151', '152'])).
% 1.38/1.56  thf('164', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 1.38/1.56      inference('demod', [status(thm)], ['109', '110'])).
% 1.38/1.56  thf('165', plain,
% 1.38/1.56      (((k1_relat_1 @ (k6_partfun1 @ sk_A)) = (k2_relat_1 @ sk_D))),
% 1.38/1.56      inference('sup+', [status(thm)], ['163', '164'])).
% 1.38/1.56  thf('166', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 1.38/1.56      inference('demod', [status(thm)], ['109', '110'])).
% 1.38/1.56  thf('167', plain, (((sk_A) = (k2_relat_1 @ sk_D))),
% 1.38/1.56      inference('demod', [status(thm)], ['165', '166'])).
% 1.38/1.56  thf('168', plain,
% 1.38/1.56      (![X8 : $i]:
% 1.38/1.56         (~ (v2_funct_1 @ X8)
% 1.38/1.56          | ((k5_relat_1 @ X8 @ (k2_funct_1 @ X8))
% 1.38/1.56              = (k6_partfun1 @ (k1_relat_1 @ X8)))
% 1.38/1.56          | ~ (v1_funct_1 @ X8)
% 1.38/1.56          | ~ (v1_relat_1 @ X8))),
% 1.38/1.56      inference('demod', [status(thm)], ['120', '121'])).
% 1.38/1.56  thf('169', plain,
% 1.38/1.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('170', plain,
% 1.38/1.56      (![X42 : $i, X43 : $i, X44 : $i]:
% 1.38/1.56         (((X42) = (k1_xboole_0))
% 1.38/1.56          | ~ (v1_funct_1 @ X43)
% 1.38/1.56          | ~ (v1_funct_2 @ X43 @ X44 @ X42)
% 1.38/1.56          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X42)))
% 1.38/1.56          | ((k5_relat_1 @ X43 @ (k2_funct_1 @ X43)) = (k6_partfun1 @ X44))
% 1.38/1.56          | ~ (v2_funct_1 @ X43)
% 1.38/1.56          | ((k2_relset_1 @ X44 @ X42 @ X43) != (X42)))),
% 1.38/1.56      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.38/1.56  thf('171', plain,
% 1.38/1.56      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.38/1.56        | ~ (v2_funct_1 @ sk_C)
% 1.38/1.56        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 1.38/1.56        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.38/1.56        | ~ (v1_funct_1 @ sk_C)
% 1.38/1.56        | ((sk_B) = (k1_xboole_0)))),
% 1.38/1.56      inference('sup-', [status(thm)], ['169', '170'])).
% 1.38/1.56  thf('172', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('173', plain, ((v2_funct_1 @ sk_C)),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('174', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('175', plain, ((v1_funct_1 @ sk_C)),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('176', plain,
% 1.38/1.56      ((((sk_B) != (sk_B))
% 1.38/1.56        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 1.38/1.56        | ((sk_B) = (k1_xboole_0)))),
% 1.38/1.56      inference('demod', [status(thm)], ['171', '172', '173', '174', '175'])).
% 1.38/1.56  thf('177', plain,
% 1.38/1.56      ((((sk_B) = (k1_xboole_0))
% 1.38/1.56        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 1.38/1.56      inference('simplify', [status(thm)], ['176'])).
% 1.38/1.56  thf('178', plain, (((sk_B) != (k1_xboole_0))),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('179', plain,
% 1.38/1.56      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 1.38/1.56      inference('simplify_reflect-', [status(thm)], ['177', '178'])).
% 1.38/1.56  thf('180', plain,
% 1.38/1.56      ((((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 1.38/1.56        | ~ (v1_relat_1 @ sk_C)
% 1.38/1.56        | ~ (v1_funct_1 @ sk_C)
% 1.38/1.56        | ~ (v2_funct_1 @ sk_C))),
% 1.38/1.56      inference('sup+', [status(thm)], ['168', '179'])).
% 1.38/1.56  thf('181', plain, ((v1_relat_1 @ sk_C)),
% 1.38/1.56      inference('demod', [status(thm)], ['103', '104'])).
% 1.38/1.56  thf('182', plain, ((v1_funct_1 @ sk_C)),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('183', plain, ((v2_funct_1 @ sk_C)),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('184', plain,
% 1.38/1.56      (((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 1.38/1.56      inference('demod', [status(thm)], ['180', '181', '182', '183'])).
% 1.38/1.56  thf('185', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 1.38/1.56      inference('demod', [status(thm)], ['109', '110'])).
% 1.38/1.56  thf('186', plain,
% 1.38/1.56      (((k1_relat_1 @ (k6_partfun1 @ sk_A)) = (k1_relat_1 @ sk_C))),
% 1.38/1.56      inference('sup+', [status(thm)], ['184', '185'])).
% 1.38/1.56  thf('187', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 1.38/1.56      inference('demod', [status(thm)], ['109', '110'])).
% 1.38/1.56  thf('188', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 1.38/1.56      inference('demod', [status(thm)], ['186', '187'])).
% 1.38/1.56  thf('189', plain, ((v1_funct_1 @ sk_D)),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('190', plain, ((v1_relat_1 @ sk_D)),
% 1.38/1.56      inference('demod', [status(thm)], ['82', '83'])).
% 1.38/1.56  thf('191', plain,
% 1.38/1.56      ((((k6_partfun1 @ sk_B) != (k6_partfun1 @ sk_B))
% 1.38/1.56        | ((sk_A) != (sk_A))
% 1.38/1.56        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 1.38/1.56      inference('demod', [status(thm)],
% 1.38/1.56                ['158', '159', '160', '161', '162', '167', '188', '189', '190'])).
% 1.38/1.56  thf('192', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 1.38/1.56      inference('simplify', [status(thm)], ['191'])).
% 1.38/1.56  thf('193', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.38/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.56  thf('194', plain, ($false),
% 1.38/1.56      inference('simplify_reflect-', [status(thm)], ['192', '193'])).
% 1.38/1.56  
% 1.38/1.56  % SZS output end Refutation
% 1.38/1.56  
% 1.38/1.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

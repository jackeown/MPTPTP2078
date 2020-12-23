%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OYUBynerqQ

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:01 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 662 expanded)
%              Number of leaves         :   44 ( 216 expanded)
%              Depth                    :   19
%              Number of atoms          : 1759 (16799 expanded)
%              Number of equality atoms :  128 (1133 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( X45 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X45 ) ) )
      | ( ( k5_relat_1 @ X46 @ ( k2_funct_1 @ X46 ) )
        = ( k6_partfun1 @ X47 ) )
      | ~ ( v2_funct_1 @ X46 )
      | ( ( k2_relset_1 @ X47 @ X45 @ X46 )
       != X45 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( X45 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X45 ) ) )
      | ( ( k5_relat_1 @ X46 @ ( k2_funct_1 @ X46 ) )
        = ( k6_relat_1 @ X47 ) )
      | ~ ( v2_funct_1 @ X46 )
      | ( ( k2_relset_1 @ X47 @ X45 @ X46 )
       != X45 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('7',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','7','8','9'])).

thf('11',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('13',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('15',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
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

thf('18',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('25',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( X15 = X18 )
      | ~ ( r2_relset_1 @ X16 @ X17 @ X15 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','26'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('28',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('29',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
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

thf('31',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( r2_relset_1 @ X42 @ X42 @ ( k1_partfun1 @ X42 @ X43 @ X43 @ X42 @ X41 @ X44 ) @ ( k6_partfun1 @ X42 ) )
      | ( ( k2_relset_1 @ X43 @ X42 @ X44 )
        = X42 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X43 @ X42 )
      | ~ ( v1_funct_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('32',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('33',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( r2_relset_1 @ X42 @ X42 @ ( k1_partfun1 @ X42 @ X43 @ X43 @ X42 @ X41 @ X44 ) @ ( k6_relat_1 @ X42 ) )
      | ( ( k2_relset_1 @ X43 @ X42 @ X44 )
        = X42 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X43 @ X42 )
      | ~ ( v1_funct_1 @ X44 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['29','37'])).

thf('39',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('40',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( r2_relset_1 @ X16 @ X17 @ X15 @ X18 )
      | ( X15 != X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('41',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_relset_1 @ X16 @ X17 @ X18 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('44',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['38','42','43','44','45','46'])).

thf('48',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','47'])).

thf('49',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
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

thf('52',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( ( k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37 )
        = ( k5_relat_1 @ X34 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('59',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf(t48_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) ) )
           => ( ( v2_funct_1 @ B )
              & ( v2_funct_1 @ A ) ) ) ) ) )).

thf('60',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v2_funct_1 @ X3 )
      | ( ( k2_relat_1 @ X2 )
       != ( k1_relat_1 @ X3 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X2 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('61',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('62',plain,(
    ! [X1: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('63',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('64',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('65',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('69',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('73',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ( X22
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('74',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('75',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('76',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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

thf('77',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('78',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['79','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('83',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('84',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['74','81','84'])).

thf('86',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('89',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( sk_B != sk_B )
    | ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['61','62','65','66','71','85','86','89'])).

thf('91',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['49','91'])).

thf('93',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['56','57','58'])).

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

thf('94',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( X4
        = ( k2_funct_1 @ X5 ) )
      | ( ( k5_relat_1 @ X4 @ X5 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X5 ) ) )
      | ( ( k2_relat_1 @ X4 )
       != ( k1_relat_1 @ X5 ) )
      | ~ ( v2_funct_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('95',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['38','42','43','44','45','46'])).

thf('97',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['63','64'])).

thf('98',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['69','70'])).

thf('100',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['74','81','84'])).

thf('101',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['87','88'])).

thf('103',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B != sk_B )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['95','96','97','98','99','100','101','102'])).

thf('104',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['90'])).

thf('106',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( k5_relat_1 @ sk_D @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['92','106'])).

thf('108',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( X4
        = ( k2_funct_1 @ X5 ) )
      | ( ( k5_relat_1 @ X4 @ X5 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X5 ) ) )
      | ( ( k2_relat_1 @ X4 )
       != ( k1_relat_1 @ X5 ) )
      | ~ ( v2_funct_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('109',plain,
    ( ( ( k6_relat_1 @ sk_B )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_D )
     != ( k1_relat_1 @ sk_C ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['69','70'])).

thf('111',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['87','88'])).

thf('112',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['38','42','43','44','45','46'])).

thf('115',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ( X22
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('117',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('119',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('121',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['118','121'])).

thf('123',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['122','123'])).

thf('125',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('127',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['117','124','127'])).

thf('129',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['63','64'])).

thf('131',plain,
    ( ( ( k6_relat_1 @ sk_B )
     != ( k6_relat_1 @ sk_B ) )
    | ( sk_A != sk_A )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['109','110','111','112','113','114','128','129','130'])).

thf('132',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['132','133'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OYUBynerqQ
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:27:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.90/1.14  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.90/1.14  % Solved by: fo/fo7.sh
% 0.90/1.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.14  % done 430 iterations in 0.678s
% 0.90/1.14  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.90/1.14  % SZS output start Refutation
% 0.90/1.14  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.90/1.14  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.90/1.14  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.90/1.14  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.90/1.14  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.90/1.14  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.90/1.14  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.14  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.90/1.14  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.90/1.14  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.90/1.14  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.14  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.90/1.14  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.90/1.14  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.90/1.14  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.90/1.14  thf(sk_D_type, type, sk_D: $i).
% 0.90/1.14  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.90/1.14  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.90/1.14  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.90/1.14  thf(sk_C_type, type, sk_C: $i).
% 0.90/1.14  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.90/1.14  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.14  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.90/1.14  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.14  thf(t36_funct_2, conjecture,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.90/1.14         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.90/1.14       ( ![D:$i]:
% 0.90/1.14         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.90/1.14             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.90/1.14           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.90/1.14               ( r2_relset_1 @
% 0.90/1.14                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.90/1.14                 ( k6_partfun1 @ A ) ) & 
% 0.90/1.14               ( v2_funct_1 @ C ) ) =>
% 0.90/1.14             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.90/1.14               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.90/1.14  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.14    (~( ![A:$i,B:$i,C:$i]:
% 0.90/1.14        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.90/1.14            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.90/1.14          ( ![D:$i]:
% 0.90/1.14            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.90/1.14                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.90/1.14              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.90/1.14                  ( r2_relset_1 @
% 0.90/1.14                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.90/1.14                    ( k6_partfun1 @ A ) ) & 
% 0.90/1.14                  ( v2_funct_1 @ C ) ) =>
% 0.90/1.14                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.90/1.14                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.90/1.14    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.90/1.14  thf('0', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(t35_funct_2, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.90/1.14         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.90/1.14       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.90/1.14         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.90/1.14           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.90/1.14             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.90/1.14  thf('1', plain,
% 0.90/1.14      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.90/1.14         (((X45) = (k1_xboole_0))
% 0.90/1.14          | ~ (v1_funct_1 @ X46)
% 0.90/1.14          | ~ (v1_funct_2 @ X46 @ X47 @ X45)
% 0.90/1.14          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X45)))
% 0.90/1.14          | ((k5_relat_1 @ X46 @ (k2_funct_1 @ X46)) = (k6_partfun1 @ X47))
% 0.90/1.14          | ~ (v2_funct_1 @ X46)
% 0.90/1.14          | ((k2_relset_1 @ X47 @ X45 @ X46) != (X45)))),
% 0.90/1.14      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.90/1.14  thf(redefinition_k6_partfun1, axiom,
% 0.90/1.14    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.90/1.14  thf('2', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 0.90/1.14      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.90/1.14  thf('3', plain,
% 0.90/1.14      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.90/1.14         (((X45) = (k1_xboole_0))
% 0.90/1.14          | ~ (v1_funct_1 @ X46)
% 0.90/1.14          | ~ (v1_funct_2 @ X46 @ X47 @ X45)
% 0.90/1.14          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X45)))
% 0.90/1.14          | ((k5_relat_1 @ X46 @ (k2_funct_1 @ X46)) = (k6_relat_1 @ X47))
% 0.90/1.14          | ~ (v2_funct_1 @ X46)
% 0.90/1.14          | ((k2_relset_1 @ X47 @ X45 @ X46) != (X45)))),
% 0.90/1.14      inference('demod', [status(thm)], ['1', '2'])).
% 0.90/1.14  thf('4', plain,
% 0.90/1.14      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 0.90/1.14        | ~ (v2_funct_1 @ sk_D)
% 0.90/1.14        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 0.90/1.14        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.90/1.14        | ~ (v1_funct_1 @ sk_D)
% 0.90/1.14        | ((sk_A) = (k1_xboole_0)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['0', '3'])).
% 0.90/1.14  thf('5', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(redefinition_k2_relset_1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.14       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.90/1.14  thf('6', plain,
% 0.90/1.14      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.90/1.14         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.90/1.14          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.90/1.14      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.90/1.14  thf('7', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.90/1.14      inference('sup-', [status(thm)], ['5', '6'])).
% 0.90/1.14  thf('8', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('10', plain,
% 0.90/1.14      ((((k2_relat_1 @ sk_D) != (sk_A))
% 0.90/1.14        | ~ (v2_funct_1 @ sk_D)
% 0.90/1.14        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 0.90/1.14        | ((sk_A) = (k1_xboole_0)))),
% 0.90/1.14      inference('demod', [status(thm)], ['4', '7', '8', '9'])).
% 0.90/1.14  thf('11', plain, (((sk_A) != (k1_xboole_0))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('12', plain,
% 0.90/1.14      ((((k2_relat_1 @ sk_D) != (sk_A))
% 0.90/1.14        | ~ (v2_funct_1 @ sk_D)
% 0.90/1.14        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B)))),
% 0.90/1.14      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.90/1.14  thf('13', plain,
% 0.90/1.14      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.14        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.90/1.14        (k6_partfun1 @ sk_A))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('14', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 0.90/1.14      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.90/1.14  thf('15', plain,
% 0.90/1.14      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.14        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.90/1.14        (k6_relat_1 @ sk_A))),
% 0.90/1.14      inference('demod', [status(thm)], ['13', '14'])).
% 0.90/1.14  thf('16', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('17', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(dt_k1_partfun1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.90/1.14     ( ( ( v1_funct_1 @ E ) & 
% 0.90/1.14         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.90/1.14         ( v1_funct_1 @ F ) & 
% 0.90/1.14         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.90/1.14       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.90/1.14         ( m1_subset_1 @
% 0.90/1.14           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.90/1.14           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.90/1.14  thf('18', plain,
% 0.90/1.14      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.90/1.14         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.90/1.14          | ~ (v1_funct_1 @ X28)
% 0.90/1.14          | ~ (v1_funct_1 @ X31)
% 0.90/1.14          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.90/1.14          | (m1_subset_1 @ (k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31) @ 
% 0.90/1.14             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X33))))),
% 0.90/1.14      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.90/1.14  thf('19', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.14         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.90/1.14           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.90/1.14          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.90/1.14          | ~ (v1_funct_1 @ X1)
% 0.90/1.14          | ~ (v1_funct_1 @ sk_C))),
% 0.90/1.14      inference('sup-', [status(thm)], ['17', '18'])).
% 0.90/1.14  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('21', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.14         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.90/1.14           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.90/1.14          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.90/1.14          | ~ (v1_funct_1 @ X1))),
% 0.90/1.14      inference('demod', [status(thm)], ['19', '20'])).
% 0.90/1.14  thf('22', plain,
% 0.90/1.14      ((~ (v1_funct_1 @ sk_D)
% 0.90/1.14        | (m1_subset_1 @ 
% 0.90/1.14           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.90/1.14           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['16', '21'])).
% 0.90/1.14  thf('23', plain, ((v1_funct_1 @ sk_D)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('24', plain,
% 0.90/1.14      ((m1_subset_1 @ 
% 0.90/1.14        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.90/1.14        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.14      inference('demod', [status(thm)], ['22', '23'])).
% 0.90/1.14  thf(redefinition_r2_relset_1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.14     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.90/1.14         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.90/1.14       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.90/1.14  thf('25', plain,
% 0.90/1.14      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.90/1.14         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.90/1.14          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.90/1.14          | ((X15) = (X18))
% 0.90/1.14          | ~ (r2_relset_1 @ X16 @ X17 @ X15 @ X18))),
% 0.90/1.14      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.90/1.14  thf('26', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.14             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.90/1.14          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.90/1.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['24', '25'])).
% 0.90/1.14  thf('27', plain,
% 0.90/1.14      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 0.90/1.14           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.90/1.14        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.90/1.14            = (k6_relat_1 @ sk_A)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['15', '26'])).
% 0.90/1.14  thf(t29_relset_1, axiom,
% 0.90/1.14    (![A:$i]:
% 0.90/1.14     ( m1_subset_1 @
% 0.90/1.14       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.90/1.14  thf('28', plain,
% 0.90/1.14      (![X19 : $i]:
% 0.90/1.14         (m1_subset_1 @ (k6_relat_1 @ X19) @ 
% 0.90/1.14          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))),
% 0.90/1.14      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.90/1.14  thf('29', plain,
% 0.90/1.14      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.90/1.14         = (k6_relat_1 @ sk_A))),
% 0.90/1.14      inference('demod', [status(thm)], ['27', '28'])).
% 0.90/1.14  thf('30', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(t24_funct_2, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.90/1.14         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.90/1.14       ( ![D:$i]:
% 0.90/1.14         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.90/1.14             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.90/1.14           ( ( r2_relset_1 @
% 0.90/1.14               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.90/1.14               ( k6_partfun1 @ B ) ) =>
% 0.90/1.14             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.90/1.14  thf('31', plain,
% 0.90/1.14      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.90/1.14         (~ (v1_funct_1 @ X41)
% 0.90/1.14          | ~ (v1_funct_2 @ X41 @ X42 @ X43)
% 0.90/1.14          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 0.90/1.14          | ~ (r2_relset_1 @ X42 @ X42 @ 
% 0.90/1.14               (k1_partfun1 @ X42 @ X43 @ X43 @ X42 @ X41 @ X44) @ 
% 0.90/1.14               (k6_partfun1 @ X42))
% 0.90/1.14          | ((k2_relset_1 @ X43 @ X42 @ X44) = (X42))
% 0.90/1.14          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42)))
% 0.90/1.14          | ~ (v1_funct_2 @ X44 @ X43 @ X42)
% 0.90/1.14          | ~ (v1_funct_1 @ X44))),
% 0.90/1.14      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.90/1.14  thf('32', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 0.90/1.14      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.90/1.14  thf('33', plain,
% 0.90/1.14      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.90/1.14         (~ (v1_funct_1 @ X41)
% 0.90/1.14          | ~ (v1_funct_2 @ X41 @ X42 @ X43)
% 0.90/1.14          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 0.90/1.14          | ~ (r2_relset_1 @ X42 @ X42 @ 
% 0.90/1.14               (k1_partfun1 @ X42 @ X43 @ X43 @ X42 @ X41 @ X44) @ 
% 0.90/1.14               (k6_relat_1 @ X42))
% 0.90/1.14          | ((k2_relset_1 @ X43 @ X42 @ X44) = (X42))
% 0.90/1.14          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42)))
% 0.90/1.14          | ~ (v1_funct_2 @ X44 @ X43 @ X42)
% 0.90/1.14          | ~ (v1_funct_1 @ X44))),
% 0.90/1.14      inference('demod', [status(thm)], ['31', '32'])).
% 0.90/1.14  thf('34', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (~ (v1_funct_1 @ X0)
% 0.90/1.14          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.90/1.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.90/1.14          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.90/1.14          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.14               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.90/1.14               (k6_relat_1 @ sk_A))
% 0.90/1.14          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.90/1.14          | ~ (v1_funct_1 @ sk_C))),
% 0.90/1.14      inference('sup-', [status(thm)], ['30', '33'])).
% 0.90/1.14  thf('35', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('36', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('37', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (~ (v1_funct_1 @ X0)
% 0.90/1.14          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.90/1.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.90/1.14          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.90/1.14          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.14               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.90/1.14               (k6_relat_1 @ sk_A)))),
% 0.90/1.14      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.90/1.14  thf('38', plain,
% 0.90/1.14      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 0.90/1.14           (k6_relat_1 @ sk_A))
% 0.90/1.14        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.90/1.14        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.90/1.14        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.90/1.14        | ~ (v1_funct_1 @ sk_D))),
% 0.90/1.14      inference('sup-', [status(thm)], ['29', '37'])).
% 0.90/1.14  thf('39', plain,
% 0.90/1.14      (![X19 : $i]:
% 0.90/1.14         (m1_subset_1 @ (k6_relat_1 @ X19) @ 
% 0.90/1.14          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))),
% 0.90/1.14      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.90/1.14  thf('40', plain,
% 0.90/1.14      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.90/1.14         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.90/1.14          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.90/1.14          | (r2_relset_1 @ X16 @ X17 @ X15 @ X18)
% 0.90/1.14          | ((X15) != (X18)))),
% 0.90/1.14      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.90/1.14  thf('41', plain,
% 0.90/1.14      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.90/1.14         ((r2_relset_1 @ X16 @ X17 @ X18 @ X18)
% 0.90/1.14          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.90/1.14      inference('simplify', [status(thm)], ['40'])).
% 0.90/1.14  thf('42', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.90/1.14      inference('sup-', [status(thm)], ['39', '41'])).
% 0.90/1.14  thf('43', plain,
% 0.90/1.14      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.90/1.14      inference('sup-', [status(thm)], ['5', '6'])).
% 0.90/1.14  thf('44', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('45', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('46', plain, ((v1_funct_1 @ sk_D)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('47', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.90/1.14      inference('demod', [status(thm)], ['38', '42', '43', '44', '45', '46'])).
% 0.90/1.14  thf('48', plain,
% 0.90/1.14      ((((sk_A) != (sk_A))
% 0.90/1.14        | ~ (v2_funct_1 @ sk_D)
% 0.90/1.14        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B)))),
% 0.90/1.14      inference('demod', [status(thm)], ['12', '47'])).
% 0.90/1.14  thf('49', plain,
% 0.90/1.14      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 0.90/1.14        | ~ (v2_funct_1 @ sk_D))),
% 0.90/1.14      inference('simplify', [status(thm)], ['48'])).
% 0.90/1.14  thf('50', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('51', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(redefinition_k1_partfun1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.90/1.14     ( ( ( v1_funct_1 @ E ) & 
% 0.90/1.14         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.90/1.14         ( v1_funct_1 @ F ) & 
% 0.90/1.14         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.90/1.14       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.90/1.14  thf('52', plain,
% 0.90/1.14      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.90/1.14         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.90/1.14          | ~ (v1_funct_1 @ X34)
% 0.90/1.14          | ~ (v1_funct_1 @ X37)
% 0.90/1.14          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.90/1.14          | ((k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37)
% 0.90/1.14              = (k5_relat_1 @ X34 @ X37)))),
% 0.90/1.14      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.90/1.14  thf('53', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.14         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.90/1.14            = (k5_relat_1 @ sk_C @ X0))
% 0.90/1.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.90/1.14          | ~ (v1_funct_1 @ X0)
% 0.90/1.14          | ~ (v1_funct_1 @ sk_C))),
% 0.90/1.14      inference('sup-', [status(thm)], ['51', '52'])).
% 0.90/1.14  thf('54', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('55', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.14         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.90/1.14            = (k5_relat_1 @ sk_C @ X0))
% 0.90/1.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.90/1.14          | ~ (v1_funct_1 @ X0))),
% 0.90/1.14      inference('demod', [status(thm)], ['53', '54'])).
% 0.90/1.14  thf('56', plain,
% 0.90/1.14      ((~ (v1_funct_1 @ sk_D)
% 0.90/1.14        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.90/1.14            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['50', '55'])).
% 0.90/1.14  thf('57', plain, ((v1_funct_1 @ sk_D)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('58', plain,
% 0.90/1.14      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.90/1.14         = (k6_relat_1 @ sk_A))),
% 0.90/1.14      inference('demod', [status(thm)], ['27', '28'])).
% 0.90/1.14  thf('59', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.90/1.14  thf(t48_funct_1, axiom,
% 0.90/1.14    (![A:$i]:
% 0.90/1.14     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.90/1.14       ( ![B:$i]:
% 0.90/1.14         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.90/1.14           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.90/1.14               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.90/1.14             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.90/1.14  thf('60', plain,
% 0.90/1.14      (![X2 : $i, X3 : $i]:
% 0.90/1.14         (~ (v1_relat_1 @ X2)
% 0.90/1.14          | ~ (v1_funct_1 @ X2)
% 0.90/1.14          | (v2_funct_1 @ X3)
% 0.90/1.14          | ((k2_relat_1 @ X2) != (k1_relat_1 @ X3))
% 0.90/1.14          | ~ (v2_funct_1 @ (k5_relat_1 @ X2 @ X3))
% 0.90/1.14          | ~ (v1_funct_1 @ X3)
% 0.90/1.14          | ~ (v1_relat_1 @ X3))),
% 0.90/1.14      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.90/1.14  thf('61', plain,
% 0.90/1.14      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 0.90/1.14        | ~ (v1_relat_1 @ sk_D)
% 0.90/1.14        | ~ (v1_funct_1 @ sk_D)
% 0.90/1.14        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.90/1.14        | (v2_funct_1 @ sk_D)
% 0.90/1.14        | ~ (v1_funct_1 @ sk_C)
% 0.90/1.14        | ~ (v1_relat_1 @ sk_C))),
% 0.90/1.14      inference('sup-', [status(thm)], ['59', '60'])).
% 0.90/1.14  thf(fc4_funct_1, axiom,
% 0.90/1.14    (![A:$i]:
% 0.90/1.14     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.90/1.14       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.90/1.14  thf('62', plain, (![X1 : $i]: (v2_funct_1 @ (k6_relat_1 @ X1))),
% 0.90/1.14      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.90/1.14  thf('63', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(cc1_relset_1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.14       ( v1_relat_1 @ C ) ))).
% 0.90/1.14  thf('64', plain,
% 0.90/1.14      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.90/1.14         ((v1_relat_1 @ X6)
% 0.90/1.14          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.90/1.14      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.90/1.14  thf('65', plain, ((v1_relat_1 @ sk_D)),
% 0.90/1.14      inference('sup-', [status(thm)], ['63', '64'])).
% 0.90/1.14  thf('66', plain, ((v1_funct_1 @ sk_D)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('67', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('68', plain,
% 0.90/1.14      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.90/1.14         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.90/1.14          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.90/1.14      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.90/1.14  thf('69', plain,
% 0.90/1.14      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.90/1.14      inference('sup-', [status(thm)], ['67', '68'])).
% 0.90/1.14  thf('70', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('71', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.90/1.14      inference('sup+', [status(thm)], ['69', '70'])).
% 0.90/1.14  thf('72', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(d1_funct_2, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.14       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.90/1.14           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.90/1.14             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.90/1.14         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.90/1.14           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.90/1.14             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.90/1.14  thf(zf_stmt_1, axiom,
% 0.90/1.14    (![C:$i,B:$i,A:$i]:
% 0.90/1.14     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.90/1.14       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.90/1.14  thf('73', plain,
% 0.90/1.14      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.90/1.14         (~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.90/1.14          | ((X22) = (k1_relset_1 @ X22 @ X23 @ X24))
% 0.90/1.14          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.90/1.14  thf('74', plain,
% 0.90/1.14      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 0.90/1.14        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['72', '73'])).
% 0.90/1.14  thf(zf_stmt_2, axiom,
% 0.90/1.14    (![B:$i,A:$i]:
% 0.90/1.14     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.90/1.14       ( zip_tseitin_0 @ B @ A ) ))).
% 0.90/1.14  thf('75', plain,
% 0.90/1.14      (![X20 : $i, X21 : $i]:
% 0.90/1.14         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.90/1.14  thf('76', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.90/1.14  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.90/1.14  thf(zf_stmt_5, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.14       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.90/1.14         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.90/1.14           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.90/1.14             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.90/1.14  thf('77', plain,
% 0.90/1.14      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.90/1.14         (~ (zip_tseitin_0 @ X25 @ X26)
% 0.90/1.14          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 0.90/1.14          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.90/1.14  thf('78', plain,
% 0.90/1.14      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 0.90/1.14      inference('sup-', [status(thm)], ['76', '77'])).
% 0.90/1.14  thf('79', plain,
% 0.90/1.14      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 0.90/1.14      inference('sup-', [status(thm)], ['75', '78'])).
% 0.90/1.14  thf('80', plain, (((sk_A) != (k1_xboole_0))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('81', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 0.90/1.14      inference('simplify_reflect-', [status(thm)], ['79', '80'])).
% 0.90/1.14  thf('82', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(redefinition_k1_relset_1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.14       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.90/1.14  thf('83', plain,
% 0.90/1.14      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.90/1.14         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.90/1.14          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.90/1.14      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.90/1.14  thf('84', plain,
% 0.90/1.14      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.90/1.14      inference('sup-', [status(thm)], ['82', '83'])).
% 0.90/1.14  thf('85', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['74', '81', '84'])).
% 0.90/1.14  thf('86', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('87', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('88', plain,
% 0.90/1.14      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.90/1.14         ((v1_relat_1 @ X6)
% 0.90/1.14          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.90/1.14      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.90/1.14  thf('89', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.14      inference('sup-', [status(thm)], ['87', '88'])).
% 0.90/1.14  thf('90', plain, ((((sk_B) != (sk_B)) | (v2_funct_1 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)],
% 0.90/1.14                ['61', '62', '65', '66', '71', '85', '86', '89'])).
% 0.90/1.14  thf('91', plain, ((v2_funct_1 @ sk_D)),
% 0.90/1.14      inference('simplify', [status(thm)], ['90'])).
% 0.90/1.14  thf('92', plain,
% 0.90/1.14      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 0.90/1.14      inference('demod', [status(thm)], ['49', '91'])).
% 0.90/1.14  thf('93', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.90/1.14  thf(t64_funct_1, axiom,
% 0.90/1.14    (![A:$i]:
% 0.90/1.14     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.90/1.14       ( ![B:$i]:
% 0.90/1.14         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.90/1.14           ( ( ( v2_funct_1 @ A ) & 
% 0.90/1.14               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.90/1.14               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.90/1.14             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.90/1.14  thf('94', plain,
% 0.90/1.14      (![X4 : $i, X5 : $i]:
% 0.90/1.14         (~ (v1_relat_1 @ X4)
% 0.90/1.14          | ~ (v1_funct_1 @ X4)
% 0.90/1.14          | ((X4) = (k2_funct_1 @ X5))
% 0.90/1.14          | ((k5_relat_1 @ X4 @ X5) != (k6_relat_1 @ (k2_relat_1 @ X5)))
% 0.90/1.14          | ((k2_relat_1 @ X4) != (k1_relat_1 @ X5))
% 0.90/1.14          | ~ (v2_funct_1 @ X5)
% 0.90/1.14          | ~ (v1_funct_1 @ X5)
% 0.90/1.14          | ~ (v1_relat_1 @ X5))),
% 0.90/1.14      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.90/1.14  thf('95', plain,
% 0.90/1.14      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ (k2_relat_1 @ sk_D)))
% 0.90/1.14        | ~ (v1_relat_1 @ sk_D)
% 0.90/1.14        | ~ (v1_funct_1 @ sk_D)
% 0.90/1.14        | ~ (v2_funct_1 @ sk_D)
% 0.90/1.14        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.90/1.14        | ((sk_C) = (k2_funct_1 @ sk_D))
% 0.90/1.14        | ~ (v1_funct_1 @ sk_C)
% 0.90/1.14        | ~ (v1_relat_1 @ sk_C))),
% 0.90/1.14      inference('sup-', [status(thm)], ['93', '94'])).
% 0.90/1.14  thf('96', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.90/1.14      inference('demod', [status(thm)], ['38', '42', '43', '44', '45', '46'])).
% 0.90/1.14  thf('97', plain, ((v1_relat_1 @ sk_D)),
% 0.90/1.14      inference('sup-', [status(thm)], ['63', '64'])).
% 0.90/1.14  thf('98', plain, ((v1_funct_1 @ sk_D)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('99', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.90/1.14      inference('sup+', [status(thm)], ['69', '70'])).
% 0.90/1.14  thf('100', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['74', '81', '84'])).
% 0.90/1.14  thf('101', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('102', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.14      inference('sup-', [status(thm)], ['87', '88'])).
% 0.90/1.14  thf('103', plain,
% 0.90/1.14      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ sk_A))
% 0.90/1.14        | ~ (v2_funct_1 @ sk_D)
% 0.90/1.14        | ((sk_B) != (sk_B))
% 0.90/1.14        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 0.90/1.14      inference('demod', [status(thm)],
% 0.90/1.14                ['95', '96', '97', '98', '99', '100', '101', '102'])).
% 0.90/1.14  thf('104', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 0.90/1.14      inference('simplify', [status(thm)], ['103'])).
% 0.90/1.14  thf('105', plain, ((v2_funct_1 @ sk_D)),
% 0.90/1.14      inference('simplify', [status(thm)], ['90'])).
% 0.90/1.14  thf('106', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['104', '105'])).
% 0.90/1.14  thf('107', plain, (((k5_relat_1 @ sk_D @ sk_C) = (k6_relat_1 @ sk_B))),
% 0.90/1.14      inference('demod', [status(thm)], ['92', '106'])).
% 0.90/1.14  thf('108', plain,
% 0.90/1.14      (![X4 : $i, X5 : $i]:
% 0.90/1.14         (~ (v1_relat_1 @ X4)
% 0.90/1.14          | ~ (v1_funct_1 @ X4)
% 0.90/1.14          | ((X4) = (k2_funct_1 @ X5))
% 0.90/1.14          | ((k5_relat_1 @ X4 @ X5) != (k6_relat_1 @ (k2_relat_1 @ X5)))
% 0.90/1.14          | ((k2_relat_1 @ X4) != (k1_relat_1 @ X5))
% 0.90/1.14          | ~ (v2_funct_1 @ X5)
% 0.90/1.14          | ~ (v1_funct_1 @ X5)
% 0.90/1.14          | ~ (v1_relat_1 @ X5))),
% 0.90/1.14      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.90/1.14  thf('109', plain,
% 0.90/1.14      ((((k6_relat_1 @ sk_B) != (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.90/1.14        | ~ (v1_relat_1 @ sk_C)
% 0.90/1.14        | ~ (v1_funct_1 @ sk_C)
% 0.90/1.14        | ~ (v2_funct_1 @ sk_C)
% 0.90/1.14        | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ sk_C))
% 0.90/1.14        | ((sk_D) = (k2_funct_1 @ sk_C))
% 0.90/1.14        | ~ (v1_funct_1 @ sk_D)
% 0.90/1.14        | ~ (v1_relat_1 @ sk_D))),
% 0.90/1.14      inference('sup-', [status(thm)], ['107', '108'])).
% 0.90/1.14  thf('110', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.90/1.14      inference('sup+', [status(thm)], ['69', '70'])).
% 0.90/1.14  thf('111', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.14      inference('sup-', [status(thm)], ['87', '88'])).
% 0.90/1.14  thf('112', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('113', plain, ((v2_funct_1 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('114', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.90/1.14      inference('demod', [status(thm)], ['38', '42', '43', '44', '45', '46'])).
% 0.90/1.14  thf('115', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('116', plain,
% 0.90/1.14      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.90/1.14         (~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.90/1.14          | ((X22) = (k1_relset_1 @ X22 @ X23 @ X24))
% 0.90/1.14          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.90/1.14  thf('117', plain,
% 0.90/1.14      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.90/1.14        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['115', '116'])).
% 0.90/1.14  thf('118', plain,
% 0.90/1.14      (![X20 : $i, X21 : $i]:
% 0.90/1.14         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.90/1.14  thf('119', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('120', plain,
% 0.90/1.14      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.90/1.14         (~ (zip_tseitin_0 @ X25 @ X26)
% 0.90/1.14          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 0.90/1.14          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.90/1.14  thf('121', plain,
% 0.90/1.14      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.90/1.14      inference('sup-', [status(thm)], ['119', '120'])).
% 0.90/1.14  thf('122', plain,
% 0.90/1.14      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.90/1.14      inference('sup-', [status(thm)], ['118', '121'])).
% 0.90/1.14  thf('123', plain, (((sk_B) != (k1_xboole_0))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('124', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.90/1.14      inference('simplify_reflect-', [status(thm)], ['122', '123'])).
% 0.90/1.14  thf('125', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('126', plain,
% 0.90/1.14      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.90/1.14         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.90/1.14          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.90/1.14      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.90/1.14  thf('127', plain,
% 0.90/1.14      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.90/1.14      inference('sup-', [status(thm)], ['125', '126'])).
% 0.90/1.14  thf('128', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['117', '124', '127'])).
% 0.90/1.14  thf('129', plain, ((v1_funct_1 @ sk_D)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('130', plain, ((v1_relat_1 @ sk_D)),
% 0.90/1.14      inference('sup-', [status(thm)], ['63', '64'])).
% 0.90/1.14  thf('131', plain,
% 0.90/1.14      ((((k6_relat_1 @ sk_B) != (k6_relat_1 @ sk_B))
% 0.90/1.14        | ((sk_A) != (sk_A))
% 0.90/1.14        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 0.90/1.14      inference('demod', [status(thm)],
% 0.90/1.14                ['109', '110', '111', '112', '113', '114', '128', '129', '130'])).
% 0.90/1.14  thf('132', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 0.90/1.14      inference('simplify', [status(thm)], ['131'])).
% 0.90/1.14  thf('133', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('134', plain, ($false),
% 0.90/1.14      inference('simplify_reflect-', [status(thm)], ['132', '133'])).
% 0.90/1.14  
% 0.90/1.14  % SZS output end Refutation
% 0.90/1.14  
% 0.90/1.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

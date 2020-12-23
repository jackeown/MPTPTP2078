%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mHbxLSmetj

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:59 EST 2020

% Result     : Theorem 0.98s
% Output     : Refutation 0.98s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 690 expanded)
%              Number of leaves         :   45 ( 226 expanded)
%              Depth                    :   19
%              Number of atoms          : 1775 (16988 expanded)
%              Number of equality atoms :  129 (1151 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( X46 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ X48 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X46 ) ) )
      | ( ( k5_relat_1 @ X47 @ ( k2_funct_1 @ X47 ) )
        = ( k6_partfun1 @ X48 ) )
      | ~ ( v2_funct_1 @ X47 )
      | ( ( k2_relset_1 @ X48 @ X46 @ X47 )
       != X46 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( X46 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ X48 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X46 ) ) )
      | ( ( k5_relat_1 @ X47 @ ( k2_funct_1 @ X47 ) )
        = ( k6_relat_1 @ X48 ) )
      | ~ ( v2_funct_1 @ X47 )
      | ( ( k2_relset_1 @ X48 @ X46 @ X47 )
       != X46 ) ) ),
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
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X32 ) ) ) ) ),
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

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('28',plain,(
    ! [X34: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('29',plain,(
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('30',plain,(
    ! [X34: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,(
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

thf('33',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( r2_relset_1 @ X43 @ X43 @ ( k1_partfun1 @ X43 @ X44 @ X44 @ X43 @ X42 @ X45 ) @ ( k6_partfun1 @ X43 ) )
      | ( ( k2_relset_1 @ X44 @ X43 @ X45 )
        = X43 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X45 @ X44 @ X43 )
      | ~ ( v1_funct_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('34',plain,(
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('35',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( r2_relset_1 @ X43 @ X43 @ ( k1_partfun1 @ X43 @ X44 @ X44 @ X43 @ X42 @ X45 ) @ ( k6_relat_1 @ X43 ) )
      | ( ( k2_relset_1 @ X44 @ X43 @ X45 )
        = X43 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X45 @ X44 @ X43 )
      | ~ ( v1_funct_1 @ X45 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['31','39'])).

thf('41',plain,(
    ! [X34: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('42',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( r2_relset_1 @ X16 @ X17 @ X15 @ X18 )
      | ( X15 != X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('43',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_relset_1 @ X16 @ X17 @ X18 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('46',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['40','44','45','46','47','48'])).

thf('50',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','49'])).

thf('51',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
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

thf('54',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( ( k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38 )
        = ( k5_relat_1 @ X35 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('61',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['58','59','60'])).

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

thf('62',plain,(
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

thf('63',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('64',plain,(
    ! [X1: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('66',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('67',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('71',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
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

thf('75',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ( X21
        = ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('76',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('77',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('78',plain,(
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

thf('79',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('80',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('85',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('86',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['76','83','86'])).

thf('88',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('91',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( sk_B != sk_B )
    | ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['63','64','67','68','73','87','88','91'])).

thf('93',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['51','93'])).

thf('95',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['58','59','60'])).

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

thf('96',plain,(
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

thf('97',plain,
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
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['40','44','45','46','47','48'])).

thf('99',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['65','66'])).

thf('100',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['71','72'])).

thf('102',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['76','83','86'])).

thf('103',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['89','90'])).

thf('105',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B != sk_B )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['97','98','99','100','101','102','103','104'])).

thf('106',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['92'])).

thf('108',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k5_relat_1 @ sk_D @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['94','108'])).

thf('110',plain,(
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

thf('111',plain,
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
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['71','72'])).

thf('113',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['89','90'])).

thf('114',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['40','44','45','46','47','48'])).

thf('117',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ( X21
        = ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('119',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('121',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('123',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['120','123'])).

thf('125',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['124','125'])).

thf('127',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('129',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['119','126','129'])).

thf('131',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['65','66'])).

thf('133',plain,
    ( ( ( k6_relat_1 @ sk_B )
     != ( k6_relat_1 @ sk_B ) )
    | ( sk_A != sk_A )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['111','112','113','114','115','116','130','131','132'])).

thf('134',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['134','135'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mHbxLSmetj
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:24:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.98/1.17  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.98/1.17  % Solved by: fo/fo7.sh
% 0.98/1.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.98/1.17  % done 430 iterations in 0.710s
% 0.98/1.17  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.98/1.17  % SZS output start Refutation
% 0.98/1.17  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.98/1.17  thf(sk_D_type, type, sk_D: $i).
% 0.98/1.17  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.98/1.17  thf(sk_B_type, type, sk_B: $i).
% 0.98/1.17  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.98/1.17  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.98/1.17  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.98/1.17  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.98/1.17  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.98/1.17  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.98/1.17  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.98/1.17  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.98/1.17  thf(sk_A_type, type, sk_A: $i).
% 0.98/1.17  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.98/1.17  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.98/1.17  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.98/1.17  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.98/1.17  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.98/1.17  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.98/1.17  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.98/1.17  thf(sk_C_type, type, sk_C: $i).
% 0.98/1.17  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.98/1.17  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.98/1.17  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.98/1.17  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.98/1.17  thf(t36_funct_2, conjecture,
% 0.98/1.17    (![A:$i,B:$i,C:$i]:
% 0.98/1.17     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.98/1.17         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.98/1.17       ( ![D:$i]:
% 0.98/1.17         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.98/1.17             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.98/1.17           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.98/1.17               ( r2_relset_1 @
% 0.98/1.17                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.98/1.17                 ( k6_partfun1 @ A ) ) & 
% 0.98/1.17               ( v2_funct_1 @ C ) ) =>
% 0.98/1.17             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.98/1.17               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.98/1.17  thf(zf_stmt_0, negated_conjecture,
% 0.98/1.17    (~( ![A:$i,B:$i,C:$i]:
% 0.98/1.17        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.98/1.17            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.98/1.17          ( ![D:$i]:
% 0.98/1.17            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.98/1.17                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.98/1.17              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.98/1.17                  ( r2_relset_1 @
% 0.98/1.17                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.98/1.17                    ( k6_partfun1 @ A ) ) & 
% 0.98/1.17                  ( v2_funct_1 @ C ) ) =>
% 0.98/1.17                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.98/1.17                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.98/1.17    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.98/1.17  thf('0', plain,
% 0.98/1.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf(t35_funct_2, axiom,
% 0.98/1.17    (![A:$i,B:$i,C:$i]:
% 0.98/1.17     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.98/1.17         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.98/1.17       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.98/1.17         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.98/1.17           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.98/1.17             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.98/1.17  thf('1', plain,
% 0.98/1.17      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.98/1.17         (((X46) = (k1_xboole_0))
% 0.98/1.17          | ~ (v1_funct_1 @ X47)
% 0.98/1.17          | ~ (v1_funct_2 @ X47 @ X48 @ X46)
% 0.98/1.17          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X46)))
% 0.98/1.17          | ((k5_relat_1 @ X47 @ (k2_funct_1 @ X47)) = (k6_partfun1 @ X48))
% 0.98/1.17          | ~ (v2_funct_1 @ X47)
% 0.98/1.17          | ((k2_relset_1 @ X48 @ X46 @ X47) != (X46)))),
% 0.98/1.17      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.98/1.17  thf(redefinition_k6_partfun1, axiom,
% 0.98/1.17    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.98/1.17  thf('2', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 0.98/1.17      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.98/1.17  thf('3', plain,
% 0.98/1.17      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.98/1.17         (((X46) = (k1_xboole_0))
% 0.98/1.17          | ~ (v1_funct_1 @ X47)
% 0.98/1.17          | ~ (v1_funct_2 @ X47 @ X48 @ X46)
% 0.98/1.17          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X46)))
% 0.98/1.17          | ((k5_relat_1 @ X47 @ (k2_funct_1 @ X47)) = (k6_relat_1 @ X48))
% 0.98/1.17          | ~ (v2_funct_1 @ X47)
% 0.98/1.17          | ((k2_relset_1 @ X48 @ X46 @ X47) != (X46)))),
% 0.98/1.17      inference('demod', [status(thm)], ['1', '2'])).
% 0.98/1.17  thf('4', plain,
% 0.98/1.17      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 0.98/1.17        | ~ (v2_funct_1 @ sk_D)
% 0.98/1.17        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 0.98/1.17        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.98/1.17        | ~ (v1_funct_1 @ sk_D)
% 0.98/1.17        | ((sk_A) = (k1_xboole_0)))),
% 0.98/1.17      inference('sup-', [status(thm)], ['0', '3'])).
% 0.98/1.17  thf('5', plain,
% 0.98/1.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf(redefinition_k2_relset_1, axiom,
% 0.98/1.17    (![A:$i,B:$i,C:$i]:
% 0.98/1.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.98/1.17       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.98/1.17  thf('6', plain,
% 0.98/1.17      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.98/1.17         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.98/1.17          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.98/1.17      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.98/1.17  thf('7', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.98/1.17      inference('sup-', [status(thm)], ['5', '6'])).
% 0.98/1.17  thf('8', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf('10', plain,
% 0.98/1.17      ((((k2_relat_1 @ sk_D) != (sk_A))
% 0.98/1.17        | ~ (v2_funct_1 @ sk_D)
% 0.98/1.17        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 0.98/1.17        | ((sk_A) = (k1_xboole_0)))),
% 0.98/1.17      inference('demod', [status(thm)], ['4', '7', '8', '9'])).
% 0.98/1.17  thf('11', plain, (((sk_A) != (k1_xboole_0))),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf('12', plain,
% 0.98/1.17      ((((k2_relat_1 @ sk_D) != (sk_A))
% 0.98/1.17        | ~ (v2_funct_1 @ sk_D)
% 0.98/1.17        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B)))),
% 0.98/1.17      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.98/1.17  thf('13', plain,
% 0.98/1.17      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.98/1.17        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.98/1.17        (k6_partfun1 @ sk_A))),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf('14', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 0.98/1.17      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.98/1.17  thf('15', plain,
% 0.98/1.17      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.98/1.17        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.98/1.17        (k6_relat_1 @ sk_A))),
% 0.98/1.17      inference('demod', [status(thm)], ['13', '14'])).
% 0.98/1.17  thf('16', plain,
% 0.98/1.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf('17', plain,
% 0.98/1.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf(dt_k1_partfun1, axiom,
% 0.98/1.17    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.98/1.17     ( ( ( v1_funct_1 @ E ) & 
% 0.98/1.17         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.98/1.17         ( v1_funct_1 @ F ) & 
% 0.98/1.17         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.98/1.17       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.98/1.17         ( m1_subset_1 @
% 0.98/1.17           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.98/1.17           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.98/1.17  thf('18', plain,
% 0.98/1.17      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.98/1.17         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.98/1.17          | ~ (v1_funct_1 @ X27)
% 0.98/1.17          | ~ (v1_funct_1 @ X30)
% 0.98/1.17          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.98/1.17          | (m1_subset_1 @ (k1_partfun1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30) @ 
% 0.98/1.17             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X32))))),
% 0.98/1.17      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.98/1.17  thf('19', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.98/1.17         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.98/1.17           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.98/1.17          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.98/1.17          | ~ (v1_funct_1 @ X1)
% 0.98/1.17          | ~ (v1_funct_1 @ sk_C))),
% 0.98/1.17      inference('sup-', [status(thm)], ['17', '18'])).
% 0.98/1.17  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf('21', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.98/1.17         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.98/1.17           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.98/1.17          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.98/1.17          | ~ (v1_funct_1 @ X1))),
% 0.98/1.17      inference('demod', [status(thm)], ['19', '20'])).
% 0.98/1.17  thf('22', plain,
% 0.98/1.17      ((~ (v1_funct_1 @ sk_D)
% 0.98/1.17        | (m1_subset_1 @ 
% 0.98/1.17           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.98/1.17           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.98/1.17      inference('sup-', [status(thm)], ['16', '21'])).
% 0.98/1.17  thf('23', plain, ((v1_funct_1 @ sk_D)),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf('24', plain,
% 0.98/1.17      ((m1_subset_1 @ 
% 0.98/1.17        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.98/1.17        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.98/1.17      inference('demod', [status(thm)], ['22', '23'])).
% 0.98/1.17  thf(redefinition_r2_relset_1, axiom,
% 0.98/1.17    (![A:$i,B:$i,C:$i,D:$i]:
% 0.98/1.17     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.98/1.17         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.98/1.17       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.98/1.17  thf('25', plain,
% 0.98/1.17      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.98/1.17         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.98/1.17          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.98/1.17          | ((X15) = (X18))
% 0.98/1.17          | ~ (r2_relset_1 @ X16 @ X17 @ X15 @ X18))),
% 0.98/1.17      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.98/1.17  thf('26', plain,
% 0.98/1.17      (![X0 : $i]:
% 0.98/1.17         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.98/1.17             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.98/1.17          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.98/1.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.98/1.17      inference('sup-', [status(thm)], ['24', '25'])).
% 0.98/1.17  thf('27', plain,
% 0.98/1.17      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 0.98/1.17           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.98/1.17        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.98/1.17            = (k6_relat_1 @ sk_A)))),
% 0.98/1.17      inference('sup-', [status(thm)], ['15', '26'])).
% 0.98/1.17  thf(dt_k6_partfun1, axiom,
% 0.98/1.17    (![A:$i]:
% 0.98/1.17     ( ( m1_subset_1 @
% 0.98/1.17         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.98/1.17       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.98/1.17  thf('28', plain,
% 0.98/1.17      (![X34 : $i]:
% 0.98/1.17         (m1_subset_1 @ (k6_partfun1 @ X34) @ 
% 0.98/1.17          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))),
% 0.98/1.17      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.98/1.17  thf('29', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 0.98/1.17      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.98/1.17  thf('30', plain,
% 0.98/1.17      (![X34 : $i]:
% 0.98/1.17         (m1_subset_1 @ (k6_relat_1 @ X34) @ 
% 0.98/1.17          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))),
% 0.98/1.17      inference('demod', [status(thm)], ['28', '29'])).
% 0.98/1.17  thf('31', plain,
% 0.98/1.17      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.98/1.17         = (k6_relat_1 @ sk_A))),
% 0.98/1.17      inference('demod', [status(thm)], ['27', '30'])).
% 0.98/1.17  thf('32', plain,
% 0.98/1.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf(t24_funct_2, axiom,
% 0.98/1.17    (![A:$i,B:$i,C:$i]:
% 0.98/1.17     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.98/1.17         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.98/1.17       ( ![D:$i]:
% 0.98/1.17         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.98/1.17             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.98/1.17           ( ( r2_relset_1 @
% 0.98/1.17               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.98/1.17               ( k6_partfun1 @ B ) ) =>
% 0.98/1.17             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.98/1.17  thf('33', plain,
% 0.98/1.17      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.98/1.17         (~ (v1_funct_1 @ X42)
% 0.98/1.17          | ~ (v1_funct_2 @ X42 @ X43 @ X44)
% 0.98/1.17          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 0.98/1.17          | ~ (r2_relset_1 @ X43 @ X43 @ 
% 0.98/1.17               (k1_partfun1 @ X43 @ X44 @ X44 @ X43 @ X42 @ X45) @ 
% 0.98/1.17               (k6_partfun1 @ X43))
% 0.98/1.17          | ((k2_relset_1 @ X44 @ X43 @ X45) = (X43))
% 0.98/1.17          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43)))
% 0.98/1.17          | ~ (v1_funct_2 @ X45 @ X44 @ X43)
% 0.98/1.17          | ~ (v1_funct_1 @ X45))),
% 0.98/1.17      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.98/1.17  thf('34', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 0.98/1.17      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.98/1.17  thf('35', plain,
% 0.98/1.17      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.98/1.17         (~ (v1_funct_1 @ X42)
% 0.98/1.17          | ~ (v1_funct_2 @ X42 @ X43 @ X44)
% 0.98/1.17          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 0.98/1.17          | ~ (r2_relset_1 @ X43 @ X43 @ 
% 0.98/1.17               (k1_partfun1 @ X43 @ X44 @ X44 @ X43 @ X42 @ X45) @ 
% 0.98/1.17               (k6_relat_1 @ X43))
% 0.98/1.17          | ((k2_relset_1 @ X44 @ X43 @ X45) = (X43))
% 0.98/1.17          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43)))
% 0.98/1.17          | ~ (v1_funct_2 @ X45 @ X44 @ X43)
% 0.98/1.17          | ~ (v1_funct_1 @ X45))),
% 0.98/1.17      inference('demod', [status(thm)], ['33', '34'])).
% 0.98/1.17  thf('36', plain,
% 0.98/1.17      (![X0 : $i]:
% 0.98/1.17         (~ (v1_funct_1 @ X0)
% 0.98/1.17          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.98/1.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.98/1.17          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.98/1.17          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.98/1.17               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.98/1.17               (k6_relat_1 @ sk_A))
% 0.98/1.17          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.98/1.17          | ~ (v1_funct_1 @ sk_C))),
% 0.98/1.17      inference('sup-', [status(thm)], ['32', '35'])).
% 0.98/1.17  thf('37', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf('38', plain, ((v1_funct_1 @ sk_C)),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf('39', plain,
% 0.98/1.17      (![X0 : $i]:
% 0.98/1.17         (~ (v1_funct_1 @ X0)
% 0.98/1.17          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.98/1.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.98/1.17          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.98/1.17          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.98/1.17               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.98/1.17               (k6_relat_1 @ sk_A)))),
% 0.98/1.17      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.98/1.17  thf('40', plain,
% 0.98/1.17      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 0.98/1.17           (k6_relat_1 @ sk_A))
% 0.98/1.17        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.98/1.17        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.98/1.17        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.98/1.17        | ~ (v1_funct_1 @ sk_D))),
% 0.98/1.17      inference('sup-', [status(thm)], ['31', '39'])).
% 0.98/1.17  thf('41', plain,
% 0.98/1.17      (![X34 : $i]:
% 0.98/1.17         (m1_subset_1 @ (k6_relat_1 @ X34) @ 
% 0.98/1.17          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))),
% 0.98/1.17      inference('demod', [status(thm)], ['28', '29'])).
% 0.98/1.17  thf('42', plain,
% 0.98/1.17      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.98/1.17         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.98/1.17          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.98/1.17          | (r2_relset_1 @ X16 @ X17 @ X15 @ X18)
% 0.98/1.17          | ((X15) != (X18)))),
% 0.98/1.17      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.98/1.17  thf('43', plain,
% 0.98/1.17      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.98/1.17         ((r2_relset_1 @ X16 @ X17 @ X18 @ X18)
% 0.98/1.17          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.98/1.17      inference('simplify', [status(thm)], ['42'])).
% 0.98/1.17  thf('44', plain,
% 0.98/1.17      (![X0 : $i]:
% 0.98/1.17         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.98/1.17      inference('sup-', [status(thm)], ['41', '43'])).
% 0.98/1.17  thf('45', plain,
% 0.98/1.17      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.98/1.17      inference('sup-', [status(thm)], ['5', '6'])).
% 0.98/1.17  thf('46', plain,
% 0.98/1.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf('47', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf('48', plain, ((v1_funct_1 @ sk_D)),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf('49', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.98/1.17      inference('demod', [status(thm)], ['40', '44', '45', '46', '47', '48'])).
% 0.98/1.17  thf('50', plain,
% 0.98/1.17      ((((sk_A) != (sk_A))
% 0.98/1.17        | ~ (v2_funct_1 @ sk_D)
% 0.98/1.17        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B)))),
% 0.98/1.17      inference('demod', [status(thm)], ['12', '49'])).
% 0.98/1.17  thf('51', plain,
% 0.98/1.17      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 0.98/1.17        | ~ (v2_funct_1 @ sk_D))),
% 0.98/1.17      inference('simplify', [status(thm)], ['50'])).
% 0.98/1.17  thf('52', plain,
% 0.98/1.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf('53', plain,
% 0.98/1.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf(redefinition_k1_partfun1, axiom,
% 0.98/1.17    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.98/1.17     ( ( ( v1_funct_1 @ E ) & 
% 0.98/1.17         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.98/1.17         ( v1_funct_1 @ F ) & 
% 0.98/1.17         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.98/1.17       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.98/1.17  thf('54', plain,
% 0.98/1.17      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.98/1.17         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.98/1.17          | ~ (v1_funct_1 @ X35)
% 0.98/1.17          | ~ (v1_funct_1 @ X38)
% 0.98/1.17          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.98/1.17          | ((k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38)
% 0.98/1.17              = (k5_relat_1 @ X35 @ X38)))),
% 0.98/1.17      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.98/1.17  thf('55', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.98/1.17         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.98/1.17            = (k5_relat_1 @ sk_C @ X0))
% 0.98/1.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.98/1.17          | ~ (v1_funct_1 @ X0)
% 0.98/1.17          | ~ (v1_funct_1 @ sk_C))),
% 0.98/1.17      inference('sup-', [status(thm)], ['53', '54'])).
% 0.98/1.17  thf('56', plain, ((v1_funct_1 @ sk_C)),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf('57', plain,
% 0.98/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.98/1.17         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.98/1.17            = (k5_relat_1 @ sk_C @ X0))
% 0.98/1.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.98/1.17          | ~ (v1_funct_1 @ X0))),
% 0.98/1.17      inference('demod', [status(thm)], ['55', '56'])).
% 0.98/1.17  thf('58', plain,
% 0.98/1.17      ((~ (v1_funct_1 @ sk_D)
% 0.98/1.17        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.98/1.17            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.98/1.17      inference('sup-', [status(thm)], ['52', '57'])).
% 0.98/1.17  thf('59', plain, ((v1_funct_1 @ sk_D)),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf('60', plain,
% 0.98/1.17      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.98/1.17         = (k6_relat_1 @ sk_A))),
% 0.98/1.17      inference('demod', [status(thm)], ['27', '30'])).
% 0.98/1.17  thf('61', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.98/1.17      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.98/1.17  thf(t48_funct_1, axiom,
% 0.98/1.17    (![A:$i]:
% 0.98/1.17     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.98/1.17       ( ![B:$i]:
% 0.98/1.17         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.98/1.17           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.98/1.17               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.98/1.17             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.98/1.17  thf('62', plain,
% 0.98/1.17      (![X2 : $i, X3 : $i]:
% 0.98/1.17         (~ (v1_relat_1 @ X2)
% 0.98/1.17          | ~ (v1_funct_1 @ X2)
% 0.98/1.17          | (v2_funct_1 @ X3)
% 0.98/1.17          | ((k2_relat_1 @ X2) != (k1_relat_1 @ X3))
% 0.98/1.17          | ~ (v2_funct_1 @ (k5_relat_1 @ X2 @ X3))
% 0.98/1.17          | ~ (v1_funct_1 @ X3)
% 0.98/1.17          | ~ (v1_relat_1 @ X3))),
% 0.98/1.17      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.98/1.17  thf('63', plain,
% 0.98/1.17      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 0.98/1.17        | ~ (v1_relat_1 @ sk_D)
% 0.98/1.17        | ~ (v1_funct_1 @ sk_D)
% 0.98/1.17        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.98/1.17        | (v2_funct_1 @ sk_D)
% 0.98/1.17        | ~ (v1_funct_1 @ sk_C)
% 0.98/1.17        | ~ (v1_relat_1 @ sk_C))),
% 0.98/1.17      inference('sup-', [status(thm)], ['61', '62'])).
% 0.98/1.17  thf(fc4_funct_1, axiom,
% 0.98/1.17    (![A:$i]:
% 0.98/1.17     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.98/1.17       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.98/1.17  thf('64', plain, (![X1 : $i]: (v2_funct_1 @ (k6_relat_1 @ X1))),
% 0.98/1.17      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.98/1.17  thf('65', plain,
% 0.98/1.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf(cc1_relset_1, axiom,
% 0.98/1.17    (![A:$i,B:$i,C:$i]:
% 0.98/1.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.98/1.17       ( v1_relat_1 @ C ) ))).
% 0.98/1.17  thf('66', plain,
% 0.98/1.17      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.98/1.17         ((v1_relat_1 @ X6)
% 0.98/1.17          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.98/1.17      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.98/1.17  thf('67', plain, ((v1_relat_1 @ sk_D)),
% 0.98/1.17      inference('sup-', [status(thm)], ['65', '66'])).
% 0.98/1.17  thf('68', plain, ((v1_funct_1 @ sk_D)),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf('69', plain,
% 0.98/1.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf('70', plain,
% 0.98/1.17      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.98/1.17         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.98/1.17          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.98/1.17      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.98/1.17  thf('71', plain,
% 0.98/1.17      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.98/1.17      inference('sup-', [status(thm)], ['69', '70'])).
% 0.98/1.17  thf('72', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf('73', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.98/1.17      inference('sup+', [status(thm)], ['71', '72'])).
% 0.98/1.17  thf('74', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf(d1_funct_2, axiom,
% 0.98/1.17    (![A:$i,B:$i,C:$i]:
% 0.98/1.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.98/1.17       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.98/1.17           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.98/1.17             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.98/1.17         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.98/1.17           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.98/1.17             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.98/1.17  thf(zf_stmt_1, axiom,
% 0.98/1.17    (![C:$i,B:$i,A:$i]:
% 0.98/1.17     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.98/1.17       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.98/1.17  thf('75', plain,
% 0.98/1.17      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.98/1.17         (~ (v1_funct_2 @ X23 @ X21 @ X22)
% 0.98/1.17          | ((X21) = (k1_relset_1 @ X21 @ X22 @ X23))
% 0.98/1.17          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.98/1.17  thf('76', plain,
% 0.98/1.17      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 0.98/1.17        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 0.98/1.17      inference('sup-', [status(thm)], ['74', '75'])).
% 0.98/1.17  thf(zf_stmt_2, axiom,
% 0.98/1.17    (![B:$i,A:$i]:
% 0.98/1.17     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.98/1.17       ( zip_tseitin_0 @ B @ A ) ))).
% 0.98/1.17  thf('77', plain,
% 0.98/1.17      (![X19 : $i, X20 : $i]:
% 0.98/1.17         ((zip_tseitin_0 @ X19 @ X20) | ((X19) = (k1_xboole_0)))),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.98/1.17  thf('78', plain,
% 0.98/1.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.98/1.17  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.98/1.17  thf(zf_stmt_5, axiom,
% 0.98/1.17    (![A:$i,B:$i,C:$i]:
% 0.98/1.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.98/1.17       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.98/1.17         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.98/1.17           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.98/1.17             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.98/1.17  thf('79', plain,
% 0.98/1.17      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.98/1.17         (~ (zip_tseitin_0 @ X24 @ X25)
% 0.98/1.17          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 0.98/1.17          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.98/1.17  thf('80', plain,
% 0.98/1.17      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 0.98/1.17      inference('sup-', [status(thm)], ['78', '79'])).
% 0.98/1.17  thf('81', plain,
% 0.98/1.17      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 0.98/1.17      inference('sup-', [status(thm)], ['77', '80'])).
% 0.98/1.17  thf('82', plain, (((sk_A) != (k1_xboole_0))),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf('83', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 0.98/1.17      inference('simplify_reflect-', [status(thm)], ['81', '82'])).
% 0.98/1.17  thf('84', plain,
% 0.98/1.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf(redefinition_k1_relset_1, axiom,
% 0.98/1.17    (![A:$i,B:$i,C:$i]:
% 0.98/1.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.98/1.17       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.98/1.17  thf('85', plain,
% 0.98/1.17      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.98/1.17         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.98/1.17          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.98/1.17      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.98/1.17  thf('86', plain,
% 0.98/1.17      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.98/1.17      inference('sup-', [status(thm)], ['84', '85'])).
% 0.98/1.17  thf('87', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.98/1.17      inference('demod', [status(thm)], ['76', '83', '86'])).
% 0.98/1.17  thf('88', plain, ((v1_funct_1 @ sk_C)),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf('89', plain,
% 0.98/1.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf('90', plain,
% 0.98/1.17      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.98/1.17         ((v1_relat_1 @ X6)
% 0.98/1.17          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.98/1.17      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.98/1.17  thf('91', plain, ((v1_relat_1 @ sk_C)),
% 0.98/1.17      inference('sup-', [status(thm)], ['89', '90'])).
% 0.98/1.17  thf('92', plain, ((((sk_B) != (sk_B)) | (v2_funct_1 @ sk_D))),
% 0.98/1.17      inference('demod', [status(thm)],
% 0.98/1.17                ['63', '64', '67', '68', '73', '87', '88', '91'])).
% 0.98/1.17  thf('93', plain, ((v2_funct_1 @ sk_D)),
% 0.98/1.17      inference('simplify', [status(thm)], ['92'])).
% 0.98/1.17  thf('94', plain,
% 0.98/1.17      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 0.98/1.17      inference('demod', [status(thm)], ['51', '93'])).
% 0.98/1.17  thf('95', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.98/1.17      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.98/1.17  thf(t64_funct_1, axiom,
% 0.98/1.17    (![A:$i]:
% 0.98/1.17     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.98/1.17       ( ![B:$i]:
% 0.98/1.17         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.98/1.17           ( ( ( v2_funct_1 @ A ) & 
% 0.98/1.17               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.98/1.17               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.98/1.17             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.98/1.17  thf('96', plain,
% 0.98/1.17      (![X4 : $i, X5 : $i]:
% 0.98/1.17         (~ (v1_relat_1 @ X4)
% 0.98/1.17          | ~ (v1_funct_1 @ X4)
% 0.98/1.17          | ((X4) = (k2_funct_1 @ X5))
% 0.98/1.17          | ((k5_relat_1 @ X4 @ X5) != (k6_relat_1 @ (k2_relat_1 @ X5)))
% 0.98/1.17          | ((k2_relat_1 @ X4) != (k1_relat_1 @ X5))
% 0.98/1.17          | ~ (v2_funct_1 @ X5)
% 0.98/1.17          | ~ (v1_funct_1 @ X5)
% 0.98/1.17          | ~ (v1_relat_1 @ X5))),
% 0.98/1.17      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.98/1.17  thf('97', plain,
% 0.98/1.17      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ (k2_relat_1 @ sk_D)))
% 0.98/1.17        | ~ (v1_relat_1 @ sk_D)
% 0.98/1.17        | ~ (v1_funct_1 @ sk_D)
% 0.98/1.17        | ~ (v2_funct_1 @ sk_D)
% 0.98/1.17        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.98/1.17        | ((sk_C) = (k2_funct_1 @ sk_D))
% 0.98/1.17        | ~ (v1_funct_1 @ sk_C)
% 0.98/1.17        | ~ (v1_relat_1 @ sk_C))),
% 0.98/1.17      inference('sup-', [status(thm)], ['95', '96'])).
% 0.98/1.17  thf('98', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.98/1.17      inference('demod', [status(thm)], ['40', '44', '45', '46', '47', '48'])).
% 0.98/1.17  thf('99', plain, ((v1_relat_1 @ sk_D)),
% 0.98/1.17      inference('sup-', [status(thm)], ['65', '66'])).
% 0.98/1.17  thf('100', plain, ((v1_funct_1 @ sk_D)),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf('101', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.98/1.17      inference('sup+', [status(thm)], ['71', '72'])).
% 0.98/1.17  thf('102', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.98/1.17      inference('demod', [status(thm)], ['76', '83', '86'])).
% 0.98/1.17  thf('103', plain, ((v1_funct_1 @ sk_C)),
% 0.98/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.17  thf('104', plain, ((v1_relat_1 @ sk_C)),
% 0.98/1.17      inference('sup-', [status(thm)], ['89', '90'])).
% 0.98/1.17  thf('105', plain,
% 0.98/1.17      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ sk_A))
% 0.98/1.17        | ~ (v2_funct_1 @ sk_D)
% 0.98/1.17        | ((sk_B) != (sk_B))
% 0.98/1.17        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 0.98/1.17      inference('demod', [status(thm)],
% 0.98/1.17                ['97', '98', '99', '100', '101', '102', '103', '104'])).
% 0.98/1.17  thf('106', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 0.98/1.17      inference('simplify', [status(thm)], ['105'])).
% 0.98/1.17  thf('107', plain, ((v2_funct_1 @ sk_D)),
% 0.98/1.17      inference('simplify', [status(thm)], ['92'])).
% 0.98/1.17  thf('108', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.98/1.17      inference('demod', [status(thm)], ['106', '107'])).
% 0.98/1.17  thf('109', plain, (((k5_relat_1 @ sk_D @ sk_C) = (k6_relat_1 @ sk_B))),
% 0.98/1.17      inference('demod', [status(thm)], ['94', '108'])).
% 0.98/1.17  thf('110', plain,
% 0.98/1.17      (![X4 : $i, X5 : $i]:
% 0.98/1.17         (~ (v1_relat_1 @ X4)
% 0.98/1.17          | ~ (v1_funct_1 @ X4)
% 0.98/1.17          | ((X4) = (k2_funct_1 @ X5))
% 0.98/1.17          | ((k5_relat_1 @ X4 @ X5) != (k6_relat_1 @ (k2_relat_1 @ X5)))
% 0.98/1.17          | ((k2_relat_1 @ X4) != (k1_relat_1 @ X5))
% 0.98/1.17          | ~ (v2_funct_1 @ X5)
% 0.98/1.17          | ~ (v1_funct_1 @ X5)
% 0.98/1.17          | ~ (v1_relat_1 @ X5))),
% 0.98/1.17      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.98/1.17  thf('111', plain,
% 0.98/1.17      ((((k6_relat_1 @ sk_B) != (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.98/1.17        | ~ (v1_relat_1 @ sk_C)
% 0.98/1.17        | ~ (v1_funct_1 @ sk_C)
% 0.98/1.17        | ~ (v2_funct_1 @ sk_C)
% 0.98/1.17        | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ sk_C))
% 0.98/1.17        | ((sk_D) = (k2_funct_1 @ sk_C))
% 0.98/1.17        | ~ (v1_funct_1 @ sk_D)
% 0.98/1.17        | ~ (v1_relat_1 @ sk_D))),
% 0.98/1.17      inference('sup-', [status(thm)], ['109', '110'])).
% 0.98/1.18  thf('112', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.98/1.18      inference('sup+', [status(thm)], ['71', '72'])).
% 0.98/1.18  thf('113', plain, ((v1_relat_1 @ sk_C)),
% 0.98/1.18      inference('sup-', [status(thm)], ['89', '90'])).
% 0.98/1.18  thf('114', plain, ((v1_funct_1 @ sk_C)),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf('115', plain, ((v2_funct_1 @ sk_C)),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf('116', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.98/1.18      inference('demod', [status(thm)], ['40', '44', '45', '46', '47', '48'])).
% 0.98/1.18  thf('117', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf('118', plain,
% 0.98/1.18      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.98/1.18         (~ (v1_funct_2 @ X23 @ X21 @ X22)
% 0.98/1.18          | ((X21) = (k1_relset_1 @ X21 @ X22 @ X23))
% 0.98/1.18          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.98/1.18  thf('119', plain,
% 0.98/1.18      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.98/1.18        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.98/1.18      inference('sup-', [status(thm)], ['117', '118'])).
% 0.98/1.18  thf('120', plain,
% 0.98/1.18      (![X19 : $i, X20 : $i]:
% 0.98/1.18         ((zip_tseitin_0 @ X19 @ X20) | ((X19) = (k1_xboole_0)))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.98/1.18  thf('121', plain,
% 0.98/1.18      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf('122', plain,
% 0.98/1.18      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.98/1.18         (~ (zip_tseitin_0 @ X24 @ X25)
% 0.98/1.18          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 0.98/1.18          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.98/1.18  thf('123', plain,
% 0.98/1.18      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.98/1.18      inference('sup-', [status(thm)], ['121', '122'])).
% 0.98/1.18  thf('124', plain,
% 0.98/1.18      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.98/1.18      inference('sup-', [status(thm)], ['120', '123'])).
% 0.98/1.18  thf('125', plain, (((sk_B) != (k1_xboole_0))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf('126', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.98/1.18      inference('simplify_reflect-', [status(thm)], ['124', '125'])).
% 0.98/1.18  thf('127', plain,
% 0.98/1.18      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf('128', plain,
% 0.98/1.18      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.98/1.18         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.98/1.18          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.98/1.18      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.98/1.18  thf('129', plain,
% 0.98/1.18      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.98/1.18      inference('sup-', [status(thm)], ['127', '128'])).
% 0.98/1.18  thf('130', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.98/1.18      inference('demod', [status(thm)], ['119', '126', '129'])).
% 0.98/1.18  thf('131', plain, ((v1_funct_1 @ sk_D)),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf('132', plain, ((v1_relat_1 @ sk_D)),
% 0.98/1.18      inference('sup-', [status(thm)], ['65', '66'])).
% 0.98/1.18  thf('133', plain,
% 0.98/1.18      ((((k6_relat_1 @ sk_B) != (k6_relat_1 @ sk_B))
% 0.98/1.18        | ((sk_A) != (sk_A))
% 0.98/1.18        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 0.98/1.18      inference('demod', [status(thm)],
% 0.98/1.18                ['111', '112', '113', '114', '115', '116', '130', '131', '132'])).
% 0.98/1.18  thf('134', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 0.98/1.18      inference('simplify', [status(thm)], ['133'])).
% 0.98/1.18  thf('135', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.98/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.18  thf('136', plain, ($false),
% 0.98/1.18      inference('simplify_reflect-', [status(thm)], ['134', '135'])).
% 0.98/1.18  
% 0.98/1.18  % SZS output end Refutation
% 0.98/1.18  
% 0.98/1.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

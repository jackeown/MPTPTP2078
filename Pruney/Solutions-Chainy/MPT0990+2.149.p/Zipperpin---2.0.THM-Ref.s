%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fATXR59ehx

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:20 EST 2020

% Result     : Theorem 0.81s
% Output     : Refutation 0.81s
% Verified   : 
% Statistics : Number of formulae       :  188 ( 714 expanded)
%              Number of leaves         :   46 ( 234 expanded)
%              Depth                    :   19
%              Number of atoms          : 1799 (17100 expanded)
%              Number of equality atoms :  129 (1151 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( X47 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_funct_2 @ X48 @ X49 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X47 ) ) )
      | ( ( k5_relat_1 @ X48 @ ( k2_funct_1 @ X48 ) )
        = ( k6_partfun1 @ X49 ) )
      | ~ ( v2_funct_1 @ X48 )
      | ( ( k2_relset_1 @ X49 @ X47 @ X48 )
       != X47 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( X47 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_funct_2 @ X48 @ X49 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X47 ) ) )
      | ( ( k5_relat_1 @ X48 @ ( k2_funct_1 @ X48 ) )
        = ( k6_relat_1 @ X49 ) )
      | ~ ( v2_funct_1 @ X48 )
      | ( ( k2_relset_1 @ X49 @ X47 @ X48 )
       != X47 ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
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
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( X16 = X19 )
      | ~ ( r2_relset_1 @ X17 @ X18 @ X16 @ X19 ) ) ),
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
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('29',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('30',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
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
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( r2_relset_1 @ X44 @ X44 @ ( k1_partfun1 @ X44 @ X45 @ X45 @ X44 @ X43 @ X46 ) @ ( k6_partfun1 @ X44 ) )
      | ( ( k2_relset_1 @ X45 @ X44 @ X46 )
        = X44 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X46 @ X45 @ X44 )
      | ~ ( v1_funct_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('34',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('35',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( r2_relset_1 @ X44 @ X44 @ ( k1_partfun1 @ X44 @ X45 @ X45 @ X44 @ X43 @ X46 ) @ ( k6_relat_1 @ X44 ) )
      | ( ( k2_relset_1 @ X45 @ X44 @ X46 )
        = X44 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X46 @ X45 @ X44 )
      | ~ ( v1_funct_1 @ X46 ) ) ),
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
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('42',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( r2_relset_1 @ X17 @ X18 @ X16 @ X19 )
      | ( X16 != X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('43',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_relset_1 @ X17 @ X18 @ X19 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
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
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( ( k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39 )
        = ( k5_relat_1 @ X36 @ X39 ) ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( v2_funct_1 @ X7 )
      | ( ( k2_relat_1 @ X6 )
       != ( k1_relat_1 @ X7 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X6 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
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
    ! [X5: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('67',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('68',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('69',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('73',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
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

thf('77',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ( X22
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('78',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('79',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('80',plain,(
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

thf('81',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('82',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['83','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('87',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('88',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['78','85','88'])).

thf('90',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('93',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('95',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( sk_B != sk_B )
    | ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['63','64','69','70','75','89','90','95'])).

thf('97',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['51','97'])).

thf('99',plain,
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

thf('100',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( X8
        = ( k2_funct_1 @ X9 ) )
      | ( ( k5_relat_1 @ X8 @ X9 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X9 ) ) )
      | ( ( k2_relat_1 @ X8 )
       != ( k1_relat_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('101',plain,
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
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['40','44','45','46','47','48'])).

thf('103',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['67','68'])).

thf('104',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['73','74'])).

thf('106',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['78','85','88'])).

thf('107',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['93','94'])).

thf('109',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B != sk_B )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['101','102','103','104','105','106','107','108'])).

thf('110',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['96'])).

thf('112',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( k5_relat_1 @ sk_D @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['98','112'])).

thf('114',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( X8
        = ( k2_funct_1 @ X9 ) )
      | ( ( k5_relat_1 @ X8 @ X9 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X9 ) ) )
      | ( ( k2_relat_1 @ X8 )
       != ( k1_relat_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('115',plain,
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
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['73','74'])).

thf('117',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['93','94'])).

thf('118',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['40','44','45','46','47','48'])).

thf('121',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ( X22
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('123',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('125',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('127',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['124','127'])).

thf('129',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['128','129'])).

thf('131',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('133',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['123','130','133'])).

thf('135',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['67','68'])).

thf('137',plain,
    ( ( ( k6_relat_1 @ sk_B )
     != ( k6_relat_1 @ sk_B ) )
    | ( sk_A != sk_A )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['115','116','117','118','119','120','134','135','136'])).

thf('138',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['138','139'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fATXR59ehx
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:50:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.81/1.03  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.81/1.03  % Solved by: fo/fo7.sh
% 0.81/1.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.81/1.03  % done 430 iterations in 0.576s
% 0.81/1.03  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.81/1.03  % SZS output start Refutation
% 0.81/1.03  thf(sk_A_type, type, sk_A: $i).
% 0.81/1.03  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.81/1.03  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.81/1.03  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.81/1.03  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.81/1.03  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.81/1.03  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.81/1.03  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.81/1.03  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.81/1.03  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.81/1.03  thf(sk_C_type, type, sk_C: $i).
% 0.81/1.03  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.81/1.03  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.81/1.03  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.81/1.03  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.81/1.03  thf(sk_D_type, type, sk_D: $i).
% 0.81/1.03  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.81/1.03  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.81/1.03  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.81/1.03  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.81/1.03  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.81/1.03  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.81/1.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.81/1.03  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.81/1.03  thf(sk_B_type, type, sk_B: $i).
% 0.81/1.03  thf(t36_funct_2, conjecture,
% 0.81/1.03    (![A:$i,B:$i,C:$i]:
% 0.81/1.03     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.81/1.03         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.81/1.03       ( ![D:$i]:
% 0.81/1.03         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.81/1.03             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.81/1.03           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.81/1.03               ( r2_relset_1 @
% 0.81/1.03                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.81/1.03                 ( k6_partfun1 @ A ) ) & 
% 0.81/1.03               ( v2_funct_1 @ C ) ) =>
% 0.81/1.03             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.81/1.03               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.81/1.03  thf(zf_stmt_0, negated_conjecture,
% 0.81/1.03    (~( ![A:$i,B:$i,C:$i]:
% 0.81/1.03        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.81/1.03            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.81/1.03          ( ![D:$i]:
% 0.81/1.03            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.81/1.03                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.81/1.03              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.81/1.03                  ( r2_relset_1 @
% 0.81/1.03                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.81/1.03                    ( k6_partfun1 @ A ) ) & 
% 0.81/1.03                  ( v2_funct_1 @ C ) ) =>
% 0.81/1.03                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.81/1.03                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.81/1.03    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.81/1.03  thf('0', plain,
% 0.81/1.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf(t35_funct_2, axiom,
% 0.81/1.03    (![A:$i,B:$i,C:$i]:
% 0.81/1.03     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.81/1.03         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.81/1.03       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.81/1.03         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.81/1.03           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.81/1.03             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.81/1.03  thf('1', plain,
% 0.81/1.03      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.81/1.03         (((X47) = (k1_xboole_0))
% 0.81/1.03          | ~ (v1_funct_1 @ X48)
% 0.81/1.03          | ~ (v1_funct_2 @ X48 @ X49 @ X47)
% 0.81/1.03          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X47)))
% 0.81/1.03          | ((k5_relat_1 @ X48 @ (k2_funct_1 @ X48)) = (k6_partfun1 @ X49))
% 0.81/1.03          | ~ (v2_funct_1 @ X48)
% 0.81/1.03          | ((k2_relset_1 @ X49 @ X47 @ X48) != (X47)))),
% 0.81/1.03      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.81/1.03  thf(redefinition_k6_partfun1, axiom,
% 0.81/1.03    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.81/1.03  thf('2', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 0.81/1.03      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.81/1.03  thf('3', plain,
% 0.81/1.03      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.81/1.03         (((X47) = (k1_xboole_0))
% 0.81/1.03          | ~ (v1_funct_1 @ X48)
% 0.81/1.03          | ~ (v1_funct_2 @ X48 @ X49 @ X47)
% 0.81/1.03          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X47)))
% 0.81/1.03          | ((k5_relat_1 @ X48 @ (k2_funct_1 @ X48)) = (k6_relat_1 @ X49))
% 0.81/1.03          | ~ (v2_funct_1 @ X48)
% 0.81/1.03          | ((k2_relset_1 @ X49 @ X47 @ X48) != (X47)))),
% 0.81/1.03      inference('demod', [status(thm)], ['1', '2'])).
% 0.81/1.03  thf('4', plain,
% 0.81/1.03      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 0.81/1.03        | ~ (v2_funct_1 @ sk_D)
% 0.81/1.03        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 0.81/1.03        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.81/1.03        | ~ (v1_funct_1 @ sk_D)
% 0.81/1.03        | ((sk_A) = (k1_xboole_0)))),
% 0.81/1.03      inference('sup-', [status(thm)], ['0', '3'])).
% 0.81/1.03  thf('5', plain,
% 0.81/1.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf(redefinition_k2_relset_1, axiom,
% 0.81/1.03    (![A:$i,B:$i,C:$i]:
% 0.81/1.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.81/1.03       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.81/1.03  thf('6', plain,
% 0.81/1.03      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.81/1.03         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 0.81/1.03          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.81/1.03      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.81/1.03  thf('7', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.81/1.03      inference('sup-', [status(thm)], ['5', '6'])).
% 0.81/1.03  thf('8', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('10', plain,
% 0.81/1.03      ((((k2_relat_1 @ sk_D) != (sk_A))
% 0.81/1.03        | ~ (v2_funct_1 @ sk_D)
% 0.81/1.03        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 0.81/1.03        | ((sk_A) = (k1_xboole_0)))),
% 0.81/1.03      inference('demod', [status(thm)], ['4', '7', '8', '9'])).
% 0.81/1.03  thf('11', plain, (((sk_A) != (k1_xboole_0))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('12', plain,
% 0.81/1.03      ((((k2_relat_1 @ sk_D) != (sk_A))
% 0.81/1.03        | ~ (v2_funct_1 @ sk_D)
% 0.81/1.03        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B)))),
% 0.81/1.03      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.81/1.03  thf('13', plain,
% 0.81/1.03      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.81/1.03        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.81/1.03        (k6_partfun1 @ sk_A))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('14', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 0.81/1.03      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.81/1.03  thf('15', plain,
% 0.81/1.03      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.81/1.03        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.81/1.03        (k6_relat_1 @ sk_A))),
% 0.81/1.03      inference('demod', [status(thm)], ['13', '14'])).
% 0.81/1.03  thf('16', plain,
% 0.81/1.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('17', plain,
% 0.81/1.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf(dt_k1_partfun1, axiom,
% 0.81/1.03    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.81/1.03     ( ( ( v1_funct_1 @ E ) & 
% 0.81/1.03         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.81/1.03         ( v1_funct_1 @ F ) & 
% 0.81/1.03         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.81/1.03       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.81/1.03         ( m1_subset_1 @
% 0.81/1.03           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.81/1.03           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.81/1.03  thf('18', plain,
% 0.81/1.03      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.81/1.03         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.81/1.03          | ~ (v1_funct_1 @ X28)
% 0.81/1.03          | ~ (v1_funct_1 @ X31)
% 0.81/1.03          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.81/1.03          | (m1_subset_1 @ (k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31) @ 
% 0.81/1.03             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X33))))),
% 0.81/1.03      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.81/1.03  thf('19', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.03         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.81/1.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.81/1.03          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.81/1.03          | ~ (v1_funct_1 @ X1)
% 0.81/1.03          | ~ (v1_funct_1 @ sk_C))),
% 0.81/1.03      inference('sup-', [status(thm)], ['17', '18'])).
% 0.81/1.03  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('21', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.03         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.81/1.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.81/1.03          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.81/1.03          | ~ (v1_funct_1 @ X1))),
% 0.81/1.03      inference('demod', [status(thm)], ['19', '20'])).
% 0.81/1.03  thf('22', plain,
% 0.81/1.03      ((~ (v1_funct_1 @ sk_D)
% 0.81/1.03        | (m1_subset_1 @ 
% 0.81/1.03           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.81/1.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.81/1.03      inference('sup-', [status(thm)], ['16', '21'])).
% 0.81/1.03  thf('23', plain, ((v1_funct_1 @ sk_D)),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('24', plain,
% 0.81/1.03      ((m1_subset_1 @ 
% 0.81/1.03        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.81/1.03        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.81/1.03      inference('demod', [status(thm)], ['22', '23'])).
% 0.81/1.03  thf(redefinition_r2_relset_1, axiom,
% 0.81/1.03    (![A:$i,B:$i,C:$i,D:$i]:
% 0.81/1.03     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.81/1.03         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.81/1.03       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.81/1.03  thf('25', plain,
% 0.81/1.03      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.81/1.03         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.81/1.03          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.81/1.03          | ((X16) = (X19))
% 0.81/1.03          | ~ (r2_relset_1 @ X17 @ X18 @ X16 @ X19))),
% 0.81/1.03      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.81/1.03  thf('26', plain,
% 0.81/1.03      (![X0 : $i]:
% 0.81/1.03         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.81/1.03             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.81/1.03          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.81/1.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.81/1.03      inference('sup-', [status(thm)], ['24', '25'])).
% 0.81/1.03  thf('27', plain,
% 0.81/1.03      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 0.81/1.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.81/1.03        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.81/1.03            = (k6_relat_1 @ sk_A)))),
% 0.81/1.03      inference('sup-', [status(thm)], ['15', '26'])).
% 0.81/1.03  thf(dt_k6_partfun1, axiom,
% 0.81/1.03    (![A:$i]:
% 0.81/1.03     ( ( m1_subset_1 @
% 0.81/1.03         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.81/1.03       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.81/1.03  thf('28', plain,
% 0.81/1.03      (![X35 : $i]:
% 0.81/1.03         (m1_subset_1 @ (k6_partfun1 @ X35) @ 
% 0.81/1.03          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 0.81/1.03      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.81/1.03  thf('29', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 0.81/1.03      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.81/1.03  thf('30', plain,
% 0.81/1.03      (![X35 : $i]:
% 0.81/1.03         (m1_subset_1 @ (k6_relat_1 @ X35) @ 
% 0.81/1.03          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 0.81/1.03      inference('demod', [status(thm)], ['28', '29'])).
% 0.81/1.03  thf('31', plain,
% 0.81/1.03      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.81/1.03         = (k6_relat_1 @ sk_A))),
% 0.81/1.03      inference('demod', [status(thm)], ['27', '30'])).
% 0.81/1.03  thf('32', plain,
% 0.81/1.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf(t24_funct_2, axiom,
% 0.81/1.03    (![A:$i,B:$i,C:$i]:
% 0.81/1.03     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.81/1.03         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.81/1.03       ( ![D:$i]:
% 0.81/1.03         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.81/1.03             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.81/1.03           ( ( r2_relset_1 @
% 0.81/1.03               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.81/1.03               ( k6_partfun1 @ B ) ) =>
% 0.81/1.03             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.81/1.03  thf('33', plain,
% 0.81/1.03      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.81/1.03         (~ (v1_funct_1 @ X43)
% 0.81/1.03          | ~ (v1_funct_2 @ X43 @ X44 @ X45)
% 0.81/1.03          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 0.81/1.03          | ~ (r2_relset_1 @ X44 @ X44 @ 
% 0.81/1.03               (k1_partfun1 @ X44 @ X45 @ X45 @ X44 @ X43 @ X46) @ 
% 0.81/1.03               (k6_partfun1 @ X44))
% 0.81/1.03          | ((k2_relset_1 @ X45 @ X44 @ X46) = (X44))
% 0.81/1.03          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 0.81/1.03          | ~ (v1_funct_2 @ X46 @ X45 @ X44)
% 0.81/1.03          | ~ (v1_funct_1 @ X46))),
% 0.81/1.03      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.81/1.03  thf('34', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 0.81/1.03      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.81/1.03  thf('35', plain,
% 0.81/1.03      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.81/1.03         (~ (v1_funct_1 @ X43)
% 0.81/1.03          | ~ (v1_funct_2 @ X43 @ X44 @ X45)
% 0.81/1.03          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 0.81/1.03          | ~ (r2_relset_1 @ X44 @ X44 @ 
% 0.81/1.03               (k1_partfun1 @ X44 @ X45 @ X45 @ X44 @ X43 @ X46) @ 
% 0.81/1.03               (k6_relat_1 @ X44))
% 0.81/1.03          | ((k2_relset_1 @ X45 @ X44 @ X46) = (X44))
% 0.81/1.03          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 0.81/1.03          | ~ (v1_funct_2 @ X46 @ X45 @ X44)
% 0.81/1.03          | ~ (v1_funct_1 @ X46))),
% 0.81/1.03      inference('demod', [status(thm)], ['33', '34'])).
% 0.81/1.03  thf('36', plain,
% 0.81/1.03      (![X0 : $i]:
% 0.81/1.03         (~ (v1_funct_1 @ X0)
% 0.81/1.03          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.81/1.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.81/1.03          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.81/1.03          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.81/1.03               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.81/1.03               (k6_relat_1 @ sk_A))
% 0.81/1.03          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.81/1.03          | ~ (v1_funct_1 @ sk_C))),
% 0.81/1.03      inference('sup-', [status(thm)], ['32', '35'])).
% 0.81/1.03  thf('37', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('38', plain, ((v1_funct_1 @ sk_C)),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('39', plain,
% 0.81/1.03      (![X0 : $i]:
% 0.81/1.03         (~ (v1_funct_1 @ X0)
% 0.81/1.03          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.81/1.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.81/1.03          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.81/1.03          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.81/1.03               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.81/1.03               (k6_relat_1 @ sk_A)))),
% 0.81/1.03      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.81/1.03  thf('40', plain,
% 0.81/1.03      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 0.81/1.03           (k6_relat_1 @ sk_A))
% 0.81/1.03        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.81/1.03        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.81/1.03        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.81/1.03        | ~ (v1_funct_1 @ sk_D))),
% 0.81/1.03      inference('sup-', [status(thm)], ['31', '39'])).
% 0.81/1.03  thf('41', plain,
% 0.81/1.03      (![X35 : $i]:
% 0.81/1.03         (m1_subset_1 @ (k6_relat_1 @ X35) @ 
% 0.81/1.03          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 0.81/1.03      inference('demod', [status(thm)], ['28', '29'])).
% 0.81/1.03  thf('42', plain,
% 0.81/1.03      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.81/1.03         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.81/1.03          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.81/1.03          | (r2_relset_1 @ X17 @ X18 @ X16 @ X19)
% 0.81/1.03          | ((X16) != (X19)))),
% 0.81/1.03      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.81/1.03  thf('43', plain,
% 0.81/1.03      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.81/1.03         ((r2_relset_1 @ X17 @ X18 @ X19 @ X19)
% 0.81/1.03          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.81/1.03      inference('simplify', [status(thm)], ['42'])).
% 0.81/1.03  thf('44', plain,
% 0.81/1.03      (![X0 : $i]:
% 0.81/1.03         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.81/1.03      inference('sup-', [status(thm)], ['41', '43'])).
% 0.81/1.03  thf('45', plain,
% 0.81/1.03      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.81/1.03      inference('sup-', [status(thm)], ['5', '6'])).
% 0.81/1.03  thf('46', plain,
% 0.81/1.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('47', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('48', plain, ((v1_funct_1 @ sk_D)),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('49', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.81/1.03      inference('demod', [status(thm)], ['40', '44', '45', '46', '47', '48'])).
% 0.81/1.03  thf('50', plain,
% 0.81/1.03      ((((sk_A) != (sk_A))
% 0.81/1.03        | ~ (v2_funct_1 @ sk_D)
% 0.81/1.03        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B)))),
% 0.81/1.03      inference('demod', [status(thm)], ['12', '49'])).
% 0.81/1.03  thf('51', plain,
% 0.81/1.03      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 0.81/1.03        | ~ (v2_funct_1 @ sk_D))),
% 0.81/1.03      inference('simplify', [status(thm)], ['50'])).
% 0.81/1.03  thf('52', plain,
% 0.81/1.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('53', plain,
% 0.81/1.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf(redefinition_k1_partfun1, axiom,
% 0.81/1.03    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.81/1.03     ( ( ( v1_funct_1 @ E ) & 
% 0.81/1.03         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.81/1.03         ( v1_funct_1 @ F ) & 
% 0.81/1.03         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.81/1.03       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.81/1.03  thf('54', plain,
% 0.81/1.03      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.81/1.03         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.81/1.03          | ~ (v1_funct_1 @ X36)
% 0.81/1.03          | ~ (v1_funct_1 @ X39)
% 0.81/1.03          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.81/1.03          | ((k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39)
% 0.81/1.03              = (k5_relat_1 @ X36 @ X39)))),
% 0.81/1.03      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.81/1.03  thf('55', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.03         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.81/1.03            = (k5_relat_1 @ sk_C @ X0))
% 0.81/1.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.81/1.03          | ~ (v1_funct_1 @ X0)
% 0.81/1.03          | ~ (v1_funct_1 @ sk_C))),
% 0.81/1.03      inference('sup-', [status(thm)], ['53', '54'])).
% 0.81/1.03  thf('56', plain, ((v1_funct_1 @ sk_C)),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('57', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.03         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.81/1.03            = (k5_relat_1 @ sk_C @ X0))
% 0.81/1.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.81/1.03          | ~ (v1_funct_1 @ X0))),
% 0.81/1.03      inference('demod', [status(thm)], ['55', '56'])).
% 0.81/1.03  thf('58', plain,
% 0.81/1.03      ((~ (v1_funct_1 @ sk_D)
% 0.81/1.03        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.81/1.03            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.81/1.03      inference('sup-', [status(thm)], ['52', '57'])).
% 0.81/1.03  thf('59', plain, ((v1_funct_1 @ sk_D)),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('60', plain,
% 0.81/1.03      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.81/1.03         = (k6_relat_1 @ sk_A))),
% 0.81/1.03      inference('demod', [status(thm)], ['27', '30'])).
% 0.81/1.03  thf('61', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.81/1.03      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.81/1.03  thf(t48_funct_1, axiom,
% 0.81/1.03    (![A:$i]:
% 0.81/1.03     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.81/1.03       ( ![B:$i]:
% 0.81/1.03         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.81/1.03           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.81/1.03               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.81/1.03             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.81/1.03  thf('62', plain,
% 0.81/1.03      (![X6 : $i, X7 : $i]:
% 0.81/1.03         (~ (v1_relat_1 @ X6)
% 0.81/1.03          | ~ (v1_funct_1 @ X6)
% 0.81/1.03          | (v2_funct_1 @ X7)
% 0.81/1.03          | ((k2_relat_1 @ X6) != (k1_relat_1 @ X7))
% 0.81/1.03          | ~ (v2_funct_1 @ (k5_relat_1 @ X6 @ X7))
% 0.81/1.03          | ~ (v1_funct_1 @ X7)
% 0.81/1.03          | ~ (v1_relat_1 @ X7))),
% 0.81/1.03      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.81/1.03  thf('63', plain,
% 0.81/1.03      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 0.81/1.03        | ~ (v1_relat_1 @ sk_D)
% 0.81/1.03        | ~ (v1_funct_1 @ sk_D)
% 0.81/1.03        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.81/1.03        | (v2_funct_1 @ sk_D)
% 0.81/1.03        | ~ (v1_funct_1 @ sk_C)
% 0.81/1.03        | ~ (v1_relat_1 @ sk_C))),
% 0.81/1.03      inference('sup-', [status(thm)], ['61', '62'])).
% 0.81/1.03  thf(fc4_funct_1, axiom,
% 0.81/1.03    (![A:$i]:
% 0.81/1.03     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.81/1.03       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.81/1.03  thf('64', plain, (![X5 : $i]: (v2_funct_1 @ (k6_relat_1 @ X5))),
% 0.81/1.03      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.81/1.03  thf('65', plain,
% 0.81/1.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf(cc2_relat_1, axiom,
% 0.81/1.03    (![A:$i]:
% 0.81/1.03     ( ( v1_relat_1 @ A ) =>
% 0.81/1.03       ( ![B:$i]:
% 0.81/1.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.81/1.03  thf('66', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i]:
% 0.81/1.03         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.81/1.03          | (v1_relat_1 @ X0)
% 0.81/1.03          | ~ (v1_relat_1 @ X1))),
% 0.81/1.03      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.81/1.03  thf('67', plain,
% 0.81/1.03      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.81/1.03      inference('sup-', [status(thm)], ['65', '66'])).
% 0.81/1.03  thf(fc6_relat_1, axiom,
% 0.81/1.03    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.81/1.03  thf('68', plain,
% 0.81/1.03      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.81/1.03      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.81/1.03  thf('69', plain, ((v1_relat_1 @ sk_D)),
% 0.81/1.03      inference('demod', [status(thm)], ['67', '68'])).
% 0.81/1.03  thf('70', plain, ((v1_funct_1 @ sk_D)),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('71', plain,
% 0.81/1.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('72', plain,
% 0.81/1.03      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.81/1.03         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 0.81/1.03          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.81/1.03      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.81/1.03  thf('73', plain,
% 0.81/1.03      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.81/1.03      inference('sup-', [status(thm)], ['71', '72'])).
% 0.81/1.03  thf('74', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('75', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.81/1.03      inference('sup+', [status(thm)], ['73', '74'])).
% 0.81/1.03  thf('76', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf(d1_funct_2, axiom,
% 0.81/1.03    (![A:$i,B:$i,C:$i]:
% 0.81/1.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.81/1.03       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.81/1.03           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.81/1.03             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.81/1.03         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.81/1.03           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.81/1.03             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.81/1.03  thf(zf_stmt_1, axiom,
% 0.81/1.03    (![C:$i,B:$i,A:$i]:
% 0.81/1.03     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.81/1.03       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.81/1.03  thf('77', plain,
% 0.81/1.03      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.81/1.03         (~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.81/1.03          | ((X22) = (k1_relset_1 @ X22 @ X23 @ X24))
% 0.81/1.03          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.81/1.03  thf('78', plain,
% 0.81/1.03      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 0.81/1.03        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 0.81/1.03      inference('sup-', [status(thm)], ['76', '77'])).
% 0.81/1.03  thf(zf_stmt_2, axiom,
% 0.81/1.03    (![B:$i,A:$i]:
% 0.81/1.03     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.81/1.03       ( zip_tseitin_0 @ B @ A ) ))).
% 0.81/1.03  thf('79', plain,
% 0.81/1.03      (![X20 : $i, X21 : $i]:
% 0.81/1.03         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.81/1.03  thf('80', plain,
% 0.81/1.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.81/1.03  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.81/1.03  thf(zf_stmt_5, axiom,
% 0.81/1.03    (![A:$i,B:$i,C:$i]:
% 0.81/1.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.81/1.03       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.81/1.03         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.81/1.03           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.81/1.03             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.81/1.03  thf('81', plain,
% 0.81/1.03      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.81/1.03         (~ (zip_tseitin_0 @ X25 @ X26)
% 0.81/1.03          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 0.81/1.03          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.81/1.03  thf('82', plain,
% 0.81/1.03      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 0.81/1.03      inference('sup-', [status(thm)], ['80', '81'])).
% 0.81/1.03  thf('83', plain,
% 0.81/1.03      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 0.81/1.03      inference('sup-', [status(thm)], ['79', '82'])).
% 0.81/1.03  thf('84', plain, (((sk_A) != (k1_xboole_0))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('85', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 0.81/1.03      inference('simplify_reflect-', [status(thm)], ['83', '84'])).
% 0.81/1.03  thf('86', plain,
% 0.81/1.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf(redefinition_k1_relset_1, axiom,
% 0.81/1.03    (![A:$i,B:$i,C:$i]:
% 0.81/1.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.81/1.03       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.81/1.03  thf('87', plain,
% 0.81/1.03      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.81/1.03         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 0.81/1.03          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.81/1.03      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.81/1.03  thf('88', plain,
% 0.81/1.03      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.81/1.03      inference('sup-', [status(thm)], ['86', '87'])).
% 0.81/1.03  thf('89', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.81/1.03      inference('demod', [status(thm)], ['78', '85', '88'])).
% 0.81/1.03  thf('90', plain, ((v1_funct_1 @ sk_C)),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('91', plain,
% 0.81/1.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('92', plain,
% 0.81/1.03      (![X0 : $i, X1 : $i]:
% 0.81/1.03         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.81/1.03          | (v1_relat_1 @ X0)
% 0.81/1.03          | ~ (v1_relat_1 @ X1))),
% 0.81/1.03      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.81/1.03  thf('93', plain,
% 0.81/1.03      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.81/1.03      inference('sup-', [status(thm)], ['91', '92'])).
% 0.81/1.03  thf('94', plain,
% 0.81/1.03      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.81/1.03      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.81/1.03  thf('95', plain, ((v1_relat_1 @ sk_C)),
% 0.81/1.03      inference('demod', [status(thm)], ['93', '94'])).
% 0.81/1.03  thf('96', plain, ((((sk_B) != (sk_B)) | (v2_funct_1 @ sk_D))),
% 0.81/1.03      inference('demod', [status(thm)],
% 0.81/1.03                ['63', '64', '69', '70', '75', '89', '90', '95'])).
% 0.81/1.03  thf('97', plain, ((v2_funct_1 @ sk_D)),
% 0.81/1.03      inference('simplify', [status(thm)], ['96'])).
% 0.81/1.03  thf('98', plain,
% 0.81/1.03      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 0.81/1.03      inference('demod', [status(thm)], ['51', '97'])).
% 0.81/1.03  thf('99', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.81/1.03      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.81/1.03  thf(t64_funct_1, axiom,
% 0.81/1.03    (![A:$i]:
% 0.81/1.03     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.81/1.03       ( ![B:$i]:
% 0.81/1.03         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.81/1.03           ( ( ( v2_funct_1 @ A ) & 
% 0.81/1.03               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.81/1.03               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.81/1.03             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.81/1.03  thf('100', plain,
% 0.81/1.03      (![X8 : $i, X9 : $i]:
% 0.81/1.03         (~ (v1_relat_1 @ X8)
% 0.81/1.03          | ~ (v1_funct_1 @ X8)
% 0.81/1.03          | ((X8) = (k2_funct_1 @ X9))
% 0.81/1.03          | ((k5_relat_1 @ X8 @ X9) != (k6_relat_1 @ (k2_relat_1 @ X9)))
% 0.81/1.03          | ((k2_relat_1 @ X8) != (k1_relat_1 @ X9))
% 0.81/1.03          | ~ (v2_funct_1 @ X9)
% 0.81/1.03          | ~ (v1_funct_1 @ X9)
% 0.81/1.03          | ~ (v1_relat_1 @ X9))),
% 0.81/1.03      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.81/1.03  thf('101', plain,
% 0.81/1.03      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ (k2_relat_1 @ sk_D)))
% 0.81/1.03        | ~ (v1_relat_1 @ sk_D)
% 0.81/1.03        | ~ (v1_funct_1 @ sk_D)
% 0.81/1.03        | ~ (v2_funct_1 @ sk_D)
% 0.81/1.03        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.81/1.03        | ((sk_C) = (k2_funct_1 @ sk_D))
% 0.81/1.03        | ~ (v1_funct_1 @ sk_C)
% 0.81/1.03        | ~ (v1_relat_1 @ sk_C))),
% 0.81/1.03      inference('sup-', [status(thm)], ['99', '100'])).
% 0.81/1.03  thf('102', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.81/1.03      inference('demod', [status(thm)], ['40', '44', '45', '46', '47', '48'])).
% 0.81/1.03  thf('103', plain, ((v1_relat_1 @ sk_D)),
% 0.81/1.03      inference('demod', [status(thm)], ['67', '68'])).
% 0.81/1.03  thf('104', plain, ((v1_funct_1 @ sk_D)),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('105', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.81/1.03      inference('sup+', [status(thm)], ['73', '74'])).
% 0.81/1.03  thf('106', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.81/1.03      inference('demod', [status(thm)], ['78', '85', '88'])).
% 0.81/1.03  thf('107', plain, ((v1_funct_1 @ sk_C)),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('108', plain, ((v1_relat_1 @ sk_C)),
% 0.81/1.03      inference('demod', [status(thm)], ['93', '94'])).
% 0.81/1.03  thf('109', plain,
% 0.81/1.03      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ sk_A))
% 0.81/1.03        | ~ (v2_funct_1 @ sk_D)
% 0.81/1.03        | ((sk_B) != (sk_B))
% 0.81/1.03        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 0.81/1.03      inference('demod', [status(thm)],
% 0.81/1.03                ['101', '102', '103', '104', '105', '106', '107', '108'])).
% 0.81/1.03  thf('110', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 0.81/1.03      inference('simplify', [status(thm)], ['109'])).
% 0.81/1.03  thf('111', plain, ((v2_funct_1 @ sk_D)),
% 0.81/1.03      inference('simplify', [status(thm)], ['96'])).
% 0.81/1.03  thf('112', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.81/1.03      inference('demod', [status(thm)], ['110', '111'])).
% 0.81/1.03  thf('113', plain, (((k5_relat_1 @ sk_D @ sk_C) = (k6_relat_1 @ sk_B))),
% 0.81/1.03      inference('demod', [status(thm)], ['98', '112'])).
% 0.81/1.03  thf('114', plain,
% 0.81/1.03      (![X8 : $i, X9 : $i]:
% 0.81/1.03         (~ (v1_relat_1 @ X8)
% 0.81/1.03          | ~ (v1_funct_1 @ X8)
% 0.81/1.03          | ((X8) = (k2_funct_1 @ X9))
% 0.81/1.03          | ((k5_relat_1 @ X8 @ X9) != (k6_relat_1 @ (k2_relat_1 @ X9)))
% 0.81/1.03          | ((k2_relat_1 @ X8) != (k1_relat_1 @ X9))
% 0.81/1.03          | ~ (v2_funct_1 @ X9)
% 0.81/1.03          | ~ (v1_funct_1 @ X9)
% 0.81/1.03          | ~ (v1_relat_1 @ X9))),
% 0.81/1.03      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.81/1.03  thf('115', plain,
% 0.81/1.03      ((((k6_relat_1 @ sk_B) != (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.81/1.03        | ~ (v1_relat_1 @ sk_C)
% 0.81/1.03        | ~ (v1_funct_1 @ sk_C)
% 0.81/1.03        | ~ (v2_funct_1 @ sk_C)
% 0.81/1.03        | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ sk_C))
% 0.81/1.03        | ((sk_D) = (k2_funct_1 @ sk_C))
% 0.81/1.03        | ~ (v1_funct_1 @ sk_D)
% 0.81/1.03        | ~ (v1_relat_1 @ sk_D))),
% 0.81/1.03      inference('sup-', [status(thm)], ['113', '114'])).
% 0.81/1.03  thf('116', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.81/1.03      inference('sup+', [status(thm)], ['73', '74'])).
% 0.81/1.03  thf('117', plain, ((v1_relat_1 @ sk_C)),
% 0.81/1.03      inference('demod', [status(thm)], ['93', '94'])).
% 0.81/1.03  thf('118', plain, ((v1_funct_1 @ sk_C)),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('119', plain, ((v2_funct_1 @ sk_C)),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('120', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.81/1.03      inference('demod', [status(thm)], ['40', '44', '45', '46', '47', '48'])).
% 0.81/1.03  thf('121', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('122', plain,
% 0.81/1.03      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.81/1.03         (~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.81/1.03          | ((X22) = (k1_relset_1 @ X22 @ X23 @ X24))
% 0.81/1.03          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.81/1.03  thf('123', plain,
% 0.81/1.03      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.81/1.03        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.81/1.03      inference('sup-', [status(thm)], ['121', '122'])).
% 0.81/1.03  thf('124', plain,
% 0.81/1.03      (![X20 : $i, X21 : $i]:
% 0.81/1.03         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.81/1.03  thf('125', plain,
% 0.81/1.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('126', plain,
% 0.81/1.03      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.81/1.03         (~ (zip_tseitin_0 @ X25 @ X26)
% 0.81/1.03          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 0.81/1.03          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.81/1.03  thf('127', plain,
% 0.81/1.03      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.81/1.03      inference('sup-', [status(thm)], ['125', '126'])).
% 0.81/1.03  thf('128', plain,
% 0.81/1.03      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.81/1.03      inference('sup-', [status(thm)], ['124', '127'])).
% 0.81/1.03  thf('129', plain, (((sk_B) != (k1_xboole_0))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('130', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.81/1.03      inference('simplify_reflect-', [status(thm)], ['128', '129'])).
% 0.81/1.03  thf('131', plain,
% 0.81/1.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('132', plain,
% 0.81/1.03      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.81/1.03         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 0.81/1.03          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.81/1.03      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.81/1.03  thf('133', plain,
% 0.81/1.03      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.81/1.03      inference('sup-', [status(thm)], ['131', '132'])).
% 0.81/1.03  thf('134', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.81/1.03      inference('demod', [status(thm)], ['123', '130', '133'])).
% 0.81/1.03  thf('135', plain, ((v1_funct_1 @ sk_D)),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('136', plain, ((v1_relat_1 @ sk_D)),
% 0.81/1.03      inference('demod', [status(thm)], ['67', '68'])).
% 0.81/1.03  thf('137', plain,
% 0.81/1.03      ((((k6_relat_1 @ sk_B) != (k6_relat_1 @ sk_B))
% 0.81/1.03        | ((sk_A) != (sk_A))
% 0.81/1.03        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 0.81/1.03      inference('demod', [status(thm)],
% 0.81/1.03                ['115', '116', '117', '118', '119', '120', '134', '135', '136'])).
% 0.81/1.03  thf('138', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 0.81/1.03      inference('simplify', [status(thm)], ['137'])).
% 0.81/1.03  thf('139', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.81/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.03  thf('140', plain, ($false),
% 0.81/1.03      inference('simplify_reflect-', [status(thm)], ['138', '139'])).
% 0.81/1.03  
% 0.81/1.03  % SZS output end Refutation
% 0.81/1.03  
% 0.81/1.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

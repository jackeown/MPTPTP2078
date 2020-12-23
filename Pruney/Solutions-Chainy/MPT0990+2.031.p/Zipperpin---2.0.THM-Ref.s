%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EXpLfdcyZD

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:59 EST 2020

% Result     : Theorem 2.32s
% Output     : Refutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 246 expanded)
%              Number of leaves         :   45 (  92 expanded)
%              Depth                    :   13
%              Number of atoms          : 1379 (5438 expanded)
%              Number of equality atoms :   97 ( 391 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

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
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( ( k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40 )
        = ( k5_relat_1 @ X37 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('22',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('23',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( X17 = X20 )
      | ~ ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','24'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('26',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('27',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','28'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('30',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('32',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( X44 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X44 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X45 ) @ X45 )
        = ( k6_partfun1 @ X44 ) )
      | ~ ( v2_funct_1 @ X45 )
      | ( ( k2_relset_1 @ X46 @ X44 @ X45 )
       != X44 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('33',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('34',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( X44 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X44 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X45 ) @ X45 )
        = ( k6_relat_1 @ X44 ) )
      | ~ ( v2_funct_1 @ X45 )
      | ( ( k2_relset_1 @ X46 @ X44 @ X45 )
       != X44 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','36','37','38','39'])).

thf('41',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['41','42'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('47',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('48',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['30','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['46','47'])).

thf('52',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['29','53'])).

thf('55',plain,(
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

thf('56',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ( X23
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('57',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('58',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('59',plain,(
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

thf('60',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('61',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('66',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('67',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['57','64','67'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('69',plain,(
    ! [X5: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X5 ) ) @ X5 )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('70',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_D )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('73',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['70','73'])).

thf('75',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ( X23
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('77',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('81',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['82','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('87',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['77','84','87'])).

thf('89',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('90',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k1_relat_1 @ X8 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('91',plain,(
    ! [X6: $i] :
      ( ( ( k5_relat_1 @ X6 @ ( k6_relat_1 @ ( k2_relat_1 @ X6 ) ) )
        = X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['88','94'])).

thf('96',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['46','47'])).

thf('97',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['95','96','97','98'])).

thf('100',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['71','72'])).

thf('101',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['54','74','99','100'])).

thf('102',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['101','102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EXpLfdcyZD
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:56:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.32/2.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.32/2.56  % Solved by: fo/fo7.sh
% 2.32/2.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.32/2.56  % done 364 iterations in 2.038s
% 2.32/2.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.32/2.56  % SZS output start Refutation
% 2.32/2.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.32/2.56  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.32/2.56  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.32/2.56  thf(sk_B_type, type, sk_B: $i).
% 2.32/2.56  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.32/2.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.32/2.56  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.32/2.56  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.32/2.56  thf(sk_A_type, type, sk_A: $i).
% 2.32/2.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.32/2.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.32/2.56  thf(sk_C_type, type, sk_C: $i).
% 2.32/2.56  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 2.32/2.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.32/2.56  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.32/2.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.32/2.56  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.32/2.56  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.32/2.56  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.32/2.56  thf(sk_D_type, type, sk_D: $i).
% 2.32/2.56  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.32/2.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.32/2.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.32/2.56  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.32/2.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.32/2.56  thf(t36_funct_2, conjecture,
% 2.32/2.56    (![A:$i,B:$i,C:$i]:
% 2.32/2.56     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.32/2.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.32/2.56       ( ![D:$i]:
% 2.32/2.56         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.32/2.56             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.32/2.56           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.32/2.56               ( r2_relset_1 @
% 2.32/2.56                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.32/2.56                 ( k6_partfun1 @ A ) ) & 
% 2.32/2.56               ( v2_funct_1 @ C ) ) =>
% 2.32/2.56             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.32/2.56               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 2.32/2.56  thf(zf_stmt_0, negated_conjecture,
% 2.32/2.56    (~( ![A:$i,B:$i,C:$i]:
% 2.32/2.56        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.32/2.56            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.32/2.56          ( ![D:$i]:
% 2.32/2.56            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.32/2.56                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.32/2.56              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.32/2.56                  ( r2_relset_1 @
% 2.32/2.56                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.32/2.56                    ( k6_partfun1 @ A ) ) & 
% 2.32/2.56                  ( v2_funct_1 @ C ) ) =>
% 2.32/2.56                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.32/2.56                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 2.32/2.56    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 2.32/2.56  thf('0', plain,
% 2.32/2.56      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.32/2.56        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.32/2.56        (k6_partfun1 @ sk_A))),
% 2.32/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.56  thf(redefinition_k6_partfun1, axiom,
% 2.32/2.56    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.32/2.56  thf('1', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 2.32/2.56      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.32/2.56  thf('2', plain,
% 2.32/2.56      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.32/2.56        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.32/2.56        (k6_relat_1 @ sk_A))),
% 2.32/2.56      inference('demod', [status(thm)], ['0', '1'])).
% 2.32/2.56  thf('3', plain,
% 2.32/2.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.32/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.56  thf('4', plain,
% 2.32/2.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.32/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.56  thf(redefinition_k1_partfun1, axiom,
% 2.32/2.56    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.32/2.56     ( ( ( v1_funct_1 @ E ) & 
% 2.32/2.56         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.32/2.56         ( v1_funct_1 @ F ) & 
% 2.32/2.56         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.32/2.56       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.32/2.56  thf('5', plain,
% 2.32/2.56      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 2.32/2.56         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 2.32/2.56          | ~ (v1_funct_1 @ X37)
% 2.32/2.56          | ~ (v1_funct_1 @ X40)
% 2.32/2.56          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 2.32/2.56          | ((k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40)
% 2.32/2.56              = (k5_relat_1 @ X37 @ X40)))),
% 2.32/2.56      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 2.32/2.56  thf('6', plain,
% 2.32/2.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.32/2.56         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.32/2.56            = (k5_relat_1 @ sk_C @ X0))
% 2.32/2.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.32/2.56          | ~ (v1_funct_1 @ X0)
% 2.32/2.56          | ~ (v1_funct_1 @ sk_C))),
% 2.32/2.56      inference('sup-', [status(thm)], ['4', '5'])).
% 2.32/2.56  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 2.32/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.56  thf('8', plain,
% 2.32/2.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.32/2.56         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.32/2.56            = (k5_relat_1 @ sk_C @ X0))
% 2.32/2.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.32/2.56          | ~ (v1_funct_1 @ X0))),
% 2.32/2.56      inference('demod', [status(thm)], ['6', '7'])).
% 2.32/2.56  thf('9', plain,
% 2.32/2.56      ((~ (v1_funct_1 @ sk_D)
% 2.32/2.56        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.32/2.56            = (k5_relat_1 @ sk_C @ sk_D)))),
% 2.32/2.56      inference('sup-', [status(thm)], ['3', '8'])).
% 2.32/2.56  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 2.32/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.56  thf('11', plain,
% 2.32/2.56      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.32/2.56         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.32/2.56      inference('demod', [status(thm)], ['9', '10'])).
% 2.32/2.56  thf('12', plain,
% 2.32/2.56      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 2.32/2.56        (k6_relat_1 @ sk_A))),
% 2.32/2.56      inference('demod', [status(thm)], ['2', '11'])).
% 2.32/2.56  thf('13', plain,
% 2.32/2.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.32/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.56  thf('14', plain,
% 2.32/2.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.32/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.56  thf(dt_k1_partfun1, axiom,
% 2.32/2.56    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.32/2.56     ( ( ( v1_funct_1 @ E ) & 
% 2.32/2.56         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.32/2.56         ( v1_funct_1 @ F ) & 
% 2.32/2.56         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.32/2.56       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.32/2.56         ( m1_subset_1 @
% 2.32/2.56           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.32/2.56           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.32/2.56  thf('15', plain,
% 2.32/2.56      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 2.32/2.56         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 2.32/2.56          | ~ (v1_funct_1 @ X29)
% 2.32/2.56          | ~ (v1_funct_1 @ X32)
% 2.32/2.56          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 2.32/2.56          | (m1_subset_1 @ (k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32) @ 
% 2.32/2.56             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X34))))),
% 2.32/2.56      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.32/2.56  thf('16', plain,
% 2.32/2.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.32/2.56         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.32/2.56           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.32/2.56          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.32/2.56          | ~ (v1_funct_1 @ X1)
% 2.32/2.56          | ~ (v1_funct_1 @ sk_C))),
% 2.32/2.56      inference('sup-', [status(thm)], ['14', '15'])).
% 2.32/2.56  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 2.32/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.56  thf('18', plain,
% 2.32/2.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.32/2.56         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.32/2.56           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.32/2.56          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.32/2.56          | ~ (v1_funct_1 @ X1))),
% 2.32/2.56      inference('demod', [status(thm)], ['16', '17'])).
% 2.32/2.56  thf('19', plain,
% 2.32/2.56      ((~ (v1_funct_1 @ sk_D)
% 2.32/2.56        | (m1_subset_1 @ 
% 2.32/2.56           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.32/2.56           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.32/2.56      inference('sup-', [status(thm)], ['13', '18'])).
% 2.32/2.56  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 2.32/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.56  thf('21', plain,
% 2.32/2.56      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.32/2.56         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.32/2.56      inference('demod', [status(thm)], ['9', '10'])).
% 2.32/2.56  thf('22', plain,
% 2.32/2.56      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 2.32/2.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.32/2.56      inference('demod', [status(thm)], ['19', '20', '21'])).
% 2.32/2.56  thf(redefinition_r2_relset_1, axiom,
% 2.32/2.56    (![A:$i,B:$i,C:$i,D:$i]:
% 2.32/2.56     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.32/2.56         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.32/2.56       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.32/2.56  thf('23', plain,
% 2.32/2.56      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 2.32/2.56         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 2.32/2.56          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 2.32/2.56          | ((X17) = (X20))
% 2.32/2.56          | ~ (r2_relset_1 @ X18 @ X19 @ X17 @ X20))),
% 2.32/2.56      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.32/2.56  thf('24', plain,
% 2.32/2.56      (![X0 : $i]:
% 2.32/2.56         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 2.32/2.56          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 2.32/2.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.32/2.56      inference('sup-', [status(thm)], ['22', '23'])).
% 2.32/2.56  thf('25', plain,
% 2.32/2.56      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 2.32/2.56           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.32/2.56        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A)))),
% 2.32/2.56      inference('sup-', [status(thm)], ['12', '24'])).
% 2.32/2.56  thf(dt_k6_partfun1, axiom,
% 2.32/2.56    (![A:$i]:
% 2.32/2.56     ( ( m1_subset_1 @
% 2.32/2.56         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 2.32/2.56       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 2.32/2.56  thf('26', plain,
% 2.32/2.56      (![X36 : $i]:
% 2.32/2.56         (m1_subset_1 @ (k6_partfun1 @ X36) @ 
% 2.32/2.56          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 2.32/2.56      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 2.32/2.56  thf('27', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 2.32/2.56      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.32/2.56  thf('28', plain,
% 2.32/2.56      (![X36 : $i]:
% 2.32/2.56         (m1_subset_1 @ (k6_relat_1 @ X36) @ 
% 2.32/2.56          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 2.32/2.56      inference('demod', [status(thm)], ['26', '27'])).
% 2.32/2.56  thf('29', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 2.32/2.56      inference('demod', [status(thm)], ['25', '28'])).
% 2.32/2.56  thf(dt_k2_funct_1, axiom,
% 2.32/2.56    (![A:$i]:
% 2.32/2.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.32/2.56       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 2.32/2.56         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 2.32/2.56  thf('30', plain,
% 2.32/2.56      (![X7 : $i]:
% 2.32/2.56         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 2.32/2.56          | ~ (v1_funct_1 @ X7)
% 2.32/2.56          | ~ (v1_relat_1 @ X7))),
% 2.32/2.56      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.32/2.56  thf('31', plain,
% 2.32/2.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.32/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.56  thf(t35_funct_2, axiom,
% 2.32/2.56    (![A:$i,B:$i,C:$i]:
% 2.32/2.56     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.32/2.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.32/2.56       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 2.32/2.56         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.32/2.56           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 2.32/2.56             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 2.32/2.56  thf('32', plain,
% 2.32/2.56      (![X44 : $i, X45 : $i, X46 : $i]:
% 2.32/2.56         (((X44) = (k1_xboole_0))
% 2.32/2.56          | ~ (v1_funct_1 @ X45)
% 2.32/2.56          | ~ (v1_funct_2 @ X45 @ X46 @ X44)
% 2.32/2.56          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X44)))
% 2.32/2.56          | ((k5_relat_1 @ (k2_funct_1 @ X45) @ X45) = (k6_partfun1 @ X44))
% 2.32/2.56          | ~ (v2_funct_1 @ X45)
% 2.32/2.56          | ((k2_relset_1 @ X46 @ X44 @ X45) != (X44)))),
% 2.32/2.56      inference('cnf', [status(esa)], [t35_funct_2])).
% 2.32/2.56  thf('33', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 2.32/2.56      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.32/2.56  thf('34', plain,
% 2.32/2.56      (![X44 : $i, X45 : $i, X46 : $i]:
% 2.32/2.56         (((X44) = (k1_xboole_0))
% 2.32/2.56          | ~ (v1_funct_1 @ X45)
% 2.32/2.56          | ~ (v1_funct_2 @ X45 @ X46 @ X44)
% 2.32/2.56          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X44)))
% 2.32/2.56          | ((k5_relat_1 @ (k2_funct_1 @ X45) @ X45) = (k6_relat_1 @ X44))
% 2.32/2.56          | ~ (v2_funct_1 @ X45)
% 2.32/2.56          | ((k2_relset_1 @ X46 @ X44 @ X45) != (X44)))),
% 2.32/2.56      inference('demod', [status(thm)], ['32', '33'])).
% 2.32/2.56  thf('35', plain,
% 2.32/2.56      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 2.32/2.56        | ~ (v2_funct_1 @ sk_C)
% 2.32/2.56        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 2.32/2.56        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.32/2.56        | ~ (v1_funct_1 @ sk_C)
% 2.32/2.56        | ((sk_B) = (k1_xboole_0)))),
% 2.32/2.56      inference('sup-', [status(thm)], ['31', '34'])).
% 2.32/2.56  thf('36', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.32/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.56  thf('37', plain, ((v2_funct_1 @ sk_C)),
% 2.32/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.56  thf('38', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.32/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.56  thf('39', plain, ((v1_funct_1 @ sk_C)),
% 2.32/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.56  thf('40', plain,
% 2.32/2.56      ((((sk_B) != (sk_B))
% 2.32/2.56        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 2.32/2.56        | ((sk_B) = (k1_xboole_0)))),
% 2.32/2.56      inference('demod', [status(thm)], ['35', '36', '37', '38', '39'])).
% 2.32/2.56  thf('41', plain,
% 2.32/2.56      ((((sk_B) = (k1_xboole_0))
% 2.32/2.56        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B)))),
% 2.32/2.56      inference('simplify', [status(thm)], ['40'])).
% 2.32/2.56  thf('42', plain, (((sk_B) != (k1_xboole_0))),
% 2.32/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.56  thf('43', plain,
% 2.32/2.56      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))),
% 2.32/2.56      inference('simplify_reflect-', [status(thm)], ['41', '42'])).
% 2.32/2.56  thf(t55_relat_1, axiom,
% 2.32/2.56    (![A:$i]:
% 2.32/2.56     ( ( v1_relat_1 @ A ) =>
% 2.32/2.56       ( ![B:$i]:
% 2.32/2.56         ( ( v1_relat_1 @ B ) =>
% 2.32/2.56           ( ![C:$i]:
% 2.32/2.56             ( ( v1_relat_1 @ C ) =>
% 2.32/2.56               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 2.32/2.56                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 2.32/2.56  thf('44', plain,
% 2.32/2.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.32/2.56         (~ (v1_relat_1 @ X0)
% 2.32/2.56          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 2.32/2.56              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 2.32/2.56          | ~ (v1_relat_1 @ X2)
% 2.32/2.56          | ~ (v1_relat_1 @ X1))),
% 2.32/2.56      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.32/2.56  thf('45', plain,
% 2.32/2.56      (![X0 : $i]:
% 2.32/2.56         (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 2.32/2.56            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 2.32/2.56          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.32/2.56          | ~ (v1_relat_1 @ X0)
% 2.32/2.56          | ~ (v1_relat_1 @ sk_C))),
% 2.32/2.56      inference('sup+', [status(thm)], ['43', '44'])).
% 2.32/2.56  thf('46', plain,
% 2.32/2.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.32/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.56  thf(cc1_relset_1, axiom,
% 2.32/2.56    (![A:$i,B:$i,C:$i]:
% 2.32/2.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.32/2.56       ( v1_relat_1 @ C ) ))).
% 2.32/2.56  thf('47', plain,
% 2.32/2.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.32/2.56         ((v1_relat_1 @ X11)
% 2.32/2.56          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 2.32/2.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.32/2.56  thf('48', plain, ((v1_relat_1 @ sk_C)),
% 2.32/2.56      inference('sup-', [status(thm)], ['46', '47'])).
% 2.32/2.56  thf('49', plain,
% 2.32/2.56      (![X0 : $i]:
% 2.32/2.56         (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 2.32/2.56            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 2.32/2.56          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.32/2.56          | ~ (v1_relat_1 @ X0))),
% 2.32/2.56      inference('demod', [status(thm)], ['45', '48'])).
% 2.32/2.56  thf('50', plain,
% 2.32/2.56      (![X0 : $i]:
% 2.32/2.56         (~ (v1_relat_1 @ sk_C)
% 2.32/2.56          | ~ (v1_funct_1 @ sk_C)
% 2.32/2.56          | ~ (v1_relat_1 @ X0)
% 2.32/2.56          | ((k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 2.32/2.56              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 2.32/2.56      inference('sup-', [status(thm)], ['30', '49'])).
% 2.32/2.56  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 2.32/2.56      inference('sup-', [status(thm)], ['46', '47'])).
% 2.32/2.56  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 2.32/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.56  thf('53', plain,
% 2.32/2.56      (![X0 : $i]:
% 2.32/2.56         (~ (v1_relat_1 @ X0)
% 2.32/2.56          | ((k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 2.32/2.56              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 2.32/2.56      inference('demod', [status(thm)], ['50', '51', '52'])).
% 2.32/2.56  thf('54', plain,
% 2.32/2.56      ((((k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_D)
% 2.32/2.56          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_relat_1 @ sk_A)))
% 2.32/2.56        | ~ (v1_relat_1 @ sk_D))),
% 2.32/2.56      inference('sup+', [status(thm)], ['29', '53'])).
% 2.32/2.56  thf('55', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.32/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.56  thf(d1_funct_2, axiom,
% 2.32/2.56    (![A:$i,B:$i,C:$i]:
% 2.32/2.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.32/2.56       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.32/2.56           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.32/2.56             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.32/2.56         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.32/2.56           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.32/2.56             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.32/2.56  thf(zf_stmt_1, axiom,
% 2.32/2.56    (![C:$i,B:$i,A:$i]:
% 2.32/2.56     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.32/2.56       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.32/2.56  thf('56', plain,
% 2.32/2.56      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.32/2.56         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 2.32/2.56          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 2.32/2.56          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 2.32/2.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.32/2.56  thf('57', plain,
% 2.32/2.56      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 2.32/2.56        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 2.32/2.56      inference('sup-', [status(thm)], ['55', '56'])).
% 2.32/2.56  thf(zf_stmt_2, axiom,
% 2.32/2.56    (![B:$i,A:$i]:
% 2.32/2.56     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.32/2.56       ( zip_tseitin_0 @ B @ A ) ))).
% 2.32/2.56  thf('58', plain,
% 2.32/2.56      (![X21 : $i, X22 : $i]:
% 2.32/2.56         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 2.32/2.56      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.32/2.56  thf('59', plain,
% 2.32/2.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.32/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.56  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.32/2.56  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.32/2.56  thf(zf_stmt_5, axiom,
% 2.32/2.56    (![A:$i,B:$i,C:$i]:
% 2.32/2.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.32/2.56       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.32/2.56         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.32/2.56           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.32/2.56             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.32/2.56  thf('60', plain,
% 2.32/2.56      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.32/2.56         (~ (zip_tseitin_0 @ X26 @ X27)
% 2.32/2.56          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 2.32/2.56          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 2.32/2.56      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.32/2.56  thf('61', plain,
% 2.32/2.56      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 2.32/2.56      inference('sup-', [status(thm)], ['59', '60'])).
% 2.32/2.56  thf('62', plain,
% 2.32/2.56      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 2.32/2.56      inference('sup-', [status(thm)], ['58', '61'])).
% 2.32/2.56  thf('63', plain, (((sk_A) != (k1_xboole_0))),
% 2.32/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.56  thf('64', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 2.32/2.56      inference('simplify_reflect-', [status(thm)], ['62', '63'])).
% 2.32/2.56  thf('65', plain,
% 2.32/2.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.32/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.56  thf(redefinition_k1_relset_1, axiom,
% 2.32/2.56    (![A:$i,B:$i,C:$i]:
% 2.32/2.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.32/2.56       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.32/2.56  thf('66', plain,
% 2.32/2.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.32/2.56         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 2.32/2.56          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 2.32/2.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.32/2.56  thf('67', plain,
% 2.32/2.56      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 2.32/2.56      inference('sup-', [status(thm)], ['65', '66'])).
% 2.32/2.56  thf('68', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 2.32/2.56      inference('demod', [status(thm)], ['57', '64', '67'])).
% 2.32/2.56  thf(t78_relat_1, axiom,
% 2.32/2.56    (![A:$i]:
% 2.32/2.56     ( ( v1_relat_1 @ A ) =>
% 2.32/2.56       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 2.32/2.56  thf('69', plain,
% 2.32/2.56      (![X5 : $i]:
% 2.32/2.56         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X5)) @ X5) = (X5))
% 2.32/2.56          | ~ (v1_relat_1 @ X5))),
% 2.32/2.56      inference('cnf', [status(esa)], [t78_relat_1])).
% 2.32/2.56  thf('70', plain,
% 2.32/2.56      ((((k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_D) = (sk_D))
% 2.32/2.56        | ~ (v1_relat_1 @ sk_D))),
% 2.32/2.56      inference('sup+', [status(thm)], ['68', '69'])).
% 2.32/2.56  thf('71', plain,
% 2.32/2.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.32/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.56  thf('72', plain,
% 2.32/2.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.32/2.56         ((v1_relat_1 @ X11)
% 2.32/2.56          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 2.32/2.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.32/2.56  thf('73', plain, ((v1_relat_1 @ sk_D)),
% 2.32/2.56      inference('sup-', [status(thm)], ['71', '72'])).
% 2.32/2.56  thf('74', plain, (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_D) = (sk_D))),
% 2.32/2.56      inference('demod', [status(thm)], ['70', '73'])).
% 2.32/2.56  thf('75', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.32/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.56  thf('76', plain,
% 2.32/2.56      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.32/2.56         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 2.32/2.56          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 2.32/2.56          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 2.32/2.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.32/2.56  thf('77', plain,
% 2.32/2.56      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 2.32/2.56        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 2.32/2.56      inference('sup-', [status(thm)], ['75', '76'])).
% 2.32/2.56  thf('78', plain,
% 2.32/2.56      (![X21 : $i, X22 : $i]:
% 2.32/2.56         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 2.32/2.56      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.32/2.56  thf('79', plain,
% 2.32/2.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.32/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.56  thf('80', plain,
% 2.32/2.56      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.32/2.56         (~ (zip_tseitin_0 @ X26 @ X27)
% 2.32/2.56          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 2.32/2.56          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 2.32/2.56      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.32/2.56  thf('81', plain,
% 2.32/2.56      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 2.32/2.56      inference('sup-', [status(thm)], ['79', '80'])).
% 2.32/2.56  thf('82', plain,
% 2.32/2.56      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 2.32/2.56      inference('sup-', [status(thm)], ['78', '81'])).
% 2.32/2.56  thf('83', plain, (((sk_B) != (k1_xboole_0))),
% 2.32/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.56  thf('84', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 2.32/2.56      inference('simplify_reflect-', [status(thm)], ['82', '83'])).
% 2.32/2.56  thf('85', plain,
% 2.32/2.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.32/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.56  thf('86', plain,
% 2.32/2.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.32/2.56         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 2.32/2.56          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 2.32/2.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.32/2.56  thf('87', plain,
% 2.32/2.56      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 2.32/2.56      inference('sup-', [status(thm)], ['85', '86'])).
% 2.32/2.56  thf('88', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 2.32/2.56      inference('demod', [status(thm)], ['77', '84', '87'])).
% 2.32/2.56  thf('89', plain,
% 2.32/2.56      (![X7 : $i]:
% 2.32/2.56         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 2.32/2.56          | ~ (v1_funct_1 @ X7)
% 2.32/2.56          | ~ (v1_relat_1 @ X7))),
% 2.32/2.56      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.32/2.56  thf(t55_funct_1, axiom,
% 2.32/2.56    (![A:$i]:
% 2.32/2.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.32/2.56       ( ( v2_funct_1 @ A ) =>
% 2.32/2.56         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 2.32/2.56           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.32/2.56  thf('90', plain,
% 2.32/2.56      (![X8 : $i]:
% 2.32/2.56         (~ (v2_funct_1 @ X8)
% 2.32/2.56          | ((k1_relat_1 @ X8) = (k2_relat_1 @ (k2_funct_1 @ X8)))
% 2.32/2.56          | ~ (v1_funct_1 @ X8)
% 2.32/2.56          | ~ (v1_relat_1 @ X8))),
% 2.32/2.56      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.32/2.56  thf(t80_relat_1, axiom,
% 2.32/2.56    (![A:$i]:
% 2.32/2.56     ( ( v1_relat_1 @ A ) =>
% 2.32/2.56       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 2.32/2.56  thf('91', plain,
% 2.32/2.56      (![X6 : $i]:
% 2.32/2.56         (((k5_relat_1 @ X6 @ (k6_relat_1 @ (k2_relat_1 @ X6))) = (X6))
% 2.32/2.56          | ~ (v1_relat_1 @ X6))),
% 2.32/2.56      inference('cnf', [status(esa)], [t80_relat_1])).
% 2.32/2.56  thf('92', plain,
% 2.32/2.56      (![X0 : $i]:
% 2.32/2.56         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 2.32/2.56            = (k2_funct_1 @ X0))
% 2.32/2.56          | ~ (v1_relat_1 @ X0)
% 2.32/2.56          | ~ (v1_funct_1 @ X0)
% 2.32/2.56          | ~ (v2_funct_1 @ X0)
% 2.32/2.56          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 2.32/2.56      inference('sup+', [status(thm)], ['90', '91'])).
% 2.32/2.56  thf('93', plain,
% 2.32/2.56      (![X0 : $i]:
% 2.32/2.56         (~ (v1_relat_1 @ X0)
% 2.32/2.56          | ~ (v1_funct_1 @ X0)
% 2.32/2.56          | ~ (v2_funct_1 @ X0)
% 2.32/2.56          | ~ (v1_funct_1 @ X0)
% 2.32/2.56          | ~ (v1_relat_1 @ X0)
% 2.32/2.56          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 2.32/2.56              = (k2_funct_1 @ X0)))),
% 2.32/2.56      inference('sup-', [status(thm)], ['89', '92'])).
% 2.32/2.56  thf('94', plain,
% 2.32/2.56      (![X0 : $i]:
% 2.32/2.56         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 2.32/2.56            = (k2_funct_1 @ X0))
% 2.32/2.56          | ~ (v2_funct_1 @ X0)
% 2.32/2.56          | ~ (v1_funct_1 @ X0)
% 2.32/2.56          | ~ (v1_relat_1 @ X0))),
% 2.32/2.56      inference('simplify', [status(thm)], ['93'])).
% 2.32/2.56  thf('95', plain,
% 2.32/2.56      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_relat_1 @ sk_A))
% 2.32/2.56          = (k2_funct_1 @ sk_C))
% 2.32/2.56        | ~ (v1_relat_1 @ sk_C)
% 2.32/2.56        | ~ (v1_funct_1 @ sk_C)
% 2.32/2.56        | ~ (v2_funct_1 @ sk_C))),
% 2.32/2.56      inference('sup+', [status(thm)], ['88', '94'])).
% 2.32/2.56  thf('96', plain, ((v1_relat_1 @ sk_C)),
% 2.32/2.56      inference('sup-', [status(thm)], ['46', '47'])).
% 2.32/2.56  thf('97', plain, ((v1_funct_1 @ sk_C)),
% 2.32/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.56  thf('98', plain, ((v2_funct_1 @ sk_C)),
% 2.32/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.56  thf('99', plain,
% 2.32/2.56      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_relat_1 @ sk_A))
% 2.32/2.56         = (k2_funct_1 @ sk_C))),
% 2.32/2.56      inference('demod', [status(thm)], ['95', '96', '97', '98'])).
% 2.32/2.56  thf('100', plain, ((v1_relat_1 @ sk_D)),
% 2.32/2.56      inference('sup-', [status(thm)], ['71', '72'])).
% 2.32/2.56  thf('101', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 2.32/2.56      inference('demod', [status(thm)], ['54', '74', '99', '100'])).
% 2.32/2.56  thf('102', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 2.32/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.56  thf('103', plain, ($false),
% 2.32/2.56      inference('simplify_reflect-', [status(thm)], ['101', '102'])).
% 2.32/2.56  
% 2.32/2.56  % SZS output end Refutation
% 2.32/2.56  
% 2.32/2.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

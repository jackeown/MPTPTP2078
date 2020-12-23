%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ad6TvCsdSX

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:04 EST 2020

% Result     : Theorem 8.45s
% Output     : Refutation 8.53s
% Verified   : 
% Statistics : Number of formulae       :  345 (1258 expanded)
%              Number of leaves         :   53 ( 397 expanded)
%              Depth                    :   38
%              Number of atoms          : 4035 (25432 expanded)
%              Number of equality atoms :  238 (1669 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
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
    ! [X59: $i,X60: $i,X61: $i] :
      ( ( X59 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X60 )
      | ~ ( v1_funct_2 @ X60 @ X61 @ X59 )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X61 @ X59 ) ) )
      | ( ( k5_relat_1 @ X60 @ ( k2_funct_1 @ X60 ) )
        = ( k6_partfun1 @ X61 ) )
      | ~ ( v2_funct_1 @ X60 )
      | ( ( k2_relset_1 @ X61 @ X59 @ X60 )
       != X59 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('2',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A_1 @ sk_D )
     != sk_A_1 )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A_1 )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('4',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('5',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A_1 )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','5','6','7'])).

thf('9',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A_1 )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
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

thf('13',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ~ ( r2_relset_1 @ X47 @ X47 @ ( k1_partfun1 @ X47 @ X48 @ X48 @ X47 @ X46 @ X49 ) @ ( k6_partfun1 @ X47 ) )
      | ( ( k2_relset_1 @ X48 @ X47 @ X49 )
        = X47 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X47 ) ) )
      | ~ ( v1_funct_2 @ X49 @ X48 @ X47 )
      | ~ ( v1_funct_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A_1 @ X0 )
        = sk_A_1 )
      | ~ ( r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A_1 ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_2 @ sk_C @ sk_A_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A_1 @ X0 )
        = sk_A_1 )
      | ~ ( r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A_1 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A_1 @ sk_D )
      = sk_A_1 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A_1 )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A_1 ),
    inference(demod,[status(thm)],['18','19','20','21','22'])).

thf('24',plain,
    ( ( sk_A_1 != sk_A_1 )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','23'])).

thf('25',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('28',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( ( k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42 )
        = ( k5_relat_1 @ X39 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('37',plain,(
    r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('40',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X32 @ X33 @ X35 @ X36 @ X31 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_A_1 ) ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('47',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_A_1 ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('48',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( X27 = X30 )
      | ~ ( r2_relset_1 @ X28 @ X29 @ X27 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_A_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_A_1 ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['37','49'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('51',plain,(
    ! [X38: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('52',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['34','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
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

thf('55',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i,X58: $i] :
      ( ~ ( v1_funct_1 @ X54 )
      | ~ ( v1_funct_2 @ X54 @ X55 @ X56 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X56 ) ) )
      | ( zip_tseitin_0 @ X54 @ X57 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X58 @ X55 @ X55 @ X56 @ X57 @ X54 ) )
      | ( zip_tseitin_1 @ X56 @ X55 )
      | ( ( k2_relset_1 @ X58 @ X55 @ X57 )
       != X55 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X55 ) ) )
      | ~ ( v1_funct_2 @ X57 @ X58 @ X55 )
      | ~ ( v1_funct_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A_1 @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A_1 @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A_1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A_1 @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A_1 @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A_1 ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A_1 @ sk_B )
    | ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['53','59'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('61',plain,(
    ! [X17: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('62',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('63',plain,(
    ! [X17: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X17 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_2 @ sk_C @ sk_A_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A_1 @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['60','63','64','65','66','67'])).

thf('69',plain,
    ( ( zip_tseitin_1 @ sk_A_1 @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X52: $i,X53: $i] :
      ( ( X52 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('71',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X50: $i,X51: $i] :
      ( ( v2_funct_1 @ X51 )
      | ~ ( zip_tseitin_0 @ X51 @ X50 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('75',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['25','75'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('77',plain,(
    ! [X13: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X13 ) ) @ X13 )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('78',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('79',plain,(
    ! [X13: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X13 ) ) @ X13 )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('80',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('81',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) @ X10 )
        = ( k5_relat_1 @ X9 @ ( k5_relat_1 @ X8 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('82',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
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

thf('83',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relat_1 @ X18 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('84',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X4 ) @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('85',plain,(
    ! [X3: $i] :
      ( ( k2_subset_1 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('86',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('87',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('88',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('89',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ( ( k5_relat_1 @ X14 @ ( k6_relat_1 @ X15 ) )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('90',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('91',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ( ( k5_relat_1 @ X14 @ ( k6_partfun1 @ X15 ) )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X13: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X13 ) ) @ X13 )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('94',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) @ X10 )
        = ( k5_relat_1 @ X9 @ ( k5_relat_1 @ X8 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X38: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('97',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['95','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['92','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['83','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['82','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('109',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X20 ) @ X20 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('110',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('111',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X20 ) @ X20 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('113',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) @ X10 )
        = ( k5_relat_1 @ X9 @ ( k5_relat_1 @ X8 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['111','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['108','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['107','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relat_1 @ X18 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('127',plain,(
    ! [X11: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('128',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('129',plain,(
    ! [X11: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X11 ) )
      = X11 ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X13: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X13 ) ) @ X13 )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) @ X0 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['126','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) @ X0 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['123','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k1_relat_1 @ X18 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) @ X0 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['137','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) @ X0 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['81','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('151',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k5_relat_1 @ X20 @ ( k2_funct_1 @ X20 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('152',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('153',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k5_relat_1 @ X20 @ ( k2_funct_1 @ X20 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) @ X10 )
        = ( k5_relat_1 @ X9 @ ( k5_relat_1 @ X8 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['150','156'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['149','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k1_relat_1 @ X18 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('164',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['157'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['164','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) @ X10 )
        = ( k5_relat_1 @ X9 @ ( k5_relat_1 @ X8 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('175',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['173','174','175'])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['163','176'])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ X0 )
        = ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['162','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ X0 )
        = ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['76','180'])).

thf('182',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('183',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('184',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X20 ) @ X20 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('185',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) @ X10 )
        = ( k5_relat_1 @ X9 @ ( k5_relat_1 @ X8 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('186',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['186'])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['183','187'])).

thf('189',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['188'])).

thf('190',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['182','189'])).

thf('191',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('193',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('197',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k1_relat_1 @ X18 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('198',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['197','198'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['196','199'])).

thf('201',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['200'])).

thf('202',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('203',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['193','194'])).

thf('204',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('205',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relat_1 @ X18 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('206',plain,(
    ! [X13: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X13 ) ) @ X13 )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('207',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['205','206'])).

thf('208',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['204','207'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['208'])).

thf('210',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['203','209'])).

thf('211',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('213',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['210','213','214','215'])).

thf('217',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) @ X10 )
        = ( k5_relat_1 @ X9 @ ( k5_relat_1 @ X8 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('218',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['216','217'])).

thf('219',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('220',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['218','219'])).

thf('221',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['202','220'])).

thf('222',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['211','212'])).

thf('223',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['221','222','223'])).

thf('225',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['201','224'])).

thf('226',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['210','213','214','215'])).

thf('227',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['211','212'])).

thf('228',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('231',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['225','226','227','228','229','230'])).

thf('232',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ( X59 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X60 )
      | ~ ( v1_funct_2 @ X60 @ X61 @ X59 )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X61 @ X59 ) ) )
      | ( ( k5_relat_1 @ X60 @ ( k2_funct_1 @ X60 ) )
        = ( k6_partfun1 @ X61 ) )
      | ~ ( v2_funct_1 @ X60 )
      | ( ( k2_relset_1 @ X61 @ X59 @ X60 )
       != X59 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('234',plain,
    ( ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A_1 ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['232','233'])).

thf('235',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('238',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k5_relat_1 @ X20 @ ( k2_funct_1 @ X20 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('239',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['193','194'])).

thf('240',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('241',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['239','240'])).

thf('242',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['211','212'])).

thf('243',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['241','242'])).

thf('244',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('245',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['243','244'])).

thf('246',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['241','242'])).

thf('247',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['211','212'])).

thf('248',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('249',plain,
    ( sk_C
    = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['245','246','247','248'])).

thf('250',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) @ X10 )
        = ( k5_relat_1 @ X9 @ ( k5_relat_1 @ X8 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('251',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['249','250'])).

thf('252',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('253',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['211','212'])).

thf('254',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['251','252','253'])).

thf('255',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['238','254'])).

thf('256',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('257',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['211','212'])).

thf('258',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('260',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['255','256','257','258','259'])).

thf('261',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['237','260'])).

thf('262',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['211','212'])).

thf('263',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['261','262','263'])).

thf('265',plain,(
    v1_funct_2 @ sk_C @ sk_A_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('266',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,
    ( ( sk_B != sk_B )
    | ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A_1 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['234','235','236','264','265','266'])).

thf('268',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A_1 ) ) ),
    inference(simplify,[status(thm)],['267'])).

thf('269',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A_1 ) ),
    inference('simplify_reflect-',[status(thm)],['268','269'])).

thf('271',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A_1 ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['231','270'])).

thf('272',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['211','212'])).

thf('273',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('274',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('275',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('277',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['275','276'])).

thf('278',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['190','195','271','272','273','274','277'])).

thf('279',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A_1 ),
    inference(demod,[status(thm)],['18','19','20','21','22'])).

thf('280',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A_1 ),
    inference(demod,[status(thm)],['18','19','20','21','22'])).

thf('281',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('282',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ sk_A_1 ) )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['280','281'])).

thf('283',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['275','276'])).

thf('284',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ sk_A_1 ) )
    = sk_D ),
    inference(demod,[status(thm)],['282','283'])).

thf('285',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['275','276'])).

thf('286',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('287',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['73','74'])).

thf('288',plain,
    ( ( k2_funct_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['181','278','279','284','285','286','287'])).

thf('289',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('290',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['288','289'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ad6TvCsdSX
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:33:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 8.45/8.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 8.45/8.68  % Solved by: fo/fo7.sh
% 8.45/8.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.45/8.68  % done 5722 iterations in 8.208s
% 8.45/8.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 8.45/8.68  % SZS output start Refutation
% 8.45/8.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.45/8.68  thf(sk_C_type, type, sk_C: $i).
% 8.45/8.68  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 8.45/8.68  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 8.45/8.68  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 8.45/8.68  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 8.45/8.68  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 8.45/8.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 8.45/8.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 8.45/8.68  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 8.45/8.68  thf(sk_B_type, type, sk_B: $i).
% 8.45/8.68  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 8.45/8.68  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 8.45/8.68  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 8.53/8.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 8.53/8.68  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 8.53/8.68  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 8.53/8.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.53/8.68  thf(sk_A_1_type, type, sk_A_1: $i).
% 8.53/8.68  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 8.53/8.68  thf(sk_D_type, type, sk_D: $i).
% 8.53/8.68  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 8.53/8.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 8.53/8.68  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 8.53/8.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 8.53/8.68  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 8.53/8.68  thf(t36_funct_2, conjecture,
% 8.53/8.68    (![A:$i,B:$i,C:$i]:
% 8.53/8.68     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 8.53/8.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 8.53/8.68       ( ![D:$i]:
% 8.53/8.68         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 8.53/8.68             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 8.53/8.68           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 8.53/8.68               ( r2_relset_1 @
% 8.53/8.68                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 8.53/8.68                 ( k6_partfun1 @ A ) ) & 
% 8.53/8.68               ( v2_funct_1 @ C ) ) =>
% 8.53/8.68             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 8.53/8.68               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 8.53/8.68  thf(zf_stmt_0, negated_conjecture,
% 8.53/8.68    (~( ![A:$i,B:$i,C:$i]:
% 8.53/8.68        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 8.53/8.68            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 8.53/8.68          ( ![D:$i]:
% 8.53/8.68            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 8.53/8.68                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 8.53/8.68              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 8.53/8.68                  ( r2_relset_1 @
% 8.53/8.68                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 8.53/8.68                    ( k6_partfun1 @ A ) ) & 
% 8.53/8.68                  ( v2_funct_1 @ C ) ) =>
% 8.53/8.68                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 8.53/8.68                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 8.53/8.68    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 8.53/8.68  thf('0', plain,
% 8.53/8.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 8.53/8.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.68  thf(t35_funct_2, axiom,
% 8.53/8.68    (![A:$i,B:$i,C:$i]:
% 8.53/8.68     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 8.53/8.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 8.53/8.68       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 8.53/8.68         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 8.53/8.68           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 8.53/8.68             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 8.53/8.68  thf('1', plain,
% 8.53/8.68      (![X59 : $i, X60 : $i, X61 : $i]:
% 8.53/8.68         (((X59) = (k1_xboole_0))
% 8.53/8.68          | ~ (v1_funct_1 @ X60)
% 8.53/8.68          | ~ (v1_funct_2 @ X60 @ X61 @ X59)
% 8.53/8.68          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X61 @ X59)))
% 8.53/8.68          | ((k5_relat_1 @ X60 @ (k2_funct_1 @ X60)) = (k6_partfun1 @ X61))
% 8.53/8.68          | ~ (v2_funct_1 @ X60)
% 8.53/8.68          | ((k2_relset_1 @ X61 @ X59 @ X60) != (X59)))),
% 8.53/8.68      inference('cnf', [status(esa)], [t35_funct_2])).
% 8.53/8.68  thf('2', plain,
% 8.53/8.68      ((((k2_relset_1 @ sk_B @ sk_A_1 @ sk_D) != (sk_A_1))
% 8.53/8.68        | ~ (v2_funct_1 @ sk_D)
% 8.53/8.68        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 8.53/8.68        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A_1)
% 8.53/8.68        | ~ (v1_funct_1 @ sk_D)
% 8.53/8.68        | ((sk_A_1) = (k1_xboole_0)))),
% 8.53/8.68      inference('sup-', [status(thm)], ['0', '1'])).
% 8.53/8.68  thf('3', plain,
% 8.53/8.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 8.53/8.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.68  thf(redefinition_k2_relset_1, axiom,
% 8.53/8.68    (![A:$i,B:$i,C:$i]:
% 8.53/8.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.53/8.68       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 8.53/8.68  thf('4', plain,
% 8.53/8.68      (![X24 : $i, X25 : $i, X26 : $i]:
% 8.53/8.68         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 8.53/8.68          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 8.53/8.68      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 8.53/8.68  thf('5', plain,
% 8.53/8.68      (((k2_relset_1 @ sk_B @ sk_A_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 8.53/8.68      inference('sup-', [status(thm)], ['3', '4'])).
% 8.53/8.68  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A_1)),
% 8.53/8.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.68  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 8.53/8.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.68  thf('8', plain,
% 8.53/8.68      ((((k2_relat_1 @ sk_D) != (sk_A_1))
% 8.53/8.68        | ~ (v2_funct_1 @ sk_D)
% 8.53/8.68        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 8.53/8.68        | ((sk_A_1) = (k1_xboole_0)))),
% 8.53/8.68      inference('demod', [status(thm)], ['2', '5', '6', '7'])).
% 8.53/8.68  thf('9', plain, (((sk_A_1) != (k1_xboole_0))),
% 8.53/8.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.68  thf('10', plain,
% 8.53/8.68      ((((k2_relat_1 @ sk_D) != (sk_A_1))
% 8.53/8.68        | ~ (v2_funct_1 @ sk_D)
% 8.53/8.68        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 8.53/8.68      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 8.53/8.68  thf('11', plain,
% 8.53/8.68      ((r2_relset_1 @ sk_A_1 @ sk_A_1 @ 
% 8.53/8.68        (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D) @ 
% 8.53/8.68        (k6_partfun1 @ sk_A_1))),
% 8.53/8.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.68  thf('12', plain,
% 8.53/8.68      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 8.53/8.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.68  thf(t24_funct_2, axiom,
% 8.53/8.68    (![A:$i,B:$i,C:$i]:
% 8.53/8.68     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 8.53/8.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 8.53/8.68       ( ![D:$i]:
% 8.53/8.68         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 8.53/8.68             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 8.53/8.68           ( ( r2_relset_1 @
% 8.53/8.68               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 8.53/8.68               ( k6_partfun1 @ B ) ) =>
% 8.53/8.68             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 8.53/8.68  thf('13', plain,
% 8.53/8.68      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 8.53/8.68         (~ (v1_funct_1 @ X46)
% 8.53/8.68          | ~ (v1_funct_2 @ X46 @ X47 @ X48)
% 8.53/8.68          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 8.53/8.68          | ~ (r2_relset_1 @ X47 @ X47 @ 
% 8.53/8.68               (k1_partfun1 @ X47 @ X48 @ X48 @ X47 @ X46 @ X49) @ 
% 8.53/8.68               (k6_partfun1 @ X47))
% 8.53/8.68          | ((k2_relset_1 @ X48 @ X47 @ X49) = (X47))
% 8.53/8.68          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X47)))
% 8.53/8.68          | ~ (v1_funct_2 @ X49 @ X48 @ X47)
% 8.53/8.68          | ~ (v1_funct_1 @ X49))),
% 8.53/8.68      inference('cnf', [status(esa)], [t24_funct_2])).
% 8.53/8.68  thf('14', plain,
% 8.53/8.68      (![X0 : $i]:
% 8.53/8.68         (~ (v1_funct_1 @ X0)
% 8.53/8.68          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A_1)
% 8.53/8.68          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))
% 8.53/8.68          | ((k2_relset_1 @ sk_B @ sk_A_1 @ X0) = (sk_A_1))
% 8.53/8.68          | ~ (r2_relset_1 @ sk_A_1 @ sk_A_1 @ 
% 8.53/8.68               (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ X0) @ 
% 8.53/8.68               (k6_partfun1 @ sk_A_1))
% 8.53/8.68          | ~ (v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)
% 8.53/8.68          | ~ (v1_funct_1 @ sk_C))),
% 8.53/8.68      inference('sup-', [status(thm)], ['12', '13'])).
% 8.53/8.68  thf('15', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)),
% 8.53/8.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.68  thf('16', plain, ((v1_funct_1 @ sk_C)),
% 8.53/8.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.68  thf('17', plain,
% 8.53/8.68      (![X0 : $i]:
% 8.53/8.68         (~ (v1_funct_1 @ X0)
% 8.53/8.68          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A_1)
% 8.53/8.68          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))
% 8.53/8.68          | ((k2_relset_1 @ sk_B @ sk_A_1 @ X0) = (sk_A_1))
% 8.53/8.68          | ~ (r2_relset_1 @ sk_A_1 @ sk_A_1 @ 
% 8.53/8.68               (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ X0) @ 
% 8.53/8.68               (k6_partfun1 @ sk_A_1)))),
% 8.53/8.68      inference('demod', [status(thm)], ['14', '15', '16'])).
% 8.53/8.68  thf('18', plain,
% 8.53/8.68      ((((k2_relset_1 @ sk_B @ sk_A_1 @ sk_D) = (sk_A_1))
% 8.53/8.68        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))
% 8.53/8.68        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A_1)
% 8.53/8.68        | ~ (v1_funct_1 @ sk_D))),
% 8.53/8.68      inference('sup-', [status(thm)], ['11', '17'])).
% 8.53/8.68  thf('19', plain,
% 8.53/8.68      (((k2_relset_1 @ sk_B @ sk_A_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 8.53/8.68      inference('sup-', [status(thm)], ['3', '4'])).
% 8.53/8.68  thf('20', plain,
% 8.53/8.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 8.53/8.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.68  thf('21', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A_1)),
% 8.53/8.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.68  thf('22', plain, ((v1_funct_1 @ sk_D)),
% 8.53/8.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.68  thf('23', plain, (((k2_relat_1 @ sk_D) = (sk_A_1))),
% 8.53/8.68      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 8.53/8.68  thf('24', plain,
% 8.53/8.68      ((((sk_A_1) != (sk_A_1))
% 8.53/8.68        | ~ (v2_funct_1 @ sk_D)
% 8.53/8.68        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 8.53/8.68      inference('demod', [status(thm)], ['10', '23'])).
% 8.53/8.68  thf('25', plain,
% 8.53/8.68      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 8.53/8.68        | ~ (v2_funct_1 @ sk_D))),
% 8.53/8.68      inference('simplify', [status(thm)], ['24'])).
% 8.53/8.68  thf('26', plain,
% 8.53/8.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 8.53/8.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.68  thf('27', plain,
% 8.53/8.68      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 8.53/8.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.68  thf(redefinition_k1_partfun1, axiom,
% 8.53/8.68    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 8.53/8.68     ( ( ( v1_funct_1 @ E ) & 
% 8.53/8.68         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 8.53/8.68         ( v1_funct_1 @ F ) & 
% 8.53/8.68         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 8.53/8.68       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 8.53/8.68  thf('28', plain,
% 8.53/8.68      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 8.53/8.68         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 8.53/8.68          | ~ (v1_funct_1 @ X39)
% 8.53/8.68          | ~ (v1_funct_1 @ X42)
% 8.53/8.68          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 8.53/8.68          | ((k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42)
% 8.53/8.68              = (k5_relat_1 @ X39 @ X42)))),
% 8.53/8.68      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 8.53/8.68  thf('29', plain,
% 8.53/8.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.53/8.68         (((k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 8.53/8.68            = (k5_relat_1 @ sk_C @ X0))
% 8.53/8.68          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 8.53/8.68          | ~ (v1_funct_1 @ X0)
% 8.53/8.68          | ~ (v1_funct_1 @ sk_C))),
% 8.53/8.68      inference('sup-', [status(thm)], ['27', '28'])).
% 8.53/8.68  thf('30', plain, ((v1_funct_1 @ sk_C)),
% 8.53/8.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.68  thf('31', plain,
% 8.53/8.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.53/8.68         (((k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 8.53/8.68            = (k5_relat_1 @ sk_C @ X0))
% 8.53/8.68          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 8.53/8.68          | ~ (v1_funct_1 @ X0))),
% 8.53/8.68      inference('demod', [status(thm)], ['29', '30'])).
% 8.53/8.68  thf('32', plain,
% 8.53/8.68      ((~ (v1_funct_1 @ sk_D)
% 8.53/8.68        | ((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 8.53/8.68            = (k5_relat_1 @ sk_C @ sk_D)))),
% 8.53/8.68      inference('sup-', [status(thm)], ['26', '31'])).
% 8.53/8.68  thf('33', plain, ((v1_funct_1 @ sk_D)),
% 8.53/8.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.68  thf('34', plain,
% 8.53/8.68      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 8.53/8.68         = (k5_relat_1 @ sk_C @ sk_D))),
% 8.53/8.68      inference('demod', [status(thm)], ['32', '33'])).
% 8.53/8.68  thf('35', plain,
% 8.53/8.68      ((r2_relset_1 @ sk_A_1 @ sk_A_1 @ 
% 8.53/8.68        (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D) @ 
% 8.53/8.68        (k6_partfun1 @ sk_A_1))),
% 8.53/8.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.68  thf('36', plain,
% 8.53/8.68      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 8.53/8.68         = (k5_relat_1 @ sk_C @ sk_D))),
% 8.53/8.68      inference('demod', [status(thm)], ['32', '33'])).
% 8.53/8.68  thf('37', plain,
% 8.53/8.68      ((r2_relset_1 @ sk_A_1 @ sk_A_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 8.53/8.68        (k6_partfun1 @ sk_A_1))),
% 8.53/8.68      inference('demod', [status(thm)], ['35', '36'])).
% 8.53/8.68  thf('38', plain,
% 8.53/8.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 8.53/8.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.68  thf('39', plain,
% 8.53/8.68      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 8.53/8.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.68  thf(dt_k1_partfun1, axiom,
% 8.53/8.68    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 8.53/8.68     ( ( ( v1_funct_1 @ E ) & 
% 8.53/8.68         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 8.53/8.68         ( v1_funct_1 @ F ) & 
% 8.53/8.68         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 8.53/8.68       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 8.53/8.68         ( m1_subset_1 @
% 8.53/8.68           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 8.53/8.68           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 8.53/8.68  thf('40', plain,
% 8.53/8.68      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 8.53/8.68         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 8.53/8.68          | ~ (v1_funct_1 @ X31)
% 8.53/8.68          | ~ (v1_funct_1 @ X34)
% 8.53/8.68          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 8.53/8.68          | (m1_subset_1 @ (k1_partfun1 @ X32 @ X33 @ X35 @ X36 @ X31 @ X34) @ 
% 8.53/8.68             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X36))))),
% 8.53/8.68      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 8.53/8.68  thf('41', plain,
% 8.53/8.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.53/8.68         ((m1_subset_1 @ (k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 8.53/8.68           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ X0)))
% 8.53/8.68          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 8.53/8.68          | ~ (v1_funct_1 @ X1)
% 8.53/8.68          | ~ (v1_funct_1 @ sk_C))),
% 8.53/8.68      inference('sup-', [status(thm)], ['39', '40'])).
% 8.53/8.68  thf('42', plain, ((v1_funct_1 @ sk_C)),
% 8.53/8.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.68  thf('43', plain,
% 8.53/8.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.53/8.68         ((m1_subset_1 @ (k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 8.53/8.68           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ X0)))
% 8.53/8.68          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 8.53/8.68          | ~ (v1_funct_1 @ X1))),
% 8.53/8.68      inference('demod', [status(thm)], ['41', '42'])).
% 8.53/8.68  thf('44', plain,
% 8.53/8.68      ((~ (v1_funct_1 @ sk_D)
% 8.53/8.68        | (m1_subset_1 @ 
% 8.53/8.68           (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D) @ 
% 8.53/8.68           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_A_1))))),
% 8.53/8.68      inference('sup-', [status(thm)], ['38', '43'])).
% 8.53/8.68  thf('45', plain, ((v1_funct_1 @ sk_D)),
% 8.53/8.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.68  thf('46', plain,
% 8.53/8.68      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 8.53/8.68         = (k5_relat_1 @ sk_C @ sk_D))),
% 8.53/8.68      inference('demod', [status(thm)], ['32', '33'])).
% 8.53/8.68  thf('47', plain,
% 8.53/8.68      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 8.53/8.68        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_A_1)))),
% 8.53/8.68      inference('demod', [status(thm)], ['44', '45', '46'])).
% 8.53/8.68  thf(redefinition_r2_relset_1, axiom,
% 8.53/8.68    (![A:$i,B:$i,C:$i,D:$i]:
% 8.53/8.68     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 8.53/8.68         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 8.53/8.68       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 8.53/8.68  thf('48', plain,
% 8.53/8.68      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 8.53/8.68         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 8.53/8.68          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 8.53/8.68          | ((X27) = (X30))
% 8.53/8.68          | ~ (r2_relset_1 @ X28 @ X29 @ X27 @ X30))),
% 8.53/8.68      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 8.53/8.68  thf('49', plain,
% 8.53/8.68      (![X0 : $i]:
% 8.53/8.68         (~ (r2_relset_1 @ sk_A_1 @ sk_A_1 @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 8.53/8.68          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 8.53/8.68          | ~ (m1_subset_1 @ X0 @ 
% 8.53/8.68               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_A_1))))),
% 8.53/8.68      inference('sup-', [status(thm)], ['47', '48'])).
% 8.53/8.68  thf('50', plain,
% 8.53/8.68      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A_1) @ 
% 8.53/8.68           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_A_1)))
% 8.53/8.68        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A_1)))),
% 8.53/8.68      inference('sup-', [status(thm)], ['37', '49'])).
% 8.53/8.68  thf(dt_k6_partfun1, axiom,
% 8.53/8.68    (![A:$i]:
% 8.53/8.68     ( ( m1_subset_1 @
% 8.53/8.68         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 8.53/8.68       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 8.53/8.68  thf('51', plain,
% 8.53/8.68      (![X38 : $i]:
% 8.53/8.68         (m1_subset_1 @ (k6_partfun1 @ X38) @ 
% 8.53/8.68          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X38)))),
% 8.53/8.68      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 8.53/8.68  thf('52', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A_1))),
% 8.53/8.68      inference('demod', [status(thm)], ['50', '51'])).
% 8.53/8.68  thf('53', plain,
% 8.53/8.68      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 8.53/8.68         = (k6_partfun1 @ sk_A_1))),
% 8.53/8.68      inference('demod', [status(thm)], ['34', '52'])).
% 8.53/8.68  thf('54', plain,
% 8.53/8.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 8.53/8.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.68  thf(t30_funct_2, axiom,
% 8.53/8.68    (![A:$i,B:$i,C:$i,D:$i]:
% 8.53/8.68     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 8.53/8.68         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 8.53/8.68       ( ![E:$i]:
% 8.53/8.68         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 8.53/8.68             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 8.53/8.68           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 8.53/8.68               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 8.53/8.68             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 8.53/8.68               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 8.53/8.68  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 8.53/8.68  thf(zf_stmt_2, axiom,
% 8.53/8.68    (![C:$i,B:$i]:
% 8.53/8.68     ( ( zip_tseitin_1 @ C @ B ) =>
% 8.53/8.68       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 8.53/8.68  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 8.53/8.68  thf(zf_stmt_4, axiom,
% 8.53/8.68    (![E:$i,D:$i]:
% 8.53/8.68     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 8.53/8.68  thf(zf_stmt_5, axiom,
% 8.53/8.68    (![A:$i,B:$i,C:$i,D:$i]:
% 8.53/8.68     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 8.53/8.68         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 8.53/8.68       ( ![E:$i]:
% 8.53/8.68         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 8.53/8.68             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 8.53/8.68           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 8.53/8.68               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 8.53/8.68             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 8.53/8.68  thf('55', plain,
% 8.53/8.68      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i, X58 : $i]:
% 8.53/8.68         (~ (v1_funct_1 @ X54)
% 8.53/8.68          | ~ (v1_funct_2 @ X54 @ X55 @ X56)
% 8.53/8.68          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X56)))
% 8.53/8.69          | (zip_tseitin_0 @ X54 @ X57)
% 8.53/8.69          | ~ (v2_funct_1 @ (k1_partfun1 @ X58 @ X55 @ X55 @ X56 @ X57 @ X54))
% 8.53/8.69          | (zip_tseitin_1 @ X56 @ X55)
% 8.53/8.69          | ((k2_relset_1 @ X58 @ X55 @ X57) != (X55))
% 8.53/8.69          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X55)))
% 8.53/8.69          | ~ (v1_funct_2 @ X57 @ X58 @ X55)
% 8.53/8.69          | ~ (v1_funct_1 @ X57))),
% 8.53/8.69      inference('cnf', [status(esa)], [zf_stmt_5])).
% 8.53/8.69  thf('56', plain,
% 8.53/8.69      (![X0 : $i, X1 : $i]:
% 8.53/8.69         (~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 8.53/8.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 8.53/8.69          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 8.53/8.69          | (zip_tseitin_1 @ sk_A_1 @ sk_B)
% 8.53/8.69          | ~ (v2_funct_1 @ 
% 8.53/8.69               (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A_1 @ X0 @ sk_D))
% 8.53/8.69          | (zip_tseitin_0 @ sk_D @ X0)
% 8.53/8.69          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A_1)
% 8.53/8.69          | ~ (v1_funct_1 @ sk_D))),
% 8.53/8.69      inference('sup-', [status(thm)], ['54', '55'])).
% 8.53/8.69  thf('57', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A_1)),
% 8.53/8.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.69  thf('58', plain, ((v1_funct_1 @ sk_D)),
% 8.53/8.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.69  thf('59', plain,
% 8.53/8.69      (![X0 : $i, X1 : $i]:
% 8.53/8.69         (~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 8.53/8.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 8.53/8.69          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 8.53/8.69          | (zip_tseitin_1 @ sk_A_1 @ sk_B)
% 8.53/8.69          | ~ (v2_funct_1 @ 
% 8.53/8.69               (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A_1 @ X0 @ sk_D))
% 8.53/8.69          | (zip_tseitin_0 @ sk_D @ X0))),
% 8.53/8.69      inference('demod', [status(thm)], ['56', '57', '58'])).
% 8.53/8.69  thf('60', plain,
% 8.53/8.69      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A_1))
% 8.53/8.69        | (zip_tseitin_0 @ sk_D @ sk_C)
% 8.53/8.69        | (zip_tseitin_1 @ sk_A_1 @ sk_B)
% 8.53/8.69        | ((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) != (sk_B))
% 8.53/8.69        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))
% 8.53/8.69        | ~ (v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)
% 8.53/8.69        | ~ (v1_funct_1 @ sk_C))),
% 8.53/8.69      inference('sup-', [status(thm)], ['53', '59'])).
% 8.53/8.69  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 8.53/8.69  thf('61', plain, (![X17 : $i]: (v2_funct_1 @ (k6_relat_1 @ X17))),
% 8.53/8.69      inference('cnf', [status(esa)], [t52_funct_1])).
% 8.53/8.69  thf(redefinition_k6_partfun1, axiom,
% 8.53/8.69    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 8.53/8.69  thf('62', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 8.53/8.69      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 8.53/8.69  thf('63', plain, (![X17 : $i]: (v2_funct_1 @ (k6_partfun1 @ X17))),
% 8.53/8.69      inference('demod', [status(thm)], ['61', '62'])).
% 8.53/8.69  thf('64', plain, (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (sk_B))),
% 8.53/8.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.69  thf('65', plain,
% 8.53/8.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 8.53/8.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.69  thf('66', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)),
% 8.53/8.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.69  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 8.53/8.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.69  thf('68', plain,
% 8.53/8.69      (((zip_tseitin_0 @ sk_D @ sk_C)
% 8.53/8.69        | (zip_tseitin_1 @ sk_A_1 @ sk_B)
% 8.53/8.69        | ((sk_B) != (sk_B)))),
% 8.53/8.69      inference('demod', [status(thm)], ['60', '63', '64', '65', '66', '67'])).
% 8.53/8.69  thf('69', plain,
% 8.53/8.69      (((zip_tseitin_1 @ sk_A_1 @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 8.53/8.69      inference('simplify', [status(thm)], ['68'])).
% 8.53/8.69  thf('70', plain,
% 8.53/8.69      (![X52 : $i, X53 : $i]:
% 8.53/8.69         (((X52) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X52 @ X53))),
% 8.53/8.69      inference('cnf', [status(esa)], [zf_stmt_2])).
% 8.53/8.69  thf('71', plain,
% 8.53/8.69      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A_1) = (k1_xboole_0)))),
% 8.53/8.69      inference('sup-', [status(thm)], ['69', '70'])).
% 8.53/8.69  thf('72', plain, (((sk_A_1) != (k1_xboole_0))),
% 8.53/8.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.69  thf('73', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 8.53/8.69      inference('simplify_reflect-', [status(thm)], ['71', '72'])).
% 8.53/8.69  thf('74', plain,
% 8.53/8.69      (![X50 : $i, X51 : $i]:
% 8.53/8.69         ((v2_funct_1 @ X51) | ~ (zip_tseitin_0 @ X51 @ X50))),
% 8.53/8.69      inference('cnf', [status(esa)], [zf_stmt_4])).
% 8.53/8.69  thf('75', plain, ((v2_funct_1 @ sk_D)),
% 8.53/8.69      inference('sup-', [status(thm)], ['73', '74'])).
% 8.53/8.69  thf('76', plain,
% 8.53/8.69      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 8.53/8.69      inference('demod', [status(thm)], ['25', '75'])).
% 8.53/8.69  thf(t78_relat_1, axiom,
% 8.53/8.69    (![A:$i]:
% 8.53/8.69     ( ( v1_relat_1 @ A ) =>
% 8.53/8.69       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 8.53/8.69  thf('77', plain,
% 8.53/8.69      (![X13 : $i]:
% 8.53/8.69         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X13)) @ X13) = (X13))
% 8.53/8.69          | ~ (v1_relat_1 @ X13))),
% 8.53/8.69      inference('cnf', [status(esa)], [t78_relat_1])).
% 8.53/8.69  thf('78', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 8.53/8.69      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 8.53/8.69  thf('79', plain,
% 8.53/8.69      (![X13 : $i]:
% 8.53/8.69         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X13)) @ X13) = (X13))
% 8.53/8.69          | ~ (v1_relat_1 @ X13))),
% 8.53/8.69      inference('demod', [status(thm)], ['77', '78'])).
% 8.53/8.69  thf(dt_k2_funct_1, axiom,
% 8.53/8.69    (![A:$i]:
% 8.53/8.69     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 8.53/8.69       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 8.53/8.69         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 8.53/8.69  thf('80', plain,
% 8.53/8.69      (![X16 : $i]:
% 8.53/8.69         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 8.53/8.69          | ~ (v1_funct_1 @ X16)
% 8.53/8.69          | ~ (v1_relat_1 @ X16))),
% 8.53/8.69      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 8.53/8.69  thf(t55_relat_1, axiom,
% 8.53/8.69    (![A:$i]:
% 8.53/8.69     ( ( v1_relat_1 @ A ) =>
% 8.53/8.69       ( ![B:$i]:
% 8.53/8.69         ( ( v1_relat_1 @ B ) =>
% 8.53/8.69           ( ![C:$i]:
% 8.53/8.69             ( ( v1_relat_1 @ C ) =>
% 8.53/8.69               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 8.53/8.69                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 8.53/8.69  thf('81', plain,
% 8.53/8.69      (![X8 : $i, X9 : $i, X10 : $i]:
% 8.53/8.69         (~ (v1_relat_1 @ X8)
% 8.53/8.69          | ((k5_relat_1 @ (k5_relat_1 @ X9 @ X8) @ X10)
% 8.53/8.69              = (k5_relat_1 @ X9 @ (k5_relat_1 @ X8 @ X10)))
% 8.53/8.69          | ~ (v1_relat_1 @ X10)
% 8.53/8.69          | ~ (v1_relat_1 @ X9))),
% 8.53/8.69      inference('cnf', [status(esa)], [t55_relat_1])).
% 8.53/8.69  thf('82', plain,
% 8.53/8.69      (![X16 : $i]:
% 8.53/8.69         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 8.53/8.69          | ~ (v1_funct_1 @ X16)
% 8.53/8.69          | ~ (v1_relat_1 @ X16))),
% 8.53/8.69      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 8.53/8.69  thf(t55_funct_1, axiom,
% 8.53/8.69    (![A:$i]:
% 8.53/8.69     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 8.53/8.69       ( ( v2_funct_1 @ A ) =>
% 8.53/8.69         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 8.53/8.69           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 8.53/8.69  thf('83', plain,
% 8.53/8.69      (![X18 : $i]:
% 8.53/8.69         (~ (v2_funct_1 @ X18)
% 8.53/8.69          | ((k2_relat_1 @ X18) = (k1_relat_1 @ (k2_funct_1 @ X18)))
% 8.53/8.69          | ~ (v1_funct_1 @ X18)
% 8.53/8.69          | ~ (v1_relat_1 @ X18))),
% 8.53/8.69      inference('cnf', [status(esa)], [t55_funct_1])).
% 8.53/8.69  thf(dt_k2_subset_1, axiom,
% 8.53/8.69    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 8.53/8.69  thf('84', plain,
% 8.53/8.69      (![X4 : $i]: (m1_subset_1 @ (k2_subset_1 @ X4) @ (k1_zfmisc_1 @ X4))),
% 8.53/8.69      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 8.53/8.69  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 8.53/8.69  thf('85', plain, (![X3 : $i]: ((k2_subset_1 @ X3) = (X3))),
% 8.53/8.69      inference('cnf', [status(esa)], [d4_subset_1])).
% 8.53/8.69  thf('86', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 8.53/8.69      inference('demod', [status(thm)], ['84', '85'])).
% 8.53/8.69  thf(t3_subset, axiom,
% 8.53/8.69    (![A:$i,B:$i]:
% 8.53/8.69     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 8.53/8.69  thf('87', plain,
% 8.53/8.69      (![X5 : $i, X6 : $i]:
% 8.53/8.69         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 8.53/8.69      inference('cnf', [status(esa)], [t3_subset])).
% 8.53/8.69  thf('88', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 8.53/8.69      inference('sup-', [status(thm)], ['86', '87'])).
% 8.53/8.69  thf(t79_relat_1, axiom,
% 8.53/8.69    (![A:$i,B:$i]:
% 8.53/8.69     ( ( v1_relat_1 @ B ) =>
% 8.53/8.69       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 8.53/8.69         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 8.53/8.69  thf('89', plain,
% 8.53/8.69      (![X14 : $i, X15 : $i]:
% 8.53/8.69         (~ (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 8.53/8.69          | ((k5_relat_1 @ X14 @ (k6_relat_1 @ X15)) = (X14))
% 8.53/8.69          | ~ (v1_relat_1 @ X14))),
% 8.53/8.69      inference('cnf', [status(esa)], [t79_relat_1])).
% 8.53/8.69  thf('90', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 8.53/8.69      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 8.53/8.69  thf('91', plain,
% 8.53/8.69      (![X14 : $i, X15 : $i]:
% 8.53/8.69         (~ (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 8.53/8.69          | ((k5_relat_1 @ X14 @ (k6_partfun1 @ X15)) = (X14))
% 8.53/8.69          | ~ (v1_relat_1 @ X14))),
% 8.53/8.69      inference('demod', [status(thm)], ['89', '90'])).
% 8.53/8.69  thf('92', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (~ (v1_relat_1 @ X0)
% 8.53/8.69          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) = (X0)))),
% 8.53/8.69      inference('sup-', [status(thm)], ['88', '91'])).
% 8.53/8.69  thf('93', plain,
% 8.53/8.69      (![X13 : $i]:
% 8.53/8.69         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X13)) @ X13) = (X13))
% 8.53/8.69          | ~ (v1_relat_1 @ X13))),
% 8.53/8.69      inference('demod', [status(thm)], ['77', '78'])).
% 8.53/8.69  thf('94', plain,
% 8.53/8.69      (![X8 : $i, X9 : $i, X10 : $i]:
% 8.53/8.69         (~ (v1_relat_1 @ X8)
% 8.53/8.69          | ((k5_relat_1 @ (k5_relat_1 @ X9 @ X8) @ X10)
% 8.53/8.69              = (k5_relat_1 @ X9 @ (k5_relat_1 @ X8 @ X10)))
% 8.53/8.69          | ~ (v1_relat_1 @ X10)
% 8.53/8.69          | ~ (v1_relat_1 @ X9))),
% 8.53/8.69      inference('cnf', [status(esa)], [t55_relat_1])).
% 8.53/8.69  thf('95', plain,
% 8.53/8.69      (![X0 : $i, X1 : $i]:
% 8.53/8.69         (((k5_relat_1 @ X0 @ X1)
% 8.53/8.69            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 8.53/8.69               (k5_relat_1 @ X0 @ X1)))
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 8.53/8.69          | ~ (v1_relat_1 @ X1)
% 8.53/8.69          | ~ (v1_relat_1 @ X0))),
% 8.53/8.69      inference('sup+', [status(thm)], ['93', '94'])).
% 8.53/8.69  thf('96', plain,
% 8.53/8.69      (![X38 : $i]:
% 8.53/8.69         (m1_subset_1 @ (k6_partfun1 @ X38) @ 
% 8.53/8.69          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X38)))),
% 8.53/8.69      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 8.53/8.69  thf(cc1_relset_1, axiom,
% 8.53/8.69    (![A:$i,B:$i,C:$i]:
% 8.53/8.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.53/8.69       ( v1_relat_1 @ C ) ))).
% 8.53/8.69  thf('97', plain,
% 8.53/8.69      (![X21 : $i, X22 : $i, X23 : $i]:
% 8.53/8.69         ((v1_relat_1 @ X21)
% 8.53/8.69          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 8.53/8.69      inference('cnf', [status(esa)], [cc1_relset_1])).
% 8.53/8.69  thf('98', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 8.53/8.69      inference('sup-', [status(thm)], ['96', '97'])).
% 8.53/8.69  thf('99', plain,
% 8.53/8.69      (![X0 : $i, X1 : $i]:
% 8.53/8.69         (((k5_relat_1 @ X0 @ X1)
% 8.53/8.69            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 8.53/8.69               (k5_relat_1 @ X0 @ X1)))
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X1)
% 8.53/8.69          | ~ (v1_relat_1 @ X0))),
% 8.53/8.69      inference('demod', [status(thm)], ['95', '98'])).
% 8.53/8.69  thf('100', plain,
% 8.53/8.69      (![X0 : $i, X1 : $i]:
% 8.53/8.69         (~ (v1_relat_1 @ X1)
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ((k5_relat_1 @ X0 @ X1)
% 8.53/8.69              = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 8.53/8.69                 (k5_relat_1 @ X0 @ X1))))),
% 8.53/8.69      inference('simplify', [status(thm)], ['99'])).
% 8.53/8.69  thf('101', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 8.53/8.69            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0))))),
% 8.53/8.69      inference('sup+', [status(thm)], ['92', '100'])).
% 8.53/8.69  thf('102', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 8.53/8.69      inference('sup-', [status(thm)], ['96', '97'])).
% 8.53/8.69  thf('103', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 8.53/8.69            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0))),
% 8.53/8.69      inference('demod', [status(thm)], ['101', '102'])).
% 8.53/8.69  thf('104', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (~ (v1_relat_1 @ X0)
% 8.53/8.69          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 8.53/8.69              = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0)))),
% 8.53/8.69      inference('simplify', [status(thm)], ['103'])).
% 8.53/8.69  thf('105', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (((k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 8.53/8.69            (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 8.53/8.69            = (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 8.53/8.69               (k2_funct_1 @ X0)))
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 8.53/8.69      inference('sup+', [status(thm)], ['83', '104'])).
% 8.53/8.69  thf('106', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 8.53/8.69              (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 8.53/8.69              = (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 8.53/8.69                 (k2_funct_1 @ X0))))),
% 8.53/8.69      inference('sup-', [status(thm)], ['82', '105'])).
% 8.53/8.69  thf('107', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (((k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 8.53/8.69            (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 8.53/8.69            = (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 8.53/8.69               (k2_funct_1 @ X0)))
% 8.53/8.69          | ~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0))),
% 8.53/8.69      inference('simplify', [status(thm)], ['106'])).
% 8.53/8.69  thf('108', plain,
% 8.53/8.69      (![X16 : $i]:
% 8.53/8.69         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 8.53/8.69          | ~ (v1_funct_1 @ X16)
% 8.53/8.69          | ~ (v1_relat_1 @ X16))),
% 8.53/8.69      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 8.53/8.69  thf(t61_funct_1, axiom,
% 8.53/8.69    (![A:$i]:
% 8.53/8.69     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 8.53/8.69       ( ( v2_funct_1 @ A ) =>
% 8.53/8.69         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 8.53/8.69             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 8.53/8.69           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 8.53/8.69             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 8.53/8.69  thf('109', plain,
% 8.53/8.69      (![X20 : $i]:
% 8.53/8.69         (~ (v2_funct_1 @ X20)
% 8.53/8.69          | ((k5_relat_1 @ (k2_funct_1 @ X20) @ X20)
% 8.53/8.69              = (k6_relat_1 @ (k2_relat_1 @ X20)))
% 8.53/8.69          | ~ (v1_funct_1 @ X20)
% 8.53/8.69          | ~ (v1_relat_1 @ X20))),
% 8.53/8.69      inference('cnf', [status(esa)], [t61_funct_1])).
% 8.53/8.69  thf('110', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 8.53/8.69      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 8.53/8.69  thf('111', plain,
% 8.53/8.69      (![X20 : $i]:
% 8.53/8.69         (~ (v2_funct_1 @ X20)
% 8.53/8.69          | ((k5_relat_1 @ (k2_funct_1 @ X20) @ X20)
% 8.53/8.69              = (k6_partfun1 @ (k2_relat_1 @ X20)))
% 8.53/8.69          | ~ (v1_funct_1 @ X20)
% 8.53/8.69          | ~ (v1_relat_1 @ X20))),
% 8.53/8.69      inference('demod', [status(thm)], ['109', '110'])).
% 8.53/8.69  thf('112', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (~ (v1_relat_1 @ X0)
% 8.53/8.69          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 8.53/8.69              = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0)))),
% 8.53/8.69      inference('simplify', [status(thm)], ['103'])).
% 8.53/8.69  thf('113', plain,
% 8.53/8.69      (![X8 : $i, X9 : $i, X10 : $i]:
% 8.53/8.69         (~ (v1_relat_1 @ X8)
% 8.53/8.69          | ((k5_relat_1 @ (k5_relat_1 @ X9 @ X8) @ X10)
% 8.53/8.69              = (k5_relat_1 @ X9 @ (k5_relat_1 @ X8 @ X10)))
% 8.53/8.69          | ~ (v1_relat_1 @ X10)
% 8.53/8.69          | ~ (v1_relat_1 @ X9))),
% 8.53/8.69      inference('cnf', [status(esa)], [t55_relat_1])).
% 8.53/8.69  thf('114', plain,
% 8.53/8.69      (![X0 : $i, X1 : $i]:
% 8.53/8.69         (((k5_relat_1 @ 
% 8.53/8.69            (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) @ X1)
% 8.53/8.69            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 8.53/8.69               (k5_relat_1 @ X0 @ X1)))
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 8.53/8.69          | ~ (v1_relat_1 @ X1)
% 8.53/8.69          | ~ (v1_relat_1 @ X0))),
% 8.53/8.69      inference('sup+', [status(thm)], ['112', '113'])).
% 8.53/8.69  thf('115', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 8.53/8.69      inference('sup-', [status(thm)], ['96', '97'])).
% 8.53/8.69  thf('116', plain,
% 8.53/8.69      (![X0 : $i, X1 : $i]:
% 8.53/8.69         (((k5_relat_1 @ 
% 8.53/8.69            (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) @ X1)
% 8.53/8.69            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 8.53/8.69               (k5_relat_1 @ X0 @ X1)))
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X1)
% 8.53/8.69          | ~ (v1_relat_1 @ X0))),
% 8.53/8.69      inference('demod', [status(thm)], ['114', '115'])).
% 8.53/8.69  thf('117', plain,
% 8.53/8.69      (![X0 : $i, X1 : $i]:
% 8.53/8.69         (~ (v1_relat_1 @ X1)
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ((k5_relat_1 @ 
% 8.53/8.69              (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) @ X1)
% 8.53/8.69              = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 8.53/8.69                 (k5_relat_1 @ X0 @ X1))))),
% 8.53/8.69      inference('simplify', [status(thm)], ['116'])).
% 8.53/8.69  thf('118', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (((k5_relat_1 @ 
% 8.53/8.69            (k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 8.53/8.69             (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))) @ 
% 8.53/8.69            X0)
% 8.53/8.69            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))) @ 
% 8.53/8.69               (k6_partfun1 @ (k2_relat_1 @ X0))))
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 8.53/8.69          | ~ (v1_relat_1 @ X0))),
% 8.53/8.69      inference('sup+', [status(thm)], ['111', '117'])).
% 8.53/8.69  thf('119', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 8.53/8.69          | ~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ((k5_relat_1 @ 
% 8.53/8.69              (k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 8.53/8.69               (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))) @ 
% 8.53/8.69              X0)
% 8.53/8.69              = (k5_relat_1 @ 
% 8.53/8.69                 (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))) @ 
% 8.53/8.69                 (k6_partfun1 @ (k2_relat_1 @ X0)))))),
% 8.53/8.69      inference('simplify', [status(thm)], ['118'])).
% 8.53/8.69  thf('120', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ((k5_relat_1 @ 
% 8.53/8.69              (k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 8.53/8.69               (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))) @ 
% 8.53/8.69              X0)
% 8.53/8.69              = (k5_relat_1 @ 
% 8.53/8.69                 (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))) @ 
% 8.53/8.69                 (k6_partfun1 @ (k2_relat_1 @ X0))))
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v2_funct_1 @ X0))),
% 8.53/8.69      inference('sup-', [status(thm)], ['108', '119'])).
% 8.53/8.69  thf('121', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (~ (v2_funct_1 @ X0)
% 8.53/8.69          | ((k5_relat_1 @ 
% 8.53/8.69              (k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 8.53/8.69               (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))) @ 
% 8.53/8.69              X0)
% 8.53/8.69              = (k5_relat_1 @ 
% 8.53/8.69                 (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))) @ 
% 8.53/8.69                 (k6_partfun1 @ (k2_relat_1 @ X0))))
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0))),
% 8.53/8.69      inference('simplify', [status(thm)], ['120'])).
% 8.53/8.69  thf('122', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (((k5_relat_1 @ 
% 8.53/8.69            (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0)) @ 
% 8.53/8.69            X0)
% 8.53/8.69            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))) @ 
% 8.53/8.69               (k6_partfun1 @ (k2_relat_1 @ X0))))
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v2_funct_1 @ X0))),
% 8.53/8.69      inference('sup+', [status(thm)], ['107', '121'])).
% 8.53/8.69  thf('123', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ((k5_relat_1 @ 
% 8.53/8.69              (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 8.53/8.69               (k2_funct_1 @ X0)) @ 
% 8.53/8.69              X0)
% 8.53/8.69              = (k5_relat_1 @ 
% 8.53/8.69                 (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))) @ 
% 8.53/8.69                 (k6_partfun1 @ (k2_relat_1 @ X0)))))),
% 8.53/8.69      inference('simplify', [status(thm)], ['122'])).
% 8.53/8.69  thf('124', plain,
% 8.53/8.69      (![X18 : $i]:
% 8.53/8.69         (~ (v2_funct_1 @ X18)
% 8.53/8.69          | ((k2_relat_1 @ X18) = (k1_relat_1 @ (k2_funct_1 @ X18)))
% 8.53/8.69          | ~ (v1_funct_1 @ X18)
% 8.53/8.69          | ~ (v1_relat_1 @ X18))),
% 8.53/8.69      inference('cnf', [status(esa)], [t55_funct_1])).
% 8.53/8.69  thf('125', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ((k5_relat_1 @ 
% 8.53/8.69              (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 8.53/8.69               (k2_funct_1 @ X0)) @ 
% 8.53/8.69              X0)
% 8.53/8.69              = (k5_relat_1 @ 
% 8.53/8.69                 (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))) @ 
% 8.53/8.69                 (k6_partfun1 @ (k2_relat_1 @ X0)))))),
% 8.53/8.69      inference('simplify', [status(thm)], ['122'])).
% 8.53/8.69  thf('126', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (((k5_relat_1 @ 
% 8.53/8.69            (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0)) @ 
% 8.53/8.69            X0)
% 8.53/8.69            = (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 8.53/8.69               (k6_partfun1 @ (k2_relat_1 @ X0))))
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v2_funct_1 @ X0))),
% 8.53/8.69      inference('sup+', [status(thm)], ['124', '125'])).
% 8.53/8.69  thf(t71_relat_1, axiom,
% 8.53/8.69    (![A:$i]:
% 8.53/8.69     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 8.53/8.69       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 8.53/8.69  thf('127', plain, (![X11 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 8.53/8.69      inference('cnf', [status(esa)], [t71_relat_1])).
% 8.53/8.69  thf('128', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 8.53/8.69      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 8.53/8.69  thf('129', plain,
% 8.53/8.69      (![X11 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X11)) = (X11))),
% 8.53/8.69      inference('demod', [status(thm)], ['127', '128'])).
% 8.53/8.69  thf('130', plain,
% 8.53/8.69      (![X13 : $i]:
% 8.53/8.69         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X13)) @ X13) = (X13))
% 8.53/8.69          | ~ (v1_relat_1 @ X13))),
% 8.53/8.69      inference('demod', [status(thm)], ['77', '78'])).
% 8.53/8.69  thf('131', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 8.53/8.69            = (k6_partfun1 @ X0))
% 8.53/8.69          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 8.53/8.69      inference('sup+', [status(thm)], ['129', '130'])).
% 8.53/8.69  thf('132', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 8.53/8.69      inference('sup-', [status(thm)], ['96', '97'])).
% 8.53/8.69  thf('133', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 8.53/8.69           = (k6_partfun1 @ X0))),
% 8.53/8.69      inference('demod', [status(thm)], ['131', '132'])).
% 8.53/8.69  thf('134', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (((k5_relat_1 @ 
% 8.53/8.69            (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0)) @ 
% 8.53/8.69            X0) = (k6_partfun1 @ (k2_relat_1 @ X0)))
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v2_funct_1 @ X0))),
% 8.53/8.69      inference('demod', [status(thm)], ['126', '133'])).
% 8.53/8.69  thf('135', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ((k5_relat_1 @ 
% 8.53/8.69              (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 8.53/8.69               (k2_funct_1 @ X0)) @ 
% 8.53/8.69              X0) = (k6_partfun1 @ (k2_relat_1 @ X0))))),
% 8.53/8.69      inference('simplify', [status(thm)], ['134'])).
% 8.53/8.69  thf('136', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))) @ 
% 8.53/8.69            (k6_partfun1 @ (k2_relat_1 @ X0)))
% 8.53/8.69            = (k6_partfun1 @ (k2_relat_1 @ X0)))
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v2_funct_1 @ X0))),
% 8.53/8.69      inference('sup+', [status(thm)], ['123', '135'])).
% 8.53/8.69  thf('137', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))) @ 
% 8.53/8.69              (k6_partfun1 @ (k2_relat_1 @ X0)))
% 8.53/8.69              = (k6_partfun1 @ (k2_relat_1 @ X0))))),
% 8.53/8.69      inference('simplify', [status(thm)], ['136'])).
% 8.53/8.69  thf('138', plain,
% 8.53/8.69      (![X18 : $i]:
% 8.53/8.69         (~ (v2_funct_1 @ X18)
% 8.53/8.69          | ((k1_relat_1 @ X18) = (k2_relat_1 @ (k2_funct_1 @ X18)))
% 8.53/8.69          | ~ (v1_funct_1 @ X18)
% 8.53/8.69          | ~ (v1_relat_1 @ X18))),
% 8.53/8.69      inference('cnf', [status(esa)], [t55_funct_1])).
% 8.53/8.69  thf('139', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (~ (v2_funct_1 @ X0)
% 8.53/8.69          | ((k5_relat_1 @ 
% 8.53/8.69              (k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 8.53/8.69               (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))) @ 
% 8.53/8.69              X0)
% 8.53/8.69              = (k5_relat_1 @ 
% 8.53/8.69                 (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))) @ 
% 8.53/8.69                 (k6_partfun1 @ (k2_relat_1 @ X0))))
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0))),
% 8.53/8.69      inference('simplify', [status(thm)], ['120'])).
% 8.53/8.69  thf('140', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (((k5_relat_1 @ 
% 8.53/8.69            (k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0))) @ 
% 8.53/8.69            X0)
% 8.53/8.69            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))) @ 
% 8.53/8.69               (k6_partfun1 @ (k2_relat_1 @ X0))))
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v2_funct_1 @ X0))),
% 8.53/8.69      inference('sup+', [status(thm)], ['138', '139'])).
% 8.53/8.69  thf('141', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ((k5_relat_1 @ 
% 8.53/8.69              (k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 8.53/8.69               (k6_partfun1 @ (k1_relat_1 @ X0))) @ 
% 8.53/8.69              X0)
% 8.53/8.69              = (k5_relat_1 @ 
% 8.53/8.69                 (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))) @ 
% 8.53/8.69                 (k6_partfun1 @ (k2_relat_1 @ X0)))))),
% 8.53/8.69      inference('simplify', [status(thm)], ['140'])).
% 8.53/8.69  thf('142', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (((k5_relat_1 @ 
% 8.53/8.69            (k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0))) @ 
% 8.53/8.69            X0) = (k6_partfun1 @ (k2_relat_1 @ X0)))
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v2_funct_1 @ X0))),
% 8.53/8.69      inference('sup+', [status(thm)], ['137', '141'])).
% 8.53/8.69  thf('143', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ((k5_relat_1 @ 
% 8.53/8.69              (k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 8.53/8.69               (k6_partfun1 @ (k1_relat_1 @ X0))) @ 
% 8.53/8.69              X0) = (k6_partfun1 @ (k2_relat_1 @ X0))))),
% 8.53/8.69      inference('simplify', [status(thm)], ['142'])).
% 8.53/8.69  thf('144', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (((k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 8.53/8.69            (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 8.53/8.69            = (k6_partfun1 @ (k2_relat_1 @ X0)))
% 8.53/8.69          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v2_funct_1 @ X0))),
% 8.53/8.69      inference('sup+', [status(thm)], ['81', '143'])).
% 8.53/8.69  thf('145', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 8.53/8.69      inference('sup-', [status(thm)], ['96', '97'])).
% 8.53/8.69  thf('146', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (((k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 8.53/8.69            (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 8.53/8.69            = (k6_partfun1 @ (k2_relat_1 @ X0)))
% 8.53/8.69          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v2_funct_1 @ X0))),
% 8.53/8.69      inference('demod', [status(thm)], ['144', '145'])).
% 8.53/8.69  thf('147', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 8.53/8.69          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 8.53/8.69              (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 8.53/8.69              = (k6_partfun1 @ (k2_relat_1 @ X0))))),
% 8.53/8.69      inference('simplify', [status(thm)], ['146'])).
% 8.53/8.69  thf('148', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 8.53/8.69              (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 8.53/8.69              = (k6_partfun1 @ (k2_relat_1 @ X0)))
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v2_funct_1 @ X0))),
% 8.53/8.69      inference('sup-', [status(thm)], ['80', '147'])).
% 8.53/8.69  thf('149', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (~ (v2_funct_1 @ X0)
% 8.53/8.69          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 8.53/8.69              (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 8.53/8.69              = (k6_partfun1 @ (k2_relat_1 @ X0)))
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0))),
% 8.53/8.69      inference('simplify', [status(thm)], ['148'])).
% 8.53/8.69  thf('150', plain,
% 8.53/8.69      (![X16 : $i]:
% 8.53/8.69         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 8.53/8.69          | ~ (v1_funct_1 @ X16)
% 8.53/8.69          | ~ (v1_relat_1 @ X16))),
% 8.53/8.69      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 8.53/8.69  thf('151', plain,
% 8.53/8.69      (![X20 : $i]:
% 8.53/8.69         (~ (v2_funct_1 @ X20)
% 8.53/8.69          | ((k5_relat_1 @ X20 @ (k2_funct_1 @ X20))
% 8.53/8.69              = (k6_relat_1 @ (k1_relat_1 @ X20)))
% 8.53/8.69          | ~ (v1_funct_1 @ X20)
% 8.53/8.69          | ~ (v1_relat_1 @ X20))),
% 8.53/8.69      inference('cnf', [status(esa)], [t61_funct_1])).
% 8.53/8.69  thf('152', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 8.53/8.69      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 8.53/8.69  thf('153', plain,
% 8.53/8.69      (![X20 : $i]:
% 8.53/8.69         (~ (v2_funct_1 @ X20)
% 8.53/8.69          | ((k5_relat_1 @ X20 @ (k2_funct_1 @ X20))
% 8.53/8.69              = (k6_partfun1 @ (k1_relat_1 @ X20)))
% 8.53/8.69          | ~ (v1_funct_1 @ X20)
% 8.53/8.69          | ~ (v1_relat_1 @ X20))),
% 8.53/8.69      inference('demod', [status(thm)], ['151', '152'])).
% 8.53/8.69  thf('154', plain,
% 8.53/8.69      (![X8 : $i, X9 : $i, X10 : $i]:
% 8.53/8.69         (~ (v1_relat_1 @ X8)
% 8.53/8.69          | ((k5_relat_1 @ (k5_relat_1 @ X9 @ X8) @ X10)
% 8.53/8.69              = (k5_relat_1 @ X9 @ (k5_relat_1 @ X8 @ X10)))
% 8.53/8.69          | ~ (v1_relat_1 @ X10)
% 8.53/8.69          | ~ (v1_relat_1 @ X9))),
% 8.53/8.69      inference('cnf', [status(esa)], [t55_relat_1])).
% 8.53/8.69  thf('155', plain,
% 8.53/8.69      (![X0 : $i, X1 : $i]:
% 8.53/8.69         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X1)
% 8.53/8.69            = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1)))
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X1)
% 8.53/8.69          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 8.53/8.69      inference('sup+', [status(thm)], ['153', '154'])).
% 8.53/8.69  thf('156', plain,
% 8.53/8.69      (![X0 : $i, X1 : $i]:
% 8.53/8.69         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 8.53/8.69          | ~ (v1_relat_1 @ X1)
% 8.53/8.69          | ~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X1)
% 8.53/8.69              = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1))))),
% 8.53/8.69      inference('simplify', [status(thm)], ['155'])).
% 8.53/8.69  thf('157', plain,
% 8.53/8.69      (![X0 : $i, X1 : $i]:
% 8.53/8.69         (~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X1)
% 8.53/8.69              = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1)))
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X1))),
% 8.53/8.69      inference('sup-', [status(thm)], ['150', '156'])).
% 8.53/8.69  thf('158', plain,
% 8.53/8.69      (![X0 : $i, X1 : $i]:
% 8.53/8.69         (~ (v1_relat_1 @ X1)
% 8.53/8.69          | ~ (v2_funct_1 @ X0)
% 8.53/8.69          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X1)
% 8.53/8.69              = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1)))
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0))),
% 8.53/8.69      inference('simplify', [status(thm)], ['157'])).
% 8.53/8.69  thf('159', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 8.53/8.69            (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 8.53/8.69            = (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ 
% 8.53/8.69               (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0)))),
% 8.53/8.69      inference('sup+', [status(thm)], ['149', '158'])).
% 8.53/8.69  thf('160', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (~ (v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 8.53/8.69          | ~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 8.53/8.69              (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 8.53/8.69              = (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))))),
% 8.53/8.69      inference('simplify', [status(thm)], ['159'])).
% 8.53/8.69  thf('161', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 8.53/8.69              (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 8.53/8.69              = (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v2_funct_1 @ X0))),
% 8.53/8.69      inference('sup-', [status(thm)], ['79', '160'])).
% 8.53/8.69  thf('162', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 8.53/8.69              (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 8.53/8.69              = (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))
% 8.53/8.69          | ~ (v1_relat_1 @ X0))),
% 8.53/8.69      inference('simplify', [status(thm)], ['161'])).
% 8.53/8.69  thf('163', plain,
% 8.53/8.69      (![X18 : $i]:
% 8.53/8.69         (~ (v2_funct_1 @ X18)
% 8.53/8.69          | ((k1_relat_1 @ X18) = (k2_relat_1 @ (k2_funct_1 @ X18)))
% 8.53/8.69          | ~ (v1_funct_1 @ X18)
% 8.53/8.69          | ~ (v1_relat_1 @ X18))),
% 8.53/8.69      inference('cnf', [status(esa)], [t55_funct_1])).
% 8.53/8.69  thf('164', plain,
% 8.53/8.69      (![X16 : $i]:
% 8.53/8.69         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 8.53/8.69          | ~ (v1_funct_1 @ X16)
% 8.53/8.69          | ~ (v1_relat_1 @ X16))),
% 8.53/8.69      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 8.53/8.69  thf('165', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (~ (v1_relat_1 @ X0)
% 8.53/8.69          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) = (X0)))),
% 8.53/8.69      inference('sup-', [status(thm)], ['88', '91'])).
% 8.53/8.69  thf('166', plain,
% 8.53/8.69      (![X0 : $i, X1 : $i]:
% 8.53/8.69         (~ (v1_relat_1 @ X1)
% 8.53/8.69          | ~ (v2_funct_1 @ X0)
% 8.53/8.69          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X1)
% 8.53/8.69              = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1)))
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0))),
% 8.53/8.69      inference('simplify', [status(thm)], ['157'])).
% 8.53/8.69  thf('167', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 8.53/8.69            (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 8.53/8.69            = (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 8.53/8.69          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 8.53/8.69      inference('sup+', [status(thm)], ['165', '166'])).
% 8.53/8.69  thf('168', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 8.53/8.69      inference('sup-', [status(thm)], ['96', '97'])).
% 8.53/8.69  thf('169', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 8.53/8.69            (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 8.53/8.69            = (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 8.53/8.69          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v2_funct_1 @ X0))),
% 8.53/8.69      inference('demod', [status(thm)], ['167', '168'])).
% 8.53/8.69  thf('170', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 8.53/8.69              (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 8.53/8.69              = (k5_relat_1 @ X0 @ (k2_funct_1 @ X0))))),
% 8.53/8.69      inference('sup-', [status(thm)], ['164', '169'])).
% 8.53/8.69  thf('171', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 8.53/8.69            (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 8.53/8.69            = (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 8.53/8.69          | ~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0))),
% 8.53/8.69      inference('simplify', [status(thm)], ['170'])).
% 8.53/8.69  thf('172', plain,
% 8.53/8.69      (![X8 : $i, X9 : $i, X10 : $i]:
% 8.53/8.69         (~ (v1_relat_1 @ X8)
% 8.53/8.69          | ((k5_relat_1 @ (k5_relat_1 @ X9 @ X8) @ X10)
% 8.53/8.69              = (k5_relat_1 @ X9 @ (k5_relat_1 @ X8 @ X10)))
% 8.53/8.69          | ~ (v1_relat_1 @ X10)
% 8.53/8.69          | ~ (v1_relat_1 @ X9))),
% 8.53/8.69      inference('cnf', [status(esa)], [t55_relat_1])).
% 8.53/8.69  thf('173', plain,
% 8.53/8.69      (![X0 : $i, X1 : $i]:
% 8.53/8.69         (((k5_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ X1)
% 8.53/8.69            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 8.53/8.69               (k5_relat_1 @ 
% 8.53/8.69                (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))) @ X1)))
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 8.53/8.69          | ~ (v1_relat_1 @ X1)
% 8.53/8.69          | ~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 8.53/8.69      inference('sup+', [status(thm)], ['171', '172'])).
% 8.53/8.69  thf('174', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 8.53/8.69      inference('sup-', [status(thm)], ['96', '97'])).
% 8.53/8.69  thf('175', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 8.53/8.69      inference('sup-', [status(thm)], ['96', '97'])).
% 8.53/8.69  thf('176', plain,
% 8.53/8.69      (![X0 : $i, X1 : $i]:
% 8.53/8.69         (((k5_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ X1)
% 8.53/8.69            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 8.53/8.69               (k5_relat_1 @ 
% 8.53/8.69                (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))) @ X1)))
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X1))),
% 8.53/8.69      inference('demod', [status(thm)], ['173', '174', '175'])).
% 8.53/8.69  thf('177', plain,
% 8.53/8.69      (![X0 : $i, X1 : $i]:
% 8.53/8.69         (((k5_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ X1)
% 8.53/8.69            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 8.53/8.69               (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X1)))
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X1)
% 8.53/8.69          | ~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0))),
% 8.53/8.69      inference('sup+', [status(thm)], ['163', '176'])).
% 8.53/8.69  thf('178', plain,
% 8.53/8.69      (![X0 : $i, X1 : $i]:
% 8.53/8.69         (~ (v1_relat_1 @ X1)
% 8.53/8.69          | ~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ((k5_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ X1)
% 8.53/8.69              = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 8.53/8.69                 (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X1))))),
% 8.53/8.69      inference('simplify', [status(thm)], ['177'])).
% 8.53/8.69  thf('179', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (((k5_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ X0)
% 8.53/8.69            = (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0))),
% 8.53/8.69      inference('sup+', [status(thm)], ['162', '178'])).
% 8.53/8.69  thf('180', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ((k5_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ X0)
% 8.53/8.69              = (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))))),
% 8.53/8.69      inference('simplify', [status(thm)], ['179'])).
% 8.53/8.69  thf('181', plain,
% 8.53/8.69      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 8.53/8.69          = (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))))
% 8.53/8.69        | ~ (v1_relat_1 @ sk_D)
% 8.53/8.69        | ~ (v1_funct_1 @ sk_D)
% 8.53/8.69        | ~ (v2_funct_1 @ sk_D))),
% 8.53/8.69      inference('sup+', [status(thm)], ['76', '180'])).
% 8.53/8.69  thf('182', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A_1))),
% 8.53/8.69      inference('demod', [status(thm)], ['50', '51'])).
% 8.53/8.69  thf('183', plain,
% 8.53/8.69      (![X16 : $i]:
% 8.53/8.69         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 8.53/8.69          | ~ (v1_funct_1 @ X16)
% 8.53/8.69          | ~ (v1_relat_1 @ X16))),
% 8.53/8.69      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 8.53/8.69  thf('184', plain,
% 8.53/8.69      (![X20 : $i]:
% 8.53/8.69         (~ (v2_funct_1 @ X20)
% 8.53/8.69          | ((k5_relat_1 @ (k2_funct_1 @ X20) @ X20)
% 8.53/8.69              = (k6_partfun1 @ (k2_relat_1 @ X20)))
% 8.53/8.69          | ~ (v1_funct_1 @ X20)
% 8.53/8.69          | ~ (v1_relat_1 @ X20))),
% 8.53/8.69      inference('demod', [status(thm)], ['109', '110'])).
% 8.53/8.69  thf('185', plain,
% 8.53/8.69      (![X8 : $i, X9 : $i, X10 : $i]:
% 8.53/8.69         (~ (v1_relat_1 @ X8)
% 8.53/8.69          | ((k5_relat_1 @ (k5_relat_1 @ X9 @ X8) @ X10)
% 8.53/8.69              = (k5_relat_1 @ X9 @ (k5_relat_1 @ X8 @ X10)))
% 8.53/8.69          | ~ (v1_relat_1 @ X10)
% 8.53/8.69          | ~ (v1_relat_1 @ X9))),
% 8.53/8.69      inference('cnf', [status(esa)], [t55_relat_1])).
% 8.53/8.69  thf('186', plain,
% 8.53/8.69      (![X0 : $i, X1 : $i]:
% 8.53/8.69         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 8.53/8.69            = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 8.53/8.69          | ~ (v1_relat_1 @ X1)
% 8.53/8.69          | ~ (v1_relat_1 @ X0))),
% 8.53/8.69      inference('sup+', [status(thm)], ['184', '185'])).
% 8.53/8.69  thf('187', plain,
% 8.53/8.69      (![X0 : $i, X1 : $i]:
% 8.53/8.69         (~ (v1_relat_1 @ X1)
% 8.53/8.69          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 8.53/8.69          | ~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 8.53/8.69              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1))))),
% 8.53/8.69      inference('simplify', [status(thm)], ['186'])).
% 8.53/8.69  thf('188', plain,
% 8.53/8.69      (![X0 : $i, X1 : $i]:
% 8.53/8.69         (~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 8.53/8.69              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X1))),
% 8.53/8.69      inference('sup-', [status(thm)], ['183', '187'])).
% 8.53/8.69  thf('189', plain,
% 8.53/8.69      (![X0 : $i, X1 : $i]:
% 8.53/8.69         (~ (v1_relat_1 @ X1)
% 8.53/8.69          | ~ (v2_funct_1 @ X0)
% 8.53/8.69          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 8.53/8.69              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0))),
% 8.53/8.69      inference('simplify', [status(thm)], ['188'])).
% 8.53/8.69  thf('190', plain,
% 8.53/8.69      ((((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)) @ sk_D)
% 8.53/8.69          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A_1)))
% 8.53/8.69        | ~ (v1_relat_1 @ sk_C)
% 8.53/8.69        | ~ (v1_funct_1 @ sk_C)
% 8.53/8.69        | ~ (v2_funct_1 @ sk_C)
% 8.53/8.69        | ~ (v1_relat_1 @ sk_D))),
% 8.53/8.69      inference('sup+', [status(thm)], ['182', '189'])).
% 8.53/8.69  thf('191', plain,
% 8.53/8.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 8.53/8.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.69  thf('192', plain,
% 8.53/8.69      (![X24 : $i, X25 : $i, X26 : $i]:
% 8.53/8.69         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 8.53/8.69          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 8.53/8.69      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 8.53/8.69  thf('193', plain,
% 8.53/8.69      (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 8.53/8.69      inference('sup-', [status(thm)], ['191', '192'])).
% 8.53/8.69  thf('194', plain, (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (sk_B))),
% 8.53/8.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.69  thf('195', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 8.53/8.69      inference('sup+', [status(thm)], ['193', '194'])).
% 8.53/8.69  thf('196', plain,
% 8.53/8.69      (![X16 : $i]:
% 8.53/8.69         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 8.53/8.69          | ~ (v1_funct_1 @ X16)
% 8.53/8.69          | ~ (v1_relat_1 @ X16))),
% 8.53/8.69      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 8.53/8.69  thf('197', plain,
% 8.53/8.69      (![X18 : $i]:
% 8.53/8.69         (~ (v2_funct_1 @ X18)
% 8.53/8.69          | ((k1_relat_1 @ X18) = (k2_relat_1 @ (k2_funct_1 @ X18)))
% 8.53/8.69          | ~ (v1_funct_1 @ X18)
% 8.53/8.69          | ~ (v1_relat_1 @ X18))),
% 8.53/8.69      inference('cnf', [status(esa)], [t55_funct_1])).
% 8.53/8.69  thf('198', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (~ (v1_relat_1 @ X0)
% 8.53/8.69          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) = (X0)))),
% 8.53/8.69      inference('sup-', [status(thm)], ['88', '91'])).
% 8.53/8.69  thf('199', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 8.53/8.69            = (k2_funct_1 @ X0))
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 8.53/8.69      inference('sup+', [status(thm)], ['197', '198'])).
% 8.53/8.69  thf('200', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 8.53/8.69              (k6_partfun1 @ (k1_relat_1 @ X0))) = (k2_funct_1 @ X0)))),
% 8.53/8.69      inference('sup-', [status(thm)], ['196', '199'])).
% 8.53/8.69  thf('201', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 8.53/8.69            = (k2_funct_1 @ X0))
% 8.53/8.69          | ~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0))),
% 8.53/8.69      inference('simplify', [status(thm)], ['200'])).
% 8.53/8.69  thf('202', plain,
% 8.53/8.69      (![X16 : $i]:
% 8.53/8.69         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 8.53/8.69          | ~ (v1_funct_1 @ X16)
% 8.53/8.69          | ~ (v1_relat_1 @ X16))),
% 8.53/8.69      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 8.53/8.69  thf('203', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 8.53/8.69      inference('sup+', [status(thm)], ['193', '194'])).
% 8.53/8.69  thf('204', plain,
% 8.53/8.69      (![X16 : $i]:
% 8.53/8.69         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 8.53/8.69          | ~ (v1_funct_1 @ X16)
% 8.53/8.69          | ~ (v1_relat_1 @ X16))),
% 8.53/8.69      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 8.53/8.69  thf('205', plain,
% 8.53/8.69      (![X18 : $i]:
% 8.53/8.69         (~ (v2_funct_1 @ X18)
% 8.53/8.69          | ((k2_relat_1 @ X18) = (k1_relat_1 @ (k2_funct_1 @ X18)))
% 8.53/8.69          | ~ (v1_funct_1 @ X18)
% 8.53/8.69          | ~ (v1_relat_1 @ X18))),
% 8.53/8.69      inference('cnf', [status(esa)], [t55_funct_1])).
% 8.53/8.69  thf('206', plain,
% 8.53/8.69      (![X13 : $i]:
% 8.53/8.69         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X13)) @ X13) = (X13))
% 8.53/8.69          | ~ (v1_relat_1 @ X13))),
% 8.53/8.69      inference('demod', [status(thm)], ['77', '78'])).
% 8.53/8.69  thf('207', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 8.53/8.69            = (k2_funct_1 @ X0))
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 8.53/8.69      inference('sup+', [status(thm)], ['205', '206'])).
% 8.53/8.69  thf('208', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 8.53/8.69              (k2_funct_1 @ X0)) = (k2_funct_1 @ X0)))),
% 8.53/8.69      inference('sup-', [status(thm)], ['204', '207'])).
% 8.53/8.69  thf('209', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 8.53/8.69            = (k2_funct_1 @ X0))
% 8.53/8.69          | ~ (v2_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_funct_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ X0))),
% 8.53/8.69      inference('simplify', [status(thm)], ['208'])).
% 8.53/8.69  thf('210', plain,
% 8.53/8.69      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 8.53/8.69          = (k2_funct_1 @ sk_C))
% 8.53/8.69        | ~ (v1_relat_1 @ sk_C)
% 8.53/8.69        | ~ (v1_funct_1 @ sk_C)
% 8.53/8.69        | ~ (v2_funct_1 @ sk_C))),
% 8.53/8.69      inference('sup+', [status(thm)], ['203', '209'])).
% 8.53/8.69  thf('211', plain,
% 8.53/8.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 8.53/8.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.69  thf('212', plain,
% 8.53/8.69      (![X21 : $i, X22 : $i, X23 : $i]:
% 8.53/8.69         ((v1_relat_1 @ X21)
% 8.53/8.69          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 8.53/8.69      inference('cnf', [status(esa)], [cc1_relset_1])).
% 8.53/8.69  thf('213', plain, ((v1_relat_1 @ sk_C)),
% 8.53/8.69      inference('sup-', [status(thm)], ['211', '212'])).
% 8.53/8.69  thf('214', plain, ((v1_funct_1 @ sk_C)),
% 8.53/8.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.69  thf('215', plain, ((v2_funct_1 @ sk_C)),
% 8.53/8.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.69  thf('216', plain,
% 8.53/8.69      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 8.53/8.69         = (k2_funct_1 @ sk_C))),
% 8.53/8.69      inference('demod', [status(thm)], ['210', '213', '214', '215'])).
% 8.53/8.69  thf('217', plain,
% 8.53/8.69      (![X8 : $i, X9 : $i, X10 : $i]:
% 8.53/8.69         (~ (v1_relat_1 @ X8)
% 8.53/8.69          | ((k5_relat_1 @ (k5_relat_1 @ X9 @ X8) @ X10)
% 8.53/8.69              = (k5_relat_1 @ X9 @ (k5_relat_1 @ X8 @ X10)))
% 8.53/8.69          | ~ (v1_relat_1 @ X10)
% 8.53/8.69          | ~ (v1_relat_1 @ X9))),
% 8.53/8.69      inference('cnf', [status(esa)], [t55_relat_1])).
% 8.53/8.69  thf('218', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 8.53/8.69            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 8.53/8.69               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 8.53/8.69          | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B))
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 8.53/8.69      inference('sup+', [status(thm)], ['216', '217'])).
% 8.53/8.69  thf('219', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 8.53/8.69      inference('sup-', [status(thm)], ['96', '97'])).
% 8.53/8.69  thf('220', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 8.53/8.69            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 8.53/8.69               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 8.53/8.69      inference('demod', [status(thm)], ['218', '219'])).
% 8.53/8.69  thf('221', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (~ (v1_relat_1 @ sk_C)
% 8.53/8.69          | ~ (v1_funct_1 @ sk_C)
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 8.53/8.69              = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 8.53/8.69                 (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))))),
% 8.53/8.69      inference('sup-', [status(thm)], ['202', '220'])).
% 8.53/8.69  thf('222', plain, ((v1_relat_1 @ sk_C)),
% 8.53/8.69      inference('sup-', [status(thm)], ['211', '212'])).
% 8.53/8.69  thf('223', plain, ((v1_funct_1 @ sk_C)),
% 8.53/8.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.69  thf('224', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (~ (v1_relat_1 @ X0)
% 8.53/8.69          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 8.53/8.69              = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 8.53/8.69                 (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))))),
% 8.53/8.69      inference('demod', [status(thm)], ['221', '222', '223'])).
% 8.53/8.69  thf('225', plain,
% 8.53/8.69      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 8.53/8.69          (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 8.53/8.69          = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C)))
% 8.53/8.69        | ~ (v1_relat_1 @ sk_C)
% 8.53/8.69        | ~ (v1_funct_1 @ sk_C)
% 8.53/8.69        | ~ (v2_funct_1 @ sk_C)
% 8.53/8.69        | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C))))),
% 8.53/8.69      inference('sup+', [status(thm)], ['201', '224'])).
% 8.53/8.69  thf('226', plain,
% 8.53/8.69      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 8.53/8.69         = (k2_funct_1 @ sk_C))),
% 8.53/8.69      inference('demod', [status(thm)], ['210', '213', '214', '215'])).
% 8.53/8.69  thf('227', plain, ((v1_relat_1 @ sk_C)),
% 8.53/8.69      inference('sup-', [status(thm)], ['211', '212'])).
% 8.53/8.69  thf('228', plain, ((v1_funct_1 @ sk_C)),
% 8.53/8.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.69  thf('229', plain, ((v2_funct_1 @ sk_C)),
% 8.53/8.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.69  thf('230', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 8.53/8.69      inference('sup-', [status(thm)], ['96', '97'])).
% 8.53/8.69  thf('231', plain,
% 8.53/8.69      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 8.53/8.69         = (k2_funct_1 @ sk_C))),
% 8.53/8.69      inference('demod', [status(thm)],
% 8.53/8.69                ['225', '226', '227', '228', '229', '230'])).
% 8.53/8.69  thf('232', plain,
% 8.53/8.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 8.53/8.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.69  thf('233', plain,
% 8.53/8.69      (![X59 : $i, X60 : $i, X61 : $i]:
% 8.53/8.69         (((X59) = (k1_xboole_0))
% 8.53/8.69          | ~ (v1_funct_1 @ X60)
% 8.53/8.69          | ~ (v1_funct_2 @ X60 @ X61 @ X59)
% 8.53/8.69          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X61 @ X59)))
% 8.53/8.69          | ((k5_relat_1 @ X60 @ (k2_funct_1 @ X60)) = (k6_partfun1 @ X61))
% 8.53/8.69          | ~ (v2_funct_1 @ X60)
% 8.53/8.69          | ((k2_relset_1 @ X61 @ X59 @ X60) != (X59)))),
% 8.53/8.69      inference('cnf', [status(esa)], [t35_funct_2])).
% 8.53/8.69  thf('234', plain,
% 8.53/8.69      ((((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) != (sk_B))
% 8.53/8.69        | ~ (v2_funct_1 @ sk_C)
% 8.53/8.69        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A_1))
% 8.53/8.69        | ~ (v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)
% 8.53/8.69        | ~ (v1_funct_1 @ sk_C)
% 8.53/8.69        | ((sk_B) = (k1_xboole_0)))),
% 8.53/8.69      inference('sup-', [status(thm)], ['232', '233'])).
% 8.53/8.69  thf('235', plain, (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (sk_B))),
% 8.53/8.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.69  thf('236', plain, ((v2_funct_1 @ sk_C)),
% 8.53/8.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.69  thf('237', plain,
% 8.53/8.69      (![X16 : $i]:
% 8.53/8.69         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 8.53/8.69          | ~ (v1_funct_1 @ X16)
% 8.53/8.69          | ~ (v1_relat_1 @ X16))),
% 8.53/8.69      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 8.53/8.69  thf('238', plain,
% 8.53/8.69      (![X20 : $i]:
% 8.53/8.69         (~ (v2_funct_1 @ X20)
% 8.53/8.69          | ((k5_relat_1 @ X20 @ (k2_funct_1 @ X20))
% 8.53/8.69              = (k6_partfun1 @ (k1_relat_1 @ X20)))
% 8.53/8.69          | ~ (v1_funct_1 @ X20)
% 8.53/8.69          | ~ (v1_relat_1 @ X20))),
% 8.53/8.69      inference('demod', [status(thm)], ['151', '152'])).
% 8.53/8.69  thf('239', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 8.53/8.69      inference('sup+', [status(thm)], ['193', '194'])).
% 8.53/8.69  thf('240', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (~ (v1_relat_1 @ X0)
% 8.53/8.69          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) = (X0)))),
% 8.53/8.69      inference('sup-', [status(thm)], ['88', '91'])).
% 8.53/8.69  thf('241', plain,
% 8.53/8.69      ((((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))
% 8.53/8.69        | ~ (v1_relat_1 @ sk_C))),
% 8.53/8.69      inference('sup+', [status(thm)], ['239', '240'])).
% 8.53/8.69  thf('242', plain, ((v1_relat_1 @ sk_C)),
% 8.53/8.69      inference('sup-', [status(thm)], ['211', '212'])).
% 8.53/8.69  thf('243', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 8.53/8.69      inference('demod', [status(thm)], ['241', '242'])).
% 8.53/8.69  thf('244', plain,
% 8.53/8.69      (![X0 : $i, X1 : $i]:
% 8.53/8.69         (~ (v1_relat_1 @ X1)
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ((k5_relat_1 @ X0 @ X1)
% 8.53/8.69              = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 8.53/8.69                 (k5_relat_1 @ X0 @ X1))))),
% 8.53/8.69      inference('simplify', [status(thm)], ['99'])).
% 8.53/8.69  thf('245', plain,
% 8.53/8.69      ((((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B))
% 8.53/8.69          = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ sk_C))
% 8.53/8.69        | ~ (v1_relat_1 @ sk_C)
% 8.53/8.69        | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B)))),
% 8.53/8.69      inference('sup+', [status(thm)], ['243', '244'])).
% 8.53/8.69  thf('246', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 8.53/8.69      inference('demod', [status(thm)], ['241', '242'])).
% 8.53/8.69  thf('247', plain, ((v1_relat_1 @ sk_C)),
% 8.53/8.69      inference('sup-', [status(thm)], ['211', '212'])).
% 8.53/8.69  thf('248', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 8.53/8.69      inference('sup-', [status(thm)], ['96', '97'])).
% 8.53/8.69  thf('249', plain,
% 8.53/8.69      (((sk_C) = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ sk_C))),
% 8.53/8.69      inference('demod', [status(thm)], ['245', '246', '247', '248'])).
% 8.53/8.69  thf('250', plain,
% 8.53/8.69      (![X8 : $i, X9 : $i, X10 : $i]:
% 8.53/8.69         (~ (v1_relat_1 @ X8)
% 8.53/8.69          | ((k5_relat_1 @ (k5_relat_1 @ X9 @ X8) @ X10)
% 8.53/8.69              = (k5_relat_1 @ X9 @ (k5_relat_1 @ X8 @ X10)))
% 8.53/8.69          | ~ (v1_relat_1 @ X10)
% 8.53/8.69          | ~ (v1_relat_1 @ X9))),
% 8.53/8.69      inference('cnf', [status(esa)], [t55_relat_1])).
% 8.53/8.69  thf('251', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (((k5_relat_1 @ sk_C @ X0)
% 8.53/8.69            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ 
% 8.53/8.69               (k5_relat_1 @ sk_C @ X0)))
% 8.53/8.69          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 8.53/8.69          | ~ (v1_relat_1 @ X0)
% 8.53/8.69          | ~ (v1_relat_1 @ sk_C))),
% 8.53/8.69      inference('sup+', [status(thm)], ['249', '250'])).
% 8.53/8.69  thf('252', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 8.53/8.69      inference('sup-', [status(thm)], ['96', '97'])).
% 8.53/8.69  thf('253', plain, ((v1_relat_1 @ sk_C)),
% 8.53/8.69      inference('sup-', [status(thm)], ['211', '212'])).
% 8.53/8.69  thf('254', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (((k5_relat_1 @ sk_C @ X0)
% 8.53/8.69            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ 
% 8.53/8.69               (k5_relat_1 @ sk_C @ X0)))
% 8.53/8.69          | ~ (v1_relat_1 @ X0))),
% 8.53/8.69      inference('demod', [status(thm)], ['251', '252', '253'])).
% 8.53/8.69  thf('255', plain,
% 8.53/8.69      ((((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 8.53/8.69          = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ 
% 8.53/8.69             (k6_partfun1 @ (k1_relat_1 @ sk_C))))
% 8.53/8.69        | ~ (v1_relat_1 @ sk_C)
% 8.53/8.69        | ~ (v1_funct_1 @ sk_C)
% 8.53/8.69        | ~ (v2_funct_1 @ sk_C)
% 8.53/8.69        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 8.53/8.69      inference('sup+', [status(thm)], ['238', '254'])).
% 8.53/8.69  thf('256', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 8.53/8.69           = (k6_partfun1 @ X0))),
% 8.53/8.69      inference('demod', [status(thm)], ['131', '132'])).
% 8.53/8.69  thf('257', plain, ((v1_relat_1 @ sk_C)),
% 8.53/8.69      inference('sup-', [status(thm)], ['211', '212'])).
% 8.53/8.69  thf('258', plain, ((v1_funct_1 @ sk_C)),
% 8.53/8.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.69  thf('259', plain, ((v2_funct_1 @ sk_C)),
% 8.53/8.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.69  thf('260', plain,
% 8.53/8.69      ((((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 8.53/8.69          = (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 8.53/8.69        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 8.53/8.69      inference('demod', [status(thm)], ['255', '256', '257', '258', '259'])).
% 8.53/8.69  thf('261', plain,
% 8.53/8.69      ((~ (v1_relat_1 @ sk_C)
% 8.53/8.69        | ~ (v1_funct_1 @ sk_C)
% 8.53/8.69        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 8.53/8.69            = (k6_partfun1 @ (k1_relat_1 @ sk_C))))),
% 8.53/8.69      inference('sup-', [status(thm)], ['237', '260'])).
% 8.53/8.69  thf('262', plain, ((v1_relat_1 @ sk_C)),
% 8.53/8.69      inference('sup-', [status(thm)], ['211', '212'])).
% 8.53/8.69  thf('263', plain, ((v1_funct_1 @ sk_C)),
% 8.53/8.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.69  thf('264', plain,
% 8.53/8.69      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 8.53/8.69         = (k6_partfun1 @ (k1_relat_1 @ sk_C)))),
% 8.53/8.69      inference('demod', [status(thm)], ['261', '262', '263'])).
% 8.53/8.69  thf('265', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)),
% 8.53/8.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.69  thf('266', plain, ((v1_funct_1 @ sk_C)),
% 8.53/8.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.69  thf('267', plain,
% 8.53/8.69      ((((sk_B) != (sk_B))
% 8.53/8.69        | ((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A_1))
% 8.53/8.69        | ((sk_B) = (k1_xboole_0)))),
% 8.53/8.69      inference('demod', [status(thm)],
% 8.53/8.69                ['234', '235', '236', '264', '265', '266'])).
% 8.53/8.69  thf('268', plain,
% 8.53/8.69      ((((sk_B) = (k1_xboole_0))
% 8.53/8.69        | ((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A_1)))),
% 8.53/8.69      inference('simplify', [status(thm)], ['267'])).
% 8.53/8.69  thf('269', plain, (((sk_B) != (k1_xboole_0))),
% 8.53/8.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.69  thf('270', plain,
% 8.53/8.69      (((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A_1))),
% 8.53/8.69      inference('simplify_reflect-', [status(thm)], ['268', '269'])).
% 8.53/8.69  thf('271', plain,
% 8.53/8.69      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A_1))
% 8.53/8.69         = (k2_funct_1 @ sk_C))),
% 8.53/8.69      inference('demod', [status(thm)], ['231', '270'])).
% 8.53/8.69  thf('272', plain, ((v1_relat_1 @ sk_C)),
% 8.53/8.69      inference('sup-', [status(thm)], ['211', '212'])).
% 8.53/8.69  thf('273', plain, ((v1_funct_1 @ sk_C)),
% 8.53/8.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.69  thf('274', plain, ((v2_funct_1 @ sk_C)),
% 8.53/8.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.69  thf('275', plain,
% 8.53/8.69      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 8.53/8.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.69  thf('276', plain,
% 8.53/8.69      (![X21 : $i, X22 : $i, X23 : $i]:
% 8.53/8.69         ((v1_relat_1 @ X21)
% 8.53/8.69          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 8.53/8.69      inference('cnf', [status(esa)], [cc1_relset_1])).
% 8.53/8.69  thf('277', plain, ((v1_relat_1 @ sk_D)),
% 8.53/8.69      inference('sup-', [status(thm)], ['275', '276'])).
% 8.53/8.69  thf('278', plain,
% 8.53/8.69      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (k2_funct_1 @ sk_C))),
% 8.53/8.69      inference('demod', [status(thm)],
% 8.53/8.69                ['190', '195', '271', '272', '273', '274', '277'])).
% 8.53/8.69  thf('279', plain, (((k2_relat_1 @ sk_D) = (sk_A_1))),
% 8.53/8.69      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 8.53/8.69  thf('280', plain, (((k2_relat_1 @ sk_D) = (sk_A_1))),
% 8.53/8.69      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 8.53/8.69  thf('281', plain,
% 8.53/8.69      (![X0 : $i]:
% 8.53/8.69         (~ (v1_relat_1 @ X0)
% 8.53/8.69          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) = (X0)))),
% 8.53/8.69      inference('sup-', [status(thm)], ['88', '91'])).
% 8.53/8.69  thf('282', plain,
% 8.53/8.69      ((((k5_relat_1 @ sk_D @ (k6_partfun1 @ sk_A_1)) = (sk_D))
% 8.53/8.69        | ~ (v1_relat_1 @ sk_D))),
% 8.53/8.69      inference('sup+', [status(thm)], ['280', '281'])).
% 8.53/8.69  thf('283', plain, ((v1_relat_1 @ sk_D)),
% 8.53/8.69      inference('sup-', [status(thm)], ['275', '276'])).
% 8.53/8.69  thf('284', plain, (((k5_relat_1 @ sk_D @ (k6_partfun1 @ sk_A_1)) = (sk_D))),
% 8.53/8.69      inference('demod', [status(thm)], ['282', '283'])).
% 8.53/8.69  thf('285', plain, ((v1_relat_1 @ sk_D)),
% 8.53/8.69      inference('sup-', [status(thm)], ['275', '276'])).
% 8.53/8.69  thf('286', plain, ((v1_funct_1 @ sk_D)),
% 8.53/8.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.69  thf('287', plain, ((v2_funct_1 @ sk_D)),
% 8.53/8.69      inference('sup-', [status(thm)], ['73', '74'])).
% 8.53/8.69  thf('288', plain, (((k2_funct_1 @ sk_C) = (sk_D))),
% 8.53/8.69      inference('demod', [status(thm)],
% 8.53/8.69                ['181', '278', '279', '284', '285', '286', '287'])).
% 8.53/8.69  thf('289', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 8.53/8.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.53/8.69  thf('290', plain, ($false),
% 8.53/8.69      inference('simplify_reflect-', [status(thm)], ['288', '289'])).
% 8.53/8.69  
% 8.53/8.69  % SZS output end Refutation
% 8.53/8.69  
% 8.53/8.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gDiui4kIAH

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:26 EST 2020

% Result     : Theorem 22.50s
% Output     : Refutation 22.50s
% Verified   : 
% Statistics : Number of formulae       :  274 ( 926 expanded)
%              Number of leaves         :   51 ( 298 expanded)
%              Depth                    :   23
%              Number of atoms          : 2633 (20327 expanded)
%              Number of equality atoms :  178 (1406 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X65: $i,X66: $i,X67: $i] :
      ( ( X65 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X66 )
      | ~ ( v1_funct_2 @ X66 @ X67 @ X65 )
      | ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X67 @ X65 ) ) )
      | ( ( k5_relat_1 @ X66 @ ( k2_funct_1 @ X66 ) )
        = ( k6_partfun1 @ X67 ) )
      | ~ ( v2_funct_1 @ X66 )
      | ( ( k2_relset_1 @ X67 @ X65 @ X66 )
       != X65 ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_relset_1 @ X31 @ X32 @ X30 )
        = ( k2_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
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
    ! [X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_funct_2 @ X52 @ X53 @ X54 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X54 ) ) )
      | ~ ( r2_relset_1 @ X53 @ X53 @ ( k1_partfun1 @ X53 @ X54 @ X54 @ X53 @ X52 @ X55 ) @ ( k6_partfun1 @ X53 ) )
      | ( ( k2_relset_1 @ X54 @ X53 @ X55 )
        = X53 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X53 ) ) )
      | ~ ( v1_funct_2 @ X55 @ X54 @ X53 )
      | ~ ( v1_funct_1 @ X55 ) ) ),
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
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ( ( k1_partfun1 @ X46 @ X47 @ X49 @ X50 @ X45 @ X48 )
        = ( k5_relat_1 @ X45 @ X48 ) ) ) ),
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
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X42 ) ) ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( X33 = X36 )
      | ~ ( r2_relset_1 @ X34 @ X35 @ X33 @ X36 ) ) ),
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
    ! [X44: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X44 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X44 ) ) ) ),
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
    ! [X60: $i,X61: $i,X62: $i,X63: $i,X64: $i] :
      ( ~ ( v1_funct_1 @ X60 )
      | ~ ( v1_funct_2 @ X60 @ X61 @ X62 )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X61 @ X62 ) ) )
      | ( zip_tseitin_0 @ X60 @ X63 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X64 @ X61 @ X61 @ X62 @ X63 @ X60 ) )
      | ( zip_tseitin_1 @ X62 @ X61 )
      | ( ( k2_relset_1 @ X64 @ X61 @ X63 )
       != X61 )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X64 @ X61 ) ) )
      | ~ ( v1_funct_2 @ X63 @ X64 @ X61 )
      | ~ ( v1_funct_1 @ X63 ) ) ),
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

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('61',plain,(
    ! [X20: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('62',plain,(
    ! [X51: $i] :
      ( ( k6_partfun1 @ X51 )
      = ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('63',plain,(
    ! [X20: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X20 ) ) ),
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
    ! [X58: $i,X59: $i] :
      ( ( X58 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X58 @ X59 ) ) ),
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
    ! [X56: $i,X57: $i] :
      ( ( v2_funct_1 @ X57 )
      | ~ ( zip_tseitin_0 @ X57 @ X56 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('75',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['25','75'])).

thf(t58_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('77',plain,(
    ! [X25: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X25 @ ( k2_funct_1 @ X25 ) ) )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('78',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ sk_B ) )
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('79',plain,(
    ! [X13: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('80',plain,(
    ! [X51: $i] :
      ( ( k6_partfun1 @ X51 )
      = ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('81',plain,(
    ! [X13: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X13 ) )
      = X13 ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('83',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('84',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('85',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('86',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['73','74'])).

thf('89',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['78','81','86','87','88'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('90',plain,(
    ! [X14: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X14 ) ) @ X14 )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('91',plain,(
    ! [X51: $i] :
      ( ( k6_partfun1 @ X51 )
      = ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('92',plain,(
    ! [X14: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X14 ) ) @ X14 )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['89','92'])).

thf('94',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('95',plain,(
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

thf('96',plain,(
    ! [X26: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X26 ) @ X26 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('97',plain,(
    ! [X51: $i] :
      ( ( k6_partfun1 @ X51 )
      = ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('98',plain,(
    ! [X26: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X26 ) @ X26 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('100',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_relset_1 @ X31 @ X32 @ X30 )
        = ( k2_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('102',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
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

thf('106',plain,(
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relat_1 @ X24 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('107',plain,(
    ! [X14: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X14 ) ) @ X14 )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['105','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['104','110'])).

thf('112',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('114',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('116',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['111','116','117','118'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('120',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) @ X11 )
        = ( k5_relat_1 @ X10 @ ( k5_relat_1 @ X9 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('122',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('123',plain,(
    ! [X51: $i] :
      ( ( k6_partfun1 @ X51 )
      = ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('124',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X17 ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['121','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['99','125'])).

thf('127',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['114','115'])).

thf('128',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['126','127','128'])).

thf('130',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['98','129'])).

thf('131',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['102','103'])).

thf('132',plain,(
    ! [X12: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('133',plain,(
    ! [X51: $i] :
      ( ( k6_partfun1 @ X51 )
      = ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('134',plain,(
    ! [X12: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X12 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X14: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X14 ) ) @ X14 )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X17 ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['114','115'])).

thf('140',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['114','115'])).

thf('143',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['130','131','138','139','140','141','142'])).

thf('144',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) @ X11 )
        = ( k5_relat_1 @ X10 @ ( k5_relat_1 @ X9 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['143','144'])).

thf('146',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['114','115'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['95','147'])).

thf('149',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['114','115'])).

thf('150',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['148','149','150'])).

thf('152',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A_1 ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['94','151'])).

thf('153',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('154',plain,(
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k1_relat_1 @ X24 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('155',plain,(
    ! [X15: $i] :
      ( ( ( k5_relat_1 @ X15 @ ( k6_relat_1 @ ( k2_relat_1 @ X15 ) ) )
        = X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('156',plain,(
    ! [X51: $i] :
      ( ( k6_partfun1 @ X51 )
      = ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('157',plain,(
    ! [X15: $i] :
      ( ( ( k5_relat_1 @ X15 @ ( k6_partfun1 @ ( k2_relat_1 @ X15 ) ) )
        = X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['154','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['153','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['126','127','128'])).

thf('162',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['160','161'])).

thf('163',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['111','116','117','118'])).

thf('164',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['114','115'])).

thf('165',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X17 ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('168',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['162','163','164','165','166','167'])).

thf('169',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    ! [X65: $i,X66: $i,X67: $i] :
      ( ( X65 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X66 )
      | ~ ( v1_funct_2 @ X66 @ X67 @ X65 )
      | ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X67 @ X65 ) ) )
      | ( ( k5_relat_1 @ X66 @ ( k2_funct_1 @ X66 ) )
        = ( k6_partfun1 @ X67 ) )
      | ~ ( v2_funct_1 @ X66 )
      | ( ( k2_relset_1 @ X67 @ X65 @ X66 )
       != X65 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('171',plain,
    ( ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A_1 ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('175',plain,(
    ! [X26: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k5_relat_1 @ X26 @ ( k2_funct_1 @ X26 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('176',plain,(
    ! [X51: $i] :
      ( ( k6_partfun1 @ X51 )
      = ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('177',plain,(
    ! [X26: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k5_relat_1 @ X26 @ ( k2_funct_1 @ X26 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('178',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['102','103'])).

thf('179',plain,(
    ! [X15: $i] :
      ( ( ( k5_relat_1 @ X15 @ ( k6_partfun1 @ ( k2_relat_1 @ X15 ) ) )
        = X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('180',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['178','179'])).

thf('181',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['114','115'])).

thf('182',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X14: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X14 ) ) @ X14 )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('184',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) @ X11 )
        = ( k5_relat_1 @ X10 @ ( k5_relat_1 @ X9 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['183','184'])).

thf('186',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X17 ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['185','186'])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['187'])).

thf('189',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['182','188'])).

thf('190',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['180','181'])).

thf('191',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['114','115'])).

thf('192',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X17 ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('193',plain,
    ( sk_C
    = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['189','190','191','192'])).

thf('194',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) @ X11 )
        = ( k5_relat_1 @ X10 @ ( k5_relat_1 @ X9 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('195',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X17 ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('197',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['114','115'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['195','196','197'])).

thf('199',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['177','198'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('201',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['114','115'])).

thf('202',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['199','200','201','202','203'])).

thf('205',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['174','204'])).

thf('206',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['114','115'])).

thf('207',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['205','206','207'])).

thf('209',plain,(
    v1_funct_2 @ sk_C @ sk_A_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,
    ( ( sk_B != sk_B )
    | ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A_1 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['171','172','173','208','209','210'])).

thf('212',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A_1 ) ) ),
    inference(simplify,[status(thm)],['211'])).

thf('213',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A_1 ) ),
    inference('simplify_reflect-',[status(thm)],['212','213'])).

thf('215',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A_1 ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['168','214'])).

thf('216',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['84','85'])).

thf('217',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['152','215','216'])).

thf('218',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['84','85'])).

thf('219',plain,
    ( ( k2_funct_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['93','217','218'])).

thf('220',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['219','220'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gDiui4kIAH
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:36:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 22.50/22.79  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 22.50/22.79  % Solved by: fo/fo7.sh
% 22.50/22.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 22.50/22.79  % done 9319 iterations in 22.303s
% 22.50/22.79  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 22.50/22.79  % SZS output start Refutation
% 22.50/22.79  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 22.50/22.79  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 22.50/22.79  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 22.50/22.79  thf(sk_A_1_type, type, sk_A_1: $i).
% 22.50/22.79  thf(sk_D_type, type, sk_D: $i).
% 22.50/22.79  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 22.50/22.79  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 22.50/22.79  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 22.50/22.79  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 22.50/22.79  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 22.50/22.79  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 22.50/22.79  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 22.50/22.79  thf(sk_B_type, type, sk_B: $i).
% 22.50/22.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 22.50/22.79  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 22.50/22.79  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 22.50/22.79  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 22.50/22.79  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 22.50/22.79  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 22.50/22.79  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 22.50/22.79  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 22.50/22.79  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 22.50/22.79  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 22.50/22.79  thf(sk_C_type, type, sk_C: $i).
% 22.50/22.79  thf(t36_funct_2, conjecture,
% 22.50/22.79    (![A:$i,B:$i,C:$i]:
% 22.50/22.79     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 22.50/22.79         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 22.50/22.79       ( ![D:$i]:
% 22.50/22.79         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 22.50/22.79             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 22.50/22.79           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 22.50/22.79               ( r2_relset_1 @
% 22.50/22.79                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 22.50/22.79                 ( k6_partfun1 @ A ) ) & 
% 22.50/22.79               ( v2_funct_1 @ C ) ) =>
% 22.50/22.79             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 22.50/22.79               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 22.50/22.79  thf(zf_stmt_0, negated_conjecture,
% 22.50/22.79    (~( ![A:$i,B:$i,C:$i]:
% 22.50/22.79        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 22.50/22.79            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 22.50/22.79          ( ![D:$i]:
% 22.50/22.79            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 22.50/22.79                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 22.50/22.79              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 22.50/22.79                  ( r2_relset_1 @
% 22.50/22.79                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 22.50/22.79                    ( k6_partfun1 @ A ) ) & 
% 22.50/22.79                  ( v2_funct_1 @ C ) ) =>
% 22.50/22.79                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 22.50/22.79                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 22.50/22.79    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 22.50/22.79  thf('0', plain,
% 22.50/22.79      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf(t35_funct_2, axiom,
% 22.50/22.79    (![A:$i,B:$i,C:$i]:
% 22.50/22.79     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 22.50/22.79         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 22.50/22.79       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 22.50/22.79         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 22.50/22.79           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 22.50/22.79             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 22.50/22.79  thf('1', plain,
% 22.50/22.79      (![X65 : $i, X66 : $i, X67 : $i]:
% 22.50/22.79         (((X65) = (k1_xboole_0))
% 22.50/22.79          | ~ (v1_funct_1 @ X66)
% 22.50/22.79          | ~ (v1_funct_2 @ X66 @ X67 @ X65)
% 22.50/22.79          | ~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X67 @ X65)))
% 22.50/22.79          | ((k5_relat_1 @ X66 @ (k2_funct_1 @ X66)) = (k6_partfun1 @ X67))
% 22.50/22.79          | ~ (v2_funct_1 @ X66)
% 22.50/22.79          | ((k2_relset_1 @ X67 @ X65 @ X66) != (X65)))),
% 22.50/22.79      inference('cnf', [status(esa)], [t35_funct_2])).
% 22.50/22.79  thf('2', plain,
% 22.50/22.79      ((((k2_relset_1 @ sk_B @ sk_A_1 @ sk_D) != (sk_A_1))
% 22.50/22.79        | ~ (v2_funct_1 @ sk_D)
% 22.50/22.79        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 22.50/22.79        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A_1)
% 22.50/22.79        | ~ (v1_funct_1 @ sk_D)
% 22.50/22.79        | ((sk_A_1) = (k1_xboole_0)))),
% 22.50/22.79      inference('sup-', [status(thm)], ['0', '1'])).
% 22.50/22.79  thf('3', plain,
% 22.50/22.79      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf(redefinition_k2_relset_1, axiom,
% 22.50/22.79    (![A:$i,B:$i,C:$i]:
% 22.50/22.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 22.50/22.79       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 22.50/22.79  thf('4', plain,
% 22.50/22.79      (![X30 : $i, X31 : $i, X32 : $i]:
% 22.50/22.79         (((k2_relset_1 @ X31 @ X32 @ X30) = (k2_relat_1 @ X30))
% 22.50/22.79          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 22.50/22.79      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 22.50/22.79  thf('5', plain,
% 22.50/22.79      (((k2_relset_1 @ sk_B @ sk_A_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 22.50/22.79      inference('sup-', [status(thm)], ['3', '4'])).
% 22.50/22.79  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A_1)),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('8', plain,
% 22.50/22.79      ((((k2_relat_1 @ sk_D) != (sk_A_1))
% 22.50/22.79        | ~ (v2_funct_1 @ sk_D)
% 22.50/22.79        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 22.50/22.79        | ((sk_A_1) = (k1_xboole_0)))),
% 22.50/22.79      inference('demod', [status(thm)], ['2', '5', '6', '7'])).
% 22.50/22.79  thf('9', plain, (((sk_A_1) != (k1_xboole_0))),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('10', plain,
% 22.50/22.79      ((((k2_relat_1 @ sk_D) != (sk_A_1))
% 22.50/22.79        | ~ (v2_funct_1 @ sk_D)
% 22.50/22.79        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 22.50/22.79      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 22.50/22.79  thf('11', plain,
% 22.50/22.79      ((r2_relset_1 @ sk_A_1 @ sk_A_1 @ 
% 22.50/22.79        (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D) @ 
% 22.50/22.79        (k6_partfun1 @ sk_A_1))),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('12', plain,
% 22.50/22.79      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf(t24_funct_2, axiom,
% 22.50/22.79    (![A:$i,B:$i,C:$i]:
% 22.50/22.79     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 22.50/22.79         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 22.50/22.79       ( ![D:$i]:
% 22.50/22.79         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 22.50/22.79             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 22.50/22.79           ( ( r2_relset_1 @
% 22.50/22.79               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 22.50/22.79               ( k6_partfun1 @ B ) ) =>
% 22.50/22.79             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 22.50/22.79  thf('13', plain,
% 22.50/22.79      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 22.50/22.79         (~ (v1_funct_1 @ X52)
% 22.50/22.79          | ~ (v1_funct_2 @ X52 @ X53 @ X54)
% 22.50/22.79          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X54)))
% 22.50/22.79          | ~ (r2_relset_1 @ X53 @ X53 @ 
% 22.50/22.79               (k1_partfun1 @ X53 @ X54 @ X54 @ X53 @ X52 @ X55) @ 
% 22.50/22.79               (k6_partfun1 @ X53))
% 22.50/22.79          | ((k2_relset_1 @ X54 @ X53 @ X55) = (X53))
% 22.50/22.79          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X53)))
% 22.50/22.79          | ~ (v1_funct_2 @ X55 @ X54 @ X53)
% 22.50/22.79          | ~ (v1_funct_1 @ X55))),
% 22.50/22.79      inference('cnf', [status(esa)], [t24_funct_2])).
% 22.50/22.79  thf('14', plain,
% 22.50/22.79      (![X0 : $i]:
% 22.50/22.79         (~ (v1_funct_1 @ X0)
% 22.50/22.79          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A_1)
% 22.50/22.79          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))
% 22.50/22.79          | ((k2_relset_1 @ sk_B @ sk_A_1 @ X0) = (sk_A_1))
% 22.50/22.79          | ~ (r2_relset_1 @ sk_A_1 @ sk_A_1 @ 
% 22.50/22.79               (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ X0) @ 
% 22.50/22.79               (k6_partfun1 @ sk_A_1))
% 22.50/22.79          | ~ (v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)
% 22.50/22.79          | ~ (v1_funct_1 @ sk_C))),
% 22.50/22.79      inference('sup-', [status(thm)], ['12', '13'])).
% 22.50/22.79  thf('15', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('16', plain, ((v1_funct_1 @ sk_C)),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('17', plain,
% 22.50/22.79      (![X0 : $i]:
% 22.50/22.79         (~ (v1_funct_1 @ X0)
% 22.50/22.79          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A_1)
% 22.50/22.79          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))
% 22.50/22.79          | ((k2_relset_1 @ sk_B @ sk_A_1 @ X0) = (sk_A_1))
% 22.50/22.79          | ~ (r2_relset_1 @ sk_A_1 @ sk_A_1 @ 
% 22.50/22.79               (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ X0) @ 
% 22.50/22.79               (k6_partfun1 @ sk_A_1)))),
% 22.50/22.79      inference('demod', [status(thm)], ['14', '15', '16'])).
% 22.50/22.79  thf('18', plain,
% 22.50/22.79      ((((k2_relset_1 @ sk_B @ sk_A_1 @ sk_D) = (sk_A_1))
% 22.50/22.79        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))
% 22.50/22.79        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A_1)
% 22.50/22.79        | ~ (v1_funct_1 @ sk_D))),
% 22.50/22.79      inference('sup-', [status(thm)], ['11', '17'])).
% 22.50/22.79  thf('19', plain,
% 22.50/22.79      (((k2_relset_1 @ sk_B @ sk_A_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 22.50/22.79      inference('sup-', [status(thm)], ['3', '4'])).
% 22.50/22.79  thf('20', plain,
% 22.50/22.79      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('21', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A_1)),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('22', plain, ((v1_funct_1 @ sk_D)),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('23', plain, (((k2_relat_1 @ sk_D) = (sk_A_1))),
% 22.50/22.79      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 22.50/22.79  thf('24', plain,
% 22.50/22.79      ((((sk_A_1) != (sk_A_1))
% 22.50/22.79        | ~ (v2_funct_1 @ sk_D)
% 22.50/22.79        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 22.50/22.79      inference('demod', [status(thm)], ['10', '23'])).
% 22.50/22.79  thf('25', plain,
% 22.50/22.79      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 22.50/22.79        | ~ (v2_funct_1 @ sk_D))),
% 22.50/22.79      inference('simplify', [status(thm)], ['24'])).
% 22.50/22.79  thf('26', plain,
% 22.50/22.79      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('27', plain,
% 22.50/22.79      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf(redefinition_k1_partfun1, axiom,
% 22.50/22.79    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 22.50/22.79     ( ( ( v1_funct_1 @ E ) & 
% 22.50/22.79         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 22.50/22.79         ( v1_funct_1 @ F ) & 
% 22.50/22.79         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 22.50/22.79       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 22.50/22.79  thf('28', plain,
% 22.50/22.79      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 22.50/22.79         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 22.50/22.79          | ~ (v1_funct_1 @ X45)
% 22.50/22.79          | ~ (v1_funct_1 @ X48)
% 22.50/22.79          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 22.50/22.79          | ((k1_partfun1 @ X46 @ X47 @ X49 @ X50 @ X45 @ X48)
% 22.50/22.79              = (k5_relat_1 @ X45 @ X48)))),
% 22.50/22.79      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 22.50/22.79  thf('29', plain,
% 22.50/22.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.50/22.79         (((k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 22.50/22.79            = (k5_relat_1 @ sk_C @ X0))
% 22.50/22.79          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 22.50/22.79          | ~ (v1_funct_1 @ X0)
% 22.50/22.79          | ~ (v1_funct_1 @ sk_C))),
% 22.50/22.79      inference('sup-', [status(thm)], ['27', '28'])).
% 22.50/22.79  thf('30', plain, ((v1_funct_1 @ sk_C)),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('31', plain,
% 22.50/22.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.50/22.79         (((k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 22.50/22.79            = (k5_relat_1 @ sk_C @ X0))
% 22.50/22.79          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 22.50/22.79          | ~ (v1_funct_1 @ X0))),
% 22.50/22.79      inference('demod', [status(thm)], ['29', '30'])).
% 22.50/22.79  thf('32', plain,
% 22.50/22.79      ((~ (v1_funct_1 @ sk_D)
% 22.50/22.79        | ((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 22.50/22.79            = (k5_relat_1 @ sk_C @ sk_D)))),
% 22.50/22.79      inference('sup-', [status(thm)], ['26', '31'])).
% 22.50/22.79  thf('33', plain, ((v1_funct_1 @ sk_D)),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('34', plain,
% 22.50/22.79      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 22.50/22.79         = (k5_relat_1 @ sk_C @ sk_D))),
% 22.50/22.79      inference('demod', [status(thm)], ['32', '33'])).
% 22.50/22.79  thf('35', plain,
% 22.50/22.79      ((r2_relset_1 @ sk_A_1 @ sk_A_1 @ 
% 22.50/22.79        (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D) @ 
% 22.50/22.79        (k6_partfun1 @ sk_A_1))),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('36', plain,
% 22.50/22.79      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 22.50/22.79         = (k5_relat_1 @ sk_C @ sk_D))),
% 22.50/22.79      inference('demod', [status(thm)], ['32', '33'])).
% 22.50/22.79  thf('37', plain,
% 22.50/22.79      ((r2_relset_1 @ sk_A_1 @ sk_A_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 22.50/22.79        (k6_partfun1 @ sk_A_1))),
% 22.50/22.79      inference('demod', [status(thm)], ['35', '36'])).
% 22.50/22.79  thf('38', plain,
% 22.50/22.79      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('39', plain,
% 22.50/22.79      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf(dt_k1_partfun1, axiom,
% 22.50/22.79    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 22.50/22.79     ( ( ( v1_funct_1 @ E ) & 
% 22.50/22.79         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 22.50/22.79         ( v1_funct_1 @ F ) & 
% 22.50/22.79         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 22.50/22.79       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 22.50/22.79         ( m1_subset_1 @
% 22.50/22.79           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 22.50/22.79           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 22.50/22.79  thf('40', plain,
% 22.50/22.79      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 22.50/22.79         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 22.50/22.79          | ~ (v1_funct_1 @ X37)
% 22.50/22.79          | ~ (v1_funct_1 @ X40)
% 22.50/22.79          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 22.50/22.79          | (m1_subset_1 @ (k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40) @ 
% 22.50/22.79             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X42))))),
% 22.50/22.79      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 22.50/22.79  thf('41', plain,
% 22.50/22.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.50/22.79         ((m1_subset_1 @ (k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 22.50/22.79           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ X0)))
% 22.50/22.79          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 22.50/22.79          | ~ (v1_funct_1 @ X1)
% 22.50/22.79          | ~ (v1_funct_1 @ sk_C))),
% 22.50/22.79      inference('sup-', [status(thm)], ['39', '40'])).
% 22.50/22.79  thf('42', plain, ((v1_funct_1 @ sk_C)),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('43', plain,
% 22.50/22.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.50/22.79         ((m1_subset_1 @ (k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 22.50/22.79           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ X0)))
% 22.50/22.79          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 22.50/22.79          | ~ (v1_funct_1 @ X1))),
% 22.50/22.79      inference('demod', [status(thm)], ['41', '42'])).
% 22.50/22.79  thf('44', plain,
% 22.50/22.79      ((~ (v1_funct_1 @ sk_D)
% 22.50/22.79        | (m1_subset_1 @ 
% 22.50/22.79           (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D) @ 
% 22.50/22.79           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_A_1))))),
% 22.50/22.79      inference('sup-', [status(thm)], ['38', '43'])).
% 22.50/22.79  thf('45', plain, ((v1_funct_1 @ sk_D)),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('46', plain,
% 22.50/22.79      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 22.50/22.79         = (k5_relat_1 @ sk_C @ sk_D))),
% 22.50/22.79      inference('demod', [status(thm)], ['32', '33'])).
% 22.50/22.79  thf('47', plain,
% 22.50/22.79      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 22.50/22.79        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_A_1)))),
% 22.50/22.79      inference('demod', [status(thm)], ['44', '45', '46'])).
% 22.50/22.79  thf(redefinition_r2_relset_1, axiom,
% 22.50/22.79    (![A:$i,B:$i,C:$i,D:$i]:
% 22.50/22.79     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 22.50/22.79         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 22.50/22.79       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 22.50/22.79  thf('48', plain,
% 22.50/22.79      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 22.50/22.79         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 22.50/22.79          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 22.50/22.79          | ((X33) = (X36))
% 22.50/22.79          | ~ (r2_relset_1 @ X34 @ X35 @ X33 @ X36))),
% 22.50/22.79      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 22.50/22.79  thf('49', plain,
% 22.50/22.79      (![X0 : $i]:
% 22.50/22.79         (~ (r2_relset_1 @ sk_A_1 @ sk_A_1 @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 22.50/22.79          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 22.50/22.79          | ~ (m1_subset_1 @ X0 @ 
% 22.50/22.79               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_A_1))))),
% 22.50/22.79      inference('sup-', [status(thm)], ['47', '48'])).
% 22.50/22.79  thf('50', plain,
% 22.50/22.79      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A_1) @ 
% 22.50/22.79           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_A_1)))
% 22.50/22.79        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A_1)))),
% 22.50/22.79      inference('sup-', [status(thm)], ['37', '49'])).
% 22.50/22.79  thf(dt_k6_partfun1, axiom,
% 22.50/22.79    (![A:$i]:
% 22.50/22.79     ( ( m1_subset_1 @
% 22.50/22.79         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 22.50/22.79       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 22.50/22.79  thf('51', plain,
% 22.50/22.79      (![X44 : $i]:
% 22.50/22.79         (m1_subset_1 @ (k6_partfun1 @ X44) @ 
% 22.50/22.79          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X44)))),
% 22.50/22.79      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 22.50/22.79  thf('52', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A_1))),
% 22.50/22.79      inference('demod', [status(thm)], ['50', '51'])).
% 22.50/22.79  thf('53', plain,
% 22.50/22.79      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 22.50/22.79         = (k6_partfun1 @ sk_A_1))),
% 22.50/22.79      inference('demod', [status(thm)], ['34', '52'])).
% 22.50/22.79  thf('54', plain,
% 22.50/22.79      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf(t30_funct_2, axiom,
% 22.50/22.79    (![A:$i,B:$i,C:$i,D:$i]:
% 22.50/22.79     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 22.50/22.79         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 22.50/22.79       ( ![E:$i]:
% 22.50/22.79         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 22.50/22.79             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 22.50/22.79           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 22.50/22.79               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 22.50/22.79             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 22.50/22.79               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 22.50/22.79  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 22.50/22.79  thf(zf_stmt_2, axiom,
% 22.50/22.79    (![C:$i,B:$i]:
% 22.50/22.79     ( ( zip_tseitin_1 @ C @ B ) =>
% 22.50/22.79       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 22.50/22.79  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 22.50/22.79  thf(zf_stmt_4, axiom,
% 22.50/22.79    (![E:$i,D:$i]:
% 22.50/22.79     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 22.50/22.79  thf(zf_stmt_5, axiom,
% 22.50/22.79    (![A:$i,B:$i,C:$i,D:$i]:
% 22.50/22.79     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 22.50/22.79         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 22.50/22.79       ( ![E:$i]:
% 22.50/22.79         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 22.50/22.79             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 22.50/22.79           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 22.50/22.79               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 22.50/22.79             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 22.50/22.79  thf('55', plain,
% 22.50/22.79      (![X60 : $i, X61 : $i, X62 : $i, X63 : $i, X64 : $i]:
% 22.50/22.79         (~ (v1_funct_1 @ X60)
% 22.50/22.79          | ~ (v1_funct_2 @ X60 @ X61 @ X62)
% 22.50/22.79          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X61 @ X62)))
% 22.50/22.79          | (zip_tseitin_0 @ X60 @ X63)
% 22.50/22.79          | ~ (v2_funct_1 @ (k1_partfun1 @ X64 @ X61 @ X61 @ X62 @ X63 @ X60))
% 22.50/22.79          | (zip_tseitin_1 @ X62 @ X61)
% 22.50/22.79          | ((k2_relset_1 @ X64 @ X61 @ X63) != (X61))
% 22.50/22.79          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X64 @ X61)))
% 22.50/22.79          | ~ (v1_funct_2 @ X63 @ X64 @ X61)
% 22.50/22.79          | ~ (v1_funct_1 @ X63))),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_5])).
% 22.50/22.79  thf('56', plain,
% 22.50/22.79      (![X0 : $i, X1 : $i]:
% 22.50/22.79         (~ (v1_funct_1 @ X0)
% 22.50/22.79          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 22.50/22.79          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 22.50/22.79          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 22.50/22.79          | (zip_tseitin_1 @ sk_A_1 @ sk_B)
% 22.50/22.79          | ~ (v2_funct_1 @ 
% 22.50/22.79               (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A_1 @ X0 @ sk_D))
% 22.50/22.79          | (zip_tseitin_0 @ sk_D @ X0)
% 22.50/22.79          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A_1)
% 22.50/22.79          | ~ (v1_funct_1 @ sk_D))),
% 22.50/22.79      inference('sup-', [status(thm)], ['54', '55'])).
% 22.50/22.79  thf('57', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A_1)),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('58', plain, ((v1_funct_1 @ sk_D)),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('59', plain,
% 22.50/22.79      (![X0 : $i, X1 : $i]:
% 22.50/22.79         (~ (v1_funct_1 @ X0)
% 22.50/22.79          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 22.50/22.79          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 22.50/22.79          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 22.50/22.79          | (zip_tseitin_1 @ sk_A_1 @ sk_B)
% 22.50/22.79          | ~ (v2_funct_1 @ 
% 22.50/22.79               (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A_1 @ X0 @ sk_D))
% 22.50/22.79          | (zip_tseitin_0 @ sk_D @ X0))),
% 22.50/22.79      inference('demod', [status(thm)], ['56', '57', '58'])).
% 22.50/22.79  thf('60', plain,
% 22.50/22.79      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A_1))
% 22.50/22.79        | (zip_tseitin_0 @ sk_D @ sk_C)
% 22.50/22.79        | (zip_tseitin_1 @ sk_A_1 @ sk_B)
% 22.50/22.79        | ((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) != (sk_B))
% 22.50/22.79        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))
% 22.50/22.79        | ~ (v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)
% 22.50/22.79        | ~ (v1_funct_1 @ sk_C))),
% 22.50/22.79      inference('sup-', [status(thm)], ['53', '59'])).
% 22.50/22.79  thf(fc4_funct_1, axiom,
% 22.50/22.79    (![A:$i]:
% 22.50/22.79     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 22.50/22.79       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 22.50/22.79  thf('61', plain, (![X20 : $i]: (v2_funct_1 @ (k6_relat_1 @ X20))),
% 22.50/22.79      inference('cnf', [status(esa)], [fc4_funct_1])).
% 22.50/22.79  thf(redefinition_k6_partfun1, axiom,
% 22.50/22.79    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 22.50/22.79  thf('62', plain, (![X51 : $i]: ((k6_partfun1 @ X51) = (k6_relat_1 @ X51))),
% 22.50/22.79      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 22.50/22.79  thf('63', plain, (![X20 : $i]: (v2_funct_1 @ (k6_partfun1 @ X20))),
% 22.50/22.79      inference('demod', [status(thm)], ['61', '62'])).
% 22.50/22.79  thf('64', plain, (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (sk_B))),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('65', plain,
% 22.50/22.79      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('66', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('68', plain,
% 22.50/22.79      (((zip_tseitin_0 @ sk_D @ sk_C)
% 22.50/22.79        | (zip_tseitin_1 @ sk_A_1 @ sk_B)
% 22.50/22.79        | ((sk_B) != (sk_B)))),
% 22.50/22.79      inference('demod', [status(thm)], ['60', '63', '64', '65', '66', '67'])).
% 22.50/22.79  thf('69', plain,
% 22.50/22.79      (((zip_tseitin_1 @ sk_A_1 @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 22.50/22.79      inference('simplify', [status(thm)], ['68'])).
% 22.50/22.79  thf('70', plain,
% 22.50/22.79      (![X58 : $i, X59 : $i]:
% 22.50/22.79         (((X58) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X58 @ X59))),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_2])).
% 22.50/22.79  thf('71', plain,
% 22.50/22.79      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A_1) = (k1_xboole_0)))),
% 22.50/22.79      inference('sup-', [status(thm)], ['69', '70'])).
% 22.50/22.79  thf('72', plain, (((sk_A_1) != (k1_xboole_0))),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('73', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 22.50/22.79      inference('simplify_reflect-', [status(thm)], ['71', '72'])).
% 22.50/22.79  thf('74', plain,
% 22.50/22.79      (![X56 : $i, X57 : $i]:
% 22.50/22.79         ((v2_funct_1 @ X57) | ~ (zip_tseitin_0 @ X57 @ X56))),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_4])).
% 22.50/22.79  thf('75', plain, ((v2_funct_1 @ sk_D)),
% 22.50/22.79      inference('sup-', [status(thm)], ['73', '74'])).
% 22.50/22.79  thf('76', plain,
% 22.50/22.79      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 22.50/22.79      inference('demod', [status(thm)], ['25', '75'])).
% 22.50/22.79  thf(t58_funct_1, axiom,
% 22.50/22.79    (![A:$i]:
% 22.50/22.79     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 22.50/22.79       ( ( v2_funct_1 @ A ) =>
% 22.50/22.79         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 22.50/22.79             ( k1_relat_1 @ A ) ) & 
% 22.50/22.79           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 22.50/22.79             ( k1_relat_1 @ A ) ) ) ) ))).
% 22.50/22.79  thf('77', plain,
% 22.50/22.79      (![X25 : $i]:
% 22.50/22.79         (~ (v2_funct_1 @ X25)
% 22.50/22.79          | ((k2_relat_1 @ (k5_relat_1 @ X25 @ (k2_funct_1 @ X25)))
% 22.50/22.79              = (k1_relat_1 @ X25))
% 22.50/22.79          | ~ (v1_funct_1 @ X25)
% 22.50/22.79          | ~ (v1_relat_1 @ X25))),
% 22.50/22.79      inference('cnf', [status(esa)], [t58_funct_1])).
% 22.50/22.79  thf('78', plain,
% 22.50/22.79      ((((k2_relat_1 @ (k6_partfun1 @ sk_B)) = (k1_relat_1 @ sk_D))
% 22.50/22.79        | ~ (v1_relat_1 @ sk_D)
% 22.50/22.79        | ~ (v1_funct_1 @ sk_D)
% 22.50/22.79        | ~ (v2_funct_1 @ sk_D))),
% 22.50/22.79      inference('sup+', [status(thm)], ['76', '77'])).
% 22.50/22.79  thf(t71_relat_1, axiom,
% 22.50/22.79    (![A:$i]:
% 22.50/22.79     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 22.50/22.79       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 22.50/22.79  thf('79', plain, (![X13 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 22.50/22.79      inference('cnf', [status(esa)], [t71_relat_1])).
% 22.50/22.79  thf('80', plain, (![X51 : $i]: ((k6_partfun1 @ X51) = (k6_relat_1 @ X51))),
% 22.50/22.79      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 22.50/22.79  thf('81', plain, (![X13 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X13)) = (X13))),
% 22.50/22.79      inference('demod', [status(thm)], ['79', '80'])).
% 22.50/22.79  thf('82', plain,
% 22.50/22.79      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf(cc2_relat_1, axiom,
% 22.50/22.79    (![A:$i]:
% 22.50/22.79     ( ( v1_relat_1 @ A ) =>
% 22.50/22.79       ( ![B:$i]:
% 22.50/22.79         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 22.50/22.79  thf('83', plain,
% 22.50/22.79      (![X3 : $i, X4 : $i]:
% 22.50/22.79         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 22.50/22.79          | (v1_relat_1 @ X3)
% 22.50/22.79          | ~ (v1_relat_1 @ X4))),
% 22.50/22.79      inference('cnf', [status(esa)], [cc2_relat_1])).
% 22.50/22.79  thf('84', plain,
% 22.50/22.79      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)) | (v1_relat_1 @ sk_D))),
% 22.50/22.79      inference('sup-', [status(thm)], ['82', '83'])).
% 22.50/22.79  thf(fc6_relat_1, axiom,
% 22.50/22.79    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 22.50/22.79  thf('85', plain,
% 22.50/22.79      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 22.50/22.79      inference('cnf', [status(esa)], [fc6_relat_1])).
% 22.50/22.79  thf('86', plain, ((v1_relat_1 @ sk_D)),
% 22.50/22.79      inference('demod', [status(thm)], ['84', '85'])).
% 22.50/22.79  thf('87', plain, ((v1_funct_1 @ sk_D)),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('88', plain, ((v2_funct_1 @ sk_D)),
% 22.50/22.79      inference('sup-', [status(thm)], ['73', '74'])).
% 22.50/22.79  thf('89', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 22.50/22.79      inference('demod', [status(thm)], ['78', '81', '86', '87', '88'])).
% 22.50/22.79  thf(t78_relat_1, axiom,
% 22.50/22.79    (![A:$i]:
% 22.50/22.79     ( ( v1_relat_1 @ A ) =>
% 22.50/22.79       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 22.50/22.79  thf('90', plain,
% 22.50/22.79      (![X14 : $i]:
% 22.50/22.79         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X14)) @ X14) = (X14))
% 22.50/22.79          | ~ (v1_relat_1 @ X14))),
% 22.50/22.79      inference('cnf', [status(esa)], [t78_relat_1])).
% 22.50/22.79  thf('91', plain, (![X51 : $i]: ((k6_partfun1 @ X51) = (k6_relat_1 @ X51))),
% 22.50/22.79      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 22.50/22.79  thf('92', plain,
% 22.50/22.79      (![X14 : $i]:
% 22.50/22.79         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X14)) @ X14) = (X14))
% 22.50/22.79          | ~ (v1_relat_1 @ X14))),
% 22.50/22.79      inference('demod', [status(thm)], ['90', '91'])).
% 22.50/22.79  thf('93', plain,
% 22.50/22.79      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))
% 22.50/22.79        | ~ (v1_relat_1 @ sk_D))),
% 22.50/22.79      inference('sup+', [status(thm)], ['89', '92'])).
% 22.50/22.79  thf('94', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A_1))),
% 22.50/22.79      inference('demod', [status(thm)], ['50', '51'])).
% 22.50/22.79  thf(dt_k2_funct_1, axiom,
% 22.50/22.79    (![A:$i]:
% 22.50/22.79     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 22.50/22.79       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 22.50/22.79         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 22.50/22.79  thf('95', plain,
% 22.50/22.79      (![X16 : $i]:
% 22.50/22.79         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 22.50/22.79          | ~ (v1_funct_1 @ X16)
% 22.50/22.79          | ~ (v1_relat_1 @ X16))),
% 22.50/22.79      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 22.50/22.79  thf(t61_funct_1, axiom,
% 22.50/22.79    (![A:$i]:
% 22.50/22.79     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 22.50/22.79       ( ( v2_funct_1 @ A ) =>
% 22.50/22.79         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 22.50/22.79             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 22.50/22.79           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 22.50/22.79             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 22.50/22.79  thf('96', plain,
% 22.50/22.79      (![X26 : $i]:
% 22.50/22.79         (~ (v2_funct_1 @ X26)
% 22.50/22.79          | ((k5_relat_1 @ (k2_funct_1 @ X26) @ X26)
% 22.50/22.79              = (k6_relat_1 @ (k2_relat_1 @ X26)))
% 22.50/22.79          | ~ (v1_funct_1 @ X26)
% 22.50/22.79          | ~ (v1_relat_1 @ X26))),
% 22.50/22.79      inference('cnf', [status(esa)], [t61_funct_1])).
% 22.50/22.79  thf('97', plain, (![X51 : $i]: ((k6_partfun1 @ X51) = (k6_relat_1 @ X51))),
% 22.50/22.79      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 22.50/22.79  thf('98', plain,
% 22.50/22.79      (![X26 : $i]:
% 22.50/22.79         (~ (v2_funct_1 @ X26)
% 22.50/22.79          | ((k5_relat_1 @ (k2_funct_1 @ X26) @ X26)
% 22.50/22.79              = (k6_partfun1 @ (k2_relat_1 @ X26)))
% 22.50/22.79          | ~ (v1_funct_1 @ X26)
% 22.50/22.79          | ~ (v1_relat_1 @ X26))),
% 22.50/22.79      inference('demod', [status(thm)], ['96', '97'])).
% 22.50/22.79  thf('99', plain,
% 22.50/22.79      (![X16 : $i]:
% 22.50/22.79         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 22.50/22.79          | ~ (v1_funct_1 @ X16)
% 22.50/22.79          | ~ (v1_relat_1 @ X16))),
% 22.50/22.79      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 22.50/22.79  thf('100', plain,
% 22.50/22.79      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('101', plain,
% 22.50/22.79      (![X30 : $i, X31 : $i, X32 : $i]:
% 22.50/22.79         (((k2_relset_1 @ X31 @ X32 @ X30) = (k2_relat_1 @ X30))
% 22.50/22.79          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 22.50/22.79      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 22.50/22.79  thf('102', plain,
% 22.50/22.79      (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 22.50/22.79      inference('sup-', [status(thm)], ['100', '101'])).
% 22.50/22.79  thf('103', plain, (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (sk_B))),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('104', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 22.50/22.79      inference('sup+', [status(thm)], ['102', '103'])).
% 22.50/22.79  thf('105', plain,
% 22.50/22.79      (![X16 : $i]:
% 22.50/22.79         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 22.50/22.79          | ~ (v1_funct_1 @ X16)
% 22.50/22.79          | ~ (v1_relat_1 @ X16))),
% 22.50/22.79      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 22.50/22.79  thf(t55_funct_1, axiom,
% 22.50/22.79    (![A:$i]:
% 22.50/22.79     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 22.50/22.79       ( ( v2_funct_1 @ A ) =>
% 22.50/22.79         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 22.50/22.79           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 22.50/22.79  thf('106', plain,
% 22.50/22.79      (![X24 : $i]:
% 22.50/22.79         (~ (v2_funct_1 @ X24)
% 22.50/22.79          | ((k2_relat_1 @ X24) = (k1_relat_1 @ (k2_funct_1 @ X24)))
% 22.50/22.79          | ~ (v1_funct_1 @ X24)
% 22.50/22.79          | ~ (v1_relat_1 @ X24))),
% 22.50/22.79      inference('cnf', [status(esa)], [t55_funct_1])).
% 22.50/22.79  thf('107', plain,
% 22.50/22.79      (![X14 : $i]:
% 22.50/22.79         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X14)) @ X14) = (X14))
% 22.50/22.79          | ~ (v1_relat_1 @ X14))),
% 22.50/22.79      inference('demod', [status(thm)], ['90', '91'])).
% 22.50/22.79  thf('108', plain,
% 22.50/22.79      (![X0 : $i]:
% 22.50/22.79         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 22.50/22.79            = (k2_funct_1 @ X0))
% 22.50/22.79          | ~ (v1_relat_1 @ X0)
% 22.50/22.79          | ~ (v1_funct_1 @ X0)
% 22.50/22.79          | ~ (v2_funct_1 @ X0)
% 22.50/22.79          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 22.50/22.79      inference('sup+', [status(thm)], ['106', '107'])).
% 22.50/22.79  thf('109', plain,
% 22.50/22.79      (![X0 : $i]:
% 22.50/22.79         (~ (v1_relat_1 @ X0)
% 22.50/22.79          | ~ (v1_funct_1 @ X0)
% 22.50/22.79          | ~ (v2_funct_1 @ X0)
% 22.50/22.79          | ~ (v1_funct_1 @ X0)
% 22.50/22.79          | ~ (v1_relat_1 @ X0)
% 22.50/22.79          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 22.50/22.79              (k2_funct_1 @ X0)) = (k2_funct_1 @ X0)))),
% 22.50/22.79      inference('sup-', [status(thm)], ['105', '108'])).
% 22.50/22.79  thf('110', plain,
% 22.50/22.79      (![X0 : $i]:
% 22.50/22.79         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 22.50/22.79            = (k2_funct_1 @ X0))
% 22.50/22.79          | ~ (v2_funct_1 @ X0)
% 22.50/22.79          | ~ (v1_funct_1 @ X0)
% 22.50/22.79          | ~ (v1_relat_1 @ X0))),
% 22.50/22.79      inference('simplify', [status(thm)], ['109'])).
% 22.50/22.79  thf('111', plain,
% 22.50/22.79      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 22.50/22.79          = (k2_funct_1 @ sk_C))
% 22.50/22.79        | ~ (v1_relat_1 @ sk_C)
% 22.50/22.79        | ~ (v1_funct_1 @ sk_C)
% 22.50/22.79        | ~ (v2_funct_1 @ sk_C))),
% 22.50/22.79      inference('sup+', [status(thm)], ['104', '110'])).
% 22.50/22.79  thf('112', plain,
% 22.50/22.79      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('113', plain,
% 22.50/22.79      (![X3 : $i, X4 : $i]:
% 22.50/22.79         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 22.50/22.79          | (v1_relat_1 @ X3)
% 22.50/22.79          | ~ (v1_relat_1 @ X4))),
% 22.50/22.79      inference('cnf', [status(esa)], [cc2_relat_1])).
% 22.50/22.79  thf('114', plain,
% 22.50/22.79      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)) | (v1_relat_1 @ sk_C))),
% 22.50/22.79      inference('sup-', [status(thm)], ['112', '113'])).
% 22.50/22.79  thf('115', plain,
% 22.50/22.79      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 22.50/22.79      inference('cnf', [status(esa)], [fc6_relat_1])).
% 22.50/22.79  thf('116', plain, ((v1_relat_1 @ sk_C)),
% 22.50/22.79      inference('demod', [status(thm)], ['114', '115'])).
% 22.50/22.79  thf('117', plain, ((v1_funct_1 @ sk_C)),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('118', plain, ((v2_funct_1 @ sk_C)),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('119', plain,
% 22.50/22.79      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 22.50/22.79         = (k2_funct_1 @ sk_C))),
% 22.50/22.79      inference('demod', [status(thm)], ['111', '116', '117', '118'])).
% 22.50/22.79  thf(t55_relat_1, axiom,
% 22.50/22.79    (![A:$i]:
% 22.50/22.79     ( ( v1_relat_1 @ A ) =>
% 22.50/22.79       ( ![B:$i]:
% 22.50/22.79         ( ( v1_relat_1 @ B ) =>
% 22.50/22.79           ( ![C:$i]:
% 22.50/22.79             ( ( v1_relat_1 @ C ) =>
% 22.50/22.79               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 22.50/22.79                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 22.50/22.79  thf('120', plain,
% 22.50/22.79      (![X9 : $i, X10 : $i, X11 : $i]:
% 22.50/22.79         (~ (v1_relat_1 @ X9)
% 22.50/22.79          | ((k5_relat_1 @ (k5_relat_1 @ X10 @ X9) @ X11)
% 22.50/22.79              = (k5_relat_1 @ X10 @ (k5_relat_1 @ X9 @ X11)))
% 22.50/22.79          | ~ (v1_relat_1 @ X11)
% 22.50/22.79          | ~ (v1_relat_1 @ X10))),
% 22.50/22.79      inference('cnf', [status(esa)], [t55_relat_1])).
% 22.50/22.79  thf('121', plain,
% 22.50/22.79      (![X0 : $i]:
% 22.50/22.79         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 22.50/22.79            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 22.50/22.79               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 22.50/22.79          | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B))
% 22.50/22.79          | ~ (v1_relat_1 @ X0)
% 22.50/22.79          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 22.50/22.79      inference('sup+', [status(thm)], ['119', '120'])).
% 22.50/22.79  thf(fc3_funct_1, axiom,
% 22.50/22.79    (![A:$i]:
% 22.50/22.79     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 22.50/22.79       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 22.50/22.79  thf('122', plain, (![X17 : $i]: (v1_relat_1 @ (k6_relat_1 @ X17))),
% 22.50/22.79      inference('cnf', [status(esa)], [fc3_funct_1])).
% 22.50/22.79  thf('123', plain, (![X51 : $i]: ((k6_partfun1 @ X51) = (k6_relat_1 @ X51))),
% 22.50/22.79      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 22.50/22.79  thf('124', plain, (![X17 : $i]: (v1_relat_1 @ (k6_partfun1 @ X17))),
% 22.50/22.79      inference('demod', [status(thm)], ['122', '123'])).
% 22.50/22.79  thf('125', plain,
% 22.50/22.79      (![X0 : $i]:
% 22.50/22.79         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 22.50/22.79            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 22.50/22.79               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 22.50/22.79          | ~ (v1_relat_1 @ X0)
% 22.50/22.79          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 22.50/22.79      inference('demod', [status(thm)], ['121', '124'])).
% 22.50/22.79  thf('126', plain,
% 22.50/22.79      (![X0 : $i]:
% 22.50/22.79         (~ (v1_relat_1 @ sk_C)
% 22.50/22.79          | ~ (v1_funct_1 @ sk_C)
% 22.50/22.79          | ~ (v1_relat_1 @ X0)
% 22.50/22.79          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 22.50/22.79              = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 22.50/22.79                 (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))))),
% 22.50/22.79      inference('sup-', [status(thm)], ['99', '125'])).
% 22.50/22.79  thf('127', plain, ((v1_relat_1 @ sk_C)),
% 22.50/22.79      inference('demod', [status(thm)], ['114', '115'])).
% 22.50/22.79  thf('128', plain, ((v1_funct_1 @ sk_C)),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('129', plain,
% 22.50/22.79      (![X0 : $i]:
% 22.50/22.79         (~ (v1_relat_1 @ X0)
% 22.50/22.79          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 22.50/22.79              = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 22.50/22.79                 (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))))),
% 22.50/22.79      inference('demod', [status(thm)], ['126', '127', '128'])).
% 22.50/22.79  thf('130', plain,
% 22.50/22.79      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 22.50/22.79          = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 22.50/22.79             (k6_partfun1 @ (k2_relat_1 @ sk_C))))
% 22.50/22.79        | ~ (v1_relat_1 @ sk_C)
% 22.50/22.79        | ~ (v1_funct_1 @ sk_C)
% 22.50/22.79        | ~ (v2_funct_1 @ sk_C)
% 22.50/22.79        | ~ (v1_relat_1 @ sk_C))),
% 22.50/22.79      inference('sup+', [status(thm)], ['98', '129'])).
% 22.50/22.79  thf('131', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 22.50/22.79      inference('sup+', [status(thm)], ['102', '103'])).
% 22.50/22.79  thf('132', plain, (![X12 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 22.50/22.79      inference('cnf', [status(esa)], [t71_relat_1])).
% 22.50/22.79  thf('133', plain, (![X51 : $i]: ((k6_partfun1 @ X51) = (k6_relat_1 @ X51))),
% 22.50/22.79      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 22.50/22.79  thf('134', plain,
% 22.50/22.79      (![X12 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X12)) = (X12))),
% 22.50/22.79      inference('demod', [status(thm)], ['132', '133'])).
% 22.50/22.79  thf('135', plain,
% 22.50/22.79      (![X14 : $i]:
% 22.50/22.79         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X14)) @ X14) = (X14))
% 22.50/22.79          | ~ (v1_relat_1 @ X14))),
% 22.50/22.79      inference('demod', [status(thm)], ['90', '91'])).
% 22.50/22.79  thf('136', plain,
% 22.50/22.79      (![X0 : $i]:
% 22.50/22.79         (((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 22.50/22.79            = (k6_partfun1 @ X0))
% 22.50/22.79          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 22.50/22.79      inference('sup+', [status(thm)], ['134', '135'])).
% 22.50/22.79  thf('137', plain, (![X17 : $i]: (v1_relat_1 @ (k6_partfun1 @ X17))),
% 22.50/22.79      inference('demod', [status(thm)], ['122', '123'])).
% 22.50/22.79  thf('138', plain,
% 22.50/22.79      (![X0 : $i]:
% 22.50/22.79         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 22.50/22.79           = (k6_partfun1 @ X0))),
% 22.50/22.79      inference('demod', [status(thm)], ['136', '137'])).
% 22.50/22.79  thf('139', plain, ((v1_relat_1 @ sk_C)),
% 22.50/22.79      inference('demod', [status(thm)], ['114', '115'])).
% 22.50/22.79  thf('140', plain, ((v1_funct_1 @ sk_C)),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('141', plain, ((v2_funct_1 @ sk_C)),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('142', plain, ((v1_relat_1 @ sk_C)),
% 22.50/22.79      inference('demod', [status(thm)], ['114', '115'])).
% 22.50/22.79  thf('143', plain,
% 22.50/22.79      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 22.50/22.79      inference('demod', [status(thm)],
% 22.50/22.79                ['130', '131', '138', '139', '140', '141', '142'])).
% 22.50/22.79  thf('144', plain,
% 22.50/22.79      (![X9 : $i, X10 : $i, X11 : $i]:
% 22.50/22.79         (~ (v1_relat_1 @ X9)
% 22.50/22.79          | ((k5_relat_1 @ (k5_relat_1 @ X10 @ X9) @ X11)
% 22.50/22.79              = (k5_relat_1 @ X10 @ (k5_relat_1 @ X9 @ X11)))
% 22.50/22.79          | ~ (v1_relat_1 @ X11)
% 22.50/22.79          | ~ (v1_relat_1 @ X10))),
% 22.50/22.79      inference('cnf', [status(esa)], [t55_relat_1])).
% 22.50/22.79  thf('145', plain,
% 22.50/22.79      (![X0 : $i]:
% 22.50/22.79         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 22.50/22.79            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 22.50/22.79          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 22.50/22.79          | ~ (v1_relat_1 @ X0)
% 22.50/22.79          | ~ (v1_relat_1 @ sk_C))),
% 22.50/22.79      inference('sup+', [status(thm)], ['143', '144'])).
% 22.50/22.79  thf('146', plain, ((v1_relat_1 @ sk_C)),
% 22.50/22.79      inference('demod', [status(thm)], ['114', '115'])).
% 22.50/22.79  thf('147', plain,
% 22.50/22.79      (![X0 : $i]:
% 22.50/22.79         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 22.50/22.79            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 22.50/22.79          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 22.50/22.79          | ~ (v1_relat_1 @ X0))),
% 22.50/22.79      inference('demod', [status(thm)], ['145', '146'])).
% 22.50/22.79  thf('148', plain,
% 22.50/22.79      (![X0 : $i]:
% 22.50/22.79         (~ (v1_relat_1 @ sk_C)
% 22.50/22.79          | ~ (v1_funct_1 @ sk_C)
% 22.50/22.79          | ~ (v1_relat_1 @ X0)
% 22.50/22.79          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 22.50/22.79              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 22.50/22.79      inference('sup-', [status(thm)], ['95', '147'])).
% 22.50/22.79  thf('149', plain, ((v1_relat_1 @ sk_C)),
% 22.50/22.79      inference('demod', [status(thm)], ['114', '115'])).
% 22.50/22.79  thf('150', plain, ((v1_funct_1 @ sk_C)),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('151', plain,
% 22.50/22.79      (![X0 : $i]:
% 22.50/22.79         (~ (v1_relat_1 @ X0)
% 22.50/22.79          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 22.50/22.79              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 22.50/22.79      inference('demod', [status(thm)], ['148', '149', '150'])).
% 22.50/22.79  thf('152', plain,
% 22.50/22.79      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 22.50/22.79          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A_1)))
% 22.50/22.79        | ~ (v1_relat_1 @ sk_D))),
% 22.50/22.79      inference('sup+', [status(thm)], ['94', '151'])).
% 22.50/22.79  thf('153', plain,
% 22.50/22.79      (![X16 : $i]:
% 22.50/22.79         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 22.50/22.79          | ~ (v1_funct_1 @ X16)
% 22.50/22.79          | ~ (v1_relat_1 @ X16))),
% 22.50/22.79      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 22.50/22.79  thf('154', plain,
% 22.50/22.79      (![X24 : $i]:
% 22.50/22.79         (~ (v2_funct_1 @ X24)
% 22.50/22.79          | ((k1_relat_1 @ X24) = (k2_relat_1 @ (k2_funct_1 @ X24)))
% 22.50/22.79          | ~ (v1_funct_1 @ X24)
% 22.50/22.79          | ~ (v1_relat_1 @ X24))),
% 22.50/22.79      inference('cnf', [status(esa)], [t55_funct_1])).
% 22.50/22.79  thf(t80_relat_1, axiom,
% 22.50/22.79    (![A:$i]:
% 22.50/22.79     ( ( v1_relat_1 @ A ) =>
% 22.50/22.79       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 22.50/22.79  thf('155', plain,
% 22.50/22.79      (![X15 : $i]:
% 22.50/22.79         (((k5_relat_1 @ X15 @ (k6_relat_1 @ (k2_relat_1 @ X15))) = (X15))
% 22.50/22.79          | ~ (v1_relat_1 @ X15))),
% 22.50/22.79      inference('cnf', [status(esa)], [t80_relat_1])).
% 22.50/22.79  thf('156', plain, (![X51 : $i]: ((k6_partfun1 @ X51) = (k6_relat_1 @ X51))),
% 22.50/22.79      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 22.50/22.79  thf('157', plain,
% 22.50/22.79      (![X15 : $i]:
% 22.50/22.79         (((k5_relat_1 @ X15 @ (k6_partfun1 @ (k2_relat_1 @ X15))) = (X15))
% 22.50/22.79          | ~ (v1_relat_1 @ X15))),
% 22.50/22.79      inference('demod', [status(thm)], ['155', '156'])).
% 22.50/22.79  thf('158', plain,
% 22.50/22.79      (![X0 : $i]:
% 22.50/22.79         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 22.50/22.79            = (k2_funct_1 @ X0))
% 22.50/22.79          | ~ (v1_relat_1 @ X0)
% 22.50/22.79          | ~ (v1_funct_1 @ X0)
% 22.50/22.79          | ~ (v2_funct_1 @ X0)
% 22.50/22.79          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 22.50/22.79      inference('sup+', [status(thm)], ['154', '157'])).
% 22.50/22.79  thf('159', plain,
% 22.50/22.79      (![X0 : $i]:
% 22.50/22.79         (~ (v1_relat_1 @ X0)
% 22.50/22.79          | ~ (v1_funct_1 @ X0)
% 22.50/22.79          | ~ (v2_funct_1 @ X0)
% 22.50/22.79          | ~ (v1_funct_1 @ X0)
% 22.50/22.79          | ~ (v1_relat_1 @ X0)
% 22.50/22.79          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 22.50/22.79              (k6_partfun1 @ (k1_relat_1 @ X0))) = (k2_funct_1 @ X0)))),
% 22.50/22.79      inference('sup-', [status(thm)], ['153', '158'])).
% 22.50/22.79  thf('160', plain,
% 22.50/22.79      (![X0 : $i]:
% 22.50/22.79         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 22.50/22.79            = (k2_funct_1 @ X0))
% 22.50/22.79          | ~ (v2_funct_1 @ X0)
% 22.50/22.79          | ~ (v1_funct_1 @ X0)
% 22.50/22.79          | ~ (v1_relat_1 @ X0))),
% 22.50/22.79      inference('simplify', [status(thm)], ['159'])).
% 22.50/22.79  thf('161', plain,
% 22.50/22.79      (![X0 : $i]:
% 22.50/22.79         (~ (v1_relat_1 @ X0)
% 22.50/22.79          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 22.50/22.79              = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 22.50/22.79                 (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))))),
% 22.50/22.79      inference('demod', [status(thm)], ['126', '127', '128'])).
% 22.50/22.79  thf('162', plain,
% 22.50/22.79      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 22.50/22.79          (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 22.50/22.79          = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C)))
% 22.50/22.79        | ~ (v1_relat_1 @ sk_C)
% 22.50/22.79        | ~ (v1_funct_1 @ sk_C)
% 22.50/22.79        | ~ (v2_funct_1 @ sk_C)
% 22.50/22.79        | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C))))),
% 22.50/22.79      inference('sup+', [status(thm)], ['160', '161'])).
% 22.50/22.79  thf('163', plain,
% 22.50/22.79      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 22.50/22.79         = (k2_funct_1 @ sk_C))),
% 22.50/22.79      inference('demod', [status(thm)], ['111', '116', '117', '118'])).
% 22.50/22.79  thf('164', plain, ((v1_relat_1 @ sk_C)),
% 22.50/22.79      inference('demod', [status(thm)], ['114', '115'])).
% 22.50/22.79  thf('165', plain, ((v1_funct_1 @ sk_C)),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('166', plain, ((v2_funct_1 @ sk_C)),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('167', plain, (![X17 : $i]: (v1_relat_1 @ (k6_partfun1 @ X17))),
% 22.50/22.79      inference('demod', [status(thm)], ['122', '123'])).
% 22.50/22.79  thf('168', plain,
% 22.50/22.79      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 22.50/22.79         = (k2_funct_1 @ sk_C))),
% 22.50/22.79      inference('demod', [status(thm)],
% 22.50/22.79                ['162', '163', '164', '165', '166', '167'])).
% 22.50/22.79  thf('169', plain,
% 22.50/22.79      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('170', plain,
% 22.50/22.79      (![X65 : $i, X66 : $i, X67 : $i]:
% 22.50/22.79         (((X65) = (k1_xboole_0))
% 22.50/22.79          | ~ (v1_funct_1 @ X66)
% 22.50/22.79          | ~ (v1_funct_2 @ X66 @ X67 @ X65)
% 22.50/22.79          | ~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X67 @ X65)))
% 22.50/22.79          | ((k5_relat_1 @ X66 @ (k2_funct_1 @ X66)) = (k6_partfun1 @ X67))
% 22.50/22.79          | ~ (v2_funct_1 @ X66)
% 22.50/22.79          | ((k2_relset_1 @ X67 @ X65 @ X66) != (X65)))),
% 22.50/22.79      inference('cnf', [status(esa)], [t35_funct_2])).
% 22.50/22.79  thf('171', plain,
% 22.50/22.79      ((((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) != (sk_B))
% 22.50/22.79        | ~ (v2_funct_1 @ sk_C)
% 22.50/22.79        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A_1))
% 22.50/22.79        | ~ (v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)
% 22.50/22.79        | ~ (v1_funct_1 @ sk_C)
% 22.50/22.79        | ((sk_B) = (k1_xboole_0)))),
% 22.50/22.79      inference('sup-', [status(thm)], ['169', '170'])).
% 22.50/22.79  thf('172', plain, (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (sk_B))),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('173', plain, ((v2_funct_1 @ sk_C)),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('174', plain,
% 22.50/22.79      (![X16 : $i]:
% 22.50/22.79         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 22.50/22.79          | ~ (v1_funct_1 @ X16)
% 22.50/22.79          | ~ (v1_relat_1 @ X16))),
% 22.50/22.79      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 22.50/22.79  thf('175', plain,
% 22.50/22.79      (![X26 : $i]:
% 22.50/22.79         (~ (v2_funct_1 @ X26)
% 22.50/22.79          | ((k5_relat_1 @ X26 @ (k2_funct_1 @ X26))
% 22.50/22.79              = (k6_relat_1 @ (k1_relat_1 @ X26)))
% 22.50/22.79          | ~ (v1_funct_1 @ X26)
% 22.50/22.79          | ~ (v1_relat_1 @ X26))),
% 22.50/22.79      inference('cnf', [status(esa)], [t61_funct_1])).
% 22.50/22.79  thf('176', plain, (![X51 : $i]: ((k6_partfun1 @ X51) = (k6_relat_1 @ X51))),
% 22.50/22.79      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 22.50/22.79  thf('177', plain,
% 22.50/22.79      (![X26 : $i]:
% 22.50/22.79         (~ (v2_funct_1 @ X26)
% 22.50/22.79          | ((k5_relat_1 @ X26 @ (k2_funct_1 @ X26))
% 22.50/22.79              = (k6_partfun1 @ (k1_relat_1 @ X26)))
% 22.50/22.79          | ~ (v1_funct_1 @ X26)
% 22.50/22.79          | ~ (v1_relat_1 @ X26))),
% 22.50/22.79      inference('demod', [status(thm)], ['175', '176'])).
% 22.50/22.79  thf('178', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 22.50/22.79      inference('sup+', [status(thm)], ['102', '103'])).
% 22.50/22.79  thf('179', plain,
% 22.50/22.79      (![X15 : $i]:
% 22.50/22.79         (((k5_relat_1 @ X15 @ (k6_partfun1 @ (k2_relat_1 @ X15))) = (X15))
% 22.50/22.79          | ~ (v1_relat_1 @ X15))),
% 22.50/22.79      inference('demod', [status(thm)], ['155', '156'])).
% 22.50/22.79  thf('180', plain,
% 22.50/22.79      ((((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))
% 22.50/22.79        | ~ (v1_relat_1 @ sk_C))),
% 22.50/22.79      inference('sup+', [status(thm)], ['178', '179'])).
% 22.50/22.79  thf('181', plain, ((v1_relat_1 @ sk_C)),
% 22.50/22.79      inference('demod', [status(thm)], ['114', '115'])).
% 22.50/22.79  thf('182', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 22.50/22.79      inference('demod', [status(thm)], ['180', '181'])).
% 22.50/22.79  thf('183', plain,
% 22.50/22.79      (![X14 : $i]:
% 22.50/22.79         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X14)) @ X14) = (X14))
% 22.50/22.79          | ~ (v1_relat_1 @ X14))),
% 22.50/22.79      inference('demod', [status(thm)], ['90', '91'])).
% 22.50/22.79  thf('184', plain,
% 22.50/22.79      (![X9 : $i, X10 : $i, X11 : $i]:
% 22.50/22.79         (~ (v1_relat_1 @ X9)
% 22.50/22.79          | ((k5_relat_1 @ (k5_relat_1 @ X10 @ X9) @ X11)
% 22.50/22.79              = (k5_relat_1 @ X10 @ (k5_relat_1 @ X9 @ X11)))
% 22.50/22.79          | ~ (v1_relat_1 @ X11)
% 22.50/22.79          | ~ (v1_relat_1 @ X10))),
% 22.50/22.79      inference('cnf', [status(esa)], [t55_relat_1])).
% 22.50/22.79  thf('185', plain,
% 22.50/22.79      (![X0 : $i, X1 : $i]:
% 22.50/22.79         (((k5_relat_1 @ X0 @ X1)
% 22.50/22.79            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 22.50/22.79               (k5_relat_1 @ X0 @ X1)))
% 22.50/22.79          | ~ (v1_relat_1 @ X0)
% 22.50/22.79          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 22.50/22.79          | ~ (v1_relat_1 @ X1)
% 22.50/22.79          | ~ (v1_relat_1 @ X0))),
% 22.50/22.79      inference('sup+', [status(thm)], ['183', '184'])).
% 22.50/22.79  thf('186', plain, (![X17 : $i]: (v1_relat_1 @ (k6_partfun1 @ X17))),
% 22.50/22.79      inference('demod', [status(thm)], ['122', '123'])).
% 22.50/22.79  thf('187', plain,
% 22.50/22.79      (![X0 : $i, X1 : $i]:
% 22.50/22.79         (((k5_relat_1 @ X0 @ X1)
% 22.50/22.79            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 22.50/22.79               (k5_relat_1 @ X0 @ X1)))
% 22.50/22.79          | ~ (v1_relat_1 @ X0)
% 22.50/22.79          | ~ (v1_relat_1 @ X1)
% 22.50/22.79          | ~ (v1_relat_1 @ X0))),
% 22.50/22.79      inference('demod', [status(thm)], ['185', '186'])).
% 22.50/22.79  thf('188', plain,
% 22.50/22.79      (![X0 : $i, X1 : $i]:
% 22.50/22.79         (~ (v1_relat_1 @ X1)
% 22.50/22.79          | ~ (v1_relat_1 @ X0)
% 22.50/22.79          | ((k5_relat_1 @ X0 @ X1)
% 22.50/22.79              = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 22.50/22.79                 (k5_relat_1 @ X0 @ X1))))),
% 22.50/22.79      inference('simplify', [status(thm)], ['187'])).
% 22.50/22.79  thf('189', plain,
% 22.50/22.79      ((((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B))
% 22.50/22.79          = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ sk_C))
% 22.50/22.79        | ~ (v1_relat_1 @ sk_C)
% 22.50/22.79        | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B)))),
% 22.50/22.79      inference('sup+', [status(thm)], ['182', '188'])).
% 22.50/22.79  thf('190', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 22.50/22.79      inference('demod', [status(thm)], ['180', '181'])).
% 22.50/22.79  thf('191', plain, ((v1_relat_1 @ sk_C)),
% 22.50/22.79      inference('demod', [status(thm)], ['114', '115'])).
% 22.50/22.79  thf('192', plain, (![X17 : $i]: (v1_relat_1 @ (k6_partfun1 @ X17))),
% 22.50/22.79      inference('demod', [status(thm)], ['122', '123'])).
% 22.50/22.79  thf('193', plain,
% 22.50/22.79      (((sk_C) = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ sk_C))),
% 22.50/22.79      inference('demod', [status(thm)], ['189', '190', '191', '192'])).
% 22.50/22.79  thf('194', plain,
% 22.50/22.79      (![X9 : $i, X10 : $i, X11 : $i]:
% 22.50/22.79         (~ (v1_relat_1 @ X9)
% 22.50/22.79          | ((k5_relat_1 @ (k5_relat_1 @ X10 @ X9) @ X11)
% 22.50/22.79              = (k5_relat_1 @ X10 @ (k5_relat_1 @ X9 @ X11)))
% 22.50/22.79          | ~ (v1_relat_1 @ X11)
% 22.50/22.79          | ~ (v1_relat_1 @ X10))),
% 22.50/22.79      inference('cnf', [status(esa)], [t55_relat_1])).
% 22.50/22.79  thf('195', plain,
% 22.50/22.79      (![X0 : $i]:
% 22.50/22.79         (((k5_relat_1 @ sk_C @ X0)
% 22.50/22.79            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ 
% 22.50/22.79               (k5_relat_1 @ sk_C @ X0)))
% 22.50/22.79          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 22.50/22.79          | ~ (v1_relat_1 @ X0)
% 22.50/22.79          | ~ (v1_relat_1 @ sk_C))),
% 22.50/22.79      inference('sup+', [status(thm)], ['193', '194'])).
% 22.50/22.79  thf('196', plain, (![X17 : $i]: (v1_relat_1 @ (k6_partfun1 @ X17))),
% 22.50/22.79      inference('demod', [status(thm)], ['122', '123'])).
% 22.50/22.79  thf('197', plain, ((v1_relat_1 @ sk_C)),
% 22.50/22.79      inference('demod', [status(thm)], ['114', '115'])).
% 22.50/22.79  thf('198', plain,
% 22.50/22.79      (![X0 : $i]:
% 22.50/22.79         (((k5_relat_1 @ sk_C @ X0)
% 22.50/22.79            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ 
% 22.50/22.79               (k5_relat_1 @ sk_C @ X0)))
% 22.50/22.79          | ~ (v1_relat_1 @ X0))),
% 22.50/22.79      inference('demod', [status(thm)], ['195', '196', '197'])).
% 22.50/22.79  thf('199', plain,
% 22.50/22.79      ((((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 22.50/22.79          = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ 
% 22.50/22.79             (k6_partfun1 @ (k1_relat_1 @ sk_C))))
% 22.50/22.79        | ~ (v1_relat_1 @ sk_C)
% 22.50/22.79        | ~ (v1_funct_1 @ sk_C)
% 22.50/22.79        | ~ (v2_funct_1 @ sk_C)
% 22.50/22.79        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 22.50/22.79      inference('sup+', [status(thm)], ['177', '198'])).
% 22.50/22.79  thf('200', plain,
% 22.50/22.79      (![X0 : $i]:
% 22.50/22.79         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 22.50/22.79           = (k6_partfun1 @ X0))),
% 22.50/22.79      inference('demod', [status(thm)], ['136', '137'])).
% 22.50/22.79  thf('201', plain, ((v1_relat_1 @ sk_C)),
% 22.50/22.79      inference('demod', [status(thm)], ['114', '115'])).
% 22.50/22.79  thf('202', plain, ((v1_funct_1 @ sk_C)),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('203', plain, ((v2_funct_1 @ sk_C)),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('204', plain,
% 22.50/22.79      ((((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 22.50/22.79          = (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 22.50/22.79        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 22.50/22.79      inference('demod', [status(thm)], ['199', '200', '201', '202', '203'])).
% 22.50/22.79  thf('205', plain,
% 22.50/22.79      ((~ (v1_relat_1 @ sk_C)
% 22.50/22.79        | ~ (v1_funct_1 @ sk_C)
% 22.50/22.79        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 22.50/22.79            = (k6_partfun1 @ (k1_relat_1 @ sk_C))))),
% 22.50/22.79      inference('sup-', [status(thm)], ['174', '204'])).
% 22.50/22.79  thf('206', plain, ((v1_relat_1 @ sk_C)),
% 22.50/22.79      inference('demod', [status(thm)], ['114', '115'])).
% 22.50/22.79  thf('207', plain, ((v1_funct_1 @ sk_C)),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('208', plain,
% 22.50/22.79      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 22.50/22.79         = (k6_partfun1 @ (k1_relat_1 @ sk_C)))),
% 22.50/22.79      inference('demod', [status(thm)], ['205', '206', '207'])).
% 22.50/22.79  thf('209', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('210', plain, ((v1_funct_1 @ sk_C)),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('211', plain,
% 22.50/22.79      ((((sk_B) != (sk_B))
% 22.50/22.79        | ((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A_1))
% 22.50/22.79        | ((sk_B) = (k1_xboole_0)))),
% 22.50/22.79      inference('demod', [status(thm)],
% 22.50/22.79                ['171', '172', '173', '208', '209', '210'])).
% 22.50/22.79  thf('212', plain,
% 22.50/22.79      ((((sk_B) = (k1_xboole_0))
% 22.50/22.79        | ((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A_1)))),
% 22.50/22.79      inference('simplify', [status(thm)], ['211'])).
% 22.50/22.79  thf('213', plain, (((sk_B) != (k1_xboole_0))),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('214', plain,
% 22.50/22.79      (((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A_1))),
% 22.50/22.79      inference('simplify_reflect-', [status(thm)], ['212', '213'])).
% 22.50/22.79  thf('215', plain,
% 22.50/22.79      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A_1))
% 22.50/22.79         = (k2_funct_1 @ sk_C))),
% 22.50/22.79      inference('demod', [status(thm)], ['168', '214'])).
% 22.50/22.79  thf('216', plain, ((v1_relat_1 @ sk_D)),
% 22.50/22.79      inference('demod', [status(thm)], ['84', '85'])).
% 22.50/22.79  thf('217', plain,
% 22.50/22.79      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (k2_funct_1 @ sk_C))),
% 22.50/22.79      inference('demod', [status(thm)], ['152', '215', '216'])).
% 22.50/22.79  thf('218', plain, ((v1_relat_1 @ sk_D)),
% 22.50/22.79      inference('demod', [status(thm)], ['84', '85'])).
% 22.50/22.79  thf('219', plain, (((k2_funct_1 @ sk_C) = (sk_D))),
% 22.50/22.79      inference('demod', [status(thm)], ['93', '217', '218'])).
% 22.50/22.79  thf('220', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 22.50/22.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.50/22.79  thf('221', plain, ($false),
% 22.50/22.79      inference('simplify_reflect-', [status(thm)], ['219', '220'])).
% 22.50/22.79  
% 22.50/22.79  % SZS output end Refutation
% 22.50/22.79  
% 22.62/22.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

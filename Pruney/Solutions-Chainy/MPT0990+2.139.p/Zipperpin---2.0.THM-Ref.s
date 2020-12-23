%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Dhg8pPvjjC

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:18 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :  270 (1091 expanded)
%              Number of leaves         :   49 ( 341 expanded)
%              Depth                    :   26
%              Number of atoms          : 2765 (27057 expanded)
%              Number of equality atoms :  172 (1858 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( X57 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X58 )
      | ~ ( v1_funct_2 @ X58 @ X59 @ X57 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X57 ) ) )
      | ( ( k5_relat_1 @ X58 @ ( k2_funct_1 @ X58 ) )
        = ( k6_partfun1 @ X59 ) )
      | ~ ( v2_funct_1 @ X58 )
      | ( ( k2_relset_1 @ X59 @ X57 @ X58 )
       != X57 ) ) ),
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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('4',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('5',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','5','6','7'])).

thf('9',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( ( k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40 )
        = ( k5_relat_1 @ X37 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
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

thf('21',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( r2_relset_1 @ X45 @ X45 @ ( k1_partfun1 @ X45 @ X46 @ X46 @ X45 @ X44 @ X47 ) @ ( k6_partfun1 @ X45 ) )
      | ( ( k2_relset_1 @ X46 @ X45 @ X47 )
        = X45 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) )
      | ~ ( v1_funct_2 @ X47 @ X46 @ X45 )
      | ~ ( v1_funct_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('29',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['26','29','30','31','32','33'])).

thf('35',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','34'])).

thf('36',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('38',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('39',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
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

thf('41',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X32 @ X33 @ X35 @ X36 @ X31 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('48',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('49',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( X26 = X29 )
      | ~ ( r2_relset_1 @ X27 @ X28 @ X26 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','50'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('52',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('53',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('54',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['37','55'])).

thf('57',plain,(
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

thf('58',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_funct_2 @ X52 @ X53 @ X54 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X54 ) ) )
      | ( zip_tseitin_0 @ X52 @ X55 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X56 @ X53 @ X53 @ X54 @ X55 @ X52 ) )
      | ( zip_tseitin_1 @ X54 @ X53 )
      | ( ( k2_relset_1 @ X56 @ X53 @ X55 )
       != X53 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X53 ) ) )
      | ~ ( v1_funct_2 @ X55 @ X56 @ X53 )
      | ~ ( v1_funct_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('59',plain,(
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
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('64',plain,(
    ! [X15: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('65',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('66',plain,(
    ! [X15: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X15 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['63','66','67','68','69','70'])).

thf('72',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X50: $i,X51: $i] :
      ( ( X50 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('74',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X48: $i,X49: $i] :
      ( ( v2_funct_1 @ X49 )
      | ~ ( zip_tseitin_0 @ X49 @ X48 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('78',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['36','78'])).

thf(t58_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('80',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X18 @ ( k2_funct_1 @ X18 ) ) )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('81',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ sk_B ) )
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('82',plain,(
    ! [X8: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('83',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('84',plain,(
    ! [X8: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X8 ) )
      = X8 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('86',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('87',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('88',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('89',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['76','77'])).

thf('92',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['81','84','89','90','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( X57 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X58 )
      | ~ ( v1_funct_2 @ X58 @ X59 @ X57 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X57 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X58 ) @ X58 )
        = ( k6_partfun1 @ X57 ) )
      | ~ ( v2_funct_1 @ X58 )
      | ( ( k2_relset_1 @ X59 @ X57 @ X58 )
       != X57 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('95',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['95','96','97','98','99'])).

thf('101',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['101','102'])).

thf(t82_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ! [D: $i] :
              ( ( v1_relat_1 @ D )
             => ( ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
                  & ( ( k5_relat_1 @ B @ C )
                    = ( k6_relat_1 @ ( k1_relat_1 @ D ) ) )
                  & ( ( k5_relat_1 @ C @ D )
                    = ( k6_relat_1 @ A ) ) )
               => ( D = B ) ) ) ) ) )).

thf('104',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X10 ) @ X11 )
      | ( ( k5_relat_1 @ X10 @ X9 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X12 ) ) )
      | ( ( k5_relat_1 @ X9 @ X12 )
       != ( k6_relat_1 @ X11 ) )
      | ( X12 = X10 )
      | ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t82_relat_1])).

thf('105',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('106',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('107',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X10 ) @ X11 )
      | ( ( k5_relat_1 @ X10 @ X9 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X12 ) ) )
      | ( ( k5_relat_1 @ X9 @ X12 )
       != ( k6_partfun1 @ X11 ) )
      | ( X12 = X10 )
      | ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_partfun1 @ sk_B )
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k2_funct_1 @ sk_C ) )
      | ( ( k5_relat_1 @ sk_C @ X0 )
       != ( k6_partfun1 @ X1 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X1 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['103','107'])).

thf('109',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('111',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('113',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_partfun1 @ sk_B )
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k2_funct_1 @ sk_C ) )
      | ( ( k5_relat_1 @ sk_C @ X0 )
       != ( k6_partfun1 @ X1 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['108','113'])).

thf('115',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('117',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['117','118'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('120',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('121',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
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

thf('122',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k2_relat_1 @ X17 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('123',plain,(
    ! [X60: $i] :
      ( ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X60 ) @ ( k2_relat_1 @ X60 ) ) ) )
      | ~ ( v1_funct_1 @ X60 )
      | ~ ( v1_relat_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['121','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['120','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['119','128'])).

thf('130',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['111','112'])).

thf('131',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['129','130','131','132'])).

thf('134',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('135',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('137',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('139',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('140',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k1_relat_1 @ X17 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('141',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['129','130','131','132'])).

thf('142',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('143',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( X57 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X58 )
      | ~ ( v1_funct_2 @ X58 @ X59 @ X57 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X57 ) ) )
      | ( ( k5_relat_1 @ X58 @ ( k2_funct_1 @ X58 ) )
        = ( k6_partfun1 @ X59 ) )
      | ~ ( v2_funct_1 @ X58 )
      | ( ( k2_relset_1 @ X59 @ X57 @ X58 )
       != X57 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('145',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['145','146','147','148','149'])).

thf('151',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X18 @ ( k2_funct_1 @ X18 ) ) )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('155',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ sk_A ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X8: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X8 ) )
      = X8 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('157',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['111','112'])).

thf('158',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['155','156','157','158','159'])).

thf('161',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['111','112'])).

thf('162',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['142','160','161','162','163'])).

thf('165',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('166',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['151','152'])).

thf('168',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['139','168'])).

thf('170',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['111','112'])).

thf('171',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['169','170','171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('174',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C ) )
      = sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('176',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( r2_relset_1 @ X27 @ X28 @ X26 @ X29 )
      | ( X26 != X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('177',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( r2_relset_1 @ X27 @ X28 @ X29 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['175','177'])).

thf('179',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['142','160','161','162','163'])).

thf('180',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('181',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['142','160','161','162','163'])).

thf('183',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['117','118'])).

thf('184',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k2_relat_1 @ X17 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('185',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('186',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('187',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k1_relat_1 @ X17 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('188',plain,(
    ! [X60: $i] :
      ( ( v1_funct_2 @ X60 @ ( k1_relat_1 @ X60 ) @ ( k2_relat_1 @ X60 ) )
      | ~ ( v1_funct_1 @ X60 )
      | ~ ( v1_relat_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['187','188'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['186','189'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['185','191'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['192'])).

thf('194',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['184','193'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['194'])).

thf('196',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['183','195'])).

thf('197',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['111','112'])).

thf('198',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['196','197','198','199'])).

thf('201',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['155','156','157','158','159'])).

thf('202',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['200','201'])).

thf('203',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['174','178','181','182','202'])).

thf('204',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['138','203'])).

thf('205',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['111','112'])).

thf('206',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['204','205','206'])).

thf('208',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_partfun1 @ sk_B )
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k2_funct_1 @ sk_C ) )
      | ( ( k5_relat_1 @ sk_C @ X0 )
       != ( k6_partfun1 @ X1 ) )
      | ~ ( r1_tarski @ sk_A @ X1 ) ) ),
    inference(demod,[status(thm)],['114','137','207'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ sk_B )
       != ( k6_partfun1 @ sk_B ) )
      | ~ ( r1_tarski @ sk_A @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
       != ( k6_partfun1 @ X0 ) )
      | ( sk_D
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['92','208'])).

thf('210',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('211',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['87','88'])).

thf('212',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ sk_B )
       != ( k6_partfun1 @ sk_B ) )
      | ~ ( r1_tarski @ sk_A @ X0 )
      | ( ( k6_partfun1 @ sk_A )
       != ( k6_partfun1 @ X0 ) )
      | ( sk_D
        = ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['209','210','211'])).

thf('213',plain,(
    ! [X0: $i] :
      ( ( sk_D
        = ( k2_funct_1 @ sk_C ) )
      | ( ( k6_partfun1 @ sk_A )
       != ( k6_partfun1 @ X0 ) )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['212'])).

thf('214',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ sk_A )
       != ( k6_partfun1 @ X0 ) )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['213','214'])).

thf('216',plain,(
    ~ ( r1_tarski @ sk_A @ sk_A ) ),
    inference(eq_res,[status(thm)],['215'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('217',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('218',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['217'])).

thf('219',plain,(
    $false ),
    inference(demod,[status(thm)],['216','218'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Dhg8pPvjjC
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:44:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.34/1.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.34/1.54  % Solved by: fo/fo7.sh
% 1.34/1.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.34/1.54  % done 1475 iterations in 1.080s
% 1.34/1.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.34/1.54  % SZS output start Refutation
% 1.34/1.54  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.34/1.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.34/1.54  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.34/1.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.34/1.54  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.34/1.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.34/1.54  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.34/1.54  thf(sk_D_type, type, sk_D: $i).
% 1.34/1.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.34/1.54  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 1.34/1.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.34/1.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.34/1.54  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.34/1.54  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.34/1.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.34/1.54  thf(sk_B_type, type, sk_B: $i).
% 1.34/1.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.34/1.54  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.34/1.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.34/1.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.34/1.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.34/1.54  thf(sk_C_type, type, sk_C: $i).
% 1.34/1.54  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.34/1.54  thf(sk_A_type, type, sk_A: $i).
% 1.34/1.54  thf(t36_funct_2, conjecture,
% 1.34/1.54    (![A:$i,B:$i,C:$i]:
% 1.34/1.54     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.34/1.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.34/1.54       ( ![D:$i]:
% 1.34/1.54         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.34/1.54             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.34/1.54           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.34/1.54               ( r2_relset_1 @
% 1.34/1.54                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.34/1.54                 ( k6_partfun1 @ A ) ) & 
% 1.34/1.54               ( v2_funct_1 @ C ) ) =>
% 1.34/1.54             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.34/1.54               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.34/1.54  thf(zf_stmt_0, negated_conjecture,
% 1.34/1.54    (~( ![A:$i,B:$i,C:$i]:
% 1.34/1.54        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.34/1.54            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.34/1.54          ( ![D:$i]:
% 1.34/1.54            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.34/1.54                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.34/1.54              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.34/1.54                  ( r2_relset_1 @
% 1.34/1.54                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.34/1.54                    ( k6_partfun1 @ A ) ) & 
% 1.34/1.54                  ( v2_funct_1 @ C ) ) =>
% 1.34/1.54                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.34/1.54                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.34/1.54    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.34/1.54  thf('0', plain,
% 1.34/1.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.34/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.54  thf(t35_funct_2, axiom,
% 1.34/1.54    (![A:$i,B:$i,C:$i]:
% 1.34/1.54     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.34/1.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.34/1.54       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.34/1.54         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.34/1.54           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 1.34/1.54             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 1.34/1.54  thf('1', plain,
% 1.34/1.54      (![X57 : $i, X58 : $i, X59 : $i]:
% 1.34/1.54         (((X57) = (k1_xboole_0))
% 1.34/1.54          | ~ (v1_funct_1 @ X58)
% 1.34/1.54          | ~ (v1_funct_2 @ X58 @ X59 @ X57)
% 1.34/1.54          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X57)))
% 1.34/1.54          | ((k5_relat_1 @ X58 @ (k2_funct_1 @ X58)) = (k6_partfun1 @ X59))
% 1.34/1.54          | ~ (v2_funct_1 @ X58)
% 1.34/1.54          | ((k2_relset_1 @ X59 @ X57 @ X58) != (X57)))),
% 1.34/1.54      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.34/1.54  thf('2', plain,
% 1.34/1.54      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 1.34/1.54        | ~ (v2_funct_1 @ sk_D)
% 1.34/1.54        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.34/1.54        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.34/1.54        | ~ (v1_funct_1 @ sk_D)
% 1.34/1.54        | ((sk_A) = (k1_xboole_0)))),
% 1.34/1.54      inference('sup-', [status(thm)], ['0', '1'])).
% 1.34/1.54  thf('3', plain,
% 1.34/1.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.34/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.54  thf(redefinition_k2_relset_1, axiom,
% 1.34/1.54    (![A:$i,B:$i,C:$i]:
% 1.34/1.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.34/1.54       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.34/1.54  thf('4', plain,
% 1.34/1.54      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.34/1.54         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 1.34/1.54          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.34/1.54      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.34/1.54  thf('5', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.34/1.54      inference('sup-', [status(thm)], ['3', '4'])).
% 1.34/1.54  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.34/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.54  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 1.34/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.54  thf('8', plain,
% 1.34/1.54      ((((k2_relat_1 @ sk_D) != (sk_A))
% 1.34/1.54        | ~ (v2_funct_1 @ sk_D)
% 1.34/1.54        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.34/1.54        | ((sk_A) = (k1_xboole_0)))),
% 1.34/1.54      inference('demod', [status(thm)], ['2', '5', '6', '7'])).
% 1.34/1.54  thf('9', plain, (((sk_A) != (k1_xboole_0))),
% 1.34/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.54  thf('10', plain,
% 1.34/1.54      ((((k2_relat_1 @ sk_D) != (sk_A))
% 1.34/1.54        | ~ (v2_funct_1 @ sk_D)
% 1.34/1.54        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 1.34/1.54      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 1.34/1.54  thf('11', plain,
% 1.34/1.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.34/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.54  thf('12', plain,
% 1.34/1.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.34/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.54  thf(redefinition_k1_partfun1, axiom,
% 1.34/1.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.34/1.54     ( ( ( v1_funct_1 @ E ) & 
% 1.34/1.54         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.34/1.54         ( v1_funct_1 @ F ) & 
% 1.34/1.54         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.34/1.54       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.34/1.54  thf('13', plain,
% 1.34/1.54      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 1.34/1.54         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 1.34/1.54          | ~ (v1_funct_1 @ X37)
% 1.34/1.54          | ~ (v1_funct_1 @ X40)
% 1.34/1.54          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 1.34/1.54          | ((k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40)
% 1.34/1.54              = (k5_relat_1 @ X37 @ X40)))),
% 1.34/1.54      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.34/1.54  thf('14', plain,
% 1.34/1.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.34/1.54         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.34/1.54            = (k5_relat_1 @ sk_C @ X0))
% 1.34/1.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.34/1.54          | ~ (v1_funct_1 @ X0)
% 1.34/1.54          | ~ (v1_funct_1 @ sk_C))),
% 1.34/1.54      inference('sup-', [status(thm)], ['12', '13'])).
% 1.34/1.54  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 1.34/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.54  thf('16', plain,
% 1.34/1.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.34/1.54         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.34/1.54            = (k5_relat_1 @ sk_C @ X0))
% 1.34/1.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.34/1.54          | ~ (v1_funct_1 @ X0))),
% 1.34/1.54      inference('demod', [status(thm)], ['14', '15'])).
% 1.34/1.54  thf('17', plain,
% 1.34/1.54      ((~ (v1_funct_1 @ sk_D)
% 1.34/1.54        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.34/1.54            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.34/1.54      inference('sup-', [status(thm)], ['11', '16'])).
% 1.34/1.54  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 1.34/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.54  thf('19', plain,
% 1.34/1.54      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.34/1.54         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.34/1.54      inference('demod', [status(thm)], ['17', '18'])).
% 1.34/1.54  thf('20', plain,
% 1.34/1.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.34/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.54  thf(t24_funct_2, axiom,
% 1.34/1.54    (![A:$i,B:$i,C:$i]:
% 1.34/1.54     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.34/1.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.34/1.54       ( ![D:$i]:
% 1.34/1.54         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.34/1.54             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.34/1.54           ( ( r2_relset_1 @
% 1.34/1.54               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 1.34/1.54               ( k6_partfun1 @ B ) ) =>
% 1.34/1.54             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 1.34/1.54  thf('21', plain,
% 1.34/1.54      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 1.34/1.54         (~ (v1_funct_1 @ X44)
% 1.34/1.54          | ~ (v1_funct_2 @ X44 @ X45 @ X46)
% 1.34/1.54          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 1.34/1.54          | ~ (r2_relset_1 @ X45 @ X45 @ 
% 1.34/1.54               (k1_partfun1 @ X45 @ X46 @ X46 @ X45 @ X44 @ X47) @ 
% 1.34/1.54               (k6_partfun1 @ X45))
% 1.34/1.54          | ((k2_relset_1 @ X46 @ X45 @ X47) = (X45))
% 1.34/1.54          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45)))
% 1.34/1.54          | ~ (v1_funct_2 @ X47 @ X46 @ X45)
% 1.34/1.54          | ~ (v1_funct_1 @ X47))),
% 1.34/1.54      inference('cnf', [status(esa)], [t24_funct_2])).
% 1.34/1.54  thf('22', plain,
% 1.34/1.54      (![X0 : $i]:
% 1.34/1.54         (~ (v1_funct_1 @ X0)
% 1.34/1.54          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.34/1.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.34/1.54          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.34/1.54          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.34/1.54               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.34/1.54               (k6_partfun1 @ sk_A))
% 1.34/1.54          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.34/1.54          | ~ (v1_funct_1 @ sk_C))),
% 1.34/1.54      inference('sup-', [status(thm)], ['20', '21'])).
% 1.34/1.54  thf('23', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.34/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.54  thf('24', plain, ((v1_funct_1 @ sk_C)),
% 1.34/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.54  thf('25', plain,
% 1.34/1.54      (![X0 : $i]:
% 1.34/1.54         (~ (v1_funct_1 @ X0)
% 1.34/1.54          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.34/1.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.34/1.54          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.34/1.54          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.34/1.54               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.34/1.54               (k6_partfun1 @ sk_A)))),
% 1.34/1.54      inference('demod', [status(thm)], ['22', '23', '24'])).
% 1.34/1.54  thf('26', plain,
% 1.34/1.54      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.34/1.54           (k6_partfun1 @ sk_A))
% 1.34/1.54        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 1.34/1.54        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.34/1.54        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.34/1.54        | ~ (v1_funct_1 @ sk_D))),
% 1.34/1.54      inference('sup-', [status(thm)], ['19', '25'])).
% 1.34/1.54  thf('27', plain,
% 1.34/1.54      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.34/1.54        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.34/1.54        (k6_partfun1 @ sk_A))),
% 1.34/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.54  thf('28', plain,
% 1.34/1.54      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.34/1.54         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.34/1.54      inference('demod', [status(thm)], ['17', '18'])).
% 1.34/1.54  thf('29', plain,
% 1.34/1.54      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.34/1.54        (k6_partfun1 @ sk_A))),
% 1.34/1.54      inference('demod', [status(thm)], ['27', '28'])).
% 1.34/1.54  thf('30', plain,
% 1.34/1.54      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.34/1.54      inference('sup-', [status(thm)], ['3', '4'])).
% 1.34/1.54  thf('31', plain,
% 1.34/1.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.34/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.54  thf('32', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.34/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.54  thf('33', plain, ((v1_funct_1 @ sk_D)),
% 1.34/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.54  thf('34', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.34/1.54      inference('demod', [status(thm)], ['26', '29', '30', '31', '32', '33'])).
% 1.34/1.54  thf('35', plain,
% 1.34/1.54      ((((sk_A) != (sk_A))
% 1.34/1.54        | ~ (v2_funct_1 @ sk_D)
% 1.34/1.54        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 1.34/1.54      inference('demod', [status(thm)], ['10', '34'])).
% 1.34/1.54  thf('36', plain,
% 1.34/1.54      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.34/1.54        | ~ (v2_funct_1 @ sk_D))),
% 1.34/1.54      inference('simplify', [status(thm)], ['35'])).
% 1.34/1.54  thf('37', plain,
% 1.34/1.54      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.34/1.54         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.34/1.54      inference('demod', [status(thm)], ['17', '18'])).
% 1.34/1.54  thf('38', plain,
% 1.34/1.54      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.34/1.54        (k6_partfun1 @ sk_A))),
% 1.34/1.54      inference('demod', [status(thm)], ['27', '28'])).
% 1.34/1.54  thf('39', plain,
% 1.34/1.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.34/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.54  thf('40', plain,
% 1.34/1.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.34/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.54  thf(dt_k1_partfun1, axiom,
% 1.34/1.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.34/1.54     ( ( ( v1_funct_1 @ E ) & 
% 1.34/1.54         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.34/1.55         ( v1_funct_1 @ F ) & 
% 1.34/1.55         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.34/1.55       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.34/1.55         ( m1_subset_1 @
% 1.34/1.55           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.34/1.55           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.34/1.55  thf('41', plain,
% 1.34/1.55      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 1.34/1.55         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.34/1.55          | ~ (v1_funct_1 @ X31)
% 1.34/1.55          | ~ (v1_funct_1 @ X34)
% 1.34/1.55          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 1.34/1.55          | (m1_subset_1 @ (k1_partfun1 @ X32 @ X33 @ X35 @ X36 @ X31 @ X34) @ 
% 1.34/1.55             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X36))))),
% 1.34/1.55      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.34/1.55  thf('42', plain,
% 1.34/1.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.34/1.55         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.34/1.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.34/1.55          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.34/1.55          | ~ (v1_funct_1 @ X1)
% 1.34/1.55          | ~ (v1_funct_1 @ sk_C))),
% 1.34/1.55      inference('sup-', [status(thm)], ['40', '41'])).
% 1.34/1.55  thf('43', plain, ((v1_funct_1 @ sk_C)),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.55  thf('44', plain,
% 1.34/1.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.34/1.55         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.34/1.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.34/1.55          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.34/1.55          | ~ (v1_funct_1 @ X1))),
% 1.34/1.55      inference('demod', [status(thm)], ['42', '43'])).
% 1.34/1.55  thf('45', plain,
% 1.34/1.55      ((~ (v1_funct_1 @ sk_D)
% 1.34/1.55        | (m1_subset_1 @ 
% 1.34/1.55           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.34/1.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.34/1.55      inference('sup-', [status(thm)], ['39', '44'])).
% 1.34/1.55  thf('46', plain, ((v1_funct_1 @ sk_D)),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.55  thf('47', plain,
% 1.34/1.55      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.34/1.55         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.34/1.55      inference('demod', [status(thm)], ['17', '18'])).
% 1.34/1.55  thf('48', plain,
% 1.34/1.55      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.34/1.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.34/1.55      inference('demod', [status(thm)], ['45', '46', '47'])).
% 1.34/1.55  thf(redefinition_r2_relset_1, axiom,
% 1.34/1.55    (![A:$i,B:$i,C:$i,D:$i]:
% 1.34/1.55     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.34/1.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.34/1.55       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.34/1.55  thf('49', plain,
% 1.34/1.55      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.34/1.55         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 1.34/1.55          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 1.34/1.55          | ((X26) = (X29))
% 1.34/1.55          | ~ (r2_relset_1 @ X27 @ X28 @ X26 @ X29))),
% 1.34/1.55      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.34/1.55  thf('50', plain,
% 1.34/1.55      (![X0 : $i]:
% 1.34/1.55         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 1.34/1.55          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 1.34/1.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.34/1.55      inference('sup-', [status(thm)], ['48', '49'])).
% 1.34/1.55  thf('51', plain,
% 1.34/1.55      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.34/1.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.34/1.55        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 1.34/1.55      inference('sup-', [status(thm)], ['38', '50'])).
% 1.34/1.55  thf(t29_relset_1, axiom,
% 1.34/1.55    (![A:$i]:
% 1.34/1.55     ( m1_subset_1 @
% 1.34/1.55       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.34/1.55  thf('52', plain,
% 1.34/1.55      (![X30 : $i]:
% 1.34/1.55         (m1_subset_1 @ (k6_relat_1 @ X30) @ 
% 1.34/1.55          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 1.34/1.55      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.34/1.55  thf(redefinition_k6_partfun1, axiom,
% 1.34/1.55    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.34/1.55  thf('53', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 1.34/1.55      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.34/1.55  thf('54', plain,
% 1.34/1.55      (![X30 : $i]:
% 1.34/1.55         (m1_subset_1 @ (k6_partfun1 @ X30) @ 
% 1.34/1.55          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 1.34/1.55      inference('demod', [status(thm)], ['52', '53'])).
% 1.34/1.55  thf('55', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.34/1.55      inference('demod', [status(thm)], ['51', '54'])).
% 1.34/1.55  thf('56', plain,
% 1.34/1.55      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.34/1.55         = (k6_partfun1 @ sk_A))),
% 1.34/1.55      inference('demod', [status(thm)], ['37', '55'])).
% 1.34/1.55  thf('57', plain,
% 1.34/1.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.55  thf(t30_funct_2, axiom,
% 1.34/1.55    (![A:$i,B:$i,C:$i,D:$i]:
% 1.34/1.55     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.34/1.55         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 1.34/1.55       ( ![E:$i]:
% 1.34/1.55         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 1.34/1.55             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 1.34/1.55           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 1.34/1.55               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 1.34/1.55             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 1.34/1.55               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 1.34/1.55  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 1.34/1.55  thf(zf_stmt_2, axiom,
% 1.34/1.55    (![C:$i,B:$i]:
% 1.34/1.55     ( ( zip_tseitin_1 @ C @ B ) =>
% 1.34/1.55       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 1.34/1.55  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.34/1.55  thf(zf_stmt_4, axiom,
% 1.34/1.55    (![E:$i,D:$i]:
% 1.34/1.55     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 1.34/1.55  thf(zf_stmt_5, axiom,
% 1.34/1.55    (![A:$i,B:$i,C:$i,D:$i]:
% 1.34/1.55     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.34/1.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.34/1.55       ( ![E:$i]:
% 1.34/1.55         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.34/1.55             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.34/1.55           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 1.34/1.55               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 1.34/1.55             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 1.34/1.55  thf('58', plain,
% 1.34/1.55      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 1.34/1.55         (~ (v1_funct_1 @ X52)
% 1.34/1.55          | ~ (v1_funct_2 @ X52 @ X53 @ X54)
% 1.34/1.55          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X54)))
% 1.34/1.55          | (zip_tseitin_0 @ X52 @ X55)
% 1.34/1.55          | ~ (v2_funct_1 @ (k1_partfun1 @ X56 @ X53 @ X53 @ X54 @ X55 @ X52))
% 1.34/1.55          | (zip_tseitin_1 @ X54 @ X53)
% 1.34/1.55          | ((k2_relset_1 @ X56 @ X53 @ X55) != (X53))
% 1.34/1.55          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X53)))
% 1.34/1.55          | ~ (v1_funct_2 @ X55 @ X56 @ X53)
% 1.34/1.55          | ~ (v1_funct_1 @ X55))),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.34/1.55  thf('59', plain,
% 1.34/1.55      (![X0 : $i, X1 : $i]:
% 1.34/1.55         (~ (v1_funct_1 @ X0)
% 1.34/1.55          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.34/1.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.34/1.55          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.34/1.55          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.34/1.55          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.34/1.55          | (zip_tseitin_0 @ sk_D @ X0)
% 1.34/1.55          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.34/1.55          | ~ (v1_funct_1 @ sk_D))),
% 1.34/1.55      inference('sup-', [status(thm)], ['57', '58'])).
% 1.34/1.55  thf('60', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.55  thf('61', plain, ((v1_funct_1 @ sk_D)),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.55  thf('62', plain,
% 1.34/1.55      (![X0 : $i, X1 : $i]:
% 1.34/1.55         (~ (v1_funct_1 @ X0)
% 1.34/1.55          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.34/1.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.34/1.55          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.34/1.55          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.34/1.55          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.34/1.55          | (zip_tseitin_0 @ sk_D @ X0))),
% 1.34/1.55      inference('demod', [status(thm)], ['59', '60', '61'])).
% 1.34/1.55  thf('63', plain,
% 1.34/1.55      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 1.34/1.55        | (zip_tseitin_0 @ sk_D @ sk_C)
% 1.34/1.55        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.34/1.55        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.34/1.55        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.34/1.55        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.34/1.55        | ~ (v1_funct_1 @ sk_C))),
% 1.34/1.55      inference('sup-', [status(thm)], ['56', '62'])).
% 1.34/1.55  thf(fc4_funct_1, axiom,
% 1.34/1.55    (![A:$i]:
% 1.34/1.55     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.34/1.55       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.34/1.55  thf('64', plain, (![X15 : $i]: (v2_funct_1 @ (k6_relat_1 @ X15))),
% 1.34/1.55      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.34/1.55  thf('65', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 1.34/1.55      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.34/1.55  thf('66', plain, (![X15 : $i]: (v2_funct_1 @ (k6_partfun1 @ X15))),
% 1.34/1.55      inference('demod', [status(thm)], ['64', '65'])).
% 1.34/1.55  thf('67', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.55  thf('68', plain,
% 1.34/1.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.55  thf('69', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.55  thf('70', plain, ((v1_funct_1 @ sk_C)),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.55  thf('71', plain,
% 1.34/1.55      (((zip_tseitin_0 @ sk_D @ sk_C)
% 1.34/1.55        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.34/1.55        | ((sk_B) != (sk_B)))),
% 1.34/1.55      inference('demod', [status(thm)], ['63', '66', '67', '68', '69', '70'])).
% 1.34/1.55  thf('72', plain,
% 1.34/1.55      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 1.34/1.55      inference('simplify', [status(thm)], ['71'])).
% 1.34/1.55  thf('73', plain,
% 1.34/1.55      (![X50 : $i, X51 : $i]:
% 1.34/1.55         (((X50) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X50 @ X51))),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.34/1.55  thf('74', plain,
% 1.34/1.55      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 1.34/1.55      inference('sup-', [status(thm)], ['72', '73'])).
% 1.34/1.55  thf('75', plain, (((sk_A) != (k1_xboole_0))),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.55  thf('76', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 1.34/1.55      inference('simplify_reflect-', [status(thm)], ['74', '75'])).
% 1.34/1.55  thf('77', plain,
% 1.34/1.55      (![X48 : $i, X49 : $i]:
% 1.34/1.55         ((v2_funct_1 @ X49) | ~ (zip_tseitin_0 @ X49 @ X48))),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.34/1.55  thf('78', plain, ((v2_funct_1 @ sk_D)),
% 1.34/1.55      inference('sup-', [status(thm)], ['76', '77'])).
% 1.34/1.55  thf('79', plain,
% 1.34/1.55      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 1.34/1.55      inference('demod', [status(thm)], ['36', '78'])).
% 1.34/1.55  thf(t58_funct_1, axiom,
% 1.34/1.55    (![A:$i]:
% 1.34/1.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.34/1.55       ( ( v2_funct_1 @ A ) =>
% 1.34/1.55         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 1.34/1.55             ( k1_relat_1 @ A ) ) & 
% 1.34/1.55           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 1.34/1.55             ( k1_relat_1 @ A ) ) ) ) ))).
% 1.34/1.55  thf('80', plain,
% 1.34/1.55      (![X18 : $i]:
% 1.34/1.55         (~ (v2_funct_1 @ X18)
% 1.34/1.55          | ((k2_relat_1 @ (k5_relat_1 @ X18 @ (k2_funct_1 @ X18)))
% 1.34/1.55              = (k1_relat_1 @ X18))
% 1.34/1.55          | ~ (v1_funct_1 @ X18)
% 1.34/1.55          | ~ (v1_relat_1 @ X18))),
% 1.34/1.55      inference('cnf', [status(esa)], [t58_funct_1])).
% 1.34/1.55  thf('81', plain,
% 1.34/1.55      ((((k2_relat_1 @ (k6_partfun1 @ sk_B)) = (k1_relat_1 @ sk_D))
% 1.34/1.55        | ~ (v1_relat_1 @ sk_D)
% 1.34/1.55        | ~ (v1_funct_1 @ sk_D)
% 1.34/1.55        | ~ (v2_funct_1 @ sk_D))),
% 1.34/1.55      inference('sup+', [status(thm)], ['79', '80'])).
% 1.34/1.55  thf(t71_relat_1, axiom,
% 1.34/1.55    (![A:$i]:
% 1.34/1.55     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.34/1.55       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.34/1.55  thf('82', plain, (![X8 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X8)) = (X8))),
% 1.34/1.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.34/1.55  thf('83', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 1.34/1.55      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.34/1.55  thf('84', plain, (![X8 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X8)) = (X8))),
% 1.34/1.55      inference('demod', [status(thm)], ['82', '83'])).
% 1.34/1.55  thf('85', plain,
% 1.34/1.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.55  thf(cc2_relat_1, axiom,
% 1.34/1.55    (![A:$i]:
% 1.34/1.55     ( ( v1_relat_1 @ A ) =>
% 1.34/1.55       ( ![B:$i]:
% 1.34/1.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.34/1.55  thf('86', plain,
% 1.34/1.55      (![X3 : $i, X4 : $i]:
% 1.34/1.55         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 1.34/1.55          | (v1_relat_1 @ X3)
% 1.34/1.55          | ~ (v1_relat_1 @ X4))),
% 1.34/1.55      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.34/1.55  thf('87', plain,
% 1.34/1.55      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 1.34/1.55      inference('sup-', [status(thm)], ['85', '86'])).
% 1.34/1.55  thf(fc6_relat_1, axiom,
% 1.34/1.55    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.34/1.55  thf('88', plain,
% 1.34/1.55      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 1.34/1.55      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.34/1.55  thf('89', plain, ((v1_relat_1 @ sk_D)),
% 1.34/1.55      inference('demod', [status(thm)], ['87', '88'])).
% 1.34/1.55  thf('90', plain, ((v1_funct_1 @ sk_D)),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.55  thf('91', plain, ((v2_funct_1 @ sk_D)),
% 1.34/1.55      inference('sup-', [status(thm)], ['76', '77'])).
% 1.34/1.55  thf('92', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.34/1.55      inference('demod', [status(thm)], ['81', '84', '89', '90', '91'])).
% 1.34/1.55  thf('93', plain,
% 1.34/1.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.55  thf('94', plain,
% 1.34/1.55      (![X57 : $i, X58 : $i, X59 : $i]:
% 1.34/1.55         (((X57) = (k1_xboole_0))
% 1.34/1.55          | ~ (v1_funct_1 @ X58)
% 1.34/1.55          | ~ (v1_funct_2 @ X58 @ X59 @ X57)
% 1.34/1.55          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X57)))
% 1.34/1.55          | ((k5_relat_1 @ (k2_funct_1 @ X58) @ X58) = (k6_partfun1 @ X57))
% 1.34/1.55          | ~ (v2_funct_1 @ X58)
% 1.34/1.55          | ((k2_relset_1 @ X59 @ X57 @ X58) != (X57)))),
% 1.34/1.55      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.34/1.55  thf('95', plain,
% 1.34/1.55      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.34/1.55        | ~ (v2_funct_1 @ sk_C)
% 1.34/1.55        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 1.34/1.55        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.34/1.55        | ~ (v1_funct_1 @ sk_C)
% 1.34/1.55        | ((sk_B) = (k1_xboole_0)))),
% 1.34/1.55      inference('sup-', [status(thm)], ['93', '94'])).
% 1.34/1.55  thf('96', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.55  thf('97', plain, ((v2_funct_1 @ sk_C)),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.55  thf('98', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.55  thf('99', plain, ((v1_funct_1 @ sk_C)),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.55  thf('100', plain,
% 1.34/1.55      ((((sk_B) != (sk_B))
% 1.34/1.55        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 1.34/1.55        | ((sk_B) = (k1_xboole_0)))),
% 1.34/1.55      inference('demod', [status(thm)], ['95', '96', '97', '98', '99'])).
% 1.34/1.55  thf('101', plain,
% 1.34/1.55      ((((sk_B) = (k1_xboole_0))
% 1.34/1.55        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 1.34/1.55      inference('simplify', [status(thm)], ['100'])).
% 1.34/1.55  thf('102', plain, (((sk_B) != (k1_xboole_0))),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.55  thf('103', plain,
% 1.34/1.55      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 1.34/1.55      inference('simplify_reflect-', [status(thm)], ['101', '102'])).
% 1.34/1.55  thf(t82_relat_1, axiom,
% 1.34/1.55    (![A:$i,B:$i]:
% 1.34/1.55     ( ( v1_relat_1 @ B ) =>
% 1.34/1.55       ( ![C:$i]:
% 1.34/1.55         ( ( v1_relat_1 @ C ) =>
% 1.34/1.55           ( ![D:$i]:
% 1.34/1.55             ( ( v1_relat_1 @ D ) =>
% 1.34/1.55               ( ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) & 
% 1.34/1.55                   ( ( k5_relat_1 @ B @ C ) =
% 1.34/1.55                     ( k6_relat_1 @ ( k1_relat_1 @ D ) ) ) & 
% 1.34/1.55                   ( ( k5_relat_1 @ C @ D ) = ( k6_relat_1 @ A ) ) ) =>
% 1.34/1.55                 ( ( D ) = ( B ) ) ) ) ) ) ) ))).
% 1.34/1.55  thf('104', plain,
% 1.34/1.55      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 1.34/1.55         (~ (v1_relat_1 @ X9)
% 1.34/1.55          | ~ (r1_tarski @ (k2_relat_1 @ X10) @ X11)
% 1.34/1.55          | ((k5_relat_1 @ X10 @ X9) != (k6_relat_1 @ (k1_relat_1 @ X12)))
% 1.34/1.55          | ((k5_relat_1 @ X9 @ X12) != (k6_relat_1 @ X11))
% 1.34/1.55          | ((X12) = (X10))
% 1.34/1.55          | ~ (v1_relat_1 @ X12)
% 1.34/1.55          | ~ (v1_relat_1 @ X10))),
% 1.34/1.55      inference('cnf', [status(esa)], [t82_relat_1])).
% 1.34/1.55  thf('105', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 1.34/1.55      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.34/1.55  thf('106', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 1.34/1.55      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.34/1.55  thf('107', plain,
% 1.34/1.55      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 1.34/1.55         (~ (v1_relat_1 @ X9)
% 1.34/1.55          | ~ (r1_tarski @ (k2_relat_1 @ X10) @ X11)
% 1.34/1.55          | ((k5_relat_1 @ X10 @ X9) != (k6_partfun1 @ (k1_relat_1 @ X12)))
% 1.34/1.55          | ((k5_relat_1 @ X9 @ X12) != (k6_partfun1 @ X11))
% 1.34/1.55          | ((X12) = (X10))
% 1.34/1.55          | ~ (v1_relat_1 @ X12)
% 1.34/1.55          | ~ (v1_relat_1 @ X10))),
% 1.34/1.55      inference('demod', [status(thm)], ['104', '105', '106'])).
% 1.34/1.55  thf('108', plain,
% 1.34/1.55      (![X0 : $i, X1 : $i]:
% 1.34/1.55         (((k6_partfun1 @ sk_B) != (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.34/1.55          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.34/1.55          | ~ (v1_relat_1 @ X0)
% 1.34/1.55          | ((X0) = (k2_funct_1 @ sk_C))
% 1.34/1.55          | ((k5_relat_1 @ sk_C @ X0) != (k6_partfun1 @ X1))
% 1.34/1.55          | ~ (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ X1)
% 1.34/1.55          | ~ (v1_relat_1 @ sk_C))),
% 1.34/1.55      inference('sup-', [status(thm)], ['103', '107'])).
% 1.34/1.55  thf('109', plain,
% 1.34/1.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.55  thf('110', plain,
% 1.34/1.55      (![X3 : $i, X4 : $i]:
% 1.34/1.55         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 1.34/1.55          | (v1_relat_1 @ X3)
% 1.34/1.55          | ~ (v1_relat_1 @ X4))),
% 1.34/1.55      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.34/1.55  thf('111', plain,
% 1.34/1.55      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 1.34/1.55      inference('sup-', [status(thm)], ['109', '110'])).
% 1.34/1.55  thf('112', plain,
% 1.34/1.55      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 1.34/1.55      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.34/1.55  thf('113', plain, ((v1_relat_1 @ sk_C)),
% 1.34/1.55      inference('demod', [status(thm)], ['111', '112'])).
% 1.34/1.55  thf('114', plain,
% 1.34/1.55      (![X0 : $i, X1 : $i]:
% 1.34/1.55         (((k6_partfun1 @ sk_B) != (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.34/1.55          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.34/1.55          | ~ (v1_relat_1 @ X0)
% 1.34/1.55          | ((X0) = (k2_funct_1 @ sk_C))
% 1.34/1.55          | ((k5_relat_1 @ sk_C @ X0) != (k6_partfun1 @ X1))
% 1.34/1.55          | ~ (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ X1))),
% 1.34/1.55      inference('demod', [status(thm)], ['108', '113'])).
% 1.34/1.55  thf('115', plain,
% 1.34/1.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.55  thf('116', plain,
% 1.34/1.55      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.34/1.55         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 1.34/1.55          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.34/1.55      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.34/1.55  thf('117', plain,
% 1.34/1.55      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.34/1.55      inference('sup-', [status(thm)], ['115', '116'])).
% 1.34/1.55  thf('118', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.55  thf('119', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.34/1.55      inference('sup+', [status(thm)], ['117', '118'])).
% 1.34/1.55  thf(dt_k2_funct_1, axiom,
% 1.34/1.55    (![A:$i]:
% 1.34/1.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.34/1.55       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.34/1.55         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.34/1.55  thf('120', plain,
% 1.34/1.55      (![X13 : $i]:
% 1.34/1.55         ((v1_funct_1 @ (k2_funct_1 @ X13))
% 1.34/1.55          | ~ (v1_funct_1 @ X13)
% 1.34/1.55          | ~ (v1_relat_1 @ X13))),
% 1.34/1.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.34/1.55  thf('121', plain,
% 1.34/1.55      (![X13 : $i]:
% 1.34/1.55         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 1.34/1.55          | ~ (v1_funct_1 @ X13)
% 1.34/1.55          | ~ (v1_relat_1 @ X13))),
% 1.34/1.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.34/1.55  thf(t55_funct_1, axiom,
% 1.34/1.55    (![A:$i]:
% 1.34/1.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.34/1.55       ( ( v2_funct_1 @ A ) =>
% 1.34/1.55         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.34/1.55           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.34/1.55  thf('122', plain,
% 1.34/1.55      (![X17 : $i]:
% 1.34/1.55         (~ (v2_funct_1 @ X17)
% 1.34/1.55          | ((k2_relat_1 @ X17) = (k1_relat_1 @ (k2_funct_1 @ X17)))
% 1.34/1.55          | ~ (v1_funct_1 @ X17)
% 1.34/1.55          | ~ (v1_relat_1 @ X17))),
% 1.34/1.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.34/1.55  thf(t3_funct_2, axiom,
% 1.34/1.55    (![A:$i]:
% 1.34/1.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.34/1.55       ( ( v1_funct_1 @ A ) & 
% 1.34/1.55         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.34/1.55         ( m1_subset_1 @
% 1.34/1.55           A @ 
% 1.34/1.55           ( k1_zfmisc_1 @
% 1.34/1.55             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.34/1.55  thf('123', plain,
% 1.34/1.55      (![X60 : $i]:
% 1.34/1.55         ((m1_subset_1 @ X60 @ 
% 1.34/1.55           (k1_zfmisc_1 @ 
% 1.34/1.55            (k2_zfmisc_1 @ (k1_relat_1 @ X60) @ (k2_relat_1 @ X60))))
% 1.34/1.55          | ~ (v1_funct_1 @ X60)
% 1.34/1.55          | ~ (v1_relat_1 @ X60))),
% 1.34/1.55      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.34/1.55  thf('124', plain,
% 1.34/1.55      (![X0 : $i]:
% 1.34/1.55         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.34/1.55           (k1_zfmisc_1 @ 
% 1.34/1.55            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 1.34/1.55          | ~ (v1_relat_1 @ X0)
% 1.34/1.55          | ~ (v1_funct_1 @ X0)
% 1.34/1.55          | ~ (v2_funct_1 @ X0)
% 1.34/1.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.34/1.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 1.34/1.55      inference('sup+', [status(thm)], ['122', '123'])).
% 1.34/1.55  thf('125', plain,
% 1.34/1.55      (![X0 : $i]:
% 1.34/1.55         (~ (v1_relat_1 @ X0)
% 1.34/1.55          | ~ (v1_funct_1 @ X0)
% 1.34/1.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.34/1.55          | ~ (v2_funct_1 @ X0)
% 1.34/1.55          | ~ (v1_funct_1 @ X0)
% 1.34/1.55          | ~ (v1_relat_1 @ X0)
% 1.34/1.55          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.34/1.55             (k1_zfmisc_1 @ 
% 1.34/1.55              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 1.34/1.55               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 1.34/1.55      inference('sup-', [status(thm)], ['121', '124'])).
% 1.34/1.55  thf('126', plain,
% 1.34/1.55      (![X0 : $i]:
% 1.34/1.55         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.34/1.55           (k1_zfmisc_1 @ 
% 1.34/1.55            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 1.34/1.55          | ~ (v2_funct_1 @ X0)
% 1.34/1.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.34/1.55          | ~ (v1_funct_1 @ X0)
% 1.34/1.55          | ~ (v1_relat_1 @ X0))),
% 1.34/1.55      inference('simplify', [status(thm)], ['125'])).
% 1.34/1.55  thf('127', plain,
% 1.34/1.55      (![X0 : $i]:
% 1.34/1.55         (~ (v1_relat_1 @ X0)
% 1.34/1.55          | ~ (v1_funct_1 @ X0)
% 1.34/1.55          | ~ (v1_relat_1 @ X0)
% 1.34/1.55          | ~ (v1_funct_1 @ X0)
% 1.34/1.55          | ~ (v2_funct_1 @ X0)
% 1.34/1.55          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.34/1.55             (k1_zfmisc_1 @ 
% 1.34/1.55              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 1.34/1.55               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 1.34/1.55      inference('sup-', [status(thm)], ['120', '126'])).
% 1.34/1.55  thf('128', plain,
% 1.34/1.55      (![X0 : $i]:
% 1.34/1.55         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.34/1.55           (k1_zfmisc_1 @ 
% 1.34/1.55            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 1.34/1.55          | ~ (v2_funct_1 @ X0)
% 1.34/1.55          | ~ (v1_funct_1 @ X0)
% 1.34/1.55          | ~ (v1_relat_1 @ X0))),
% 1.34/1.55      inference('simplify', [status(thm)], ['127'])).
% 1.34/1.55  thf('129', plain,
% 1.34/1.55      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.34/1.55         (k1_zfmisc_1 @ 
% 1.34/1.55          (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))
% 1.34/1.55        | ~ (v1_relat_1 @ sk_C)
% 1.34/1.55        | ~ (v1_funct_1 @ sk_C)
% 1.34/1.55        | ~ (v2_funct_1 @ sk_C))),
% 1.34/1.55      inference('sup+', [status(thm)], ['119', '128'])).
% 1.34/1.55  thf('130', plain, ((v1_relat_1 @ sk_C)),
% 1.34/1.55      inference('demod', [status(thm)], ['111', '112'])).
% 1.34/1.55  thf('131', plain, ((v1_funct_1 @ sk_C)),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.55  thf('132', plain, ((v2_funct_1 @ sk_C)),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.55  thf('133', plain,
% 1.34/1.55      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.34/1.55        (k1_zfmisc_1 @ 
% 1.34/1.55         (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 1.34/1.55      inference('demod', [status(thm)], ['129', '130', '131', '132'])).
% 1.34/1.55  thf('134', plain,
% 1.34/1.55      (![X3 : $i, X4 : $i]:
% 1.34/1.55         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 1.34/1.55          | (v1_relat_1 @ X3)
% 1.34/1.55          | ~ (v1_relat_1 @ X4))),
% 1.34/1.55      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.34/1.55  thf('135', plain,
% 1.34/1.55      ((~ (v1_relat_1 @ 
% 1.34/1.55           (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 1.34/1.55        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.34/1.55      inference('sup-', [status(thm)], ['133', '134'])).
% 1.34/1.55  thf('136', plain,
% 1.34/1.55      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 1.34/1.55      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.34/1.55  thf('137', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.34/1.55      inference('demod', [status(thm)], ['135', '136'])).
% 1.34/1.55  thf('138', plain,
% 1.34/1.55      (![X13 : $i]:
% 1.34/1.55         ((v1_funct_1 @ (k2_funct_1 @ X13))
% 1.34/1.55          | ~ (v1_funct_1 @ X13)
% 1.34/1.55          | ~ (v1_relat_1 @ X13))),
% 1.34/1.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.34/1.55  thf('139', plain,
% 1.34/1.55      (![X13 : $i]:
% 1.34/1.55         ((v1_funct_1 @ (k2_funct_1 @ X13))
% 1.34/1.55          | ~ (v1_funct_1 @ X13)
% 1.34/1.55          | ~ (v1_relat_1 @ X13))),
% 1.34/1.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.34/1.55  thf('140', plain,
% 1.34/1.55      (![X17 : $i]:
% 1.34/1.55         (~ (v2_funct_1 @ X17)
% 1.34/1.55          | ((k1_relat_1 @ X17) = (k2_relat_1 @ (k2_funct_1 @ X17)))
% 1.34/1.55          | ~ (v1_funct_1 @ X17)
% 1.34/1.55          | ~ (v1_relat_1 @ X17))),
% 1.34/1.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.34/1.55  thf('141', plain,
% 1.34/1.55      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.34/1.55        (k1_zfmisc_1 @ 
% 1.34/1.55         (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 1.34/1.55      inference('demod', [status(thm)], ['129', '130', '131', '132'])).
% 1.34/1.55  thf('142', plain,
% 1.34/1.55      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.34/1.55         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C))))
% 1.34/1.55        | ~ (v1_relat_1 @ sk_C)
% 1.34/1.55        | ~ (v1_funct_1 @ sk_C)
% 1.34/1.55        | ~ (v2_funct_1 @ sk_C))),
% 1.34/1.55      inference('sup+', [status(thm)], ['140', '141'])).
% 1.34/1.55  thf('143', plain,
% 1.34/1.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.55  thf('144', plain,
% 1.34/1.55      (![X57 : $i, X58 : $i, X59 : $i]:
% 1.34/1.55         (((X57) = (k1_xboole_0))
% 1.34/1.55          | ~ (v1_funct_1 @ X58)
% 1.34/1.55          | ~ (v1_funct_2 @ X58 @ X59 @ X57)
% 1.34/1.55          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X57)))
% 1.34/1.55          | ((k5_relat_1 @ X58 @ (k2_funct_1 @ X58)) = (k6_partfun1 @ X59))
% 1.34/1.55          | ~ (v2_funct_1 @ X58)
% 1.34/1.55          | ((k2_relset_1 @ X59 @ X57 @ X58) != (X57)))),
% 1.34/1.55      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.34/1.55  thf('145', plain,
% 1.34/1.55      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.34/1.55        | ~ (v2_funct_1 @ sk_C)
% 1.34/1.55        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 1.34/1.55        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.34/1.55        | ~ (v1_funct_1 @ sk_C)
% 1.34/1.55        | ((sk_B) = (k1_xboole_0)))),
% 1.34/1.55      inference('sup-', [status(thm)], ['143', '144'])).
% 1.34/1.55  thf('146', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.55  thf('147', plain, ((v2_funct_1 @ sk_C)),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.55  thf('148', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.55  thf('149', plain, ((v1_funct_1 @ sk_C)),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.55  thf('150', plain,
% 1.34/1.55      ((((sk_B) != (sk_B))
% 1.34/1.55        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 1.34/1.55        | ((sk_B) = (k1_xboole_0)))),
% 1.34/1.55      inference('demod', [status(thm)], ['145', '146', '147', '148', '149'])).
% 1.34/1.55  thf('151', plain,
% 1.34/1.55      ((((sk_B) = (k1_xboole_0))
% 1.34/1.55        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 1.34/1.55      inference('simplify', [status(thm)], ['150'])).
% 1.34/1.55  thf('152', plain, (((sk_B) != (k1_xboole_0))),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.55  thf('153', plain,
% 1.34/1.55      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 1.34/1.55      inference('simplify_reflect-', [status(thm)], ['151', '152'])).
% 1.34/1.55  thf('154', plain,
% 1.34/1.55      (![X18 : $i]:
% 1.34/1.55         (~ (v2_funct_1 @ X18)
% 1.34/1.55          | ((k2_relat_1 @ (k5_relat_1 @ X18 @ (k2_funct_1 @ X18)))
% 1.34/1.55              = (k1_relat_1 @ X18))
% 1.34/1.55          | ~ (v1_funct_1 @ X18)
% 1.34/1.55          | ~ (v1_relat_1 @ X18))),
% 1.34/1.55      inference('cnf', [status(esa)], [t58_funct_1])).
% 1.34/1.55  thf('155', plain,
% 1.34/1.55      ((((k2_relat_1 @ (k6_partfun1 @ sk_A)) = (k1_relat_1 @ sk_C))
% 1.34/1.55        | ~ (v1_relat_1 @ sk_C)
% 1.34/1.55        | ~ (v1_funct_1 @ sk_C)
% 1.34/1.55        | ~ (v2_funct_1 @ sk_C))),
% 1.34/1.55      inference('sup+', [status(thm)], ['153', '154'])).
% 1.34/1.55  thf('156', plain, (![X8 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X8)) = (X8))),
% 1.34/1.55      inference('demod', [status(thm)], ['82', '83'])).
% 1.34/1.55  thf('157', plain, ((v1_relat_1 @ sk_C)),
% 1.34/1.55      inference('demod', [status(thm)], ['111', '112'])).
% 1.34/1.55  thf('158', plain, ((v1_funct_1 @ sk_C)),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.55  thf('159', plain, ((v2_funct_1 @ sk_C)),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.55  thf('160', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 1.34/1.55      inference('demod', [status(thm)], ['155', '156', '157', '158', '159'])).
% 1.34/1.55  thf('161', plain, ((v1_relat_1 @ sk_C)),
% 1.34/1.55      inference('demod', [status(thm)], ['111', '112'])).
% 1.34/1.55  thf('162', plain, ((v1_funct_1 @ sk_C)),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.55  thf('163', plain, ((v2_funct_1 @ sk_C)),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.55  thf('164', plain,
% 1.34/1.55      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.34/1.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.34/1.55      inference('demod', [status(thm)], ['142', '160', '161', '162', '163'])).
% 1.34/1.55  thf('165', plain,
% 1.34/1.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.34/1.55         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.34/1.55            = (k5_relat_1 @ sk_C @ X0))
% 1.34/1.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.34/1.55          | ~ (v1_funct_1 @ X0))),
% 1.34/1.55      inference('demod', [status(thm)], ['14', '15'])).
% 1.34/1.55  thf('166', plain,
% 1.34/1.55      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.34/1.55        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ 
% 1.34/1.55            (k2_funct_1 @ sk_C)) = (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))))),
% 1.34/1.55      inference('sup-', [status(thm)], ['164', '165'])).
% 1.34/1.55  thf('167', plain,
% 1.34/1.55      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 1.34/1.55      inference('simplify_reflect-', [status(thm)], ['151', '152'])).
% 1.34/1.55  thf('168', plain,
% 1.34/1.55      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.34/1.55        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ 
% 1.34/1.55            (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 1.34/1.55      inference('demod', [status(thm)], ['166', '167'])).
% 1.34/1.55  thf('169', plain,
% 1.34/1.55      ((~ (v1_relat_1 @ sk_C)
% 1.34/1.55        | ~ (v1_funct_1 @ sk_C)
% 1.34/1.55        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ 
% 1.34/1.55            (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 1.34/1.55      inference('sup-', [status(thm)], ['139', '168'])).
% 1.34/1.55  thf('170', plain, ((v1_relat_1 @ sk_C)),
% 1.34/1.55      inference('demod', [status(thm)], ['111', '112'])).
% 1.34/1.55  thf('171', plain, ((v1_funct_1 @ sk_C)),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.55  thf('172', plain,
% 1.34/1.55      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ (k2_funct_1 @ sk_C))
% 1.34/1.55         = (k6_partfun1 @ sk_A))),
% 1.34/1.55      inference('demod', [status(thm)], ['169', '170', '171'])).
% 1.34/1.55  thf('173', plain,
% 1.34/1.55      (![X0 : $i]:
% 1.34/1.55         (~ (v1_funct_1 @ X0)
% 1.34/1.55          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.34/1.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.34/1.55          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.34/1.55          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.34/1.55               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.34/1.55               (k6_partfun1 @ sk_A)))),
% 1.34/1.55      inference('demod', [status(thm)], ['22', '23', '24'])).
% 1.34/1.55  thf('174', plain,
% 1.34/1.55      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 1.34/1.55           (k6_partfun1 @ sk_A))
% 1.34/1.55        | ((k2_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C)) = (sk_A))
% 1.34/1.55        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.34/1.55             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.34/1.55        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 1.34/1.55        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.34/1.55      inference('sup-', [status(thm)], ['172', '173'])).
% 1.34/1.55  thf('175', plain,
% 1.34/1.55      (![X30 : $i]:
% 1.34/1.55         (m1_subset_1 @ (k6_partfun1 @ X30) @ 
% 1.34/1.55          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 1.34/1.55      inference('demod', [status(thm)], ['52', '53'])).
% 1.34/1.55  thf('176', plain,
% 1.34/1.55      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.34/1.55         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 1.34/1.55          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 1.34/1.55          | (r2_relset_1 @ X27 @ X28 @ X26 @ X29)
% 1.34/1.55          | ((X26) != (X29)))),
% 1.34/1.55      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.34/1.55  thf('177', plain,
% 1.34/1.55      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.34/1.55         ((r2_relset_1 @ X27 @ X28 @ X29 @ X29)
% 1.34/1.55          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 1.34/1.55      inference('simplify', [status(thm)], ['176'])).
% 1.34/1.55  thf('178', plain,
% 1.34/1.55      (![X0 : $i]:
% 1.34/1.55         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 1.34/1.55      inference('sup-', [status(thm)], ['175', '177'])).
% 1.34/1.55  thf('179', plain,
% 1.34/1.55      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.34/1.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.34/1.55      inference('demod', [status(thm)], ['142', '160', '161', '162', '163'])).
% 1.34/1.55  thf('180', plain,
% 1.34/1.55      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.34/1.55         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 1.34/1.55          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.34/1.55      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.34/1.55  thf('181', plain,
% 1.34/1.55      (((k2_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C))
% 1.34/1.55         = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.34/1.55      inference('sup-', [status(thm)], ['179', '180'])).
% 1.34/1.55  thf('182', plain,
% 1.34/1.55      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.34/1.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.34/1.55      inference('demod', [status(thm)], ['142', '160', '161', '162', '163'])).
% 1.34/1.55  thf('183', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.34/1.55      inference('sup+', [status(thm)], ['117', '118'])).
% 1.34/1.55  thf('184', plain,
% 1.34/1.55      (![X17 : $i]:
% 1.34/1.55         (~ (v2_funct_1 @ X17)
% 1.34/1.55          | ((k2_relat_1 @ X17) = (k1_relat_1 @ (k2_funct_1 @ X17)))
% 1.34/1.55          | ~ (v1_funct_1 @ X17)
% 1.34/1.55          | ~ (v1_relat_1 @ X17))),
% 1.34/1.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.34/1.55  thf('185', plain,
% 1.34/1.55      (![X13 : $i]:
% 1.34/1.55         ((v1_funct_1 @ (k2_funct_1 @ X13))
% 1.34/1.55          | ~ (v1_funct_1 @ X13)
% 1.34/1.55          | ~ (v1_relat_1 @ X13))),
% 1.34/1.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.34/1.55  thf('186', plain,
% 1.34/1.55      (![X13 : $i]:
% 1.34/1.55         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 1.34/1.55          | ~ (v1_funct_1 @ X13)
% 1.34/1.55          | ~ (v1_relat_1 @ X13))),
% 1.34/1.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.34/1.55  thf('187', plain,
% 1.34/1.55      (![X17 : $i]:
% 1.34/1.55         (~ (v2_funct_1 @ X17)
% 1.34/1.55          | ((k1_relat_1 @ X17) = (k2_relat_1 @ (k2_funct_1 @ X17)))
% 1.34/1.55          | ~ (v1_funct_1 @ X17)
% 1.34/1.55          | ~ (v1_relat_1 @ X17))),
% 1.34/1.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.34/1.55  thf('188', plain,
% 1.34/1.55      (![X60 : $i]:
% 1.34/1.55         ((v1_funct_2 @ X60 @ (k1_relat_1 @ X60) @ (k2_relat_1 @ X60))
% 1.34/1.55          | ~ (v1_funct_1 @ X60)
% 1.34/1.55          | ~ (v1_relat_1 @ X60))),
% 1.34/1.55      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.34/1.55  thf('189', plain,
% 1.34/1.55      (![X0 : $i]:
% 1.34/1.55         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 1.34/1.55           (k1_relat_1 @ X0))
% 1.34/1.55          | ~ (v1_relat_1 @ X0)
% 1.34/1.55          | ~ (v1_funct_1 @ X0)
% 1.34/1.55          | ~ (v2_funct_1 @ X0)
% 1.34/1.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.34/1.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 1.34/1.55      inference('sup+', [status(thm)], ['187', '188'])).
% 1.34/1.55  thf('190', plain,
% 1.34/1.55      (![X0 : $i]:
% 1.34/1.55         (~ (v1_relat_1 @ X0)
% 1.34/1.55          | ~ (v1_funct_1 @ X0)
% 1.34/1.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.34/1.55          | ~ (v2_funct_1 @ X0)
% 1.34/1.55          | ~ (v1_funct_1 @ X0)
% 1.34/1.55          | ~ (v1_relat_1 @ X0)
% 1.34/1.55          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 1.34/1.55             (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 1.34/1.55      inference('sup-', [status(thm)], ['186', '189'])).
% 1.34/1.55  thf('191', plain,
% 1.34/1.55      (![X0 : $i]:
% 1.34/1.55         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 1.34/1.55           (k1_relat_1 @ X0))
% 1.34/1.55          | ~ (v2_funct_1 @ X0)
% 1.34/1.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.34/1.55          | ~ (v1_funct_1 @ X0)
% 1.34/1.55          | ~ (v1_relat_1 @ X0))),
% 1.34/1.55      inference('simplify', [status(thm)], ['190'])).
% 1.34/1.55  thf('192', plain,
% 1.34/1.55      (![X0 : $i]:
% 1.34/1.55         (~ (v1_relat_1 @ X0)
% 1.34/1.55          | ~ (v1_funct_1 @ X0)
% 1.34/1.55          | ~ (v1_relat_1 @ X0)
% 1.34/1.55          | ~ (v1_funct_1 @ X0)
% 1.34/1.55          | ~ (v2_funct_1 @ X0)
% 1.34/1.55          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 1.34/1.55             (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 1.34/1.55      inference('sup-', [status(thm)], ['185', '191'])).
% 1.34/1.55  thf('193', plain,
% 1.34/1.55      (![X0 : $i]:
% 1.34/1.55         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 1.34/1.55           (k1_relat_1 @ X0))
% 1.34/1.55          | ~ (v2_funct_1 @ X0)
% 1.34/1.55          | ~ (v1_funct_1 @ X0)
% 1.34/1.55          | ~ (v1_relat_1 @ X0))),
% 1.34/1.55      inference('simplify', [status(thm)], ['192'])).
% 1.34/1.55  thf('194', plain,
% 1.34/1.55      (![X0 : $i]:
% 1.34/1.55         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.34/1.55           (k1_relat_1 @ X0))
% 1.34/1.55          | ~ (v1_relat_1 @ X0)
% 1.34/1.55          | ~ (v1_funct_1 @ X0)
% 1.34/1.55          | ~ (v2_funct_1 @ X0)
% 1.34/1.55          | ~ (v1_relat_1 @ X0)
% 1.34/1.55          | ~ (v1_funct_1 @ X0)
% 1.34/1.55          | ~ (v2_funct_1 @ X0))),
% 1.34/1.55      inference('sup+', [status(thm)], ['184', '193'])).
% 1.34/1.55  thf('195', plain,
% 1.34/1.55      (![X0 : $i]:
% 1.34/1.55         (~ (v2_funct_1 @ X0)
% 1.34/1.55          | ~ (v1_funct_1 @ X0)
% 1.34/1.55          | ~ (v1_relat_1 @ X0)
% 1.34/1.55          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 1.34/1.55             (k1_relat_1 @ X0)))),
% 1.34/1.55      inference('simplify', [status(thm)], ['194'])).
% 1.34/1.55  thf('196', plain,
% 1.34/1.55      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))
% 1.34/1.55        | ~ (v1_relat_1 @ sk_C)
% 1.34/1.55        | ~ (v1_funct_1 @ sk_C)
% 1.34/1.55        | ~ (v2_funct_1 @ sk_C))),
% 1.34/1.55      inference('sup+', [status(thm)], ['183', '195'])).
% 1.34/1.55  thf('197', plain, ((v1_relat_1 @ sk_C)),
% 1.34/1.55      inference('demod', [status(thm)], ['111', '112'])).
% 1.34/1.55  thf('198', plain, ((v1_funct_1 @ sk_C)),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.55  thf('199', plain, ((v2_funct_1 @ sk_C)),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.55  thf('200', plain,
% 1.34/1.55      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))),
% 1.34/1.55      inference('demod', [status(thm)], ['196', '197', '198', '199'])).
% 1.34/1.55  thf('201', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 1.34/1.55      inference('demod', [status(thm)], ['155', '156', '157', '158', '159'])).
% 1.34/1.55  thf('202', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 1.34/1.55      inference('demod', [status(thm)], ['200', '201'])).
% 1.34/1.55  thf('203', plain,
% 1.34/1.55      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_A))
% 1.34/1.55        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.34/1.55      inference('demod', [status(thm)], ['174', '178', '181', '182', '202'])).
% 1.34/1.55  thf('204', plain,
% 1.34/1.55      ((~ (v1_relat_1 @ sk_C)
% 1.34/1.55        | ~ (v1_funct_1 @ sk_C)
% 1.34/1.55        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_A)))),
% 1.34/1.55      inference('sup-', [status(thm)], ['138', '203'])).
% 1.34/1.55  thf('205', plain, ((v1_relat_1 @ sk_C)),
% 1.34/1.55      inference('demod', [status(thm)], ['111', '112'])).
% 1.34/1.55  thf('206', plain, ((v1_funct_1 @ sk_C)),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.55  thf('207', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_A))),
% 1.34/1.55      inference('demod', [status(thm)], ['204', '205', '206'])).
% 1.34/1.55  thf('208', plain,
% 1.34/1.55      (![X0 : $i, X1 : $i]:
% 1.34/1.55         (((k6_partfun1 @ sk_B) != (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.34/1.55          | ~ (v1_relat_1 @ X0)
% 1.34/1.55          | ((X0) = (k2_funct_1 @ sk_C))
% 1.34/1.55          | ((k5_relat_1 @ sk_C @ X0) != (k6_partfun1 @ X1))
% 1.34/1.55          | ~ (r1_tarski @ sk_A @ X1))),
% 1.34/1.55      inference('demod', [status(thm)], ['114', '137', '207'])).
% 1.34/1.55  thf('209', plain,
% 1.34/1.55      (![X0 : $i]:
% 1.34/1.55         (((k6_partfun1 @ sk_B) != (k6_partfun1 @ sk_B))
% 1.34/1.55          | ~ (r1_tarski @ sk_A @ X0)
% 1.34/1.55          | ((k5_relat_1 @ sk_C @ sk_D) != (k6_partfun1 @ X0))
% 1.34/1.55          | ((sk_D) = (k2_funct_1 @ sk_C))
% 1.34/1.55          | ~ (v1_relat_1 @ sk_D))),
% 1.34/1.55      inference('sup-', [status(thm)], ['92', '208'])).
% 1.34/1.55  thf('210', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.34/1.55      inference('demod', [status(thm)], ['51', '54'])).
% 1.34/1.55  thf('211', plain, ((v1_relat_1 @ sk_D)),
% 1.34/1.55      inference('demod', [status(thm)], ['87', '88'])).
% 1.34/1.55  thf('212', plain,
% 1.34/1.55      (![X0 : $i]:
% 1.34/1.55         (((k6_partfun1 @ sk_B) != (k6_partfun1 @ sk_B))
% 1.34/1.55          | ~ (r1_tarski @ sk_A @ X0)
% 1.34/1.55          | ((k6_partfun1 @ sk_A) != (k6_partfun1 @ X0))
% 1.34/1.55          | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 1.34/1.55      inference('demod', [status(thm)], ['209', '210', '211'])).
% 1.34/1.55  thf('213', plain,
% 1.34/1.55      (![X0 : $i]:
% 1.34/1.55         (((sk_D) = (k2_funct_1 @ sk_C))
% 1.34/1.55          | ((k6_partfun1 @ sk_A) != (k6_partfun1 @ X0))
% 1.34/1.55          | ~ (r1_tarski @ sk_A @ X0))),
% 1.34/1.55      inference('simplify', [status(thm)], ['212'])).
% 1.34/1.55  thf('214', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.34/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.34/1.55  thf('215', plain,
% 1.34/1.55      (![X0 : $i]:
% 1.34/1.55         (((k6_partfun1 @ sk_A) != (k6_partfun1 @ X0))
% 1.34/1.55          | ~ (r1_tarski @ sk_A @ X0))),
% 1.34/1.55      inference('simplify_reflect-', [status(thm)], ['213', '214'])).
% 1.34/1.55  thf('216', plain, (~ (r1_tarski @ sk_A @ sk_A)),
% 1.34/1.55      inference('eq_res', [status(thm)], ['215'])).
% 1.34/1.55  thf(d10_xboole_0, axiom,
% 1.34/1.55    (![A:$i,B:$i]:
% 1.34/1.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.34/1.55  thf('217', plain,
% 1.34/1.55      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.34/1.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.34/1.55  thf('218', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.34/1.55      inference('simplify', [status(thm)], ['217'])).
% 1.34/1.55  thf('219', plain, ($false), inference('demod', [status(thm)], ['216', '218'])).
% 1.34/1.55  
% 1.34/1.55  % SZS output end Refutation
% 1.34/1.55  
% 1.34/1.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

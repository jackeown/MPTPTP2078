%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VUNFytv8IZ

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:27 EST 2020

% Result     : Theorem 2.32s
% Output     : Refutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 764 expanded)
%              Number of leaves         :   47 ( 237 expanded)
%              Depth                    :   26
%              Number of atoms          : 1795 (20235 expanded)
%              Number of equality atoms :  109 (1342 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

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

thf('1',plain,(
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

thf('2',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( X48 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X48 ) ) )
      | ( ( k5_relat_1 @ X49 @ ( k2_funct_1 @ X49 ) )
        = ( k6_partfun1 @ X50 ) )
      | ~ ( v2_funct_1 @ X49 )
      | ( ( k2_relset_1 @ X50 @ X48 @ X49 )
       != X48 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('3',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('6',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
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

thf('9',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 )
        = ( k5_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
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

thf('17',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( r2_relset_1 @ X36 @ X36 @ ( k1_partfun1 @ X36 @ X37 @ X37 @ X36 @ X35 @ X38 ) @ ( k6_partfun1 @ X36 ) )
      | ( ( k2_relset_1 @ X37 @ X36 @ X38 )
        = X36 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X36 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('25',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['22','25','26','27','28','29'])).

thf('31',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['6','30'])).

thf('32',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','31','32','33'])).

thf('35',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('39',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
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

thf('42',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('49',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('50',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( X17 = X20 )
      | ~ ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','51'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('53',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('54',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('55',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['52','55'])).

thf('57',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['38','56'])).

thf('58',plain,(
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

thf('59',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ( zip_tseitin_0 @ X43 @ X46 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X47 @ X44 @ X44 @ X45 @ X46 @ X43 ) )
      | ( zip_tseitin_1 @ X45 @ X44 )
      | ( ( k2_relset_1 @ X47 @ X44 @ X46 )
       != X44 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X44 )
      | ~ ( v1_funct_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('60',plain,(
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
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['57','63'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('65',plain,(
    ! [X11: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('66',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('67',plain,(
    ! [X11: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X11 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['64','67','68','69','70','71'])).

thf('73',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X41: $i,X42: $i] :
      ( ( X41 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('75',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X39: $i,X40: $i] :
      ( ( v2_funct_1 @ X40 )
      | ~ ( zip_tseitin_0 @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('79',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['37','79'])).

thf('81',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['52','55'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('82',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) @ X6 )
        = ( k5_relat_1 @ X5 @ ( k5_relat_1 @ X4 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('86',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('87',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('88',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('91',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('93',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['83','88','93'])).

thf('95',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k2_funct_1 @ sk_D ) )
      = ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['80','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('98',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['98','99'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('101',plain,(
    ! [X8: $i] :
      ( ( ( k5_relat_1 @ X8 @ ( k6_relat_1 @ ( k2_relat_1 @ X8 ) ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('102',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('103',plain,(
    ! [X8: $i] :
      ( ( ( k5_relat_1 @ X8 @ ( k6_partfun1 @ ( k2_relat_1 @ X8 ) ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['100','103'])).

thf('105',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['86','87'])).

thf('106',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k2_funct_1 @ sk_D ) )
      = sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['95','106'])).

thf('108',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['22','25','26','27','28','29'])).

thf('109',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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

thf('110',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_relat_1 @ X12 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('111',plain,(
    ! [X7: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X7 ) ) @ X7 )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('112',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('113',plain,(
    ! [X7: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X7 ) ) @ X7 )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['110','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['109','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k2_funct_1 @ sk_D ) )
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['108','116'])).

thf('118',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['91','92'])).

thf('119',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k2_funct_1 @ sk_D ) )
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['77','78'])).

thf('122',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k2_funct_1 @ sk_D ) )
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( ( k2_funct_1 @ sk_D )
      = sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['107','122'])).

thf('124',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k2_funct_1 @ sk_D )
      = sk_C ) ),
    inference('sup-',[status(thm)],['0','123'])).

thf('125',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['91','92'])).

thf('126',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( k2_funct_1 @ sk_D )
    = sk_C ),
    inference(demod,[status(thm)],['124','125','126'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('128',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('129',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['91','92'])).

thf('131',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['77','78'])).

thf('133',plain,
    ( ( k2_funct_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['129','130','131','132'])).

thf('134',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['133','134'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VUNFytv8IZ
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:38:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.32/2.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.32/2.54  % Solved by: fo/fo7.sh
% 2.32/2.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.32/2.54  % done 1869 iterations in 2.082s
% 2.32/2.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.32/2.54  % SZS output start Refutation
% 2.32/2.54  thf(sk_C_type, type, sk_C: $i).
% 2.32/2.54  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.32/2.54  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.32/2.54  thf(sk_A_type, type, sk_A: $i).
% 2.32/2.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.32/2.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.32/2.54  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.32/2.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.32/2.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.32/2.54  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.32/2.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.32/2.54  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.32/2.54  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.32/2.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.32/2.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.32/2.54  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 2.32/2.54  thf(sk_B_type, type, sk_B: $i).
% 2.32/2.54  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.32/2.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.32/2.54  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.32/2.54  thf(sk_D_type, type, sk_D: $i).
% 2.32/2.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.32/2.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.32/2.54  thf(dt_k2_funct_1, axiom,
% 2.32/2.54    (![A:$i]:
% 2.32/2.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.32/2.54       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 2.32/2.54         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 2.32/2.54  thf('0', plain,
% 2.32/2.54      (![X9 : $i]:
% 2.32/2.54         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 2.32/2.54          | ~ (v1_funct_1 @ X9)
% 2.32/2.54          | ~ (v1_relat_1 @ X9))),
% 2.32/2.54      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.32/2.54  thf(t36_funct_2, conjecture,
% 2.32/2.54    (![A:$i,B:$i,C:$i]:
% 2.32/2.54     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.32/2.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.32/2.54       ( ![D:$i]:
% 2.32/2.54         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.32/2.54             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.32/2.54           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.32/2.54               ( r2_relset_1 @
% 2.32/2.54                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.32/2.54                 ( k6_partfun1 @ A ) ) & 
% 2.32/2.54               ( v2_funct_1 @ C ) ) =>
% 2.32/2.54             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.32/2.54               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 2.32/2.54  thf(zf_stmt_0, negated_conjecture,
% 2.32/2.54    (~( ![A:$i,B:$i,C:$i]:
% 2.32/2.54        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.32/2.54            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.32/2.54          ( ![D:$i]:
% 2.32/2.54            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.32/2.54                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.32/2.54              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.32/2.54                  ( r2_relset_1 @
% 2.32/2.54                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.32/2.54                    ( k6_partfun1 @ A ) ) & 
% 2.32/2.54                  ( v2_funct_1 @ C ) ) =>
% 2.32/2.54                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.32/2.54                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 2.32/2.54    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 2.32/2.54  thf('1', plain,
% 2.32/2.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.32/2.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.54  thf(t35_funct_2, axiom,
% 2.32/2.54    (![A:$i,B:$i,C:$i]:
% 2.32/2.54     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.32/2.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.32/2.54       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 2.32/2.54         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.32/2.54           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 2.32/2.54             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 2.32/2.54  thf('2', plain,
% 2.32/2.54      (![X48 : $i, X49 : $i, X50 : $i]:
% 2.32/2.54         (((X48) = (k1_xboole_0))
% 2.32/2.54          | ~ (v1_funct_1 @ X49)
% 2.32/2.54          | ~ (v1_funct_2 @ X49 @ X50 @ X48)
% 2.32/2.54          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X48)))
% 2.32/2.54          | ((k5_relat_1 @ X49 @ (k2_funct_1 @ X49)) = (k6_partfun1 @ X50))
% 2.32/2.54          | ~ (v2_funct_1 @ X49)
% 2.32/2.54          | ((k2_relset_1 @ X50 @ X48 @ X49) != (X48)))),
% 2.32/2.54      inference('cnf', [status(esa)], [t35_funct_2])).
% 2.32/2.54  thf('3', plain,
% 2.32/2.54      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 2.32/2.54        | ~ (v2_funct_1 @ sk_D)
% 2.32/2.54        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 2.32/2.54        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.32/2.54        | ~ (v1_funct_1 @ sk_D)
% 2.32/2.54        | ((sk_A) = (k1_xboole_0)))),
% 2.32/2.54      inference('sup-', [status(thm)], ['1', '2'])).
% 2.32/2.54  thf('4', plain,
% 2.32/2.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.32/2.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.54  thf(redefinition_k2_relset_1, axiom,
% 2.32/2.54    (![A:$i,B:$i,C:$i]:
% 2.32/2.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.32/2.54       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.32/2.54  thf('5', plain,
% 2.32/2.54      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.32/2.54         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 2.32/2.54          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 2.32/2.54      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.32/2.54  thf('6', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.32/2.54      inference('sup-', [status(thm)], ['4', '5'])).
% 2.32/2.54  thf('7', plain,
% 2.32/2.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.32/2.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.54  thf('8', plain,
% 2.32/2.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.32/2.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.54  thf(redefinition_k1_partfun1, axiom,
% 2.32/2.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.32/2.54     ( ( ( v1_funct_1 @ E ) & 
% 2.32/2.54         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.32/2.54         ( v1_funct_1 @ F ) & 
% 2.32/2.54         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.32/2.54       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.32/2.54  thf('9', plain,
% 2.32/2.54      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 2.32/2.55         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 2.32/2.55          | ~ (v1_funct_1 @ X28)
% 2.32/2.55          | ~ (v1_funct_1 @ X31)
% 2.32/2.55          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 2.32/2.55          | ((k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31)
% 2.32/2.55              = (k5_relat_1 @ X28 @ X31)))),
% 2.32/2.55      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 2.32/2.55  thf('10', plain,
% 2.32/2.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.32/2.55         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.32/2.55            = (k5_relat_1 @ sk_C @ X0))
% 2.32/2.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.32/2.55          | ~ (v1_funct_1 @ X0)
% 2.32/2.55          | ~ (v1_funct_1 @ sk_C))),
% 2.32/2.55      inference('sup-', [status(thm)], ['8', '9'])).
% 2.32/2.55  thf('11', plain, ((v1_funct_1 @ sk_C)),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('12', plain,
% 2.32/2.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.32/2.55         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.32/2.55            = (k5_relat_1 @ sk_C @ X0))
% 2.32/2.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.32/2.55          | ~ (v1_funct_1 @ X0))),
% 2.32/2.55      inference('demod', [status(thm)], ['10', '11'])).
% 2.32/2.55  thf('13', plain,
% 2.32/2.55      ((~ (v1_funct_1 @ sk_D)
% 2.32/2.55        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.32/2.55            = (k5_relat_1 @ sk_C @ sk_D)))),
% 2.32/2.55      inference('sup-', [status(thm)], ['7', '12'])).
% 2.32/2.55  thf('14', plain, ((v1_funct_1 @ sk_D)),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('15', plain,
% 2.32/2.55      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.32/2.55         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.32/2.55      inference('demod', [status(thm)], ['13', '14'])).
% 2.32/2.55  thf('16', plain,
% 2.32/2.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf(t24_funct_2, axiom,
% 2.32/2.55    (![A:$i,B:$i,C:$i]:
% 2.32/2.55     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.32/2.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.32/2.55       ( ![D:$i]:
% 2.32/2.55         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.32/2.55             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.32/2.55           ( ( r2_relset_1 @
% 2.32/2.55               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 2.32/2.55               ( k6_partfun1 @ B ) ) =>
% 2.32/2.55             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 2.32/2.55  thf('17', plain,
% 2.32/2.55      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 2.32/2.55         (~ (v1_funct_1 @ X35)
% 2.32/2.55          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 2.32/2.55          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 2.32/2.55          | ~ (r2_relset_1 @ X36 @ X36 @ 
% 2.32/2.55               (k1_partfun1 @ X36 @ X37 @ X37 @ X36 @ X35 @ X38) @ 
% 2.32/2.55               (k6_partfun1 @ X36))
% 2.32/2.55          | ((k2_relset_1 @ X37 @ X36 @ X38) = (X36))
% 2.32/2.55          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 2.32/2.55          | ~ (v1_funct_2 @ X38 @ X37 @ X36)
% 2.32/2.55          | ~ (v1_funct_1 @ X38))),
% 2.32/2.55      inference('cnf', [status(esa)], [t24_funct_2])).
% 2.32/2.55  thf('18', plain,
% 2.32/2.55      (![X0 : $i]:
% 2.32/2.55         (~ (v1_funct_1 @ X0)
% 2.32/2.55          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.32/2.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.32/2.55          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.32/2.55          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.32/2.55               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.32/2.55               (k6_partfun1 @ sk_A))
% 2.32/2.55          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.32/2.55          | ~ (v1_funct_1 @ sk_C))),
% 2.32/2.55      inference('sup-', [status(thm)], ['16', '17'])).
% 2.32/2.55  thf('19', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('21', plain,
% 2.32/2.55      (![X0 : $i]:
% 2.32/2.55         (~ (v1_funct_1 @ X0)
% 2.32/2.55          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.32/2.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.32/2.55          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.32/2.55          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.32/2.55               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.32/2.55               (k6_partfun1 @ sk_A)))),
% 2.32/2.55      inference('demod', [status(thm)], ['18', '19', '20'])).
% 2.32/2.55  thf('22', plain,
% 2.32/2.55      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 2.32/2.55           (k6_partfun1 @ sk_A))
% 2.32/2.55        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 2.32/2.55        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.32/2.55        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.32/2.55        | ~ (v1_funct_1 @ sk_D))),
% 2.32/2.55      inference('sup-', [status(thm)], ['15', '21'])).
% 2.32/2.55  thf('23', plain,
% 2.32/2.55      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.32/2.55        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.32/2.55        (k6_partfun1 @ sk_A))),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('24', plain,
% 2.32/2.55      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.32/2.55         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.32/2.55      inference('demod', [status(thm)], ['13', '14'])).
% 2.32/2.55  thf('25', plain,
% 2.32/2.55      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 2.32/2.55        (k6_partfun1 @ sk_A))),
% 2.32/2.55      inference('demod', [status(thm)], ['23', '24'])).
% 2.32/2.55  thf('26', plain,
% 2.32/2.55      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.32/2.55      inference('sup-', [status(thm)], ['4', '5'])).
% 2.32/2.55  thf('27', plain,
% 2.32/2.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('28', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('29', plain, ((v1_funct_1 @ sk_D)),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('30', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.32/2.55      inference('demod', [status(thm)], ['22', '25', '26', '27', '28', '29'])).
% 2.32/2.55  thf('31', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))),
% 2.32/2.55      inference('demod', [status(thm)], ['6', '30'])).
% 2.32/2.55  thf('32', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('33', plain, ((v1_funct_1 @ sk_D)),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('34', plain,
% 2.32/2.55      ((((sk_A) != (sk_A))
% 2.32/2.55        | ~ (v2_funct_1 @ sk_D)
% 2.32/2.55        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 2.32/2.55        | ((sk_A) = (k1_xboole_0)))),
% 2.32/2.55      inference('demod', [status(thm)], ['3', '31', '32', '33'])).
% 2.32/2.55  thf('35', plain,
% 2.32/2.55      ((((sk_A) = (k1_xboole_0))
% 2.32/2.55        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 2.32/2.55        | ~ (v2_funct_1 @ sk_D))),
% 2.32/2.55      inference('simplify', [status(thm)], ['34'])).
% 2.32/2.55  thf('36', plain, (((sk_A) != (k1_xboole_0))),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('37', plain,
% 2.32/2.55      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 2.32/2.55        | ~ (v2_funct_1 @ sk_D))),
% 2.32/2.55      inference('simplify_reflect-', [status(thm)], ['35', '36'])).
% 2.32/2.55  thf('38', plain,
% 2.32/2.55      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.32/2.55         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.32/2.55      inference('demod', [status(thm)], ['13', '14'])).
% 2.32/2.55  thf('39', plain,
% 2.32/2.55      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 2.32/2.55        (k6_partfun1 @ sk_A))),
% 2.32/2.55      inference('demod', [status(thm)], ['23', '24'])).
% 2.32/2.55  thf('40', plain,
% 2.32/2.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('41', plain,
% 2.32/2.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf(dt_k1_partfun1, axiom,
% 2.32/2.55    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.32/2.55     ( ( ( v1_funct_1 @ E ) & 
% 2.32/2.55         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.32/2.55         ( v1_funct_1 @ F ) & 
% 2.32/2.55         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.32/2.55       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.32/2.55         ( m1_subset_1 @
% 2.32/2.55           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.32/2.55           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.32/2.55  thf('42', plain,
% 2.32/2.55      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 2.32/2.55         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 2.32/2.55          | ~ (v1_funct_1 @ X22)
% 2.32/2.55          | ~ (v1_funct_1 @ X25)
% 2.32/2.55          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 2.32/2.55          | (m1_subset_1 @ (k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25) @ 
% 2.32/2.55             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X27))))),
% 2.32/2.55      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.32/2.55  thf('43', plain,
% 2.32/2.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.32/2.55         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.32/2.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.32/2.55          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.32/2.55          | ~ (v1_funct_1 @ X1)
% 2.32/2.55          | ~ (v1_funct_1 @ sk_C))),
% 2.32/2.55      inference('sup-', [status(thm)], ['41', '42'])).
% 2.32/2.55  thf('44', plain, ((v1_funct_1 @ sk_C)),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('45', plain,
% 2.32/2.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.32/2.55         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.32/2.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.32/2.55          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.32/2.55          | ~ (v1_funct_1 @ X1))),
% 2.32/2.55      inference('demod', [status(thm)], ['43', '44'])).
% 2.32/2.55  thf('46', plain,
% 2.32/2.55      ((~ (v1_funct_1 @ sk_D)
% 2.32/2.55        | (m1_subset_1 @ 
% 2.32/2.55           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.32/2.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.32/2.55      inference('sup-', [status(thm)], ['40', '45'])).
% 2.32/2.55  thf('47', plain, ((v1_funct_1 @ sk_D)),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('48', plain,
% 2.32/2.55      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.32/2.55         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.32/2.55      inference('demod', [status(thm)], ['13', '14'])).
% 2.32/2.55  thf('49', plain,
% 2.32/2.55      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 2.32/2.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.32/2.55      inference('demod', [status(thm)], ['46', '47', '48'])).
% 2.32/2.55  thf(redefinition_r2_relset_1, axiom,
% 2.32/2.55    (![A:$i,B:$i,C:$i,D:$i]:
% 2.32/2.55     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.32/2.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.32/2.55       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.32/2.55  thf('50', plain,
% 2.32/2.55      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 2.32/2.55         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 2.32/2.55          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 2.32/2.55          | ((X17) = (X20))
% 2.32/2.55          | ~ (r2_relset_1 @ X18 @ X19 @ X17 @ X20))),
% 2.32/2.55      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.32/2.55  thf('51', plain,
% 2.32/2.55      (![X0 : $i]:
% 2.32/2.55         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 2.32/2.55          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 2.32/2.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.32/2.55      inference('sup-', [status(thm)], ['49', '50'])).
% 2.32/2.55  thf('52', plain,
% 2.32/2.55      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 2.32/2.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.32/2.55        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 2.32/2.55      inference('sup-', [status(thm)], ['39', '51'])).
% 2.32/2.55  thf(t29_relset_1, axiom,
% 2.32/2.55    (![A:$i]:
% 2.32/2.55     ( m1_subset_1 @
% 2.32/2.55       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 2.32/2.55  thf('53', plain,
% 2.32/2.55      (![X21 : $i]:
% 2.32/2.55         (m1_subset_1 @ (k6_relat_1 @ X21) @ 
% 2.32/2.55          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 2.32/2.55      inference('cnf', [status(esa)], [t29_relset_1])).
% 2.32/2.55  thf(redefinition_k6_partfun1, axiom,
% 2.32/2.55    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.32/2.55  thf('54', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 2.32/2.55      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.32/2.55  thf('55', plain,
% 2.32/2.55      (![X21 : $i]:
% 2.32/2.55         (m1_subset_1 @ (k6_partfun1 @ X21) @ 
% 2.32/2.55          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 2.32/2.55      inference('demod', [status(thm)], ['53', '54'])).
% 2.32/2.55  thf('56', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 2.32/2.55      inference('demod', [status(thm)], ['52', '55'])).
% 2.32/2.55  thf('57', plain,
% 2.32/2.55      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.32/2.55         = (k6_partfun1 @ sk_A))),
% 2.32/2.55      inference('demod', [status(thm)], ['38', '56'])).
% 2.32/2.55  thf('58', plain,
% 2.32/2.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf(t30_funct_2, axiom,
% 2.32/2.55    (![A:$i,B:$i,C:$i,D:$i]:
% 2.32/2.55     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.32/2.55         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 2.32/2.55       ( ![E:$i]:
% 2.32/2.55         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 2.32/2.55             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 2.32/2.55           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 2.32/2.55               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 2.32/2.55             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 2.32/2.55               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 2.32/2.55  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 2.32/2.55  thf(zf_stmt_2, axiom,
% 2.32/2.55    (![C:$i,B:$i]:
% 2.32/2.55     ( ( zip_tseitin_1 @ C @ B ) =>
% 2.32/2.55       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 2.32/2.55  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 2.32/2.55  thf(zf_stmt_4, axiom,
% 2.32/2.55    (![E:$i,D:$i]:
% 2.32/2.55     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 2.32/2.55  thf(zf_stmt_5, axiom,
% 2.32/2.55    (![A:$i,B:$i,C:$i,D:$i]:
% 2.32/2.55     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.32/2.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.32/2.55       ( ![E:$i]:
% 2.32/2.55         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.32/2.55             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.32/2.55           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 2.32/2.55               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 2.32/2.55             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 2.32/2.55  thf('59', plain,
% 2.32/2.55      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 2.32/2.55         (~ (v1_funct_1 @ X43)
% 2.32/2.55          | ~ (v1_funct_2 @ X43 @ X44 @ X45)
% 2.32/2.55          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 2.32/2.55          | (zip_tseitin_0 @ X43 @ X46)
% 2.32/2.55          | ~ (v2_funct_1 @ (k1_partfun1 @ X47 @ X44 @ X44 @ X45 @ X46 @ X43))
% 2.32/2.55          | (zip_tseitin_1 @ X45 @ X44)
% 2.32/2.55          | ((k2_relset_1 @ X47 @ X44 @ X46) != (X44))
% 2.32/2.55          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X44)))
% 2.32/2.55          | ~ (v1_funct_2 @ X46 @ X47 @ X44)
% 2.32/2.55          | ~ (v1_funct_1 @ X46))),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.32/2.55  thf('60', plain,
% 2.32/2.55      (![X0 : $i, X1 : $i]:
% 2.32/2.55         (~ (v1_funct_1 @ X0)
% 2.32/2.55          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.32/2.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.32/2.55          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 2.32/2.55          | (zip_tseitin_1 @ sk_A @ sk_B)
% 2.32/2.55          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 2.32/2.55          | (zip_tseitin_0 @ sk_D @ X0)
% 2.32/2.55          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.32/2.55          | ~ (v1_funct_1 @ sk_D))),
% 2.32/2.55      inference('sup-', [status(thm)], ['58', '59'])).
% 2.32/2.55  thf('61', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('62', plain, ((v1_funct_1 @ sk_D)),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('63', plain,
% 2.32/2.55      (![X0 : $i, X1 : $i]:
% 2.32/2.55         (~ (v1_funct_1 @ X0)
% 2.32/2.55          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.32/2.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.32/2.55          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 2.32/2.55          | (zip_tseitin_1 @ sk_A @ sk_B)
% 2.32/2.55          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 2.32/2.55          | (zip_tseitin_0 @ sk_D @ X0))),
% 2.32/2.55      inference('demod', [status(thm)], ['60', '61', '62'])).
% 2.32/2.55  thf('64', plain,
% 2.32/2.55      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 2.32/2.55        | (zip_tseitin_0 @ sk_D @ sk_C)
% 2.32/2.55        | (zip_tseitin_1 @ sk_A @ sk_B)
% 2.32/2.55        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 2.32/2.55        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 2.32/2.55        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.32/2.55        | ~ (v1_funct_1 @ sk_C))),
% 2.32/2.55      inference('sup-', [status(thm)], ['57', '63'])).
% 2.32/2.55  thf(fc4_funct_1, axiom,
% 2.32/2.55    (![A:$i]:
% 2.32/2.55     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 2.32/2.55       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 2.32/2.55  thf('65', plain, (![X11 : $i]: (v2_funct_1 @ (k6_relat_1 @ X11))),
% 2.32/2.55      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.32/2.55  thf('66', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 2.32/2.55      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.32/2.55  thf('67', plain, (![X11 : $i]: (v2_funct_1 @ (k6_partfun1 @ X11))),
% 2.32/2.55      inference('demod', [status(thm)], ['65', '66'])).
% 2.32/2.55  thf('68', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('69', plain,
% 2.32/2.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('70', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('71', plain, ((v1_funct_1 @ sk_C)),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('72', plain,
% 2.32/2.55      (((zip_tseitin_0 @ sk_D @ sk_C)
% 2.32/2.55        | (zip_tseitin_1 @ sk_A @ sk_B)
% 2.32/2.55        | ((sk_B) != (sk_B)))),
% 2.32/2.55      inference('demod', [status(thm)], ['64', '67', '68', '69', '70', '71'])).
% 2.32/2.55  thf('73', plain,
% 2.32/2.55      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 2.32/2.55      inference('simplify', [status(thm)], ['72'])).
% 2.32/2.55  thf('74', plain,
% 2.32/2.55      (![X41 : $i, X42 : $i]:
% 2.32/2.55         (((X41) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X41 @ X42))),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.32/2.55  thf('75', plain,
% 2.32/2.55      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 2.32/2.55      inference('sup-', [status(thm)], ['73', '74'])).
% 2.32/2.55  thf('76', plain, (((sk_A) != (k1_xboole_0))),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('77', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 2.32/2.55      inference('simplify_reflect-', [status(thm)], ['75', '76'])).
% 2.32/2.55  thf('78', plain,
% 2.32/2.55      (![X39 : $i, X40 : $i]:
% 2.32/2.55         ((v2_funct_1 @ X40) | ~ (zip_tseitin_0 @ X40 @ X39))),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_4])).
% 2.32/2.55  thf('79', plain, ((v2_funct_1 @ sk_D)),
% 2.32/2.55      inference('sup-', [status(thm)], ['77', '78'])).
% 2.32/2.55  thf('80', plain,
% 2.32/2.55      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 2.32/2.55      inference('demod', [status(thm)], ['37', '79'])).
% 2.32/2.55  thf('81', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 2.32/2.55      inference('demod', [status(thm)], ['52', '55'])).
% 2.32/2.55  thf(t55_relat_1, axiom,
% 2.32/2.55    (![A:$i]:
% 2.32/2.55     ( ( v1_relat_1 @ A ) =>
% 2.32/2.55       ( ![B:$i]:
% 2.32/2.55         ( ( v1_relat_1 @ B ) =>
% 2.32/2.55           ( ![C:$i]:
% 2.32/2.55             ( ( v1_relat_1 @ C ) =>
% 2.32/2.55               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 2.32/2.55                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 2.32/2.55  thf('82', plain,
% 2.32/2.55      (![X4 : $i, X5 : $i, X6 : $i]:
% 2.32/2.55         (~ (v1_relat_1 @ X4)
% 2.32/2.55          | ((k5_relat_1 @ (k5_relat_1 @ X5 @ X4) @ X6)
% 2.32/2.55              = (k5_relat_1 @ X5 @ (k5_relat_1 @ X4 @ X6)))
% 2.32/2.55          | ~ (v1_relat_1 @ X6)
% 2.32/2.55          | ~ (v1_relat_1 @ X5))),
% 2.32/2.55      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.32/2.55  thf('83', plain,
% 2.32/2.55      (![X0 : $i]:
% 2.32/2.55         (((k5_relat_1 @ (k6_partfun1 @ sk_A) @ X0)
% 2.32/2.55            = (k5_relat_1 @ sk_C @ (k5_relat_1 @ sk_D @ X0)))
% 2.32/2.55          | ~ (v1_relat_1 @ sk_C)
% 2.32/2.55          | ~ (v1_relat_1 @ X0)
% 2.32/2.55          | ~ (v1_relat_1 @ sk_D))),
% 2.32/2.55      inference('sup+', [status(thm)], ['81', '82'])).
% 2.32/2.55  thf('84', plain,
% 2.32/2.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf(cc2_relat_1, axiom,
% 2.32/2.55    (![A:$i]:
% 2.32/2.55     ( ( v1_relat_1 @ A ) =>
% 2.32/2.55       ( ![B:$i]:
% 2.32/2.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.32/2.55  thf('85', plain,
% 2.32/2.55      (![X0 : $i, X1 : $i]:
% 2.32/2.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 2.32/2.55          | (v1_relat_1 @ X0)
% 2.32/2.55          | ~ (v1_relat_1 @ X1))),
% 2.32/2.55      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.32/2.55  thf('86', plain,
% 2.32/2.55      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 2.32/2.55      inference('sup-', [status(thm)], ['84', '85'])).
% 2.32/2.55  thf(fc6_relat_1, axiom,
% 2.32/2.55    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.32/2.55  thf('87', plain,
% 2.32/2.55      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 2.32/2.55      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.32/2.55  thf('88', plain, ((v1_relat_1 @ sk_C)),
% 2.32/2.55      inference('demod', [status(thm)], ['86', '87'])).
% 2.32/2.55  thf('89', plain,
% 2.32/2.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('90', plain,
% 2.32/2.55      (![X0 : $i, X1 : $i]:
% 2.32/2.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 2.32/2.55          | (v1_relat_1 @ X0)
% 2.32/2.55          | ~ (v1_relat_1 @ X1))),
% 2.32/2.55      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.32/2.55  thf('91', plain,
% 2.32/2.55      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 2.32/2.55      inference('sup-', [status(thm)], ['89', '90'])).
% 2.32/2.55  thf('92', plain,
% 2.32/2.55      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 2.32/2.55      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.32/2.55  thf('93', plain, ((v1_relat_1 @ sk_D)),
% 2.32/2.55      inference('demod', [status(thm)], ['91', '92'])).
% 2.32/2.55  thf('94', plain,
% 2.32/2.55      (![X0 : $i]:
% 2.32/2.55         (((k5_relat_1 @ (k6_partfun1 @ sk_A) @ X0)
% 2.32/2.55            = (k5_relat_1 @ sk_C @ (k5_relat_1 @ sk_D @ X0)))
% 2.32/2.55          | ~ (v1_relat_1 @ X0))),
% 2.32/2.55      inference('demod', [status(thm)], ['83', '88', '93'])).
% 2.32/2.55  thf('95', plain,
% 2.32/2.55      ((((k5_relat_1 @ (k6_partfun1 @ sk_A) @ (k2_funct_1 @ sk_D))
% 2.32/2.55          = (k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)))
% 2.32/2.55        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D)))),
% 2.32/2.55      inference('sup+', [status(thm)], ['80', '94'])).
% 2.32/2.55  thf('96', plain,
% 2.32/2.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('97', plain,
% 2.32/2.55      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.32/2.55         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 2.32/2.55          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 2.32/2.55      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.32/2.55  thf('98', plain,
% 2.32/2.55      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 2.32/2.55      inference('sup-', [status(thm)], ['96', '97'])).
% 2.32/2.55  thf('99', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('100', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.32/2.55      inference('sup+', [status(thm)], ['98', '99'])).
% 2.32/2.55  thf(t80_relat_1, axiom,
% 2.32/2.55    (![A:$i]:
% 2.32/2.55     ( ( v1_relat_1 @ A ) =>
% 2.32/2.55       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 2.32/2.55  thf('101', plain,
% 2.32/2.55      (![X8 : $i]:
% 2.32/2.55         (((k5_relat_1 @ X8 @ (k6_relat_1 @ (k2_relat_1 @ X8))) = (X8))
% 2.32/2.55          | ~ (v1_relat_1 @ X8))),
% 2.32/2.55      inference('cnf', [status(esa)], [t80_relat_1])).
% 2.32/2.55  thf('102', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 2.32/2.55      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.32/2.55  thf('103', plain,
% 2.32/2.55      (![X8 : $i]:
% 2.32/2.55         (((k5_relat_1 @ X8 @ (k6_partfun1 @ (k2_relat_1 @ X8))) = (X8))
% 2.32/2.55          | ~ (v1_relat_1 @ X8))),
% 2.32/2.55      inference('demod', [status(thm)], ['101', '102'])).
% 2.32/2.55  thf('104', plain,
% 2.32/2.55      ((((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))
% 2.32/2.55        | ~ (v1_relat_1 @ sk_C))),
% 2.32/2.55      inference('sup+', [status(thm)], ['100', '103'])).
% 2.32/2.55  thf('105', plain, ((v1_relat_1 @ sk_C)),
% 2.32/2.55      inference('demod', [status(thm)], ['86', '87'])).
% 2.32/2.55  thf('106', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 2.32/2.55      inference('demod', [status(thm)], ['104', '105'])).
% 2.32/2.55  thf('107', plain,
% 2.32/2.55      ((((k5_relat_1 @ (k6_partfun1 @ sk_A) @ (k2_funct_1 @ sk_D)) = (sk_C))
% 2.32/2.55        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D)))),
% 2.32/2.55      inference('demod', [status(thm)], ['95', '106'])).
% 2.32/2.55  thf('108', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.32/2.55      inference('demod', [status(thm)], ['22', '25', '26', '27', '28', '29'])).
% 2.32/2.55  thf('109', plain,
% 2.32/2.55      (![X9 : $i]:
% 2.32/2.55         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 2.32/2.55          | ~ (v1_funct_1 @ X9)
% 2.32/2.55          | ~ (v1_relat_1 @ X9))),
% 2.32/2.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.32/2.55  thf(t55_funct_1, axiom,
% 2.32/2.55    (![A:$i]:
% 2.32/2.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.32/2.55       ( ( v2_funct_1 @ A ) =>
% 2.32/2.55         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 2.32/2.55           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.32/2.55  thf('110', plain,
% 2.32/2.55      (![X12 : $i]:
% 2.32/2.55         (~ (v2_funct_1 @ X12)
% 2.32/2.55          | ((k2_relat_1 @ X12) = (k1_relat_1 @ (k2_funct_1 @ X12)))
% 2.32/2.55          | ~ (v1_funct_1 @ X12)
% 2.32/2.55          | ~ (v1_relat_1 @ X12))),
% 2.32/2.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.32/2.55  thf(t78_relat_1, axiom,
% 2.32/2.55    (![A:$i]:
% 2.32/2.55     ( ( v1_relat_1 @ A ) =>
% 2.32/2.55       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 2.32/2.55  thf('111', plain,
% 2.32/2.55      (![X7 : $i]:
% 2.32/2.55         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X7)) @ X7) = (X7))
% 2.32/2.55          | ~ (v1_relat_1 @ X7))),
% 2.32/2.55      inference('cnf', [status(esa)], [t78_relat_1])).
% 2.32/2.55  thf('112', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 2.32/2.55      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.32/2.55  thf('113', plain,
% 2.32/2.55      (![X7 : $i]:
% 2.32/2.55         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X7)) @ X7) = (X7))
% 2.32/2.55          | ~ (v1_relat_1 @ X7))),
% 2.32/2.55      inference('demod', [status(thm)], ['111', '112'])).
% 2.32/2.55  thf('114', plain,
% 2.32/2.55      (![X0 : $i]:
% 2.32/2.55         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 2.32/2.55            = (k2_funct_1 @ X0))
% 2.32/2.55          | ~ (v1_relat_1 @ X0)
% 2.32/2.55          | ~ (v1_funct_1 @ X0)
% 2.32/2.55          | ~ (v2_funct_1 @ X0)
% 2.32/2.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 2.32/2.55      inference('sup+', [status(thm)], ['110', '113'])).
% 2.32/2.55  thf('115', plain,
% 2.32/2.55      (![X0 : $i]:
% 2.32/2.55         (~ (v1_relat_1 @ X0)
% 2.32/2.55          | ~ (v1_funct_1 @ X0)
% 2.32/2.55          | ~ (v2_funct_1 @ X0)
% 2.32/2.55          | ~ (v1_funct_1 @ X0)
% 2.32/2.55          | ~ (v1_relat_1 @ X0)
% 2.32/2.55          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 2.32/2.55              (k2_funct_1 @ X0)) = (k2_funct_1 @ X0)))),
% 2.32/2.55      inference('sup-', [status(thm)], ['109', '114'])).
% 2.32/2.55  thf('116', plain,
% 2.32/2.55      (![X0 : $i]:
% 2.32/2.55         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 2.32/2.55            = (k2_funct_1 @ X0))
% 2.32/2.55          | ~ (v2_funct_1 @ X0)
% 2.32/2.55          | ~ (v1_funct_1 @ X0)
% 2.32/2.55          | ~ (v1_relat_1 @ X0))),
% 2.32/2.55      inference('simplify', [status(thm)], ['115'])).
% 2.32/2.55  thf('117', plain,
% 2.32/2.55      ((((k5_relat_1 @ (k6_partfun1 @ sk_A) @ (k2_funct_1 @ sk_D))
% 2.32/2.55          = (k2_funct_1 @ sk_D))
% 2.32/2.55        | ~ (v1_relat_1 @ sk_D)
% 2.32/2.55        | ~ (v1_funct_1 @ sk_D)
% 2.32/2.55        | ~ (v2_funct_1 @ sk_D))),
% 2.32/2.55      inference('sup+', [status(thm)], ['108', '116'])).
% 2.32/2.55  thf('118', plain, ((v1_relat_1 @ sk_D)),
% 2.32/2.55      inference('demod', [status(thm)], ['91', '92'])).
% 2.32/2.55  thf('119', plain, ((v1_funct_1 @ sk_D)),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('120', plain,
% 2.32/2.55      ((((k5_relat_1 @ (k6_partfun1 @ sk_A) @ (k2_funct_1 @ sk_D))
% 2.32/2.55          = (k2_funct_1 @ sk_D))
% 2.32/2.55        | ~ (v2_funct_1 @ sk_D))),
% 2.32/2.55      inference('demod', [status(thm)], ['117', '118', '119'])).
% 2.32/2.55  thf('121', plain, ((v2_funct_1 @ sk_D)),
% 2.32/2.55      inference('sup-', [status(thm)], ['77', '78'])).
% 2.32/2.55  thf('122', plain,
% 2.32/2.55      (((k5_relat_1 @ (k6_partfun1 @ sk_A) @ (k2_funct_1 @ sk_D))
% 2.32/2.55         = (k2_funct_1 @ sk_D))),
% 2.32/2.55      inference('demod', [status(thm)], ['120', '121'])).
% 2.32/2.55  thf('123', plain,
% 2.32/2.55      ((((k2_funct_1 @ sk_D) = (sk_C)) | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D)))),
% 2.32/2.55      inference('demod', [status(thm)], ['107', '122'])).
% 2.32/2.55  thf('124', plain,
% 2.32/2.55      ((~ (v1_relat_1 @ sk_D)
% 2.32/2.55        | ~ (v1_funct_1 @ sk_D)
% 2.32/2.55        | ((k2_funct_1 @ sk_D) = (sk_C)))),
% 2.32/2.55      inference('sup-', [status(thm)], ['0', '123'])).
% 2.32/2.55  thf('125', plain, ((v1_relat_1 @ sk_D)),
% 2.32/2.55      inference('demod', [status(thm)], ['91', '92'])).
% 2.32/2.55  thf('126', plain, ((v1_funct_1 @ sk_D)),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('127', plain, (((k2_funct_1 @ sk_D) = (sk_C))),
% 2.32/2.55      inference('demod', [status(thm)], ['124', '125', '126'])).
% 2.32/2.55  thf(t65_funct_1, axiom,
% 2.32/2.55    (![A:$i]:
% 2.32/2.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.32/2.55       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 2.32/2.55  thf('128', plain,
% 2.32/2.55      (![X13 : $i]:
% 2.32/2.55         (~ (v2_funct_1 @ X13)
% 2.32/2.55          | ((k2_funct_1 @ (k2_funct_1 @ X13)) = (X13))
% 2.32/2.55          | ~ (v1_funct_1 @ X13)
% 2.32/2.55          | ~ (v1_relat_1 @ X13))),
% 2.32/2.55      inference('cnf', [status(esa)], [t65_funct_1])).
% 2.32/2.55  thf('129', plain,
% 2.32/2.55      ((((k2_funct_1 @ sk_C) = (sk_D))
% 2.32/2.55        | ~ (v1_relat_1 @ sk_D)
% 2.32/2.55        | ~ (v1_funct_1 @ sk_D)
% 2.32/2.55        | ~ (v2_funct_1 @ sk_D))),
% 2.32/2.55      inference('sup+', [status(thm)], ['127', '128'])).
% 2.32/2.55  thf('130', plain, ((v1_relat_1 @ sk_D)),
% 2.32/2.55      inference('demod', [status(thm)], ['91', '92'])).
% 2.32/2.55  thf('131', plain, ((v1_funct_1 @ sk_D)),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('132', plain, ((v2_funct_1 @ sk_D)),
% 2.32/2.55      inference('sup-', [status(thm)], ['77', '78'])).
% 2.32/2.55  thf('133', plain, (((k2_funct_1 @ sk_C) = (sk_D))),
% 2.32/2.55      inference('demod', [status(thm)], ['129', '130', '131', '132'])).
% 2.32/2.55  thf('134', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 2.32/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.55  thf('135', plain, ($false),
% 2.32/2.55      inference('simplify_reflect-', [status(thm)], ['133', '134'])).
% 2.32/2.55  
% 2.32/2.55  % SZS output end Refutation
% 2.32/2.55  
% 2.32/2.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

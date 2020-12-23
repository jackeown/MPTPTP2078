%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.i3fYPAJLiJ

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:05 EST 2020

% Result     : Theorem 1.75s
% Output     : Refutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :  273 (1221 expanded)
%              Number of leaves         :   50 ( 377 expanded)
%              Depth                    :   25
%              Number of atoms          : 2740 (27244 expanded)
%              Number of equality atoms :  192 (1861 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( X49 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X49 ) ) )
      | ( ( k5_relat_1 @ X50 @ ( k2_funct_1 @ X50 ) )
        = ( k6_partfun1 @ X51 ) )
      | ~ ( v2_funct_1 @ X50 )
      | ( ( k2_relset_1 @ X51 @ X49 @ X50 )
       != X49 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( X49 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X49 ) ) )
      | ( ( k5_relat_1 @ X50 @ ( k2_funct_1 @ X50 ) )
        = ( k6_relat_1 @ X51 ) )
      | ~ ( v2_funct_1 @ X50 )
      | ( ( k2_relset_1 @ X51 @ X49 @ X50 )
       != X49 ) ) ),
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

thf('6',plain,(
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

thf('7',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 )
        = ( k5_relat_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( r2_relset_1 @ X37 @ X37 @ ( k1_partfun1 @ X37 @ X38 @ X38 @ X37 @ X36 @ X39 ) @ ( k6_partfun1 @ X37 ) )
      | ( ( k2_relset_1 @ X38 @ X37 @ X39 )
        = X37 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X38 @ X37 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('16',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('17',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( r2_relset_1 @ X37 @ X37 @ ( k1_partfun1 @ X37 @ X38 @ X38 @ X37 @ X36 @ X39 ) @ ( k6_relat_1 @ X37 ) )
      | ( ( k2_relset_1 @ X38 @ X37 @ X39 )
        = X37 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X38 @ X37 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

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
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['13','21'])).

thf('23',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('25',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('27',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['22','27','28','29','30'])).

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
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','31','32','33'])).

thf('35',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('39',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

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
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X26 ) ) ) ) ),
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
    inference(demod,[status(thm)],['11','12'])).

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
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','51'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('53',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('54',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('55',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['52','55'])).

thf('57',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
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
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ( zip_tseitin_0 @ X44 @ X47 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X48 @ X45 @ X45 @ X46 @ X47 @ X44 ) )
      | ( zip_tseitin_1 @ X46 @ X45 )
      | ( ( k2_relset_1 @ X48 @ X45 @ X47 )
       != X45 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X45 ) ) )
      | ~ ( v1_funct_2 @ X47 @ X48 @ X45 )
      | ~ ( v1_funct_1 @ X47 ) ) ),
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
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
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
    ! [X12: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('66',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['64','65','66','67','68','69'])).

thf('71',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X42: $i,X43: $i] :
      ( ( X42 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('73',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X40: $i,X41: $i] :
      ( ( v2_funct_1 @ X41 )
      | ~ ( zip_tseitin_0 @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('77',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['37','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('80',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('81',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['79','80'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('82',plain,(
    ! [X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('83',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('85',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_funct_1 @ X9 )
        = ( k4_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('87',plain,(
    ! [X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('89',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('90',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_funct_1 @ X9 )
        = ( k4_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('91',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('92',plain,(
    ! [X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['90','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('96',plain,(
    ! [X7: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X7 ) ) @ X7 )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['89','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['88','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) @ ( k4_relat_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['85','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) @ ( k4_relat_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('104',plain,(
    ! [X8: $i] :
      ( ( ( k5_relat_1 @ X8 @ ( k6_relat_1 @ ( k2_relat_1 @ X8 ) ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('105',plain,(
    ! [X7: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X7 ) ) @ X7 )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('106',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['104','110'])).

thf('112',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['103','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['84','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_D ) ) )
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['83','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('120',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('121',plain,(
    ! [X8: $i] :
      ( ( ( k5_relat_1 @ X8 @ ( k6_relat_1 @ ( k2_relat_1 @ X8 ) ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('122',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_D ) ) )
      = ( k4_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_D ) ) )
      = ( k4_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['119','122'])).

thf('124',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['79','80'])).

thf('125',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_D ) ) )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['79','80'])).

thf('127',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( ( k4_relat_1 @ sk_D )
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['118','125','126','127'])).

thf('129',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['75','76'])).

thf('130',plain,
    ( ( k4_relat_1 @ sk_D )
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( k5_relat_1 @ sk_D @ ( k4_relat_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['78','130'])).

thf('132',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_funct_1 @ X9 )
        = ( k4_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf(t58_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('133',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X13 @ ( k2_funct_1 @ X13 ) ) )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ sk_B ) )
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['131','135'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('137',plain,(
    ! [X6: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('138',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['79','80'])).

thf('139',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['75','76'])).

thf('141',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['136','137','138','139','140'])).

thf('142',plain,(
    ! [X7: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X7 ) ) @ X7 )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('143',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_D )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['141','142'])).

thf('144',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['52','55'])).

thf('145',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( X49 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X49 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X50 ) @ X50 )
        = ( k6_partfun1 @ X49 ) )
      | ~ ( v2_funct_1 @ X50 )
      | ( ( k2_relset_1 @ X51 @ X49 @ X50 )
       != X49 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('147',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('148',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( X49 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X49 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X50 ) @ X50 )
        = ( k6_relat_1 @ X49 ) )
      | ~ ( v2_funct_1 @ X50 )
      | ( ( k2_relset_1 @ X51 @ X49 @ X50 )
       != X49 ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['145','148'])).

thf('150',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('154',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('156',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('158',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('160',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('161',plain,(
    ! [X8: $i] :
      ( ( ( k5_relat_1 @ X8 @ ( k6_relat_1 @ ( k2_relat_1 @ X8 ) ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('162',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['160','161'])).

thf('163',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
      = ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['159','162'])).

thf('164',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['152','153'])).

thf('165',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['152','153'])).

thf('167',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( k4_relat_1 @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['158','165','166','167','168'])).

thf('170',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['149','150','151','169','170','171'])).

thf('173',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['175','176'])).

thf('178',plain,
    ( ( k4_relat_1 @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['158','165','166','167','168'])).

thf('179',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('180',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['178','179'])).

thf('181',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['152','153'])).

thf('182',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['180','181','182'])).

thf('184',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['152','153'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['177','183','184'])).

thf('186',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['144','185'])).

thf('187',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('188',plain,
    ( ( k4_relat_1 @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['158','165','166','167','168'])).

thf('189',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X13 @ ( k2_funct_1 @ X13 ) ) )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('190',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ sk_C ) ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['188','189'])).

thf('191',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['152','153'])).

thf('192',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ sk_C ) ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['190','191','192','193'])).

thf('195',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( X49 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X49 ) ) )
      | ( ( k5_relat_1 @ X50 @ ( k2_funct_1 @ X50 ) )
        = ( k6_relat_1 @ X51 ) )
      | ~ ( v2_funct_1 @ X50 )
      | ( ( k2_relset_1 @ X51 @ X49 @ X50 )
       != X49 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('197',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( k4_relat_1 @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['158','165','166','167','168'])).

thf('201',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['197','198','199','200','201','202'])).

thf('204',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['203'])).

thf('205',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['204','205'])).

thf('207',plain,(
    ! [X6: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('208',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['194','206','207'])).

thf('209',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['187','208'])).

thf('210',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['79','80'])).

thf('211',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_D )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['186','209','210'])).

thf('212',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['79','80'])).

thf('213',plain,
    ( ( k4_relat_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['143','211','212'])).

thf('214',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_funct_1 @ X9 )
        = ( k4_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('215',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,
    ( ( sk_D
     != ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['152','153'])).

thf('218',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    sk_D
 != ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['216','217','218','219'])).

thf('221',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['213','220'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.i3fYPAJLiJ
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:11:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.75/1.92  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.75/1.92  % Solved by: fo/fo7.sh
% 1.75/1.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.75/1.92  % done 1508 iterations in 1.467s
% 1.75/1.92  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.75/1.92  % SZS output start Refutation
% 1.75/1.92  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.75/1.92  thf(sk_A_type, type, sk_A: $i).
% 1.75/1.92  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.75/1.92  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.75/1.92  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.75/1.92  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.75/1.92  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.75/1.92  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.75/1.92  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.75/1.92  thf(sk_C_type, type, sk_C: $i).
% 1.75/1.92  thf(sk_B_type, type, sk_B: $i).
% 1.75/1.92  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.75/1.92  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.75/1.92  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.75/1.92  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 1.75/1.92  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.75/1.92  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.75/1.92  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.75/1.92  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.75/1.92  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.75/1.92  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.75/1.92  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.75/1.92  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.75/1.92  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 1.75/1.92  thf(sk_D_type, type, sk_D: $i).
% 1.75/1.92  thf(t36_funct_2, conjecture,
% 1.75/1.92    (![A:$i,B:$i,C:$i]:
% 1.75/1.92     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.75/1.92         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.75/1.92       ( ![D:$i]:
% 1.75/1.92         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.75/1.92             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.75/1.92           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.75/1.92               ( r2_relset_1 @
% 1.75/1.92                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.75/1.92                 ( k6_partfun1 @ A ) ) & 
% 1.75/1.92               ( v2_funct_1 @ C ) ) =>
% 1.75/1.92             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.75/1.92               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.75/1.92  thf(zf_stmt_0, negated_conjecture,
% 1.75/1.92    (~( ![A:$i,B:$i,C:$i]:
% 1.75/1.92        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.75/1.92            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.75/1.92          ( ![D:$i]:
% 1.75/1.92            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.75/1.92                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.75/1.92              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.75/1.92                  ( r2_relset_1 @
% 1.75/1.92                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.75/1.92                    ( k6_partfun1 @ A ) ) & 
% 1.75/1.92                  ( v2_funct_1 @ C ) ) =>
% 1.75/1.92                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.75/1.92                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.75/1.92    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.75/1.92  thf('0', plain,
% 1.75/1.92      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf(t35_funct_2, axiom,
% 1.75/1.92    (![A:$i,B:$i,C:$i]:
% 1.75/1.92     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.75/1.92         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.75/1.92       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.75/1.92         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.75/1.92           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 1.75/1.92             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 1.75/1.92  thf('1', plain,
% 1.75/1.92      (![X49 : $i, X50 : $i, X51 : $i]:
% 1.75/1.92         (((X49) = (k1_xboole_0))
% 1.75/1.92          | ~ (v1_funct_1 @ X50)
% 1.75/1.92          | ~ (v1_funct_2 @ X50 @ X51 @ X49)
% 1.75/1.92          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X49)))
% 1.75/1.92          | ((k5_relat_1 @ X50 @ (k2_funct_1 @ X50)) = (k6_partfun1 @ X51))
% 1.75/1.92          | ~ (v2_funct_1 @ X50)
% 1.75/1.92          | ((k2_relset_1 @ X51 @ X49 @ X50) != (X49)))),
% 1.75/1.92      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.75/1.92  thf(redefinition_k6_partfun1, axiom,
% 1.75/1.92    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.75/1.92  thf('2', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 1.75/1.92      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.75/1.92  thf('3', plain,
% 1.75/1.92      (![X49 : $i, X50 : $i, X51 : $i]:
% 1.75/1.92         (((X49) = (k1_xboole_0))
% 1.75/1.92          | ~ (v1_funct_1 @ X50)
% 1.75/1.92          | ~ (v1_funct_2 @ X50 @ X51 @ X49)
% 1.75/1.92          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X49)))
% 1.75/1.92          | ((k5_relat_1 @ X50 @ (k2_funct_1 @ X50)) = (k6_relat_1 @ X51))
% 1.75/1.92          | ~ (v2_funct_1 @ X50)
% 1.75/1.92          | ((k2_relset_1 @ X51 @ X49 @ X50) != (X49)))),
% 1.75/1.92      inference('demod', [status(thm)], ['1', '2'])).
% 1.75/1.92  thf('4', plain,
% 1.75/1.92      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 1.75/1.92        | ~ (v2_funct_1 @ sk_D)
% 1.75/1.92        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 1.75/1.92        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.75/1.92        | ~ (v1_funct_1 @ sk_D)
% 1.75/1.92        | ((sk_A) = (k1_xboole_0)))),
% 1.75/1.92      inference('sup-', [status(thm)], ['0', '3'])).
% 1.75/1.92  thf('5', plain,
% 1.75/1.92      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('6', plain,
% 1.75/1.92      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf(redefinition_k1_partfun1, axiom,
% 1.75/1.92    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.75/1.92     ( ( ( v1_funct_1 @ E ) & 
% 1.75/1.92         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.75/1.92         ( v1_funct_1 @ F ) & 
% 1.75/1.92         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.75/1.92       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.75/1.92  thf('7', plain,
% 1.75/1.92      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.75/1.92         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.75/1.92          | ~ (v1_funct_1 @ X29)
% 1.75/1.92          | ~ (v1_funct_1 @ X32)
% 1.75/1.92          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 1.75/1.92          | ((k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32)
% 1.75/1.92              = (k5_relat_1 @ X29 @ X32)))),
% 1.75/1.92      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.75/1.92  thf('8', plain,
% 1.75/1.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.92         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.75/1.92            = (k5_relat_1 @ sk_C @ X0))
% 1.75/1.92          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.75/1.92          | ~ (v1_funct_1 @ X0)
% 1.75/1.92          | ~ (v1_funct_1 @ sk_C))),
% 1.75/1.92      inference('sup-', [status(thm)], ['6', '7'])).
% 1.75/1.92  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('10', plain,
% 1.75/1.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.92         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.75/1.92            = (k5_relat_1 @ sk_C @ X0))
% 1.75/1.92          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.75/1.92          | ~ (v1_funct_1 @ X0))),
% 1.75/1.92      inference('demod', [status(thm)], ['8', '9'])).
% 1.75/1.92  thf('11', plain,
% 1.75/1.92      ((~ (v1_funct_1 @ sk_D)
% 1.75/1.92        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.75/1.92            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.75/1.92      inference('sup-', [status(thm)], ['5', '10'])).
% 1.75/1.92  thf('12', plain, ((v1_funct_1 @ sk_D)),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('13', plain,
% 1.75/1.92      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.75/1.92         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.75/1.92      inference('demod', [status(thm)], ['11', '12'])).
% 1.75/1.92  thf('14', plain,
% 1.75/1.92      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf(t24_funct_2, axiom,
% 1.75/1.92    (![A:$i,B:$i,C:$i]:
% 1.75/1.92     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.75/1.92         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.75/1.92       ( ![D:$i]:
% 1.75/1.92         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.75/1.92             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.75/1.92           ( ( r2_relset_1 @
% 1.75/1.92               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 1.75/1.92               ( k6_partfun1 @ B ) ) =>
% 1.75/1.92             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 1.75/1.92  thf('15', plain,
% 1.75/1.92      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 1.75/1.92         (~ (v1_funct_1 @ X36)
% 1.75/1.92          | ~ (v1_funct_2 @ X36 @ X37 @ X38)
% 1.75/1.92          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 1.75/1.92          | ~ (r2_relset_1 @ X37 @ X37 @ 
% 1.75/1.92               (k1_partfun1 @ X37 @ X38 @ X38 @ X37 @ X36 @ X39) @ 
% 1.75/1.92               (k6_partfun1 @ X37))
% 1.75/1.92          | ((k2_relset_1 @ X38 @ X37 @ X39) = (X37))
% 1.75/1.92          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 1.75/1.92          | ~ (v1_funct_2 @ X39 @ X38 @ X37)
% 1.75/1.92          | ~ (v1_funct_1 @ X39))),
% 1.75/1.92      inference('cnf', [status(esa)], [t24_funct_2])).
% 1.75/1.92  thf('16', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 1.75/1.92      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.75/1.92  thf('17', plain,
% 1.75/1.92      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 1.75/1.92         (~ (v1_funct_1 @ X36)
% 1.75/1.92          | ~ (v1_funct_2 @ X36 @ X37 @ X38)
% 1.75/1.92          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 1.75/1.92          | ~ (r2_relset_1 @ X37 @ X37 @ 
% 1.75/1.92               (k1_partfun1 @ X37 @ X38 @ X38 @ X37 @ X36 @ X39) @ 
% 1.75/1.92               (k6_relat_1 @ X37))
% 1.75/1.92          | ((k2_relset_1 @ X38 @ X37 @ X39) = (X37))
% 1.75/1.92          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 1.75/1.92          | ~ (v1_funct_2 @ X39 @ X38 @ X37)
% 1.75/1.92          | ~ (v1_funct_1 @ X39))),
% 1.75/1.92      inference('demod', [status(thm)], ['15', '16'])).
% 1.75/1.92  thf('18', plain,
% 1.75/1.92      (![X0 : $i]:
% 1.75/1.92         (~ (v1_funct_1 @ X0)
% 1.75/1.92          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.75/1.92          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.75/1.92          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.75/1.92          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.75/1.92               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.75/1.92               (k6_relat_1 @ sk_A))
% 1.75/1.92          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.75/1.92          | ~ (v1_funct_1 @ sk_C))),
% 1.75/1.92      inference('sup-', [status(thm)], ['14', '17'])).
% 1.75/1.92  thf('19', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('21', plain,
% 1.75/1.92      (![X0 : $i]:
% 1.75/1.92         (~ (v1_funct_1 @ X0)
% 1.75/1.92          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.75/1.92          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.75/1.92          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.75/1.92          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.75/1.92               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.75/1.92               (k6_relat_1 @ sk_A)))),
% 1.75/1.92      inference('demod', [status(thm)], ['18', '19', '20'])).
% 1.75/1.92  thf('22', plain,
% 1.75/1.92      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.75/1.92           (k6_relat_1 @ sk_A))
% 1.75/1.92        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 1.75/1.92        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.75/1.92        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.75/1.92        | ~ (v1_funct_1 @ sk_D))),
% 1.75/1.92      inference('sup-', [status(thm)], ['13', '21'])).
% 1.75/1.92  thf('23', plain,
% 1.75/1.92      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.75/1.92        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.75/1.92        (k6_partfun1 @ sk_A))),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('24', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 1.75/1.92      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.75/1.92  thf('25', plain,
% 1.75/1.92      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.75/1.92        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.75/1.92        (k6_relat_1 @ sk_A))),
% 1.75/1.92      inference('demod', [status(thm)], ['23', '24'])).
% 1.75/1.92  thf('26', plain,
% 1.75/1.92      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.75/1.92         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.75/1.92      inference('demod', [status(thm)], ['11', '12'])).
% 1.75/1.92  thf('27', plain,
% 1.75/1.92      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.75/1.92        (k6_relat_1 @ sk_A))),
% 1.75/1.92      inference('demod', [status(thm)], ['25', '26'])).
% 1.75/1.92  thf('28', plain,
% 1.75/1.92      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('29', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('30', plain, ((v1_funct_1 @ sk_D)),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('31', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))),
% 1.75/1.92      inference('demod', [status(thm)], ['22', '27', '28', '29', '30'])).
% 1.75/1.92  thf('32', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('33', plain, ((v1_funct_1 @ sk_D)),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('34', plain,
% 1.75/1.92      ((((sk_A) != (sk_A))
% 1.75/1.92        | ~ (v2_funct_1 @ sk_D)
% 1.75/1.92        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 1.75/1.92        | ((sk_A) = (k1_xboole_0)))),
% 1.75/1.92      inference('demod', [status(thm)], ['4', '31', '32', '33'])).
% 1.75/1.92  thf('35', plain,
% 1.75/1.92      ((((sk_A) = (k1_xboole_0))
% 1.75/1.92        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 1.75/1.92        | ~ (v2_funct_1 @ sk_D))),
% 1.75/1.92      inference('simplify', [status(thm)], ['34'])).
% 1.75/1.92  thf('36', plain, (((sk_A) != (k1_xboole_0))),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('37', plain,
% 1.75/1.92      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 1.75/1.92        | ~ (v2_funct_1 @ sk_D))),
% 1.75/1.92      inference('simplify_reflect-', [status(thm)], ['35', '36'])).
% 1.75/1.92  thf('38', plain,
% 1.75/1.92      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.75/1.92         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.75/1.92      inference('demod', [status(thm)], ['11', '12'])).
% 1.75/1.92  thf('39', plain,
% 1.75/1.92      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.75/1.92        (k6_relat_1 @ sk_A))),
% 1.75/1.92      inference('demod', [status(thm)], ['25', '26'])).
% 1.75/1.92  thf('40', plain,
% 1.75/1.92      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('41', plain,
% 1.75/1.92      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf(dt_k1_partfun1, axiom,
% 1.75/1.92    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.75/1.92     ( ( ( v1_funct_1 @ E ) & 
% 1.75/1.92         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.75/1.92         ( v1_funct_1 @ F ) & 
% 1.75/1.92         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.75/1.92       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.75/1.92         ( m1_subset_1 @
% 1.75/1.92           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.75/1.92           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.75/1.92  thf('42', plain,
% 1.75/1.92      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.75/1.92         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 1.75/1.92          | ~ (v1_funct_1 @ X21)
% 1.75/1.92          | ~ (v1_funct_1 @ X24)
% 1.75/1.92          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 1.75/1.92          | (m1_subset_1 @ (k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24) @ 
% 1.75/1.92             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X26))))),
% 1.75/1.92      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.75/1.92  thf('43', plain,
% 1.75/1.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.92         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.75/1.92           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.75/1.92          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.75/1.92          | ~ (v1_funct_1 @ X1)
% 1.75/1.92          | ~ (v1_funct_1 @ sk_C))),
% 1.75/1.92      inference('sup-', [status(thm)], ['41', '42'])).
% 1.75/1.92  thf('44', plain, ((v1_funct_1 @ sk_C)),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('45', plain,
% 1.75/1.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.92         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.75/1.92           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.75/1.92          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.75/1.92          | ~ (v1_funct_1 @ X1))),
% 1.75/1.92      inference('demod', [status(thm)], ['43', '44'])).
% 1.75/1.92  thf('46', plain,
% 1.75/1.92      ((~ (v1_funct_1 @ sk_D)
% 1.75/1.92        | (m1_subset_1 @ 
% 1.75/1.92           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.75/1.92           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.75/1.92      inference('sup-', [status(thm)], ['40', '45'])).
% 1.75/1.92  thf('47', plain, ((v1_funct_1 @ sk_D)),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('48', plain,
% 1.75/1.92      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.75/1.92         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.75/1.92      inference('demod', [status(thm)], ['11', '12'])).
% 1.75/1.92  thf('49', plain,
% 1.75/1.92      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.75/1.92        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.75/1.92      inference('demod', [status(thm)], ['46', '47', '48'])).
% 1.75/1.92  thf(redefinition_r2_relset_1, axiom,
% 1.75/1.92    (![A:$i,B:$i,C:$i,D:$i]:
% 1.75/1.92     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.75/1.92         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.75/1.92       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.75/1.92  thf('50', plain,
% 1.75/1.92      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.75/1.92         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 1.75/1.92          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 1.75/1.92          | ((X17) = (X20))
% 1.75/1.92          | ~ (r2_relset_1 @ X18 @ X19 @ X17 @ X20))),
% 1.75/1.92      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.75/1.92  thf('51', plain,
% 1.75/1.92      (![X0 : $i]:
% 1.75/1.92         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 1.75/1.92          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 1.75/1.92          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.75/1.92      inference('sup-', [status(thm)], ['49', '50'])).
% 1.75/1.92  thf('52', plain,
% 1.75/1.92      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 1.75/1.92           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.75/1.92        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A)))),
% 1.75/1.92      inference('sup-', [status(thm)], ['39', '51'])).
% 1.75/1.92  thf(dt_k6_partfun1, axiom,
% 1.75/1.92    (![A:$i]:
% 1.75/1.92     ( ( m1_subset_1 @
% 1.75/1.92         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 1.75/1.92       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 1.75/1.92  thf('53', plain,
% 1.75/1.92      (![X28 : $i]:
% 1.75/1.92         (m1_subset_1 @ (k6_partfun1 @ X28) @ 
% 1.75/1.92          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 1.75/1.92      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.75/1.92  thf('54', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 1.75/1.92      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.75/1.92  thf('55', plain,
% 1.75/1.92      (![X28 : $i]:
% 1.75/1.92         (m1_subset_1 @ (k6_relat_1 @ X28) @ 
% 1.75/1.92          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 1.75/1.92      inference('demod', [status(thm)], ['53', '54'])).
% 1.75/1.92  thf('56', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 1.75/1.92      inference('demod', [status(thm)], ['52', '55'])).
% 1.75/1.92  thf('57', plain,
% 1.75/1.92      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.75/1.92         = (k6_relat_1 @ sk_A))),
% 1.75/1.92      inference('demod', [status(thm)], ['38', '56'])).
% 1.75/1.92  thf('58', plain,
% 1.75/1.92      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf(t30_funct_2, axiom,
% 1.75/1.92    (![A:$i,B:$i,C:$i,D:$i]:
% 1.75/1.92     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.75/1.92         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 1.75/1.92       ( ![E:$i]:
% 1.75/1.92         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 1.75/1.92             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 1.75/1.92           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 1.75/1.92               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 1.75/1.92             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 1.75/1.92               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 1.75/1.92  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 1.75/1.92  thf(zf_stmt_2, axiom,
% 1.75/1.92    (![C:$i,B:$i]:
% 1.75/1.92     ( ( zip_tseitin_1 @ C @ B ) =>
% 1.75/1.92       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 1.75/1.92  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.75/1.92  thf(zf_stmt_4, axiom,
% 1.75/1.92    (![E:$i,D:$i]:
% 1.75/1.92     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 1.75/1.92  thf(zf_stmt_5, axiom,
% 1.75/1.92    (![A:$i,B:$i,C:$i,D:$i]:
% 1.75/1.92     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.75/1.92         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.75/1.92       ( ![E:$i]:
% 1.75/1.92         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.75/1.92             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.75/1.92           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 1.75/1.92               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 1.75/1.92             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 1.75/1.92  thf('59', plain,
% 1.75/1.92      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 1.75/1.92         (~ (v1_funct_1 @ X44)
% 1.75/1.92          | ~ (v1_funct_2 @ X44 @ X45 @ X46)
% 1.75/1.92          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 1.75/1.92          | (zip_tseitin_0 @ X44 @ X47)
% 1.75/1.92          | ~ (v2_funct_1 @ (k1_partfun1 @ X48 @ X45 @ X45 @ X46 @ X47 @ X44))
% 1.75/1.92          | (zip_tseitin_1 @ X46 @ X45)
% 1.75/1.92          | ((k2_relset_1 @ X48 @ X45 @ X47) != (X45))
% 1.75/1.92          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X45)))
% 1.75/1.92          | ~ (v1_funct_2 @ X47 @ X48 @ X45)
% 1.75/1.92          | ~ (v1_funct_1 @ X47))),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.75/1.92  thf('60', plain,
% 1.75/1.92      (![X0 : $i, X1 : $i]:
% 1.75/1.92         (~ (v1_funct_1 @ X0)
% 1.75/1.92          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.75/1.92          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.75/1.92          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.75/1.92          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.75/1.92          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.75/1.92          | (zip_tseitin_0 @ sk_D @ X0)
% 1.75/1.92          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.75/1.92          | ~ (v1_funct_1 @ sk_D))),
% 1.75/1.92      inference('sup-', [status(thm)], ['58', '59'])).
% 1.75/1.92  thf('61', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('62', plain, ((v1_funct_1 @ sk_D)),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('63', plain,
% 1.75/1.92      (![X0 : $i, X1 : $i]:
% 1.75/1.92         (~ (v1_funct_1 @ X0)
% 1.75/1.92          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.75/1.92          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.75/1.92          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.75/1.92          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.75/1.92          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.75/1.92          | (zip_tseitin_0 @ sk_D @ X0))),
% 1.75/1.92      inference('demod', [status(thm)], ['60', '61', '62'])).
% 1.75/1.92  thf('64', plain,
% 1.75/1.92      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 1.75/1.92        | (zip_tseitin_0 @ sk_D @ sk_C)
% 1.75/1.92        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.75/1.92        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.75/1.92        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.75/1.92        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.75/1.92        | ~ (v1_funct_1 @ sk_C))),
% 1.75/1.92      inference('sup-', [status(thm)], ['57', '63'])).
% 1.75/1.92  thf(fc4_funct_1, axiom,
% 1.75/1.92    (![A:$i]:
% 1.75/1.92     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.75/1.92       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.75/1.92  thf('65', plain, (![X12 : $i]: (v2_funct_1 @ (k6_relat_1 @ X12))),
% 1.75/1.92      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.75/1.92  thf('66', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('67', plain,
% 1.75/1.92      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('68', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('69', plain, ((v1_funct_1 @ sk_C)),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('70', plain,
% 1.75/1.92      (((zip_tseitin_0 @ sk_D @ sk_C)
% 1.75/1.92        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.75/1.92        | ((sk_B) != (sk_B)))),
% 1.75/1.92      inference('demod', [status(thm)], ['64', '65', '66', '67', '68', '69'])).
% 1.75/1.92  thf('71', plain,
% 1.75/1.92      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 1.75/1.92      inference('simplify', [status(thm)], ['70'])).
% 1.75/1.92  thf('72', plain,
% 1.75/1.92      (![X42 : $i, X43 : $i]:
% 1.75/1.92         (((X42) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X42 @ X43))),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.75/1.92  thf('73', plain,
% 1.75/1.92      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 1.75/1.92      inference('sup-', [status(thm)], ['71', '72'])).
% 1.75/1.92  thf('74', plain, (((sk_A) != (k1_xboole_0))),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('75', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 1.75/1.92      inference('simplify_reflect-', [status(thm)], ['73', '74'])).
% 1.75/1.92  thf('76', plain,
% 1.75/1.92      (![X40 : $i, X41 : $i]:
% 1.75/1.92         ((v2_funct_1 @ X41) | ~ (zip_tseitin_0 @ X41 @ X40))),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.75/1.92  thf('77', plain, ((v2_funct_1 @ sk_D)),
% 1.75/1.92      inference('sup-', [status(thm)], ['75', '76'])).
% 1.75/1.92  thf('78', plain,
% 1.75/1.92      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 1.75/1.92      inference('demod', [status(thm)], ['37', '77'])).
% 1.75/1.92  thf('79', plain,
% 1.75/1.92      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf(cc1_relset_1, axiom,
% 1.75/1.92    (![A:$i,B:$i,C:$i]:
% 1.75/1.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.75/1.92       ( v1_relat_1 @ C ) ))).
% 1.75/1.92  thf('80', plain,
% 1.75/1.92      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.75/1.92         ((v1_relat_1 @ X14)
% 1.75/1.92          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.75/1.92      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.75/1.92  thf('81', plain, ((v1_relat_1 @ sk_D)),
% 1.75/1.92      inference('sup-', [status(thm)], ['79', '80'])).
% 1.75/1.92  thf(t37_relat_1, axiom,
% 1.75/1.92    (![A:$i]:
% 1.75/1.92     ( ( v1_relat_1 @ A ) =>
% 1.75/1.92       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 1.75/1.92         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 1.75/1.92  thf('82', plain,
% 1.75/1.92      (![X1 : $i]:
% 1.75/1.92         (((k1_relat_1 @ X1) = (k2_relat_1 @ (k4_relat_1 @ X1)))
% 1.75/1.92          | ~ (v1_relat_1 @ X1))),
% 1.75/1.92      inference('cnf', [status(esa)], [t37_relat_1])).
% 1.75/1.92  thf('83', plain,
% 1.75/1.92      (((k1_relat_1 @ sk_D) = (k2_relat_1 @ (k4_relat_1 @ sk_D)))),
% 1.75/1.92      inference('sup-', [status(thm)], ['81', '82'])).
% 1.75/1.92  thf(dt_k4_relat_1, axiom,
% 1.75/1.92    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 1.75/1.92  thf('84', plain,
% 1.75/1.92      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 1.75/1.92      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 1.75/1.92  thf(d9_funct_1, axiom,
% 1.75/1.92    (![A:$i]:
% 1.75/1.92     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.75/1.92       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 1.75/1.92  thf('85', plain,
% 1.75/1.92      (![X9 : $i]:
% 1.75/1.92         (~ (v2_funct_1 @ X9)
% 1.75/1.92          | ((k2_funct_1 @ X9) = (k4_relat_1 @ X9))
% 1.75/1.92          | ~ (v1_funct_1 @ X9)
% 1.75/1.92          | ~ (v1_relat_1 @ X9))),
% 1.75/1.92      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.75/1.92  thf('86', plain,
% 1.75/1.92      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 1.75/1.92      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 1.75/1.92  thf('87', plain,
% 1.75/1.92      (![X1 : $i]:
% 1.75/1.92         (((k1_relat_1 @ X1) = (k2_relat_1 @ (k4_relat_1 @ X1)))
% 1.75/1.92          | ~ (v1_relat_1 @ X1))),
% 1.75/1.92      inference('cnf', [status(esa)], [t37_relat_1])).
% 1.75/1.92  thf('88', plain,
% 1.75/1.92      (![X0 : $i]:
% 1.75/1.92         (~ (v1_relat_1 @ X0)
% 1.75/1.92          | ((k1_relat_1 @ (k4_relat_1 @ X0))
% 1.75/1.92              = (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))))),
% 1.75/1.92      inference('sup-', [status(thm)], ['86', '87'])).
% 1.75/1.92  thf(dt_k2_funct_1, axiom,
% 1.75/1.92    (![A:$i]:
% 1.75/1.92     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.75/1.92       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.75/1.92         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.75/1.92  thf('89', plain,
% 1.75/1.92      (![X10 : $i]:
% 1.75/1.92         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 1.75/1.92          | ~ (v1_funct_1 @ X10)
% 1.75/1.92          | ~ (v1_relat_1 @ X10))),
% 1.75/1.92      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.75/1.92  thf('90', plain,
% 1.75/1.92      (![X9 : $i]:
% 1.75/1.92         (~ (v2_funct_1 @ X9)
% 1.75/1.92          | ((k2_funct_1 @ X9) = (k4_relat_1 @ X9))
% 1.75/1.92          | ~ (v1_funct_1 @ X9)
% 1.75/1.92          | ~ (v1_relat_1 @ X9))),
% 1.75/1.92      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.75/1.92  thf('91', plain,
% 1.75/1.92      (![X10 : $i]:
% 1.75/1.92         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 1.75/1.92          | ~ (v1_funct_1 @ X10)
% 1.75/1.92          | ~ (v1_relat_1 @ X10))),
% 1.75/1.92      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.75/1.92  thf('92', plain,
% 1.75/1.92      (![X1 : $i]:
% 1.75/1.92         (((k1_relat_1 @ X1) = (k2_relat_1 @ (k4_relat_1 @ X1)))
% 1.75/1.92          | ~ (v1_relat_1 @ X1))),
% 1.75/1.92      inference('cnf', [status(esa)], [t37_relat_1])).
% 1.75/1.92  thf('93', plain,
% 1.75/1.92      (![X0 : $i]:
% 1.75/1.92         (~ (v1_relat_1 @ X0)
% 1.75/1.92          | ~ (v1_funct_1 @ X0)
% 1.75/1.92          | ((k1_relat_1 @ (k2_funct_1 @ X0))
% 1.75/1.92              = (k2_relat_1 @ (k4_relat_1 @ (k2_funct_1 @ X0)))))),
% 1.75/1.92      inference('sup-', [status(thm)], ['91', '92'])).
% 1.75/1.92  thf('94', plain,
% 1.75/1.92      (![X0 : $i]:
% 1.75/1.92         (((k1_relat_1 @ (k2_funct_1 @ X0))
% 1.75/1.92            = (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 1.75/1.92          | ~ (v1_relat_1 @ X0)
% 1.75/1.92          | ~ (v1_funct_1 @ X0)
% 1.75/1.92          | ~ (v2_funct_1 @ X0)
% 1.75/1.92          | ~ (v1_funct_1 @ X0)
% 1.75/1.92          | ~ (v1_relat_1 @ X0))),
% 1.75/1.92      inference('sup+', [status(thm)], ['90', '93'])).
% 1.75/1.92  thf('95', plain,
% 1.75/1.92      (![X0 : $i]:
% 1.75/1.92         (~ (v2_funct_1 @ X0)
% 1.75/1.92          | ~ (v1_funct_1 @ X0)
% 1.75/1.92          | ~ (v1_relat_1 @ X0)
% 1.75/1.92          | ((k1_relat_1 @ (k2_funct_1 @ X0))
% 1.75/1.92              = (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))))),
% 1.75/1.92      inference('simplify', [status(thm)], ['94'])).
% 1.75/1.92  thf(t78_relat_1, axiom,
% 1.75/1.92    (![A:$i]:
% 1.75/1.92     ( ( v1_relat_1 @ A ) =>
% 1.75/1.92       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 1.75/1.92  thf('96', plain,
% 1.75/1.92      (![X7 : $i]:
% 1.75/1.92         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X7)) @ X7) = (X7))
% 1.75/1.92          | ~ (v1_relat_1 @ X7))),
% 1.75/1.92      inference('cnf', [status(esa)], [t78_relat_1])).
% 1.75/1.92  thf('97', plain,
% 1.75/1.92      (![X0 : $i]:
% 1.75/1.92         (((k5_relat_1 @ 
% 1.75/1.92            (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))) @ 
% 1.75/1.92            (k2_funct_1 @ X0)) = (k2_funct_1 @ X0))
% 1.75/1.92          | ~ (v1_relat_1 @ X0)
% 1.75/1.92          | ~ (v1_funct_1 @ X0)
% 1.75/1.92          | ~ (v2_funct_1 @ X0)
% 1.75/1.92          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.75/1.92      inference('sup+', [status(thm)], ['95', '96'])).
% 1.75/1.92  thf('98', plain,
% 1.75/1.92      (![X0 : $i]:
% 1.75/1.92         (~ (v1_relat_1 @ X0)
% 1.75/1.92          | ~ (v1_funct_1 @ X0)
% 1.75/1.92          | ~ (v2_funct_1 @ X0)
% 1.75/1.92          | ~ (v1_funct_1 @ X0)
% 1.75/1.92          | ~ (v1_relat_1 @ X0)
% 1.75/1.92          | ((k5_relat_1 @ 
% 1.75/1.92              (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))) @ 
% 1.75/1.92              (k2_funct_1 @ X0)) = (k2_funct_1 @ X0)))),
% 1.75/1.92      inference('sup-', [status(thm)], ['89', '97'])).
% 1.75/1.92  thf('99', plain,
% 1.75/1.92      (![X0 : $i]:
% 1.75/1.92         (((k5_relat_1 @ 
% 1.75/1.92            (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))) @ 
% 1.75/1.92            (k2_funct_1 @ X0)) = (k2_funct_1 @ X0))
% 1.75/1.92          | ~ (v2_funct_1 @ X0)
% 1.75/1.92          | ~ (v1_funct_1 @ X0)
% 1.75/1.92          | ~ (v1_relat_1 @ X0))),
% 1.75/1.92      inference('simplify', [status(thm)], ['98'])).
% 1.75/1.92  thf('100', plain,
% 1.75/1.92      (![X0 : $i]:
% 1.75/1.92         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ (k4_relat_1 @ X0))) @ 
% 1.75/1.92            (k2_funct_1 @ X0)) = (k2_funct_1 @ X0))
% 1.75/1.92          | ~ (v1_relat_1 @ X0)
% 1.75/1.92          | ~ (v1_relat_1 @ X0)
% 1.75/1.92          | ~ (v1_funct_1 @ X0)
% 1.75/1.92          | ~ (v2_funct_1 @ X0))),
% 1.75/1.92      inference('sup+', [status(thm)], ['88', '99'])).
% 1.75/1.92  thf('101', plain,
% 1.75/1.92      (![X0 : $i]:
% 1.75/1.92         (~ (v2_funct_1 @ X0)
% 1.75/1.92          | ~ (v1_funct_1 @ X0)
% 1.75/1.92          | ~ (v1_relat_1 @ X0)
% 1.75/1.92          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ (k4_relat_1 @ X0))) @ 
% 1.75/1.92              (k2_funct_1 @ X0)) = (k2_funct_1 @ X0)))),
% 1.75/1.92      inference('simplify', [status(thm)], ['100'])).
% 1.75/1.92  thf('102', plain,
% 1.75/1.92      (![X0 : $i]:
% 1.75/1.92         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ (k4_relat_1 @ X0))) @ 
% 1.75/1.92            (k4_relat_1 @ X0)) = (k2_funct_1 @ X0))
% 1.75/1.92          | ~ (v1_relat_1 @ X0)
% 1.75/1.92          | ~ (v1_funct_1 @ X0)
% 1.75/1.92          | ~ (v2_funct_1 @ X0)
% 1.75/1.92          | ~ (v1_relat_1 @ X0)
% 1.75/1.92          | ~ (v1_funct_1 @ X0)
% 1.75/1.92          | ~ (v2_funct_1 @ X0))),
% 1.75/1.92      inference('sup+', [status(thm)], ['85', '101'])).
% 1.75/1.92  thf('103', plain,
% 1.75/1.92      (![X0 : $i]:
% 1.75/1.92         (~ (v2_funct_1 @ X0)
% 1.75/1.92          | ~ (v1_funct_1 @ X0)
% 1.75/1.92          | ~ (v1_relat_1 @ X0)
% 1.75/1.92          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ (k4_relat_1 @ X0))) @ 
% 1.75/1.92              (k4_relat_1 @ X0)) = (k2_funct_1 @ X0)))),
% 1.75/1.92      inference('simplify', [status(thm)], ['102'])).
% 1.75/1.92  thf(t80_relat_1, axiom,
% 1.75/1.92    (![A:$i]:
% 1.75/1.92     ( ( v1_relat_1 @ A ) =>
% 1.75/1.92       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 1.75/1.92  thf('104', plain,
% 1.75/1.92      (![X8 : $i]:
% 1.75/1.92         (((k5_relat_1 @ X8 @ (k6_relat_1 @ (k2_relat_1 @ X8))) = (X8))
% 1.75/1.92          | ~ (v1_relat_1 @ X8))),
% 1.75/1.92      inference('cnf', [status(esa)], [t80_relat_1])).
% 1.75/1.92  thf('105', plain,
% 1.75/1.92      (![X7 : $i]:
% 1.75/1.92         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X7)) @ X7) = (X7))
% 1.75/1.92          | ~ (v1_relat_1 @ X7))),
% 1.75/1.92      inference('cnf', [status(esa)], [t78_relat_1])).
% 1.75/1.92  thf(t55_relat_1, axiom,
% 1.75/1.92    (![A:$i]:
% 1.75/1.92     ( ( v1_relat_1 @ A ) =>
% 1.75/1.92       ( ![B:$i]:
% 1.75/1.92         ( ( v1_relat_1 @ B ) =>
% 1.75/1.92           ( ![C:$i]:
% 1.75/1.92             ( ( v1_relat_1 @ C ) =>
% 1.75/1.92               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 1.75/1.92                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 1.75/1.92  thf('106', plain,
% 1.75/1.92      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.75/1.92         (~ (v1_relat_1 @ X2)
% 1.75/1.92          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 1.75/1.92              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 1.75/1.92          | ~ (v1_relat_1 @ X4)
% 1.75/1.92          | ~ (v1_relat_1 @ X3))),
% 1.75/1.92      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.75/1.92  thf('107', plain,
% 1.75/1.92      (![X0 : $i, X1 : $i]:
% 1.75/1.92         (((k5_relat_1 @ X0 @ X1)
% 1.75/1.92            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 1.75/1.92               (k5_relat_1 @ X0 @ X1)))
% 1.75/1.92          | ~ (v1_relat_1 @ X0)
% 1.75/1.92          | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 1.75/1.92          | ~ (v1_relat_1 @ X1)
% 1.75/1.92          | ~ (v1_relat_1 @ X0))),
% 1.75/1.92      inference('sup+', [status(thm)], ['105', '106'])).
% 1.75/1.92  thf('108', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.75/1.92      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.75/1.92  thf('109', plain,
% 1.75/1.92      (![X0 : $i, X1 : $i]:
% 1.75/1.92         (((k5_relat_1 @ X0 @ X1)
% 1.75/1.92            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 1.75/1.92               (k5_relat_1 @ X0 @ X1)))
% 1.75/1.92          | ~ (v1_relat_1 @ X0)
% 1.75/1.92          | ~ (v1_relat_1 @ X1)
% 1.75/1.92          | ~ (v1_relat_1 @ X0))),
% 1.75/1.92      inference('demod', [status(thm)], ['107', '108'])).
% 1.75/1.92  thf('110', plain,
% 1.75/1.92      (![X0 : $i, X1 : $i]:
% 1.75/1.92         (~ (v1_relat_1 @ X1)
% 1.75/1.92          | ~ (v1_relat_1 @ X0)
% 1.75/1.92          | ((k5_relat_1 @ X0 @ X1)
% 1.75/1.92              = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 1.75/1.92                 (k5_relat_1 @ X0 @ X1))))),
% 1.75/1.92      inference('simplify', [status(thm)], ['109'])).
% 1.75/1.92  thf('111', plain,
% 1.75/1.92      (![X0 : $i]:
% 1.75/1.92         (((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 1.75/1.92            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0))
% 1.75/1.92          | ~ (v1_relat_1 @ X0)
% 1.75/1.92          | ~ (v1_relat_1 @ X0)
% 1.75/1.92          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))),
% 1.75/1.92      inference('sup+', [status(thm)], ['104', '110'])).
% 1.75/1.92  thf('112', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 1.75/1.92      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.75/1.92  thf('113', plain,
% 1.75/1.92      (![X0 : $i]:
% 1.75/1.92         (((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 1.75/1.92            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0))
% 1.75/1.92          | ~ (v1_relat_1 @ X0)
% 1.75/1.92          | ~ (v1_relat_1 @ X0))),
% 1.75/1.92      inference('demod', [status(thm)], ['111', '112'])).
% 1.75/1.92  thf('114', plain,
% 1.75/1.92      (![X0 : $i]:
% 1.75/1.92         (~ (v1_relat_1 @ X0)
% 1.75/1.92          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 1.75/1.92              = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0)))),
% 1.75/1.92      inference('simplify', [status(thm)], ['113'])).
% 1.75/1.92  thf('115', plain,
% 1.75/1.92      (![X0 : $i]:
% 1.75/1.92         (((k5_relat_1 @ (k4_relat_1 @ X0) @ 
% 1.75/1.92            (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ X0))))
% 1.75/1.92            = (k2_funct_1 @ X0))
% 1.75/1.92          | ~ (v1_relat_1 @ X0)
% 1.75/1.92          | ~ (v1_funct_1 @ X0)
% 1.75/1.92          | ~ (v2_funct_1 @ X0)
% 1.75/1.92          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 1.75/1.92      inference('sup+', [status(thm)], ['103', '114'])).
% 1.75/1.92  thf('116', plain,
% 1.75/1.92      (![X0 : $i]:
% 1.75/1.92         (~ (v1_relat_1 @ X0)
% 1.75/1.92          | ~ (v2_funct_1 @ X0)
% 1.75/1.92          | ~ (v1_funct_1 @ X0)
% 1.75/1.92          | ~ (v1_relat_1 @ X0)
% 1.75/1.92          | ((k5_relat_1 @ (k4_relat_1 @ X0) @ 
% 1.75/1.92              (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ X0))))
% 1.75/1.92              = (k2_funct_1 @ X0)))),
% 1.75/1.92      inference('sup-', [status(thm)], ['84', '115'])).
% 1.75/1.92  thf('117', plain,
% 1.75/1.92      (![X0 : $i]:
% 1.75/1.92         (((k5_relat_1 @ (k4_relat_1 @ X0) @ 
% 1.75/1.92            (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ X0))))
% 1.75/1.92            = (k2_funct_1 @ X0))
% 1.75/1.92          | ~ (v1_funct_1 @ X0)
% 1.75/1.92          | ~ (v2_funct_1 @ X0)
% 1.75/1.92          | ~ (v1_relat_1 @ X0))),
% 1.75/1.92      inference('simplify', [status(thm)], ['116'])).
% 1.75/1.92  thf('118', plain,
% 1.75/1.92      ((((k5_relat_1 @ (k4_relat_1 @ sk_D) @ (k6_relat_1 @ (k1_relat_1 @ sk_D)))
% 1.75/1.92          = (k2_funct_1 @ sk_D))
% 1.75/1.92        | ~ (v1_relat_1 @ sk_D)
% 1.75/1.92        | ~ (v2_funct_1 @ sk_D)
% 1.75/1.92        | ~ (v1_funct_1 @ sk_D))),
% 1.75/1.92      inference('sup+', [status(thm)], ['83', '117'])).
% 1.75/1.92  thf('119', plain,
% 1.75/1.92      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 1.75/1.92      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 1.75/1.92  thf('120', plain,
% 1.75/1.92      (((k1_relat_1 @ sk_D) = (k2_relat_1 @ (k4_relat_1 @ sk_D)))),
% 1.75/1.92      inference('sup-', [status(thm)], ['81', '82'])).
% 1.75/1.92  thf('121', plain,
% 1.75/1.92      (![X8 : $i]:
% 1.75/1.92         (((k5_relat_1 @ X8 @ (k6_relat_1 @ (k2_relat_1 @ X8))) = (X8))
% 1.75/1.92          | ~ (v1_relat_1 @ X8))),
% 1.75/1.92      inference('cnf', [status(esa)], [t80_relat_1])).
% 1.75/1.92  thf('122', plain,
% 1.75/1.92      ((((k5_relat_1 @ (k4_relat_1 @ sk_D) @ (k6_relat_1 @ (k1_relat_1 @ sk_D)))
% 1.75/1.92          = (k4_relat_1 @ sk_D))
% 1.75/1.92        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_D)))),
% 1.75/1.92      inference('sup+', [status(thm)], ['120', '121'])).
% 1.75/1.92  thf('123', plain,
% 1.75/1.92      ((~ (v1_relat_1 @ sk_D)
% 1.75/1.92        | ((k5_relat_1 @ (k4_relat_1 @ sk_D) @ 
% 1.75/1.92            (k6_relat_1 @ (k1_relat_1 @ sk_D))) = (k4_relat_1 @ sk_D)))),
% 1.75/1.92      inference('sup-', [status(thm)], ['119', '122'])).
% 1.75/1.92  thf('124', plain, ((v1_relat_1 @ sk_D)),
% 1.75/1.92      inference('sup-', [status(thm)], ['79', '80'])).
% 1.75/1.92  thf('125', plain,
% 1.75/1.92      (((k5_relat_1 @ (k4_relat_1 @ sk_D) @ (k6_relat_1 @ (k1_relat_1 @ sk_D)))
% 1.75/1.92         = (k4_relat_1 @ sk_D))),
% 1.75/1.92      inference('demod', [status(thm)], ['123', '124'])).
% 1.75/1.92  thf('126', plain, ((v1_relat_1 @ sk_D)),
% 1.75/1.92      inference('sup-', [status(thm)], ['79', '80'])).
% 1.75/1.92  thf('127', plain, ((v1_funct_1 @ sk_D)),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('128', plain,
% 1.75/1.92      ((((k4_relat_1 @ sk_D) = (k2_funct_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 1.75/1.92      inference('demod', [status(thm)], ['118', '125', '126', '127'])).
% 1.75/1.92  thf('129', plain, ((v2_funct_1 @ sk_D)),
% 1.75/1.92      inference('sup-', [status(thm)], ['75', '76'])).
% 1.75/1.92  thf('130', plain, (((k4_relat_1 @ sk_D) = (k2_funct_1 @ sk_D))),
% 1.75/1.92      inference('demod', [status(thm)], ['128', '129'])).
% 1.75/1.92  thf('131', plain,
% 1.75/1.92      (((k5_relat_1 @ sk_D @ (k4_relat_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 1.75/1.92      inference('demod', [status(thm)], ['78', '130'])).
% 1.75/1.92  thf('132', plain,
% 1.75/1.92      (![X9 : $i]:
% 1.75/1.92         (~ (v2_funct_1 @ X9)
% 1.75/1.92          | ((k2_funct_1 @ X9) = (k4_relat_1 @ X9))
% 1.75/1.92          | ~ (v1_funct_1 @ X9)
% 1.75/1.92          | ~ (v1_relat_1 @ X9))),
% 1.75/1.92      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.75/1.92  thf(t58_funct_1, axiom,
% 1.75/1.92    (![A:$i]:
% 1.75/1.92     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.75/1.92       ( ( v2_funct_1 @ A ) =>
% 1.75/1.92         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 1.75/1.92             ( k1_relat_1 @ A ) ) & 
% 1.75/1.92           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 1.75/1.92             ( k1_relat_1 @ A ) ) ) ) ))).
% 1.75/1.92  thf('133', plain,
% 1.75/1.92      (![X13 : $i]:
% 1.75/1.92         (~ (v2_funct_1 @ X13)
% 1.75/1.92          | ((k2_relat_1 @ (k5_relat_1 @ X13 @ (k2_funct_1 @ X13)))
% 1.75/1.92              = (k1_relat_1 @ X13))
% 1.75/1.92          | ~ (v1_funct_1 @ X13)
% 1.75/1.92          | ~ (v1_relat_1 @ X13))),
% 1.75/1.92      inference('cnf', [status(esa)], [t58_funct_1])).
% 1.75/1.92  thf('134', plain,
% 1.75/1.92      (![X0 : $i]:
% 1.75/1.92         (((k2_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ X0)))
% 1.75/1.92            = (k1_relat_1 @ X0))
% 1.75/1.92          | ~ (v1_relat_1 @ X0)
% 1.75/1.92          | ~ (v1_funct_1 @ X0)
% 1.75/1.92          | ~ (v2_funct_1 @ X0)
% 1.75/1.92          | ~ (v1_relat_1 @ X0)
% 1.75/1.92          | ~ (v1_funct_1 @ X0)
% 1.75/1.92          | ~ (v2_funct_1 @ X0))),
% 1.75/1.92      inference('sup+', [status(thm)], ['132', '133'])).
% 1.75/1.92  thf('135', plain,
% 1.75/1.92      (![X0 : $i]:
% 1.75/1.92         (~ (v2_funct_1 @ X0)
% 1.75/1.92          | ~ (v1_funct_1 @ X0)
% 1.75/1.92          | ~ (v1_relat_1 @ X0)
% 1.75/1.92          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ X0)))
% 1.75/1.92              = (k1_relat_1 @ X0)))),
% 1.75/1.92      inference('simplify', [status(thm)], ['134'])).
% 1.75/1.92  thf('136', plain,
% 1.75/1.92      ((((k2_relat_1 @ (k6_relat_1 @ sk_B)) = (k1_relat_1 @ sk_D))
% 1.75/1.92        | ~ (v1_relat_1 @ sk_D)
% 1.75/1.92        | ~ (v1_funct_1 @ sk_D)
% 1.75/1.92        | ~ (v2_funct_1 @ sk_D))),
% 1.75/1.92      inference('sup+', [status(thm)], ['131', '135'])).
% 1.75/1.92  thf(t71_relat_1, axiom,
% 1.75/1.92    (![A:$i]:
% 1.75/1.92     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.75/1.92       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.75/1.92  thf('137', plain, (![X6 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X6)) = (X6))),
% 1.75/1.92      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.75/1.92  thf('138', plain, ((v1_relat_1 @ sk_D)),
% 1.75/1.92      inference('sup-', [status(thm)], ['79', '80'])).
% 1.75/1.92  thf('139', plain, ((v1_funct_1 @ sk_D)),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('140', plain, ((v2_funct_1 @ sk_D)),
% 1.75/1.92      inference('sup-', [status(thm)], ['75', '76'])).
% 1.75/1.92  thf('141', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.75/1.92      inference('demod', [status(thm)], ['136', '137', '138', '139', '140'])).
% 1.75/1.92  thf('142', plain,
% 1.75/1.92      (![X7 : $i]:
% 1.75/1.92         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X7)) @ X7) = (X7))
% 1.75/1.92          | ~ (v1_relat_1 @ X7))),
% 1.75/1.92      inference('cnf', [status(esa)], [t78_relat_1])).
% 1.75/1.92  thf('143', plain,
% 1.75/1.92      ((((k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_D) = (sk_D))
% 1.75/1.92        | ~ (v1_relat_1 @ sk_D))),
% 1.75/1.92      inference('sup+', [status(thm)], ['141', '142'])).
% 1.75/1.92  thf('144', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 1.75/1.92      inference('demod', [status(thm)], ['52', '55'])).
% 1.75/1.92  thf('145', plain,
% 1.75/1.92      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('146', plain,
% 1.75/1.92      (![X49 : $i, X50 : $i, X51 : $i]:
% 1.75/1.92         (((X49) = (k1_xboole_0))
% 1.75/1.92          | ~ (v1_funct_1 @ X50)
% 1.75/1.92          | ~ (v1_funct_2 @ X50 @ X51 @ X49)
% 1.75/1.92          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X49)))
% 1.75/1.92          | ((k5_relat_1 @ (k2_funct_1 @ X50) @ X50) = (k6_partfun1 @ X49))
% 1.75/1.92          | ~ (v2_funct_1 @ X50)
% 1.75/1.92          | ((k2_relset_1 @ X51 @ X49 @ X50) != (X49)))),
% 1.75/1.92      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.75/1.92  thf('147', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 1.75/1.92      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.75/1.92  thf('148', plain,
% 1.75/1.92      (![X49 : $i, X50 : $i, X51 : $i]:
% 1.75/1.92         (((X49) = (k1_xboole_0))
% 1.75/1.92          | ~ (v1_funct_1 @ X50)
% 1.75/1.92          | ~ (v1_funct_2 @ X50 @ X51 @ X49)
% 1.75/1.92          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X49)))
% 1.75/1.92          | ((k5_relat_1 @ (k2_funct_1 @ X50) @ X50) = (k6_relat_1 @ X49))
% 1.75/1.92          | ~ (v2_funct_1 @ X50)
% 1.75/1.92          | ((k2_relset_1 @ X51 @ X49 @ X50) != (X49)))),
% 1.75/1.92      inference('demod', [status(thm)], ['146', '147'])).
% 1.75/1.92  thf('149', plain,
% 1.75/1.92      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.75/1.92        | ~ (v2_funct_1 @ sk_C)
% 1.75/1.92        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 1.75/1.92        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.75/1.92        | ~ (v1_funct_1 @ sk_C)
% 1.75/1.92        | ((sk_B) = (k1_xboole_0)))),
% 1.75/1.92      inference('sup-', [status(thm)], ['145', '148'])).
% 1.75/1.92  thf('150', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('151', plain, ((v2_funct_1 @ sk_C)),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('152', plain,
% 1.75/1.92      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('153', plain,
% 1.75/1.92      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.75/1.92         ((v1_relat_1 @ X14)
% 1.75/1.92          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.75/1.92      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.75/1.92  thf('154', plain, ((v1_relat_1 @ sk_C)),
% 1.75/1.92      inference('sup-', [status(thm)], ['152', '153'])).
% 1.75/1.92  thf('155', plain,
% 1.75/1.92      (![X1 : $i]:
% 1.75/1.92         (((k1_relat_1 @ X1) = (k2_relat_1 @ (k4_relat_1 @ X1)))
% 1.75/1.92          | ~ (v1_relat_1 @ X1))),
% 1.75/1.92      inference('cnf', [status(esa)], [t37_relat_1])).
% 1.75/1.92  thf('156', plain,
% 1.75/1.92      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.75/1.92      inference('sup-', [status(thm)], ['154', '155'])).
% 1.75/1.92  thf('157', plain,
% 1.75/1.92      (![X0 : $i]:
% 1.75/1.92         (((k5_relat_1 @ (k4_relat_1 @ X0) @ 
% 1.75/1.92            (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ X0))))
% 1.75/1.92            = (k2_funct_1 @ X0))
% 1.75/1.92          | ~ (v1_funct_1 @ X0)
% 1.75/1.92          | ~ (v2_funct_1 @ X0)
% 1.75/1.92          | ~ (v1_relat_1 @ X0))),
% 1.75/1.92      inference('simplify', [status(thm)], ['116'])).
% 1.75/1.92  thf('158', plain,
% 1.75/1.92      ((((k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_relat_1 @ (k1_relat_1 @ sk_C)))
% 1.75/1.92          = (k2_funct_1 @ sk_C))
% 1.75/1.92        | ~ (v1_relat_1 @ sk_C)
% 1.75/1.92        | ~ (v2_funct_1 @ sk_C)
% 1.75/1.92        | ~ (v1_funct_1 @ sk_C))),
% 1.75/1.92      inference('sup+', [status(thm)], ['156', '157'])).
% 1.75/1.92  thf('159', plain,
% 1.75/1.92      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 1.75/1.92      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 1.75/1.92  thf('160', plain,
% 1.75/1.92      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.75/1.92      inference('sup-', [status(thm)], ['154', '155'])).
% 1.75/1.92  thf('161', plain,
% 1.75/1.92      (![X8 : $i]:
% 1.75/1.92         (((k5_relat_1 @ X8 @ (k6_relat_1 @ (k2_relat_1 @ X8))) = (X8))
% 1.75/1.92          | ~ (v1_relat_1 @ X8))),
% 1.75/1.92      inference('cnf', [status(esa)], [t80_relat_1])).
% 1.75/1.92  thf('162', plain,
% 1.75/1.92      ((((k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_relat_1 @ (k1_relat_1 @ sk_C)))
% 1.75/1.92          = (k4_relat_1 @ sk_C))
% 1.75/1.92        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.75/1.92      inference('sup+', [status(thm)], ['160', '161'])).
% 1.75/1.92  thf('163', plain,
% 1.75/1.92      ((~ (v1_relat_1 @ sk_C)
% 1.75/1.92        | ((k5_relat_1 @ (k4_relat_1 @ sk_C) @ 
% 1.75/1.92            (k6_relat_1 @ (k1_relat_1 @ sk_C))) = (k4_relat_1 @ sk_C)))),
% 1.75/1.92      inference('sup-', [status(thm)], ['159', '162'])).
% 1.75/1.92  thf('164', plain, ((v1_relat_1 @ sk_C)),
% 1.75/1.92      inference('sup-', [status(thm)], ['152', '153'])).
% 1.75/1.92  thf('165', plain,
% 1.75/1.92      (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_relat_1 @ (k1_relat_1 @ sk_C)))
% 1.75/1.92         = (k4_relat_1 @ sk_C))),
% 1.75/1.92      inference('demod', [status(thm)], ['163', '164'])).
% 1.75/1.92  thf('166', plain, ((v1_relat_1 @ sk_C)),
% 1.75/1.92      inference('sup-', [status(thm)], ['152', '153'])).
% 1.75/1.92  thf('167', plain, ((v2_funct_1 @ sk_C)),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('168', plain, ((v1_funct_1 @ sk_C)),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('169', plain, (((k4_relat_1 @ sk_C) = (k2_funct_1 @ sk_C))),
% 1.75/1.92      inference('demod', [status(thm)], ['158', '165', '166', '167', '168'])).
% 1.75/1.92  thf('170', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('171', plain, ((v1_funct_1 @ sk_C)),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('172', plain,
% 1.75/1.92      ((((sk_B) != (sk_B))
% 1.75/1.92        | ((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 1.75/1.92        | ((sk_B) = (k1_xboole_0)))),
% 1.75/1.92      inference('demod', [status(thm)],
% 1.75/1.92                ['149', '150', '151', '169', '170', '171'])).
% 1.75/1.92  thf('173', plain,
% 1.75/1.92      ((((sk_B) = (k1_xboole_0))
% 1.75/1.92        | ((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B)))),
% 1.75/1.92      inference('simplify', [status(thm)], ['172'])).
% 1.75/1.92  thf('174', plain, (((sk_B) != (k1_xboole_0))),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('175', plain,
% 1.75/1.92      (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))),
% 1.75/1.92      inference('simplify_reflect-', [status(thm)], ['173', '174'])).
% 1.75/1.92  thf('176', plain,
% 1.75/1.92      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.75/1.92         (~ (v1_relat_1 @ X2)
% 1.75/1.92          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 1.75/1.92              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 1.75/1.92          | ~ (v1_relat_1 @ X4)
% 1.75/1.92          | ~ (v1_relat_1 @ X3))),
% 1.75/1.92      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.75/1.92  thf('177', plain,
% 1.75/1.92      (![X0 : $i]:
% 1.75/1.92         (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 1.75/1.92            = (k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.75/1.92          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 1.75/1.92          | ~ (v1_relat_1 @ X0)
% 1.75/1.92          | ~ (v1_relat_1 @ sk_C))),
% 1.75/1.92      inference('sup+', [status(thm)], ['175', '176'])).
% 1.75/1.92  thf('178', plain, (((k4_relat_1 @ sk_C) = (k2_funct_1 @ sk_C))),
% 1.75/1.92      inference('demod', [status(thm)], ['158', '165', '166', '167', '168'])).
% 1.75/1.92  thf('179', plain,
% 1.75/1.92      (![X10 : $i]:
% 1.75/1.92         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 1.75/1.92          | ~ (v1_funct_1 @ X10)
% 1.75/1.92          | ~ (v1_relat_1 @ X10))),
% 1.75/1.92      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.75/1.92  thf('180', plain,
% 1.75/1.92      (((v1_relat_1 @ (k4_relat_1 @ sk_C))
% 1.75/1.92        | ~ (v1_relat_1 @ sk_C)
% 1.75/1.92        | ~ (v1_funct_1 @ sk_C))),
% 1.75/1.92      inference('sup+', [status(thm)], ['178', '179'])).
% 1.75/1.92  thf('181', plain, ((v1_relat_1 @ sk_C)),
% 1.75/1.92      inference('sup-', [status(thm)], ['152', '153'])).
% 1.75/1.92  thf('182', plain, ((v1_funct_1 @ sk_C)),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('183', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 1.75/1.92      inference('demod', [status(thm)], ['180', '181', '182'])).
% 1.75/1.92  thf('184', plain, ((v1_relat_1 @ sk_C)),
% 1.75/1.92      inference('sup-', [status(thm)], ['152', '153'])).
% 1.75/1.92  thf('185', plain,
% 1.75/1.92      (![X0 : $i]:
% 1.75/1.92         (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 1.75/1.92            = (k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.75/1.92          | ~ (v1_relat_1 @ X0))),
% 1.75/1.92      inference('demod', [status(thm)], ['177', '183', '184'])).
% 1.75/1.92  thf('186', plain,
% 1.75/1.92      ((((k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_D)
% 1.75/1.92          = (k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_relat_1 @ sk_A)))
% 1.75/1.92        | ~ (v1_relat_1 @ sk_D))),
% 1.75/1.92      inference('sup+', [status(thm)], ['144', '185'])).
% 1.75/1.92  thf('187', plain,
% 1.75/1.92      (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_relat_1 @ (k1_relat_1 @ sk_C)))
% 1.75/1.92         = (k4_relat_1 @ sk_C))),
% 1.75/1.92      inference('demod', [status(thm)], ['163', '164'])).
% 1.75/1.92  thf('188', plain, (((k4_relat_1 @ sk_C) = (k2_funct_1 @ sk_C))),
% 1.75/1.92      inference('demod', [status(thm)], ['158', '165', '166', '167', '168'])).
% 1.75/1.92  thf('189', plain,
% 1.75/1.92      (![X13 : $i]:
% 1.75/1.92         (~ (v2_funct_1 @ X13)
% 1.75/1.92          | ((k2_relat_1 @ (k5_relat_1 @ X13 @ (k2_funct_1 @ X13)))
% 1.75/1.92              = (k1_relat_1 @ X13))
% 1.75/1.92          | ~ (v1_funct_1 @ X13)
% 1.75/1.92          | ~ (v1_relat_1 @ X13))),
% 1.75/1.92      inference('cnf', [status(esa)], [t58_funct_1])).
% 1.75/1.92  thf('190', plain,
% 1.75/1.92      ((((k2_relat_1 @ (k5_relat_1 @ sk_C @ (k4_relat_1 @ sk_C)))
% 1.75/1.92          = (k1_relat_1 @ sk_C))
% 1.75/1.92        | ~ (v1_relat_1 @ sk_C)
% 1.75/1.92        | ~ (v1_funct_1 @ sk_C)
% 1.75/1.92        | ~ (v2_funct_1 @ sk_C))),
% 1.75/1.92      inference('sup+', [status(thm)], ['188', '189'])).
% 1.75/1.92  thf('191', plain, ((v1_relat_1 @ sk_C)),
% 1.75/1.92      inference('sup-', [status(thm)], ['152', '153'])).
% 1.75/1.92  thf('192', plain, ((v1_funct_1 @ sk_C)),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('193', plain, ((v2_funct_1 @ sk_C)),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('194', plain,
% 1.75/1.92      (((k2_relat_1 @ (k5_relat_1 @ sk_C @ (k4_relat_1 @ sk_C)))
% 1.75/1.92         = (k1_relat_1 @ sk_C))),
% 1.75/1.92      inference('demod', [status(thm)], ['190', '191', '192', '193'])).
% 1.75/1.92  thf('195', plain,
% 1.75/1.92      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('196', plain,
% 1.75/1.92      (![X49 : $i, X50 : $i, X51 : $i]:
% 1.75/1.92         (((X49) = (k1_xboole_0))
% 1.75/1.92          | ~ (v1_funct_1 @ X50)
% 1.75/1.92          | ~ (v1_funct_2 @ X50 @ X51 @ X49)
% 1.75/1.92          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X49)))
% 1.75/1.92          | ((k5_relat_1 @ X50 @ (k2_funct_1 @ X50)) = (k6_relat_1 @ X51))
% 1.75/1.92          | ~ (v2_funct_1 @ X50)
% 1.75/1.92          | ((k2_relset_1 @ X51 @ X49 @ X50) != (X49)))),
% 1.75/1.92      inference('demod', [status(thm)], ['1', '2'])).
% 1.75/1.92  thf('197', plain,
% 1.75/1.92      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.75/1.92        | ~ (v2_funct_1 @ sk_C)
% 1.75/1.92        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 1.75/1.92        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.75/1.92        | ~ (v1_funct_1 @ sk_C)
% 1.75/1.92        | ((sk_B) = (k1_xboole_0)))),
% 1.75/1.92      inference('sup-', [status(thm)], ['195', '196'])).
% 1.75/1.92  thf('198', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('199', plain, ((v2_funct_1 @ sk_C)),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('200', plain, (((k4_relat_1 @ sk_C) = (k2_funct_1 @ sk_C))),
% 1.75/1.92      inference('demod', [status(thm)], ['158', '165', '166', '167', '168'])).
% 1.75/1.92  thf('201', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('202', plain, ((v1_funct_1 @ sk_C)),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('203', plain,
% 1.75/1.92      ((((sk_B) != (sk_B))
% 1.75/1.92        | ((k5_relat_1 @ sk_C @ (k4_relat_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 1.75/1.92        | ((sk_B) = (k1_xboole_0)))),
% 1.75/1.92      inference('demod', [status(thm)],
% 1.75/1.92                ['197', '198', '199', '200', '201', '202'])).
% 1.75/1.92  thf('204', plain,
% 1.75/1.92      ((((sk_B) = (k1_xboole_0))
% 1.75/1.92        | ((k5_relat_1 @ sk_C @ (k4_relat_1 @ sk_C)) = (k6_relat_1 @ sk_A)))),
% 1.75/1.92      inference('simplify', [status(thm)], ['203'])).
% 1.75/1.92  thf('205', plain, (((sk_B) != (k1_xboole_0))),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('206', plain,
% 1.75/1.92      (((k5_relat_1 @ sk_C @ (k4_relat_1 @ sk_C)) = (k6_relat_1 @ sk_A))),
% 1.75/1.92      inference('simplify_reflect-', [status(thm)], ['204', '205'])).
% 1.75/1.92  thf('207', plain, (![X6 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X6)) = (X6))),
% 1.75/1.92      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.75/1.92  thf('208', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 1.75/1.92      inference('demod', [status(thm)], ['194', '206', '207'])).
% 1.75/1.92  thf('209', plain,
% 1.75/1.92      (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_relat_1 @ sk_A))
% 1.75/1.92         = (k4_relat_1 @ sk_C))),
% 1.75/1.92      inference('demod', [status(thm)], ['187', '208'])).
% 1.75/1.92  thf('210', plain, ((v1_relat_1 @ sk_D)),
% 1.75/1.92      inference('sup-', [status(thm)], ['79', '80'])).
% 1.75/1.92  thf('211', plain,
% 1.75/1.92      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_D) = (k4_relat_1 @ sk_C))),
% 1.75/1.92      inference('demod', [status(thm)], ['186', '209', '210'])).
% 1.75/1.92  thf('212', plain, ((v1_relat_1 @ sk_D)),
% 1.75/1.92      inference('sup-', [status(thm)], ['79', '80'])).
% 1.75/1.92  thf('213', plain, (((k4_relat_1 @ sk_C) = (sk_D))),
% 1.75/1.92      inference('demod', [status(thm)], ['143', '211', '212'])).
% 1.75/1.92  thf('214', plain,
% 1.75/1.92      (![X9 : $i]:
% 1.75/1.92         (~ (v2_funct_1 @ X9)
% 1.75/1.92          | ((k2_funct_1 @ X9) = (k4_relat_1 @ X9))
% 1.75/1.92          | ~ (v1_funct_1 @ X9)
% 1.75/1.92          | ~ (v1_relat_1 @ X9))),
% 1.75/1.92      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.75/1.92  thf('215', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('216', plain,
% 1.75/1.92      ((((sk_D) != (k4_relat_1 @ sk_C))
% 1.75/1.92        | ~ (v1_relat_1 @ sk_C)
% 1.75/1.92        | ~ (v1_funct_1 @ sk_C)
% 1.75/1.92        | ~ (v2_funct_1 @ sk_C))),
% 1.75/1.92      inference('sup-', [status(thm)], ['214', '215'])).
% 1.75/1.92  thf('217', plain, ((v1_relat_1 @ sk_C)),
% 1.75/1.92      inference('sup-', [status(thm)], ['152', '153'])).
% 1.75/1.92  thf('218', plain, ((v1_funct_1 @ sk_C)),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('219', plain, ((v2_funct_1 @ sk_C)),
% 1.75/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.92  thf('220', plain, (((sk_D) != (k4_relat_1 @ sk_C))),
% 1.75/1.92      inference('demod', [status(thm)], ['216', '217', '218', '219'])).
% 1.75/1.92  thf('221', plain, ($false),
% 1.75/1.92      inference('simplify_reflect-', [status(thm)], ['213', '220'])).
% 1.75/1.92  
% 1.75/1.92  % SZS output end Refutation
% 1.75/1.92  
% 1.75/1.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

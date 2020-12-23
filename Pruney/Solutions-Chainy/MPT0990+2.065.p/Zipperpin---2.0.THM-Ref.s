%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TMbDkUxnNc

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:04 EST 2020

% Result     : Theorem 8.86s
% Output     : Refutation 8.86s
% Verified   : 
% Statistics : Number of formulae       :  346 (1338 expanded)
%              Number of leaves         :   52 ( 423 expanded)
%              Depth                    :   38
%              Number of atoms          : 4045 (25795 expanded)
%              Number of equality atoms :  239 (1723 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    ! [X56: $i,X57: $i,X58: $i] :
      ( ( X56 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X57 )
      | ~ ( v1_funct_2 @ X57 @ X58 @ X56 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X56 ) ) )
      | ( ( k5_relat_1 @ X57 @ ( k2_funct_1 @ X57 ) )
        = ( k6_partfun1 @ X58 ) )
      | ~ ( v2_funct_1 @ X57 )
      | ( ( k2_relset_1 @ X58 @ X56 @ X57 )
       != X56 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
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
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( ( k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39 )
        = ( k5_relat_1 @ X36 @ X39 ) ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X35 ) ) ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( X25 = X28 )
      | ~ ( r2_relset_1 @ X26 @ X27 @ X25 @ X28 ) ) ),
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

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('51',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('52',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('53',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['50','53'])).

thf('55',plain,
    ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['34','54'])).

thf('56',plain,(
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

thf('57',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_2 @ X51 @ X52 @ X53 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) )
      | ( zip_tseitin_0 @ X51 @ X54 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X55 @ X52 @ X52 @ X53 @ X54 @ X51 ) )
      | ( zip_tseitin_1 @ X53 @ X52 )
      | ( ( k2_relset_1 @ X55 @ X52 @ X54 )
       != X52 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X52 ) ) )
      | ~ ( v1_funct_2 @ X54 @ X55 @ X52 )
      | ~ ( v1_funct_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('58',plain,(
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
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A_1 @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A_1 @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A_1 ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A_1 @ sk_B )
    | ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['55','61'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('63',plain,(
    ! [X15: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('64',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('65',plain,(
    ! [X15: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X15 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_2 @ sk_C @ sk_A_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A_1 @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['62','65','66','67','68','69'])).

thf('71',plain,
    ( ( zip_tseitin_1 @ sk_A_1 @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X49: $i,X50: $i] :
      ( ( X49 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('73',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X47: $i,X48: $i] :
      ( ( v2_funct_1 @ X48 )
      | ~ ( zip_tseitin_0 @ X48 @ X47 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('77',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['25','77'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('79',plain,(
    ! [X11: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X11 ) ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('80',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('81',plain,(
    ! [X11: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X11 ) ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('82',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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

thf('83',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) @ X8 )
        = ( k5_relat_1 @ X7 @ ( k5_relat_1 @ X6 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('84',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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

thf('85',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_relat_1 @ X16 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('86',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X2 ) @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('87',plain,(
    ! [X1: $i] :
      ( ( k2_subset_1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('88',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('89',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('90',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('91',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ( ( k5_relat_1 @ X12 @ ( k6_relat_1 @ X13 ) )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('92',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('93',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ( ( k5_relat_1 @ X12 @ ( k6_partfun1 @ X13 ) )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('95',plain,(
    ! [X11: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X11 ) ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('96',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) @ X8 )
        = ( k5_relat_1 @ X7 @ ( k5_relat_1 @ X6 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('100',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['98','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['94','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['85','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['84','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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

thf('111',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X18 ) @ X18 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('112',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('113',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X18 ) @ X18 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('115',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) @ X8 )
        = ( k5_relat_1 @ X7 @ ( k5_relat_1 @ X6 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['113','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['110','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['109','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_relat_1 @ X16 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('129',plain,(
    ! [X9: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('130',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('131',plain,(
    ! [X9: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X9 ) )
      = X9 ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X11: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X11 ) ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) @ X0 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['128','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) @ X0 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['125','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k1_relat_1 @ X16 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) @ X0 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['139','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) @ X0 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('153',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k5_relat_1 @ X18 @ ( k2_funct_1 @ X18 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('154',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('155',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k5_relat_1 @ X18 @ ( k2_funct_1 @ X18 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) @ X8 )
        = ( k5_relat_1 @ X7 @ ( k5_relat_1 @ X6 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['152','158'])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,(
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
    inference('sup+',[status(thm)],['151','160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k1_relat_1 @ X16 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('166',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['166','171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) @ X8 )
        = ( k5_relat_1 @ X7 @ ( k5_relat_1 @ X6 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('175',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('177',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['175','176','177'])).

thf('179',plain,(
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
    inference('sup+',[status(thm)],['165','178'])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,(
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
    inference('sup+',[status(thm)],['164','180'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ X0 )
        = ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['181'])).

thf('183',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['78','182'])).

thf('184',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['50','53'])).

thf('185',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('186',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X18 ) @ X18 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('187',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) @ X8 )
        = ( k5_relat_1 @ X7 @ ( k5_relat_1 @ X6 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['188'])).

thf('190',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['185','189'])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['184','191'])).

thf('193',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('195',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['195','196'])).

thf('198',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('199',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k1_relat_1 @ X16 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('200',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('201',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['199','200'])).

thf('202',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['198','201'])).

thf('203',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['202'])).

thf('204',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('205',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['195','196'])).

thf('206',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('207',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_relat_1 @ X16 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('208',plain,(
    ! [X11: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X11 ) ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['207','208'])).

thf('210',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['206','209'])).

thf('211',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['210'])).

thf('212',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['205','211'])).

thf('213',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('215',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['212','215','216','217'])).

thf('219',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) @ X8 )
        = ( k5_relat_1 @ X7 @ ( k5_relat_1 @ X6 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('220',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['218','219'])).

thf('221',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('222',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['220','221'])).

thf('223',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['204','222'])).

thf('224',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['213','214'])).

thf('225',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['223','224','225'])).

thf('227',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['203','226'])).

thf('228',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['212','215','216','217'])).

thf('229',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['213','214'])).

thf('230',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('233',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['227','228','229','230','231','232'])).

thf('234',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ( X56 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X57 )
      | ~ ( v1_funct_2 @ X57 @ X58 @ X56 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X56 ) ) )
      | ( ( k5_relat_1 @ X57 @ ( k2_funct_1 @ X57 ) )
        = ( k6_partfun1 @ X58 ) )
      | ~ ( v2_funct_1 @ X57 )
      | ( ( k2_relset_1 @ X58 @ X56 @ X57 )
       != X56 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('236',plain,
    ( ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A_1 ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['234','235'])).

thf('237',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('240',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k5_relat_1 @ X18 @ ( k2_funct_1 @ X18 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('241',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['195','196'])).

thf('242',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('243',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['241','242'])).

thf('244',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['213','214'])).

thf('245',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['243','244'])).

thf('246',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['98','101'])).

thf('247',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['245','246'])).

thf('248',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['243','244'])).

thf('249',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['213','214'])).

thf('250',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('251',plain,
    ( sk_C
    = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['247','248','249','250'])).

thf('252',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) @ X8 )
        = ( k5_relat_1 @ X7 @ ( k5_relat_1 @ X6 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('253',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['251','252'])).

thf('254',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('255',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['213','214'])).

thf('256',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['253','254','255'])).

thf('257',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['240','256'])).

thf('258',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('259',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['213','214'])).

thf('260',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['257','258','259','260','261'])).

thf('263',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['239','262'])).

thf('264',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['213','214'])).

thf('265',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('266',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['263','264','265'])).

thf('267',plain,(
    v1_funct_2 @ sk_C @ sk_A_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('268',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('269',plain,
    ( ( sk_B != sk_B )
    | ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A_1 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['236','237','238','266','267','268'])).

thf('270',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A_1 ) ) ),
    inference(simplify,[status(thm)],['269'])).

thf('271',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('272',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A_1 ) ),
    inference('simplify_reflect-',[status(thm)],['270','271'])).

thf('273',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A_1 ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['233','272'])).

thf('274',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['213','214'])).

thf('275',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('277',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('278',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('279',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['277','278'])).

thf('280',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['192','197','273','274','275','276','279'])).

thf('281',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A_1 ),
    inference(demod,[status(thm)],['18','19','20','21','22'])).

thf('282',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A_1 ),
    inference(demod,[status(thm)],['18','19','20','21','22'])).

thf('283',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('284',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ sk_A_1 ) )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['282','283'])).

thf('285',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['277','278'])).

thf('286',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ sk_A_1 ) )
    = sk_D ),
    inference(demod,[status(thm)],['284','285'])).

thf('287',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['277','278'])).

thf('288',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('289',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['75','76'])).

thf('290',plain,
    ( ( k2_funct_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['183','280','281','286','287','288','289'])).

thf('291',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('292',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['290','291'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TMbDkUxnNc
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:39:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 8.86/9.10  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 8.86/9.10  % Solved by: fo/fo7.sh
% 8.86/9.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.86/9.10  % done 5893 iterations in 8.633s
% 8.86/9.10  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 8.86/9.10  % SZS output start Refutation
% 8.86/9.10  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 8.86/9.10  thf(sk_D_type, type, sk_D: $i).
% 8.86/9.10  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 8.86/9.10  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 8.86/9.10  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 8.86/9.10  thf(sk_C_type, type, sk_C: $i).
% 8.86/9.10  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 8.86/9.10  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 8.86/9.10  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 8.86/9.10  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 8.86/9.10  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.86/9.10  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 8.86/9.10  thf(sk_A_1_type, type, sk_A_1: $i).
% 8.86/9.10  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 8.86/9.10  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 8.86/9.10  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 8.86/9.10  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 8.86/9.10  thf(sk_B_type, type, sk_B: $i).
% 8.86/9.10  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 8.86/9.10  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 8.86/9.10  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 8.86/9.10  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 8.86/9.10  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 8.86/9.10  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.86/9.10  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 8.86/9.10  thf(t36_funct_2, conjecture,
% 8.86/9.10    (![A:$i,B:$i,C:$i]:
% 8.86/9.10     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 8.86/9.10         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 8.86/9.10       ( ![D:$i]:
% 8.86/9.10         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 8.86/9.10             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 8.86/9.10           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 8.86/9.10               ( r2_relset_1 @
% 8.86/9.10                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 8.86/9.10                 ( k6_partfun1 @ A ) ) & 
% 8.86/9.10               ( v2_funct_1 @ C ) ) =>
% 8.86/9.10             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 8.86/9.10               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 8.86/9.10  thf(zf_stmt_0, negated_conjecture,
% 8.86/9.10    (~( ![A:$i,B:$i,C:$i]:
% 8.86/9.10        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 8.86/9.10            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 8.86/9.10          ( ![D:$i]:
% 8.86/9.10            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 8.86/9.10                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 8.86/9.10              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 8.86/9.10                  ( r2_relset_1 @
% 8.86/9.10                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 8.86/9.10                    ( k6_partfun1 @ A ) ) & 
% 8.86/9.10                  ( v2_funct_1 @ C ) ) =>
% 8.86/9.10                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 8.86/9.10                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 8.86/9.10    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 8.86/9.10  thf('0', plain,
% 8.86/9.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf(t35_funct_2, axiom,
% 8.86/9.10    (![A:$i,B:$i,C:$i]:
% 8.86/9.10     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 8.86/9.10         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 8.86/9.10       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 8.86/9.10         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 8.86/9.10           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 8.86/9.10             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 8.86/9.10  thf('1', plain,
% 8.86/9.10      (![X56 : $i, X57 : $i, X58 : $i]:
% 8.86/9.10         (((X56) = (k1_xboole_0))
% 8.86/9.10          | ~ (v1_funct_1 @ X57)
% 8.86/9.10          | ~ (v1_funct_2 @ X57 @ X58 @ X56)
% 8.86/9.10          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X56)))
% 8.86/9.10          | ((k5_relat_1 @ X57 @ (k2_funct_1 @ X57)) = (k6_partfun1 @ X58))
% 8.86/9.10          | ~ (v2_funct_1 @ X57)
% 8.86/9.10          | ((k2_relset_1 @ X58 @ X56 @ X57) != (X56)))),
% 8.86/9.10      inference('cnf', [status(esa)], [t35_funct_2])).
% 8.86/9.10  thf('2', plain,
% 8.86/9.10      ((((k2_relset_1 @ sk_B @ sk_A_1 @ sk_D) != (sk_A_1))
% 8.86/9.10        | ~ (v2_funct_1 @ sk_D)
% 8.86/9.10        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 8.86/9.10        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A_1)
% 8.86/9.10        | ~ (v1_funct_1 @ sk_D)
% 8.86/9.10        | ((sk_A_1) = (k1_xboole_0)))),
% 8.86/9.10      inference('sup-', [status(thm)], ['0', '1'])).
% 8.86/9.10  thf('3', plain,
% 8.86/9.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf(redefinition_k2_relset_1, axiom,
% 8.86/9.10    (![A:$i,B:$i,C:$i]:
% 8.86/9.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.86/9.10       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 8.86/9.10  thf('4', plain,
% 8.86/9.10      (![X22 : $i, X23 : $i, X24 : $i]:
% 8.86/9.10         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 8.86/9.10          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 8.86/9.10      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 8.86/9.10  thf('5', plain,
% 8.86/9.10      (((k2_relset_1 @ sk_B @ sk_A_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 8.86/9.10      inference('sup-', [status(thm)], ['3', '4'])).
% 8.86/9.10  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A_1)),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('8', plain,
% 8.86/9.10      ((((k2_relat_1 @ sk_D) != (sk_A_1))
% 8.86/9.10        | ~ (v2_funct_1 @ sk_D)
% 8.86/9.10        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 8.86/9.10        | ((sk_A_1) = (k1_xboole_0)))),
% 8.86/9.10      inference('demod', [status(thm)], ['2', '5', '6', '7'])).
% 8.86/9.10  thf('9', plain, (((sk_A_1) != (k1_xboole_0))),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('10', plain,
% 8.86/9.10      ((((k2_relat_1 @ sk_D) != (sk_A_1))
% 8.86/9.10        | ~ (v2_funct_1 @ sk_D)
% 8.86/9.10        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 8.86/9.10      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 8.86/9.10  thf('11', plain,
% 8.86/9.10      ((r2_relset_1 @ sk_A_1 @ sk_A_1 @ 
% 8.86/9.10        (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D) @ 
% 8.86/9.10        (k6_partfun1 @ sk_A_1))),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('12', plain,
% 8.86/9.10      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf(t24_funct_2, axiom,
% 8.86/9.10    (![A:$i,B:$i,C:$i]:
% 8.86/9.10     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 8.86/9.10         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 8.86/9.10       ( ![D:$i]:
% 8.86/9.10         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 8.86/9.10             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 8.86/9.10           ( ( r2_relset_1 @
% 8.86/9.10               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 8.86/9.10               ( k6_partfun1 @ B ) ) =>
% 8.86/9.10             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 8.86/9.10  thf('13', plain,
% 8.86/9.10      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 8.86/9.10         (~ (v1_funct_1 @ X43)
% 8.86/9.10          | ~ (v1_funct_2 @ X43 @ X44 @ X45)
% 8.86/9.10          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 8.86/9.10          | ~ (r2_relset_1 @ X44 @ X44 @ 
% 8.86/9.10               (k1_partfun1 @ X44 @ X45 @ X45 @ X44 @ X43 @ X46) @ 
% 8.86/9.10               (k6_partfun1 @ X44))
% 8.86/9.10          | ((k2_relset_1 @ X45 @ X44 @ X46) = (X44))
% 8.86/9.10          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 8.86/9.10          | ~ (v1_funct_2 @ X46 @ X45 @ X44)
% 8.86/9.10          | ~ (v1_funct_1 @ X46))),
% 8.86/9.10      inference('cnf', [status(esa)], [t24_funct_2])).
% 8.86/9.10  thf('14', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A_1)
% 8.86/9.10          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))
% 8.86/9.10          | ((k2_relset_1 @ sk_B @ sk_A_1 @ X0) = (sk_A_1))
% 8.86/9.10          | ~ (r2_relset_1 @ sk_A_1 @ sk_A_1 @ 
% 8.86/9.10               (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ X0) @ 
% 8.86/9.10               (k6_partfun1 @ sk_A_1))
% 8.86/9.10          | ~ (v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)
% 8.86/9.10          | ~ (v1_funct_1 @ sk_C))),
% 8.86/9.10      inference('sup-', [status(thm)], ['12', '13'])).
% 8.86/9.10  thf('15', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('16', plain, ((v1_funct_1 @ sk_C)),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('17', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A_1)
% 8.86/9.10          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))
% 8.86/9.10          | ((k2_relset_1 @ sk_B @ sk_A_1 @ X0) = (sk_A_1))
% 8.86/9.10          | ~ (r2_relset_1 @ sk_A_1 @ sk_A_1 @ 
% 8.86/9.10               (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ X0) @ 
% 8.86/9.10               (k6_partfun1 @ sk_A_1)))),
% 8.86/9.10      inference('demod', [status(thm)], ['14', '15', '16'])).
% 8.86/9.10  thf('18', plain,
% 8.86/9.10      ((((k2_relset_1 @ sk_B @ sk_A_1 @ sk_D) = (sk_A_1))
% 8.86/9.10        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))
% 8.86/9.10        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A_1)
% 8.86/9.10        | ~ (v1_funct_1 @ sk_D))),
% 8.86/9.10      inference('sup-', [status(thm)], ['11', '17'])).
% 8.86/9.10  thf('19', plain,
% 8.86/9.10      (((k2_relset_1 @ sk_B @ sk_A_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 8.86/9.10      inference('sup-', [status(thm)], ['3', '4'])).
% 8.86/9.10  thf('20', plain,
% 8.86/9.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('21', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A_1)),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('22', plain, ((v1_funct_1 @ sk_D)),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('23', plain, (((k2_relat_1 @ sk_D) = (sk_A_1))),
% 8.86/9.10      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 8.86/9.10  thf('24', plain,
% 8.86/9.10      ((((sk_A_1) != (sk_A_1))
% 8.86/9.10        | ~ (v2_funct_1 @ sk_D)
% 8.86/9.10        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 8.86/9.10      inference('demod', [status(thm)], ['10', '23'])).
% 8.86/9.10  thf('25', plain,
% 8.86/9.10      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 8.86/9.10        | ~ (v2_funct_1 @ sk_D))),
% 8.86/9.10      inference('simplify', [status(thm)], ['24'])).
% 8.86/9.10  thf('26', plain,
% 8.86/9.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('27', plain,
% 8.86/9.10      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf(redefinition_k1_partfun1, axiom,
% 8.86/9.10    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 8.86/9.10     ( ( ( v1_funct_1 @ E ) & 
% 8.86/9.10         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 8.86/9.10         ( v1_funct_1 @ F ) & 
% 8.86/9.10         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 8.86/9.10       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 8.86/9.10  thf('28', plain,
% 8.86/9.10      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 8.86/9.10         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 8.86/9.10          | ~ (v1_funct_1 @ X36)
% 8.86/9.10          | ~ (v1_funct_1 @ X39)
% 8.86/9.10          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 8.86/9.10          | ((k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39)
% 8.86/9.10              = (k5_relat_1 @ X36 @ X39)))),
% 8.86/9.10      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 8.86/9.10  thf('29', plain,
% 8.86/9.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.86/9.10         (((k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 8.86/9.10            = (k5_relat_1 @ sk_C @ X0))
% 8.86/9.10          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ sk_C))),
% 8.86/9.10      inference('sup-', [status(thm)], ['27', '28'])).
% 8.86/9.10  thf('30', plain, ((v1_funct_1 @ sk_C)),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('31', plain,
% 8.86/9.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.86/9.10         (((k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 8.86/9.10            = (k5_relat_1 @ sk_C @ X0))
% 8.86/9.10          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 8.86/9.10          | ~ (v1_funct_1 @ X0))),
% 8.86/9.10      inference('demod', [status(thm)], ['29', '30'])).
% 8.86/9.10  thf('32', plain,
% 8.86/9.10      ((~ (v1_funct_1 @ sk_D)
% 8.86/9.10        | ((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 8.86/9.10            = (k5_relat_1 @ sk_C @ sk_D)))),
% 8.86/9.10      inference('sup-', [status(thm)], ['26', '31'])).
% 8.86/9.10  thf('33', plain, ((v1_funct_1 @ sk_D)),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('34', plain,
% 8.86/9.10      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 8.86/9.10         = (k5_relat_1 @ sk_C @ sk_D))),
% 8.86/9.10      inference('demod', [status(thm)], ['32', '33'])).
% 8.86/9.10  thf('35', plain,
% 8.86/9.10      ((r2_relset_1 @ sk_A_1 @ sk_A_1 @ 
% 8.86/9.10        (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D) @ 
% 8.86/9.10        (k6_partfun1 @ sk_A_1))),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('36', plain,
% 8.86/9.10      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 8.86/9.10         = (k5_relat_1 @ sk_C @ sk_D))),
% 8.86/9.10      inference('demod', [status(thm)], ['32', '33'])).
% 8.86/9.10  thf('37', plain,
% 8.86/9.10      ((r2_relset_1 @ sk_A_1 @ sk_A_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 8.86/9.10        (k6_partfun1 @ sk_A_1))),
% 8.86/9.10      inference('demod', [status(thm)], ['35', '36'])).
% 8.86/9.10  thf('38', plain,
% 8.86/9.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('39', plain,
% 8.86/9.10      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf(dt_k1_partfun1, axiom,
% 8.86/9.10    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 8.86/9.10     ( ( ( v1_funct_1 @ E ) & 
% 8.86/9.10         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 8.86/9.10         ( v1_funct_1 @ F ) & 
% 8.86/9.10         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 8.86/9.10       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 8.86/9.10         ( m1_subset_1 @
% 8.86/9.10           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 8.86/9.10           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 8.86/9.10  thf('40', plain,
% 8.86/9.10      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 8.86/9.10         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 8.86/9.10          | ~ (v1_funct_1 @ X30)
% 8.86/9.10          | ~ (v1_funct_1 @ X33)
% 8.86/9.10          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 8.86/9.10          | (m1_subset_1 @ (k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33) @ 
% 8.86/9.10             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X35))))),
% 8.86/9.10      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 8.86/9.10  thf('41', plain,
% 8.86/9.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.86/9.10         ((m1_subset_1 @ (k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 8.86/9.10           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ X0)))
% 8.86/9.10          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 8.86/9.10          | ~ (v1_funct_1 @ X1)
% 8.86/9.10          | ~ (v1_funct_1 @ sk_C))),
% 8.86/9.10      inference('sup-', [status(thm)], ['39', '40'])).
% 8.86/9.10  thf('42', plain, ((v1_funct_1 @ sk_C)),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('43', plain,
% 8.86/9.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.86/9.10         ((m1_subset_1 @ (k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 8.86/9.10           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ X0)))
% 8.86/9.10          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 8.86/9.10          | ~ (v1_funct_1 @ X1))),
% 8.86/9.10      inference('demod', [status(thm)], ['41', '42'])).
% 8.86/9.10  thf('44', plain,
% 8.86/9.10      ((~ (v1_funct_1 @ sk_D)
% 8.86/9.10        | (m1_subset_1 @ 
% 8.86/9.10           (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D) @ 
% 8.86/9.10           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_A_1))))),
% 8.86/9.10      inference('sup-', [status(thm)], ['38', '43'])).
% 8.86/9.10  thf('45', plain, ((v1_funct_1 @ sk_D)),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('46', plain,
% 8.86/9.10      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 8.86/9.10         = (k5_relat_1 @ sk_C @ sk_D))),
% 8.86/9.10      inference('demod', [status(thm)], ['32', '33'])).
% 8.86/9.10  thf('47', plain,
% 8.86/9.10      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 8.86/9.10        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_A_1)))),
% 8.86/9.10      inference('demod', [status(thm)], ['44', '45', '46'])).
% 8.86/9.10  thf(redefinition_r2_relset_1, axiom,
% 8.86/9.10    (![A:$i,B:$i,C:$i,D:$i]:
% 8.86/9.10     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 8.86/9.10         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 8.86/9.10       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 8.86/9.10  thf('48', plain,
% 8.86/9.10      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 8.86/9.10         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 8.86/9.10          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 8.86/9.10          | ((X25) = (X28))
% 8.86/9.10          | ~ (r2_relset_1 @ X26 @ X27 @ X25 @ X28))),
% 8.86/9.10      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 8.86/9.10  thf('49', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (~ (r2_relset_1 @ sk_A_1 @ sk_A_1 @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 8.86/9.10          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 8.86/9.10          | ~ (m1_subset_1 @ X0 @ 
% 8.86/9.10               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_A_1))))),
% 8.86/9.10      inference('sup-', [status(thm)], ['47', '48'])).
% 8.86/9.10  thf('50', plain,
% 8.86/9.10      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A_1) @ 
% 8.86/9.10           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_A_1)))
% 8.86/9.10        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A_1)))),
% 8.86/9.10      inference('sup-', [status(thm)], ['37', '49'])).
% 8.86/9.10  thf(t29_relset_1, axiom,
% 8.86/9.10    (![A:$i]:
% 8.86/9.10     ( m1_subset_1 @
% 8.86/9.10       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 8.86/9.10  thf('51', plain,
% 8.86/9.10      (![X29 : $i]:
% 8.86/9.10         (m1_subset_1 @ (k6_relat_1 @ X29) @ 
% 8.86/9.10          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 8.86/9.10      inference('cnf', [status(esa)], [t29_relset_1])).
% 8.86/9.10  thf(redefinition_k6_partfun1, axiom,
% 8.86/9.10    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 8.86/9.10  thf('52', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 8.86/9.10      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 8.86/9.10  thf('53', plain,
% 8.86/9.10      (![X29 : $i]:
% 8.86/9.10         (m1_subset_1 @ (k6_partfun1 @ X29) @ 
% 8.86/9.10          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 8.86/9.10      inference('demod', [status(thm)], ['51', '52'])).
% 8.86/9.10  thf('54', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A_1))),
% 8.86/9.10      inference('demod', [status(thm)], ['50', '53'])).
% 8.86/9.10  thf('55', plain,
% 8.86/9.10      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 8.86/9.10         = (k6_partfun1 @ sk_A_1))),
% 8.86/9.10      inference('demod', [status(thm)], ['34', '54'])).
% 8.86/9.10  thf('56', plain,
% 8.86/9.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf(t30_funct_2, axiom,
% 8.86/9.10    (![A:$i,B:$i,C:$i,D:$i]:
% 8.86/9.10     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 8.86/9.10         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 8.86/9.10       ( ![E:$i]:
% 8.86/9.10         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 8.86/9.10             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 8.86/9.10           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 8.86/9.10               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 8.86/9.10             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 8.86/9.10               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 8.86/9.10  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 8.86/9.10  thf(zf_stmt_2, axiom,
% 8.86/9.10    (![C:$i,B:$i]:
% 8.86/9.10     ( ( zip_tseitin_1 @ C @ B ) =>
% 8.86/9.10       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 8.86/9.10  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 8.86/9.10  thf(zf_stmt_4, axiom,
% 8.86/9.10    (![E:$i,D:$i]:
% 8.86/9.10     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 8.86/9.10  thf(zf_stmt_5, axiom,
% 8.86/9.10    (![A:$i,B:$i,C:$i,D:$i]:
% 8.86/9.10     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 8.86/9.10         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 8.86/9.10       ( ![E:$i]:
% 8.86/9.10         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 8.86/9.10             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 8.86/9.10           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 8.86/9.10               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 8.86/9.10             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 8.86/9.10  thf('57', plain,
% 8.86/9.10      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 8.86/9.10         (~ (v1_funct_1 @ X51)
% 8.86/9.10          | ~ (v1_funct_2 @ X51 @ X52 @ X53)
% 8.86/9.10          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53)))
% 8.86/9.10          | (zip_tseitin_0 @ X51 @ X54)
% 8.86/9.10          | ~ (v2_funct_1 @ (k1_partfun1 @ X55 @ X52 @ X52 @ X53 @ X54 @ X51))
% 8.86/9.10          | (zip_tseitin_1 @ X53 @ X52)
% 8.86/9.10          | ((k2_relset_1 @ X55 @ X52 @ X54) != (X52))
% 8.86/9.10          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X52)))
% 8.86/9.10          | ~ (v1_funct_2 @ X54 @ X55 @ X52)
% 8.86/9.10          | ~ (v1_funct_1 @ X54))),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_5])).
% 8.86/9.10  thf('58', plain,
% 8.86/9.10      (![X0 : $i, X1 : $i]:
% 8.86/9.10         (~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 8.86/9.10          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 8.86/9.10          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 8.86/9.10          | (zip_tseitin_1 @ sk_A_1 @ sk_B)
% 8.86/9.10          | ~ (v2_funct_1 @ 
% 8.86/9.10               (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A_1 @ X0 @ sk_D))
% 8.86/9.10          | (zip_tseitin_0 @ sk_D @ X0)
% 8.86/9.10          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A_1)
% 8.86/9.10          | ~ (v1_funct_1 @ sk_D))),
% 8.86/9.10      inference('sup-', [status(thm)], ['56', '57'])).
% 8.86/9.10  thf('59', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A_1)),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('60', plain, ((v1_funct_1 @ sk_D)),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('61', plain,
% 8.86/9.10      (![X0 : $i, X1 : $i]:
% 8.86/9.10         (~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 8.86/9.10          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 8.86/9.10          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 8.86/9.10          | (zip_tseitin_1 @ sk_A_1 @ sk_B)
% 8.86/9.10          | ~ (v2_funct_1 @ 
% 8.86/9.10               (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A_1 @ X0 @ sk_D))
% 8.86/9.10          | (zip_tseitin_0 @ sk_D @ X0))),
% 8.86/9.10      inference('demod', [status(thm)], ['58', '59', '60'])).
% 8.86/9.10  thf('62', plain,
% 8.86/9.10      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A_1))
% 8.86/9.10        | (zip_tseitin_0 @ sk_D @ sk_C)
% 8.86/9.10        | (zip_tseitin_1 @ sk_A_1 @ sk_B)
% 8.86/9.10        | ((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) != (sk_B))
% 8.86/9.10        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))
% 8.86/9.10        | ~ (v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)
% 8.86/9.10        | ~ (v1_funct_1 @ sk_C))),
% 8.86/9.10      inference('sup-', [status(thm)], ['55', '61'])).
% 8.86/9.10  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 8.86/9.10  thf('63', plain, (![X15 : $i]: (v2_funct_1 @ (k6_relat_1 @ X15))),
% 8.86/9.10      inference('cnf', [status(esa)], [t52_funct_1])).
% 8.86/9.10  thf('64', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 8.86/9.10      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 8.86/9.10  thf('65', plain, (![X15 : $i]: (v2_funct_1 @ (k6_partfun1 @ X15))),
% 8.86/9.10      inference('demod', [status(thm)], ['63', '64'])).
% 8.86/9.10  thf('66', plain, (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (sk_B))),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('67', plain,
% 8.86/9.10      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('68', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('69', plain, ((v1_funct_1 @ sk_C)),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('70', plain,
% 8.86/9.10      (((zip_tseitin_0 @ sk_D @ sk_C)
% 8.86/9.10        | (zip_tseitin_1 @ sk_A_1 @ sk_B)
% 8.86/9.10        | ((sk_B) != (sk_B)))),
% 8.86/9.10      inference('demod', [status(thm)], ['62', '65', '66', '67', '68', '69'])).
% 8.86/9.10  thf('71', plain,
% 8.86/9.10      (((zip_tseitin_1 @ sk_A_1 @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 8.86/9.10      inference('simplify', [status(thm)], ['70'])).
% 8.86/9.10  thf('72', plain,
% 8.86/9.10      (![X49 : $i, X50 : $i]:
% 8.86/9.10         (((X49) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X49 @ X50))),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_2])).
% 8.86/9.10  thf('73', plain,
% 8.86/9.10      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A_1) = (k1_xboole_0)))),
% 8.86/9.10      inference('sup-', [status(thm)], ['71', '72'])).
% 8.86/9.10  thf('74', plain, (((sk_A_1) != (k1_xboole_0))),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('75', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 8.86/9.10      inference('simplify_reflect-', [status(thm)], ['73', '74'])).
% 8.86/9.10  thf('76', plain,
% 8.86/9.10      (![X47 : $i, X48 : $i]:
% 8.86/9.10         ((v2_funct_1 @ X48) | ~ (zip_tseitin_0 @ X48 @ X47))),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_4])).
% 8.86/9.10  thf('77', plain, ((v2_funct_1 @ sk_D)),
% 8.86/9.10      inference('sup-', [status(thm)], ['75', '76'])).
% 8.86/9.10  thf('78', plain,
% 8.86/9.10      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 8.86/9.10      inference('demod', [status(thm)], ['25', '77'])).
% 8.86/9.10  thf(t78_relat_1, axiom,
% 8.86/9.10    (![A:$i]:
% 8.86/9.10     ( ( v1_relat_1 @ A ) =>
% 8.86/9.10       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 8.86/9.10  thf('79', plain,
% 8.86/9.10      (![X11 : $i]:
% 8.86/9.10         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X11)) @ X11) = (X11))
% 8.86/9.10          | ~ (v1_relat_1 @ X11))),
% 8.86/9.10      inference('cnf', [status(esa)], [t78_relat_1])).
% 8.86/9.10  thf('80', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 8.86/9.10      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 8.86/9.10  thf('81', plain,
% 8.86/9.10      (![X11 : $i]:
% 8.86/9.10         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X11)) @ X11) = (X11))
% 8.86/9.10          | ~ (v1_relat_1 @ X11))),
% 8.86/9.10      inference('demod', [status(thm)], ['79', '80'])).
% 8.86/9.10  thf(dt_k2_funct_1, axiom,
% 8.86/9.10    (![A:$i]:
% 8.86/9.10     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 8.86/9.10       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 8.86/9.10         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 8.86/9.10  thf('82', plain,
% 8.86/9.10      (![X14 : $i]:
% 8.86/9.10         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 8.86/9.10          | ~ (v1_funct_1 @ X14)
% 8.86/9.10          | ~ (v1_relat_1 @ X14))),
% 8.86/9.10      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 8.86/9.10  thf(t55_relat_1, axiom,
% 8.86/9.10    (![A:$i]:
% 8.86/9.10     ( ( v1_relat_1 @ A ) =>
% 8.86/9.10       ( ![B:$i]:
% 8.86/9.10         ( ( v1_relat_1 @ B ) =>
% 8.86/9.10           ( ![C:$i]:
% 8.86/9.10             ( ( v1_relat_1 @ C ) =>
% 8.86/9.10               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 8.86/9.10                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 8.86/9.10  thf('83', plain,
% 8.86/9.10      (![X6 : $i, X7 : $i, X8 : $i]:
% 8.86/9.10         (~ (v1_relat_1 @ X6)
% 8.86/9.10          | ((k5_relat_1 @ (k5_relat_1 @ X7 @ X6) @ X8)
% 8.86/9.10              = (k5_relat_1 @ X7 @ (k5_relat_1 @ X6 @ X8)))
% 8.86/9.10          | ~ (v1_relat_1 @ X8)
% 8.86/9.10          | ~ (v1_relat_1 @ X7))),
% 8.86/9.10      inference('cnf', [status(esa)], [t55_relat_1])).
% 8.86/9.10  thf('84', plain,
% 8.86/9.10      (![X14 : $i]:
% 8.86/9.10         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 8.86/9.10          | ~ (v1_funct_1 @ X14)
% 8.86/9.10          | ~ (v1_relat_1 @ X14))),
% 8.86/9.10      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 8.86/9.10  thf(t55_funct_1, axiom,
% 8.86/9.10    (![A:$i]:
% 8.86/9.10     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 8.86/9.10       ( ( v2_funct_1 @ A ) =>
% 8.86/9.10         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 8.86/9.10           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 8.86/9.10  thf('85', plain,
% 8.86/9.10      (![X16 : $i]:
% 8.86/9.10         (~ (v2_funct_1 @ X16)
% 8.86/9.10          | ((k2_relat_1 @ X16) = (k1_relat_1 @ (k2_funct_1 @ X16)))
% 8.86/9.10          | ~ (v1_funct_1 @ X16)
% 8.86/9.10          | ~ (v1_relat_1 @ X16))),
% 8.86/9.10      inference('cnf', [status(esa)], [t55_funct_1])).
% 8.86/9.10  thf(dt_k2_subset_1, axiom,
% 8.86/9.10    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 8.86/9.10  thf('86', plain,
% 8.86/9.10      (![X2 : $i]: (m1_subset_1 @ (k2_subset_1 @ X2) @ (k1_zfmisc_1 @ X2))),
% 8.86/9.10      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 8.86/9.10  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 8.86/9.10  thf('87', plain, (![X1 : $i]: ((k2_subset_1 @ X1) = (X1))),
% 8.86/9.10      inference('cnf', [status(esa)], [d4_subset_1])).
% 8.86/9.10  thf('88', plain, (![X2 : $i]: (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X2))),
% 8.86/9.10      inference('demod', [status(thm)], ['86', '87'])).
% 8.86/9.10  thf(t3_subset, axiom,
% 8.86/9.10    (![A:$i,B:$i]:
% 8.86/9.10     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 8.86/9.10  thf('89', plain,
% 8.86/9.10      (![X3 : $i, X4 : $i]:
% 8.86/9.10         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 8.86/9.10      inference('cnf', [status(esa)], [t3_subset])).
% 8.86/9.10  thf('90', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 8.86/9.10      inference('sup-', [status(thm)], ['88', '89'])).
% 8.86/9.10  thf(t79_relat_1, axiom,
% 8.86/9.10    (![A:$i,B:$i]:
% 8.86/9.10     ( ( v1_relat_1 @ B ) =>
% 8.86/9.10       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 8.86/9.10         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 8.86/9.10  thf('91', plain,
% 8.86/9.10      (![X12 : $i, X13 : $i]:
% 8.86/9.10         (~ (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 8.86/9.10          | ((k5_relat_1 @ X12 @ (k6_relat_1 @ X13)) = (X12))
% 8.86/9.10          | ~ (v1_relat_1 @ X12))),
% 8.86/9.10      inference('cnf', [status(esa)], [t79_relat_1])).
% 8.86/9.10  thf('92', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 8.86/9.10      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 8.86/9.10  thf('93', plain,
% 8.86/9.10      (![X12 : $i, X13 : $i]:
% 8.86/9.10         (~ (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 8.86/9.10          | ((k5_relat_1 @ X12 @ (k6_partfun1 @ X13)) = (X12))
% 8.86/9.10          | ~ (v1_relat_1 @ X12))),
% 8.86/9.10      inference('demod', [status(thm)], ['91', '92'])).
% 8.86/9.10  thf('94', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (~ (v1_relat_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) = (X0)))),
% 8.86/9.10      inference('sup-', [status(thm)], ['90', '93'])).
% 8.86/9.10  thf('95', plain,
% 8.86/9.10      (![X11 : $i]:
% 8.86/9.10         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X11)) @ X11) = (X11))
% 8.86/9.10          | ~ (v1_relat_1 @ X11))),
% 8.86/9.10      inference('demod', [status(thm)], ['79', '80'])).
% 8.86/9.10  thf('96', plain,
% 8.86/9.10      (![X6 : $i, X7 : $i, X8 : $i]:
% 8.86/9.10         (~ (v1_relat_1 @ X6)
% 8.86/9.10          | ((k5_relat_1 @ (k5_relat_1 @ X7 @ X6) @ X8)
% 8.86/9.10              = (k5_relat_1 @ X7 @ (k5_relat_1 @ X6 @ X8)))
% 8.86/9.10          | ~ (v1_relat_1 @ X8)
% 8.86/9.10          | ~ (v1_relat_1 @ X7))),
% 8.86/9.10      inference('cnf', [status(esa)], [t55_relat_1])).
% 8.86/9.10  thf('97', plain,
% 8.86/9.10      (![X0 : $i, X1 : $i]:
% 8.86/9.10         (((k5_relat_1 @ X0 @ X1)
% 8.86/9.10            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 8.86/9.10               (k5_relat_1 @ X0 @ X1)))
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 8.86/9.10          | ~ (v1_relat_1 @ X1)
% 8.86/9.10          | ~ (v1_relat_1 @ X0))),
% 8.86/9.10      inference('sup+', [status(thm)], ['95', '96'])).
% 8.86/9.10  thf('98', plain,
% 8.86/9.10      (![X0 : $i, X1 : $i]:
% 8.86/9.10         (~ (v1_relat_1 @ X1)
% 8.86/9.10          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ X0 @ X1)
% 8.86/9.10              = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 8.86/9.10                 (k5_relat_1 @ X0 @ X1))))),
% 8.86/9.10      inference('simplify', [status(thm)], ['97'])).
% 8.86/9.10  thf('99', plain,
% 8.86/9.10      (![X29 : $i]:
% 8.86/9.10         (m1_subset_1 @ (k6_partfun1 @ X29) @ 
% 8.86/9.10          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 8.86/9.10      inference('demod', [status(thm)], ['51', '52'])).
% 8.86/9.10  thf(cc1_relset_1, axiom,
% 8.86/9.10    (![A:$i,B:$i,C:$i]:
% 8.86/9.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.86/9.10       ( v1_relat_1 @ C ) ))).
% 8.86/9.10  thf('100', plain,
% 8.86/9.10      (![X19 : $i, X20 : $i, X21 : $i]:
% 8.86/9.10         ((v1_relat_1 @ X19)
% 8.86/9.10          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 8.86/9.10      inference('cnf', [status(esa)], [cc1_relset_1])).
% 8.86/9.10  thf('101', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 8.86/9.10      inference('sup-', [status(thm)], ['99', '100'])).
% 8.86/9.10  thf('102', plain,
% 8.86/9.10      (![X0 : $i, X1 : $i]:
% 8.86/9.10         (~ (v1_relat_1 @ X1)
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ X0 @ X1)
% 8.86/9.10              = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 8.86/9.10                 (k5_relat_1 @ X0 @ X1))))),
% 8.86/9.10      inference('demod', [status(thm)], ['98', '101'])).
% 8.86/9.10  thf('103', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 8.86/9.10            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0))))),
% 8.86/9.10      inference('sup+', [status(thm)], ['94', '102'])).
% 8.86/9.10  thf('104', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 8.86/9.10      inference('sup-', [status(thm)], ['99', '100'])).
% 8.86/9.10  thf('105', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 8.86/9.10            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0))),
% 8.86/9.10      inference('demod', [status(thm)], ['103', '104'])).
% 8.86/9.10  thf('106', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (~ (v1_relat_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 8.86/9.10              = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0)))),
% 8.86/9.10      inference('simplify', [status(thm)], ['105'])).
% 8.86/9.10  thf('107', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (((k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 8.86/9.10            (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 8.86/9.10            = (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 8.86/9.10               (k2_funct_1 @ X0)))
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 8.86/9.10      inference('sup+', [status(thm)], ['85', '106'])).
% 8.86/9.10  thf('108', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 8.86/9.10              (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 8.86/9.10              = (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 8.86/9.10                 (k2_funct_1 @ X0))))),
% 8.86/9.10      inference('sup-', [status(thm)], ['84', '107'])).
% 8.86/9.10  thf('109', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (((k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 8.86/9.10            (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 8.86/9.10            = (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 8.86/9.10               (k2_funct_1 @ X0)))
% 8.86/9.10          | ~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0))),
% 8.86/9.10      inference('simplify', [status(thm)], ['108'])).
% 8.86/9.10  thf('110', plain,
% 8.86/9.10      (![X14 : $i]:
% 8.86/9.10         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 8.86/9.10          | ~ (v1_funct_1 @ X14)
% 8.86/9.10          | ~ (v1_relat_1 @ X14))),
% 8.86/9.10      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 8.86/9.10  thf(t61_funct_1, axiom,
% 8.86/9.10    (![A:$i]:
% 8.86/9.10     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 8.86/9.10       ( ( v2_funct_1 @ A ) =>
% 8.86/9.10         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 8.86/9.10             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 8.86/9.10           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 8.86/9.10             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 8.86/9.10  thf('111', plain,
% 8.86/9.10      (![X18 : $i]:
% 8.86/9.10         (~ (v2_funct_1 @ X18)
% 8.86/9.10          | ((k5_relat_1 @ (k2_funct_1 @ X18) @ X18)
% 8.86/9.10              = (k6_relat_1 @ (k2_relat_1 @ X18)))
% 8.86/9.10          | ~ (v1_funct_1 @ X18)
% 8.86/9.10          | ~ (v1_relat_1 @ X18))),
% 8.86/9.10      inference('cnf', [status(esa)], [t61_funct_1])).
% 8.86/9.10  thf('112', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 8.86/9.10      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 8.86/9.10  thf('113', plain,
% 8.86/9.10      (![X18 : $i]:
% 8.86/9.10         (~ (v2_funct_1 @ X18)
% 8.86/9.10          | ((k5_relat_1 @ (k2_funct_1 @ X18) @ X18)
% 8.86/9.10              = (k6_partfun1 @ (k2_relat_1 @ X18)))
% 8.86/9.10          | ~ (v1_funct_1 @ X18)
% 8.86/9.10          | ~ (v1_relat_1 @ X18))),
% 8.86/9.10      inference('demod', [status(thm)], ['111', '112'])).
% 8.86/9.10  thf('114', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (~ (v1_relat_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 8.86/9.10              = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0)))),
% 8.86/9.10      inference('simplify', [status(thm)], ['105'])).
% 8.86/9.10  thf('115', plain,
% 8.86/9.10      (![X6 : $i, X7 : $i, X8 : $i]:
% 8.86/9.10         (~ (v1_relat_1 @ X6)
% 8.86/9.10          | ((k5_relat_1 @ (k5_relat_1 @ X7 @ X6) @ X8)
% 8.86/9.10              = (k5_relat_1 @ X7 @ (k5_relat_1 @ X6 @ X8)))
% 8.86/9.10          | ~ (v1_relat_1 @ X8)
% 8.86/9.10          | ~ (v1_relat_1 @ X7))),
% 8.86/9.10      inference('cnf', [status(esa)], [t55_relat_1])).
% 8.86/9.10  thf('116', plain,
% 8.86/9.10      (![X0 : $i, X1 : $i]:
% 8.86/9.10         (((k5_relat_1 @ 
% 8.86/9.10            (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) @ X1)
% 8.86/9.10            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 8.86/9.10               (k5_relat_1 @ X0 @ X1)))
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 8.86/9.10          | ~ (v1_relat_1 @ X1)
% 8.86/9.10          | ~ (v1_relat_1 @ X0))),
% 8.86/9.10      inference('sup+', [status(thm)], ['114', '115'])).
% 8.86/9.10  thf('117', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 8.86/9.10      inference('sup-', [status(thm)], ['99', '100'])).
% 8.86/9.10  thf('118', plain,
% 8.86/9.10      (![X0 : $i, X1 : $i]:
% 8.86/9.10         (((k5_relat_1 @ 
% 8.86/9.10            (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) @ X1)
% 8.86/9.10            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 8.86/9.10               (k5_relat_1 @ X0 @ X1)))
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X1)
% 8.86/9.10          | ~ (v1_relat_1 @ X0))),
% 8.86/9.10      inference('demod', [status(thm)], ['116', '117'])).
% 8.86/9.10  thf('119', plain,
% 8.86/9.10      (![X0 : $i, X1 : $i]:
% 8.86/9.10         (~ (v1_relat_1 @ X1)
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ 
% 8.86/9.10              (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) @ X1)
% 8.86/9.10              = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 8.86/9.10                 (k5_relat_1 @ X0 @ X1))))),
% 8.86/9.10      inference('simplify', [status(thm)], ['118'])).
% 8.86/9.10  thf('120', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (((k5_relat_1 @ 
% 8.86/9.10            (k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 8.86/9.10             (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))) @ 
% 8.86/9.10            X0)
% 8.86/9.10            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))) @ 
% 8.86/9.10               (k6_partfun1 @ (k2_relat_1 @ X0))))
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 8.86/9.10          | ~ (v1_relat_1 @ X0))),
% 8.86/9.10      inference('sup+', [status(thm)], ['113', '119'])).
% 8.86/9.10  thf('121', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 8.86/9.10          | ~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ 
% 8.86/9.10              (k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 8.86/9.10               (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))) @ 
% 8.86/9.10              X0)
% 8.86/9.10              = (k5_relat_1 @ 
% 8.86/9.10                 (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))) @ 
% 8.86/9.10                 (k6_partfun1 @ (k2_relat_1 @ X0)))))),
% 8.86/9.10      inference('simplify', [status(thm)], ['120'])).
% 8.86/9.10  thf('122', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ 
% 8.86/9.10              (k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 8.86/9.10               (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))) @ 
% 8.86/9.10              X0)
% 8.86/9.10              = (k5_relat_1 @ 
% 8.86/9.10                 (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))) @ 
% 8.86/9.10                 (k6_partfun1 @ (k2_relat_1 @ X0))))
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v2_funct_1 @ X0))),
% 8.86/9.10      inference('sup-', [status(thm)], ['110', '121'])).
% 8.86/9.10  thf('123', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (~ (v2_funct_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ 
% 8.86/9.10              (k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 8.86/9.10               (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))) @ 
% 8.86/9.10              X0)
% 8.86/9.10              = (k5_relat_1 @ 
% 8.86/9.10                 (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))) @ 
% 8.86/9.10                 (k6_partfun1 @ (k2_relat_1 @ X0))))
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0))),
% 8.86/9.10      inference('simplify', [status(thm)], ['122'])).
% 8.86/9.10  thf('124', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (((k5_relat_1 @ 
% 8.86/9.10            (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0)) @ 
% 8.86/9.10            X0)
% 8.86/9.10            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))) @ 
% 8.86/9.10               (k6_partfun1 @ (k2_relat_1 @ X0))))
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v2_funct_1 @ X0))),
% 8.86/9.10      inference('sup+', [status(thm)], ['109', '123'])).
% 8.86/9.10  thf('125', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ 
% 8.86/9.10              (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 8.86/9.10               (k2_funct_1 @ X0)) @ 
% 8.86/9.10              X0)
% 8.86/9.10              = (k5_relat_1 @ 
% 8.86/9.10                 (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))) @ 
% 8.86/9.10                 (k6_partfun1 @ (k2_relat_1 @ X0)))))),
% 8.86/9.10      inference('simplify', [status(thm)], ['124'])).
% 8.86/9.10  thf('126', plain,
% 8.86/9.10      (![X16 : $i]:
% 8.86/9.10         (~ (v2_funct_1 @ X16)
% 8.86/9.10          | ((k2_relat_1 @ X16) = (k1_relat_1 @ (k2_funct_1 @ X16)))
% 8.86/9.10          | ~ (v1_funct_1 @ X16)
% 8.86/9.10          | ~ (v1_relat_1 @ X16))),
% 8.86/9.10      inference('cnf', [status(esa)], [t55_funct_1])).
% 8.86/9.10  thf('127', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ 
% 8.86/9.10              (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 8.86/9.10               (k2_funct_1 @ X0)) @ 
% 8.86/9.10              X0)
% 8.86/9.10              = (k5_relat_1 @ 
% 8.86/9.10                 (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))) @ 
% 8.86/9.10                 (k6_partfun1 @ (k2_relat_1 @ X0)))))),
% 8.86/9.10      inference('simplify', [status(thm)], ['124'])).
% 8.86/9.10  thf('128', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (((k5_relat_1 @ 
% 8.86/9.10            (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0)) @ 
% 8.86/9.10            X0)
% 8.86/9.10            = (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 8.86/9.10               (k6_partfun1 @ (k2_relat_1 @ X0))))
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v2_funct_1 @ X0))),
% 8.86/9.10      inference('sup+', [status(thm)], ['126', '127'])).
% 8.86/9.10  thf(t71_relat_1, axiom,
% 8.86/9.10    (![A:$i]:
% 8.86/9.10     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 8.86/9.10       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 8.86/9.10  thf('129', plain, (![X9 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 8.86/9.10      inference('cnf', [status(esa)], [t71_relat_1])).
% 8.86/9.10  thf('130', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 8.86/9.10      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 8.86/9.10  thf('131', plain, (![X9 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X9)) = (X9))),
% 8.86/9.10      inference('demod', [status(thm)], ['129', '130'])).
% 8.86/9.10  thf('132', plain,
% 8.86/9.10      (![X11 : $i]:
% 8.86/9.10         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X11)) @ X11) = (X11))
% 8.86/9.10          | ~ (v1_relat_1 @ X11))),
% 8.86/9.10      inference('demod', [status(thm)], ['79', '80'])).
% 8.86/9.10  thf('133', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 8.86/9.10            = (k6_partfun1 @ X0))
% 8.86/9.10          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 8.86/9.10      inference('sup+', [status(thm)], ['131', '132'])).
% 8.86/9.10  thf('134', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 8.86/9.10      inference('sup-', [status(thm)], ['99', '100'])).
% 8.86/9.10  thf('135', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 8.86/9.10           = (k6_partfun1 @ X0))),
% 8.86/9.10      inference('demod', [status(thm)], ['133', '134'])).
% 8.86/9.10  thf('136', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (((k5_relat_1 @ 
% 8.86/9.10            (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0)) @ 
% 8.86/9.10            X0) = (k6_partfun1 @ (k2_relat_1 @ X0)))
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v2_funct_1 @ X0))),
% 8.86/9.10      inference('demod', [status(thm)], ['128', '135'])).
% 8.86/9.10  thf('137', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ 
% 8.86/9.10              (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 8.86/9.10               (k2_funct_1 @ X0)) @ 
% 8.86/9.10              X0) = (k6_partfun1 @ (k2_relat_1 @ X0))))),
% 8.86/9.10      inference('simplify', [status(thm)], ['136'])).
% 8.86/9.10  thf('138', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))) @ 
% 8.86/9.10            (k6_partfun1 @ (k2_relat_1 @ X0)))
% 8.86/9.10            = (k6_partfun1 @ (k2_relat_1 @ X0)))
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v2_funct_1 @ X0))),
% 8.86/9.10      inference('sup+', [status(thm)], ['125', '137'])).
% 8.86/9.10  thf('139', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))) @ 
% 8.86/9.10              (k6_partfun1 @ (k2_relat_1 @ X0)))
% 8.86/9.10              = (k6_partfun1 @ (k2_relat_1 @ X0))))),
% 8.86/9.10      inference('simplify', [status(thm)], ['138'])).
% 8.86/9.10  thf('140', plain,
% 8.86/9.10      (![X16 : $i]:
% 8.86/9.10         (~ (v2_funct_1 @ X16)
% 8.86/9.10          | ((k1_relat_1 @ X16) = (k2_relat_1 @ (k2_funct_1 @ X16)))
% 8.86/9.10          | ~ (v1_funct_1 @ X16)
% 8.86/9.10          | ~ (v1_relat_1 @ X16))),
% 8.86/9.10      inference('cnf', [status(esa)], [t55_funct_1])).
% 8.86/9.10  thf('141', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (~ (v2_funct_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ 
% 8.86/9.10              (k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 8.86/9.10               (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))) @ 
% 8.86/9.10              X0)
% 8.86/9.10              = (k5_relat_1 @ 
% 8.86/9.10                 (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))) @ 
% 8.86/9.10                 (k6_partfun1 @ (k2_relat_1 @ X0))))
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0))),
% 8.86/9.10      inference('simplify', [status(thm)], ['122'])).
% 8.86/9.10  thf('142', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (((k5_relat_1 @ 
% 8.86/9.10            (k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0))) @ 
% 8.86/9.10            X0)
% 8.86/9.10            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))) @ 
% 8.86/9.10               (k6_partfun1 @ (k2_relat_1 @ X0))))
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v2_funct_1 @ X0))),
% 8.86/9.10      inference('sup+', [status(thm)], ['140', '141'])).
% 8.86/9.10  thf('143', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ 
% 8.86/9.10              (k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 8.86/9.10               (k6_partfun1 @ (k1_relat_1 @ X0))) @ 
% 8.86/9.10              X0)
% 8.86/9.10              = (k5_relat_1 @ 
% 8.86/9.10                 (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))) @ 
% 8.86/9.10                 (k6_partfun1 @ (k2_relat_1 @ X0)))))),
% 8.86/9.10      inference('simplify', [status(thm)], ['142'])).
% 8.86/9.10  thf('144', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (((k5_relat_1 @ 
% 8.86/9.10            (k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0))) @ 
% 8.86/9.10            X0) = (k6_partfun1 @ (k2_relat_1 @ X0)))
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v2_funct_1 @ X0))),
% 8.86/9.10      inference('sup+', [status(thm)], ['139', '143'])).
% 8.86/9.10  thf('145', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ 
% 8.86/9.10              (k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 8.86/9.10               (k6_partfun1 @ (k1_relat_1 @ X0))) @ 
% 8.86/9.10              X0) = (k6_partfun1 @ (k2_relat_1 @ X0))))),
% 8.86/9.10      inference('simplify', [status(thm)], ['144'])).
% 8.86/9.10  thf('146', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (((k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 8.86/9.10            (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 8.86/9.10            = (k6_partfun1 @ (k2_relat_1 @ X0)))
% 8.86/9.10          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v2_funct_1 @ X0))),
% 8.86/9.10      inference('sup+', [status(thm)], ['83', '145'])).
% 8.86/9.10  thf('147', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 8.86/9.10      inference('sup-', [status(thm)], ['99', '100'])).
% 8.86/9.10  thf('148', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (((k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 8.86/9.10            (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 8.86/9.10            = (k6_partfun1 @ (k2_relat_1 @ X0)))
% 8.86/9.10          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v2_funct_1 @ X0))),
% 8.86/9.10      inference('demod', [status(thm)], ['146', '147'])).
% 8.86/9.10  thf('149', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 8.86/9.10          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 8.86/9.10              (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 8.86/9.10              = (k6_partfun1 @ (k2_relat_1 @ X0))))),
% 8.86/9.10      inference('simplify', [status(thm)], ['148'])).
% 8.86/9.10  thf('150', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 8.86/9.10              (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 8.86/9.10              = (k6_partfun1 @ (k2_relat_1 @ X0)))
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v2_funct_1 @ X0))),
% 8.86/9.10      inference('sup-', [status(thm)], ['82', '149'])).
% 8.86/9.10  thf('151', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (~ (v2_funct_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 8.86/9.10              (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 8.86/9.10              = (k6_partfun1 @ (k2_relat_1 @ X0)))
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0))),
% 8.86/9.10      inference('simplify', [status(thm)], ['150'])).
% 8.86/9.10  thf('152', plain,
% 8.86/9.10      (![X14 : $i]:
% 8.86/9.10         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 8.86/9.10          | ~ (v1_funct_1 @ X14)
% 8.86/9.10          | ~ (v1_relat_1 @ X14))),
% 8.86/9.10      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 8.86/9.10  thf('153', plain,
% 8.86/9.10      (![X18 : $i]:
% 8.86/9.10         (~ (v2_funct_1 @ X18)
% 8.86/9.10          | ((k5_relat_1 @ X18 @ (k2_funct_1 @ X18))
% 8.86/9.10              = (k6_relat_1 @ (k1_relat_1 @ X18)))
% 8.86/9.10          | ~ (v1_funct_1 @ X18)
% 8.86/9.10          | ~ (v1_relat_1 @ X18))),
% 8.86/9.10      inference('cnf', [status(esa)], [t61_funct_1])).
% 8.86/9.10  thf('154', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 8.86/9.10      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 8.86/9.10  thf('155', plain,
% 8.86/9.10      (![X18 : $i]:
% 8.86/9.10         (~ (v2_funct_1 @ X18)
% 8.86/9.10          | ((k5_relat_1 @ X18 @ (k2_funct_1 @ X18))
% 8.86/9.10              = (k6_partfun1 @ (k1_relat_1 @ X18)))
% 8.86/9.10          | ~ (v1_funct_1 @ X18)
% 8.86/9.10          | ~ (v1_relat_1 @ X18))),
% 8.86/9.10      inference('demod', [status(thm)], ['153', '154'])).
% 8.86/9.10  thf('156', plain,
% 8.86/9.10      (![X6 : $i, X7 : $i, X8 : $i]:
% 8.86/9.10         (~ (v1_relat_1 @ X6)
% 8.86/9.10          | ((k5_relat_1 @ (k5_relat_1 @ X7 @ X6) @ X8)
% 8.86/9.10              = (k5_relat_1 @ X7 @ (k5_relat_1 @ X6 @ X8)))
% 8.86/9.10          | ~ (v1_relat_1 @ X8)
% 8.86/9.10          | ~ (v1_relat_1 @ X7))),
% 8.86/9.10      inference('cnf', [status(esa)], [t55_relat_1])).
% 8.86/9.10  thf('157', plain,
% 8.86/9.10      (![X0 : $i, X1 : $i]:
% 8.86/9.10         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X1)
% 8.86/9.10            = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1)))
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X1)
% 8.86/9.10          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 8.86/9.10      inference('sup+', [status(thm)], ['155', '156'])).
% 8.86/9.10  thf('158', plain,
% 8.86/9.10      (![X0 : $i, X1 : $i]:
% 8.86/9.10         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 8.86/9.10          | ~ (v1_relat_1 @ X1)
% 8.86/9.10          | ~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X1)
% 8.86/9.10              = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1))))),
% 8.86/9.10      inference('simplify', [status(thm)], ['157'])).
% 8.86/9.10  thf('159', plain,
% 8.86/9.10      (![X0 : $i, X1 : $i]:
% 8.86/9.10         (~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X1)
% 8.86/9.10              = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1)))
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X1))),
% 8.86/9.10      inference('sup-', [status(thm)], ['152', '158'])).
% 8.86/9.10  thf('160', plain,
% 8.86/9.10      (![X0 : $i, X1 : $i]:
% 8.86/9.10         (~ (v1_relat_1 @ X1)
% 8.86/9.10          | ~ (v2_funct_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X1)
% 8.86/9.10              = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1)))
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0))),
% 8.86/9.10      inference('simplify', [status(thm)], ['159'])).
% 8.86/9.10  thf('161', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 8.86/9.10            (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 8.86/9.10            = (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ 
% 8.86/9.10               (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0)))),
% 8.86/9.10      inference('sup+', [status(thm)], ['151', '160'])).
% 8.86/9.10  thf('162', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (~ (v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 8.86/9.10          | ~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 8.86/9.10              (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 8.86/9.10              = (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))))),
% 8.86/9.10      inference('simplify', [status(thm)], ['161'])).
% 8.86/9.10  thf('163', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 8.86/9.10              (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 8.86/9.10              = (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v2_funct_1 @ X0))),
% 8.86/9.10      inference('sup-', [status(thm)], ['81', '162'])).
% 8.86/9.10  thf('164', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 8.86/9.10              (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 8.86/9.10              = (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))
% 8.86/9.10          | ~ (v1_relat_1 @ X0))),
% 8.86/9.10      inference('simplify', [status(thm)], ['163'])).
% 8.86/9.10  thf('165', plain,
% 8.86/9.10      (![X16 : $i]:
% 8.86/9.10         (~ (v2_funct_1 @ X16)
% 8.86/9.10          | ((k1_relat_1 @ X16) = (k2_relat_1 @ (k2_funct_1 @ X16)))
% 8.86/9.10          | ~ (v1_funct_1 @ X16)
% 8.86/9.10          | ~ (v1_relat_1 @ X16))),
% 8.86/9.10      inference('cnf', [status(esa)], [t55_funct_1])).
% 8.86/9.10  thf('166', plain,
% 8.86/9.10      (![X14 : $i]:
% 8.86/9.10         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 8.86/9.10          | ~ (v1_funct_1 @ X14)
% 8.86/9.10          | ~ (v1_relat_1 @ X14))),
% 8.86/9.10      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 8.86/9.10  thf('167', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (~ (v1_relat_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) = (X0)))),
% 8.86/9.10      inference('sup-', [status(thm)], ['90', '93'])).
% 8.86/9.10  thf('168', plain,
% 8.86/9.10      (![X0 : $i, X1 : $i]:
% 8.86/9.10         (~ (v1_relat_1 @ X1)
% 8.86/9.10          | ~ (v2_funct_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X1)
% 8.86/9.10              = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1)))
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0))),
% 8.86/9.10      inference('simplify', [status(thm)], ['159'])).
% 8.86/9.10  thf('169', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 8.86/9.10            (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 8.86/9.10            = (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 8.86/9.10          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 8.86/9.10      inference('sup+', [status(thm)], ['167', '168'])).
% 8.86/9.10  thf('170', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 8.86/9.10      inference('sup-', [status(thm)], ['99', '100'])).
% 8.86/9.10  thf('171', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 8.86/9.10            (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 8.86/9.10            = (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 8.86/9.10          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v2_funct_1 @ X0))),
% 8.86/9.10      inference('demod', [status(thm)], ['169', '170'])).
% 8.86/9.10  thf('172', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 8.86/9.10              (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 8.86/9.10              = (k5_relat_1 @ X0 @ (k2_funct_1 @ X0))))),
% 8.86/9.10      inference('sup-', [status(thm)], ['166', '171'])).
% 8.86/9.10  thf('173', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 8.86/9.10            (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 8.86/9.10            = (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 8.86/9.10          | ~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0))),
% 8.86/9.10      inference('simplify', [status(thm)], ['172'])).
% 8.86/9.10  thf('174', plain,
% 8.86/9.10      (![X6 : $i, X7 : $i, X8 : $i]:
% 8.86/9.10         (~ (v1_relat_1 @ X6)
% 8.86/9.10          | ((k5_relat_1 @ (k5_relat_1 @ X7 @ X6) @ X8)
% 8.86/9.10              = (k5_relat_1 @ X7 @ (k5_relat_1 @ X6 @ X8)))
% 8.86/9.10          | ~ (v1_relat_1 @ X8)
% 8.86/9.10          | ~ (v1_relat_1 @ X7))),
% 8.86/9.10      inference('cnf', [status(esa)], [t55_relat_1])).
% 8.86/9.10  thf('175', plain,
% 8.86/9.10      (![X0 : $i, X1 : $i]:
% 8.86/9.10         (((k5_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ X1)
% 8.86/9.10            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 8.86/9.10               (k5_relat_1 @ 
% 8.86/9.10                (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))) @ X1)))
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 8.86/9.10          | ~ (v1_relat_1 @ X1)
% 8.86/9.10          | ~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 8.86/9.10      inference('sup+', [status(thm)], ['173', '174'])).
% 8.86/9.10  thf('176', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 8.86/9.10      inference('sup-', [status(thm)], ['99', '100'])).
% 8.86/9.10  thf('177', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 8.86/9.10      inference('sup-', [status(thm)], ['99', '100'])).
% 8.86/9.10  thf('178', plain,
% 8.86/9.10      (![X0 : $i, X1 : $i]:
% 8.86/9.10         (((k5_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ X1)
% 8.86/9.10            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 8.86/9.10               (k5_relat_1 @ 
% 8.86/9.10                (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))) @ X1)))
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X1))),
% 8.86/9.10      inference('demod', [status(thm)], ['175', '176', '177'])).
% 8.86/9.10  thf('179', plain,
% 8.86/9.10      (![X0 : $i, X1 : $i]:
% 8.86/9.10         (((k5_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ X1)
% 8.86/9.10            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 8.86/9.10               (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X1)))
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X1)
% 8.86/9.10          | ~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0))),
% 8.86/9.10      inference('sup+', [status(thm)], ['165', '178'])).
% 8.86/9.10  thf('180', plain,
% 8.86/9.10      (![X0 : $i, X1 : $i]:
% 8.86/9.10         (~ (v1_relat_1 @ X1)
% 8.86/9.10          | ~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ X1)
% 8.86/9.10              = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 8.86/9.10                 (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X1))))),
% 8.86/9.10      inference('simplify', [status(thm)], ['179'])).
% 8.86/9.10  thf('181', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (((k5_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ X0)
% 8.86/9.10            = (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0))),
% 8.86/9.10      inference('sup+', [status(thm)], ['164', '180'])).
% 8.86/9.10  thf('182', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ X0)
% 8.86/9.10              = (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))))),
% 8.86/9.10      inference('simplify', [status(thm)], ['181'])).
% 8.86/9.10  thf('183', plain,
% 8.86/9.10      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 8.86/9.10          = (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))))
% 8.86/9.10        | ~ (v1_relat_1 @ sk_D)
% 8.86/9.10        | ~ (v1_funct_1 @ sk_D)
% 8.86/9.10        | ~ (v2_funct_1 @ sk_D))),
% 8.86/9.10      inference('sup+', [status(thm)], ['78', '182'])).
% 8.86/9.10  thf('184', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A_1))),
% 8.86/9.10      inference('demod', [status(thm)], ['50', '53'])).
% 8.86/9.10  thf('185', plain,
% 8.86/9.10      (![X14 : $i]:
% 8.86/9.10         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 8.86/9.10          | ~ (v1_funct_1 @ X14)
% 8.86/9.10          | ~ (v1_relat_1 @ X14))),
% 8.86/9.10      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 8.86/9.10  thf('186', plain,
% 8.86/9.10      (![X18 : $i]:
% 8.86/9.10         (~ (v2_funct_1 @ X18)
% 8.86/9.10          | ((k5_relat_1 @ (k2_funct_1 @ X18) @ X18)
% 8.86/9.10              = (k6_partfun1 @ (k2_relat_1 @ X18)))
% 8.86/9.10          | ~ (v1_funct_1 @ X18)
% 8.86/9.10          | ~ (v1_relat_1 @ X18))),
% 8.86/9.10      inference('demod', [status(thm)], ['111', '112'])).
% 8.86/9.10  thf('187', plain,
% 8.86/9.10      (![X6 : $i, X7 : $i, X8 : $i]:
% 8.86/9.10         (~ (v1_relat_1 @ X6)
% 8.86/9.10          | ((k5_relat_1 @ (k5_relat_1 @ X7 @ X6) @ X8)
% 8.86/9.10              = (k5_relat_1 @ X7 @ (k5_relat_1 @ X6 @ X8)))
% 8.86/9.10          | ~ (v1_relat_1 @ X8)
% 8.86/9.10          | ~ (v1_relat_1 @ X7))),
% 8.86/9.10      inference('cnf', [status(esa)], [t55_relat_1])).
% 8.86/9.10  thf('188', plain,
% 8.86/9.10      (![X0 : $i, X1 : $i]:
% 8.86/9.10         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 8.86/9.10            = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 8.86/9.10          | ~ (v1_relat_1 @ X1)
% 8.86/9.10          | ~ (v1_relat_1 @ X0))),
% 8.86/9.10      inference('sup+', [status(thm)], ['186', '187'])).
% 8.86/9.10  thf('189', plain,
% 8.86/9.10      (![X0 : $i, X1 : $i]:
% 8.86/9.10         (~ (v1_relat_1 @ X1)
% 8.86/9.10          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 8.86/9.10          | ~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 8.86/9.10              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1))))),
% 8.86/9.10      inference('simplify', [status(thm)], ['188'])).
% 8.86/9.10  thf('190', plain,
% 8.86/9.10      (![X0 : $i, X1 : $i]:
% 8.86/9.10         (~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 8.86/9.10              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X1))),
% 8.86/9.10      inference('sup-', [status(thm)], ['185', '189'])).
% 8.86/9.10  thf('191', plain,
% 8.86/9.10      (![X0 : $i, X1 : $i]:
% 8.86/9.10         (~ (v1_relat_1 @ X1)
% 8.86/9.10          | ~ (v2_funct_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 8.86/9.10              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0))),
% 8.86/9.10      inference('simplify', [status(thm)], ['190'])).
% 8.86/9.10  thf('192', plain,
% 8.86/9.10      ((((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)) @ sk_D)
% 8.86/9.10          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A_1)))
% 8.86/9.10        | ~ (v1_relat_1 @ sk_C)
% 8.86/9.10        | ~ (v1_funct_1 @ sk_C)
% 8.86/9.10        | ~ (v2_funct_1 @ sk_C)
% 8.86/9.10        | ~ (v1_relat_1 @ sk_D))),
% 8.86/9.10      inference('sup+', [status(thm)], ['184', '191'])).
% 8.86/9.10  thf('193', plain,
% 8.86/9.10      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('194', plain,
% 8.86/9.10      (![X22 : $i, X23 : $i, X24 : $i]:
% 8.86/9.10         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 8.86/9.10          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 8.86/9.10      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 8.86/9.10  thf('195', plain,
% 8.86/9.10      (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 8.86/9.10      inference('sup-', [status(thm)], ['193', '194'])).
% 8.86/9.10  thf('196', plain, (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (sk_B))),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('197', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 8.86/9.10      inference('sup+', [status(thm)], ['195', '196'])).
% 8.86/9.10  thf('198', plain,
% 8.86/9.10      (![X14 : $i]:
% 8.86/9.10         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 8.86/9.10          | ~ (v1_funct_1 @ X14)
% 8.86/9.10          | ~ (v1_relat_1 @ X14))),
% 8.86/9.10      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 8.86/9.10  thf('199', plain,
% 8.86/9.10      (![X16 : $i]:
% 8.86/9.10         (~ (v2_funct_1 @ X16)
% 8.86/9.10          | ((k1_relat_1 @ X16) = (k2_relat_1 @ (k2_funct_1 @ X16)))
% 8.86/9.10          | ~ (v1_funct_1 @ X16)
% 8.86/9.10          | ~ (v1_relat_1 @ X16))),
% 8.86/9.10      inference('cnf', [status(esa)], [t55_funct_1])).
% 8.86/9.10  thf('200', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (~ (v1_relat_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) = (X0)))),
% 8.86/9.10      inference('sup-', [status(thm)], ['90', '93'])).
% 8.86/9.10  thf('201', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 8.86/9.10            = (k2_funct_1 @ X0))
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 8.86/9.10      inference('sup+', [status(thm)], ['199', '200'])).
% 8.86/9.10  thf('202', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 8.86/9.10              (k6_partfun1 @ (k1_relat_1 @ X0))) = (k2_funct_1 @ X0)))),
% 8.86/9.10      inference('sup-', [status(thm)], ['198', '201'])).
% 8.86/9.10  thf('203', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 8.86/9.10            = (k2_funct_1 @ X0))
% 8.86/9.10          | ~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0))),
% 8.86/9.10      inference('simplify', [status(thm)], ['202'])).
% 8.86/9.10  thf('204', plain,
% 8.86/9.10      (![X14 : $i]:
% 8.86/9.10         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 8.86/9.10          | ~ (v1_funct_1 @ X14)
% 8.86/9.10          | ~ (v1_relat_1 @ X14))),
% 8.86/9.10      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 8.86/9.10  thf('205', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 8.86/9.10      inference('sup+', [status(thm)], ['195', '196'])).
% 8.86/9.10  thf('206', plain,
% 8.86/9.10      (![X14 : $i]:
% 8.86/9.10         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 8.86/9.10          | ~ (v1_funct_1 @ X14)
% 8.86/9.10          | ~ (v1_relat_1 @ X14))),
% 8.86/9.10      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 8.86/9.10  thf('207', plain,
% 8.86/9.10      (![X16 : $i]:
% 8.86/9.10         (~ (v2_funct_1 @ X16)
% 8.86/9.10          | ((k2_relat_1 @ X16) = (k1_relat_1 @ (k2_funct_1 @ X16)))
% 8.86/9.10          | ~ (v1_funct_1 @ X16)
% 8.86/9.10          | ~ (v1_relat_1 @ X16))),
% 8.86/9.10      inference('cnf', [status(esa)], [t55_funct_1])).
% 8.86/9.10  thf('208', plain,
% 8.86/9.10      (![X11 : $i]:
% 8.86/9.10         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X11)) @ X11) = (X11))
% 8.86/9.10          | ~ (v1_relat_1 @ X11))),
% 8.86/9.10      inference('demod', [status(thm)], ['79', '80'])).
% 8.86/9.10  thf('209', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 8.86/9.10            = (k2_funct_1 @ X0))
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 8.86/9.10      inference('sup+', [status(thm)], ['207', '208'])).
% 8.86/9.10  thf('210', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 8.86/9.10              (k2_funct_1 @ X0)) = (k2_funct_1 @ X0)))),
% 8.86/9.10      inference('sup-', [status(thm)], ['206', '209'])).
% 8.86/9.10  thf('211', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 8.86/9.10            = (k2_funct_1 @ X0))
% 8.86/9.10          | ~ (v2_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_funct_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ X0))),
% 8.86/9.10      inference('simplify', [status(thm)], ['210'])).
% 8.86/9.10  thf('212', plain,
% 8.86/9.10      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 8.86/9.10          = (k2_funct_1 @ sk_C))
% 8.86/9.10        | ~ (v1_relat_1 @ sk_C)
% 8.86/9.10        | ~ (v1_funct_1 @ sk_C)
% 8.86/9.10        | ~ (v2_funct_1 @ sk_C))),
% 8.86/9.10      inference('sup+', [status(thm)], ['205', '211'])).
% 8.86/9.10  thf('213', plain,
% 8.86/9.10      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('214', plain,
% 8.86/9.10      (![X19 : $i, X20 : $i, X21 : $i]:
% 8.86/9.10         ((v1_relat_1 @ X19)
% 8.86/9.10          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 8.86/9.10      inference('cnf', [status(esa)], [cc1_relset_1])).
% 8.86/9.10  thf('215', plain, ((v1_relat_1 @ sk_C)),
% 8.86/9.10      inference('sup-', [status(thm)], ['213', '214'])).
% 8.86/9.10  thf('216', plain, ((v1_funct_1 @ sk_C)),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('217', plain, ((v2_funct_1 @ sk_C)),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('218', plain,
% 8.86/9.10      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 8.86/9.10         = (k2_funct_1 @ sk_C))),
% 8.86/9.10      inference('demod', [status(thm)], ['212', '215', '216', '217'])).
% 8.86/9.10  thf('219', plain,
% 8.86/9.10      (![X6 : $i, X7 : $i, X8 : $i]:
% 8.86/9.10         (~ (v1_relat_1 @ X6)
% 8.86/9.10          | ((k5_relat_1 @ (k5_relat_1 @ X7 @ X6) @ X8)
% 8.86/9.10              = (k5_relat_1 @ X7 @ (k5_relat_1 @ X6 @ X8)))
% 8.86/9.10          | ~ (v1_relat_1 @ X8)
% 8.86/9.10          | ~ (v1_relat_1 @ X7))),
% 8.86/9.10      inference('cnf', [status(esa)], [t55_relat_1])).
% 8.86/9.10  thf('220', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 8.86/9.10            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 8.86/9.10               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 8.86/9.10          | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B))
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 8.86/9.10      inference('sup+', [status(thm)], ['218', '219'])).
% 8.86/9.10  thf('221', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 8.86/9.10      inference('sup-', [status(thm)], ['99', '100'])).
% 8.86/9.10  thf('222', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 8.86/9.10            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 8.86/9.10               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 8.86/9.10      inference('demod', [status(thm)], ['220', '221'])).
% 8.86/9.10  thf('223', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (~ (v1_relat_1 @ sk_C)
% 8.86/9.10          | ~ (v1_funct_1 @ sk_C)
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 8.86/9.10              = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 8.86/9.10                 (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))))),
% 8.86/9.10      inference('sup-', [status(thm)], ['204', '222'])).
% 8.86/9.10  thf('224', plain, ((v1_relat_1 @ sk_C)),
% 8.86/9.10      inference('sup-', [status(thm)], ['213', '214'])).
% 8.86/9.10  thf('225', plain, ((v1_funct_1 @ sk_C)),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('226', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (~ (v1_relat_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 8.86/9.10              = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 8.86/9.10                 (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))))),
% 8.86/9.10      inference('demod', [status(thm)], ['223', '224', '225'])).
% 8.86/9.10  thf('227', plain,
% 8.86/9.10      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 8.86/9.10          (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 8.86/9.10          = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C)))
% 8.86/9.10        | ~ (v1_relat_1 @ sk_C)
% 8.86/9.10        | ~ (v1_funct_1 @ sk_C)
% 8.86/9.10        | ~ (v2_funct_1 @ sk_C)
% 8.86/9.10        | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C))))),
% 8.86/9.10      inference('sup+', [status(thm)], ['203', '226'])).
% 8.86/9.10  thf('228', plain,
% 8.86/9.10      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 8.86/9.10         = (k2_funct_1 @ sk_C))),
% 8.86/9.10      inference('demod', [status(thm)], ['212', '215', '216', '217'])).
% 8.86/9.10  thf('229', plain, ((v1_relat_1 @ sk_C)),
% 8.86/9.10      inference('sup-', [status(thm)], ['213', '214'])).
% 8.86/9.10  thf('230', plain, ((v1_funct_1 @ sk_C)),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('231', plain, ((v2_funct_1 @ sk_C)),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('232', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 8.86/9.10      inference('sup-', [status(thm)], ['99', '100'])).
% 8.86/9.10  thf('233', plain,
% 8.86/9.10      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 8.86/9.10         = (k2_funct_1 @ sk_C))),
% 8.86/9.10      inference('demod', [status(thm)],
% 8.86/9.10                ['227', '228', '229', '230', '231', '232'])).
% 8.86/9.10  thf('234', plain,
% 8.86/9.10      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('235', plain,
% 8.86/9.10      (![X56 : $i, X57 : $i, X58 : $i]:
% 8.86/9.10         (((X56) = (k1_xboole_0))
% 8.86/9.10          | ~ (v1_funct_1 @ X57)
% 8.86/9.10          | ~ (v1_funct_2 @ X57 @ X58 @ X56)
% 8.86/9.10          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X56)))
% 8.86/9.10          | ((k5_relat_1 @ X57 @ (k2_funct_1 @ X57)) = (k6_partfun1 @ X58))
% 8.86/9.10          | ~ (v2_funct_1 @ X57)
% 8.86/9.10          | ((k2_relset_1 @ X58 @ X56 @ X57) != (X56)))),
% 8.86/9.10      inference('cnf', [status(esa)], [t35_funct_2])).
% 8.86/9.10  thf('236', plain,
% 8.86/9.10      ((((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) != (sk_B))
% 8.86/9.10        | ~ (v2_funct_1 @ sk_C)
% 8.86/9.10        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A_1))
% 8.86/9.10        | ~ (v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)
% 8.86/9.10        | ~ (v1_funct_1 @ sk_C)
% 8.86/9.10        | ((sk_B) = (k1_xboole_0)))),
% 8.86/9.10      inference('sup-', [status(thm)], ['234', '235'])).
% 8.86/9.10  thf('237', plain, (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (sk_B))),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('238', plain, ((v2_funct_1 @ sk_C)),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('239', plain,
% 8.86/9.10      (![X14 : $i]:
% 8.86/9.10         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 8.86/9.10          | ~ (v1_funct_1 @ X14)
% 8.86/9.10          | ~ (v1_relat_1 @ X14))),
% 8.86/9.10      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 8.86/9.10  thf('240', plain,
% 8.86/9.10      (![X18 : $i]:
% 8.86/9.10         (~ (v2_funct_1 @ X18)
% 8.86/9.10          | ((k5_relat_1 @ X18 @ (k2_funct_1 @ X18))
% 8.86/9.10              = (k6_partfun1 @ (k1_relat_1 @ X18)))
% 8.86/9.10          | ~ (v1_funct_1 @ X18)
% 8.86/9.10          | ~ (v1_relat_1 @ X18))),
% 8.86/9.10      inference('demod', [status(thm)], ['153', '154'])).
% 8.86/9.10  thf('241', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 8.86/9.10      inference('sup+', [status(thm)], ['195', '196'])).
% 8.86/9.10  thf('242', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (~ (v1_relat_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) = (X0)))),
% 8.86/9.10      inference('sup-', [status(thm)], ['90', '93'])).
% 8.86/9.10  thf('243', plain,
% 8.86/9.10      ((((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))
% 8.86/9.10        | ~ (v1_relat_1 @ sk_C))),
% 8.86/9.10      inference('sup+', [status(thm)], ['241', '242'])).
% 8.86/9.10  thf('244', plain, ((v1_relat_1 @ sk_C)),
% 8.86/9.10      inference('sup-', [status(thm)], ['213', '214'])).
% 8.86/9.10  thf('245', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 8.86/9.10      inference('demod', [status(thm)], ['243', '244'])).
% 8.86/9.10  thf('246', plain,
% 8.86/9.10      (![X0 : $i, X1 : $i]:
% 8.86/9.10         (~ (v1_relat_1 @ X1)
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ X0 @ X1)
% 8.86/9.10              = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 8.86/9.10                 (k5_relat_1 @ X0 @ X1))))),
% 8.86/9.10      inference('demod', [status(thm)], ['98', '101'])).
% 8.86/9.10  thf('247', plain,
% 8.86/9.10      ((((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B))
% 8.86/9.10          = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ sk_C))
% 8.86/9.10        | ~ (v1_relat_1 @ sk_C)
% 8.86/9.10        | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B)))),
% 8.86/9.10      inference('sup+', [status(thm)], ['245', '246'])).
% 8.86/9.10  thf('248', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 8.86/9.10      inference('demod', [status(thm)], ['243', '244'])).
% 8.86/9.10  thf('249', plain, ((v1_relat_1 @ sk_C)),
% 8.86/9.10      inference('sup-', [status(thm)], ['213', '214'])).
% 8.86/9.10  thf('250', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 8.86/9.10      inference('sup-', [status(thm)], ['99', '100'])).
% 8.86/9.10  thf('251', plain,
% 8.86/9.10      (((sk_C) = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ sk_C))),
% 8.86/9.10      inference('demod', [status(thm)], ['247', '248', '249', '250'])).
% 8.86/9.10  thf('252', plain,
% 8.86/9.10      (![X6 : $i, X7 : $i, X8 : $i]:
% 8.86/9.10         (~ (v1_relat_1 @ X6)
% 8.86/9.10          | ((k5_relat_1 @ (k5_relat_1 @ X7 @ X6) @ X8)
% 8.86/9.10              = (k5_relat_1 @ X7 @ (k5_relat_1 @ X6 @ X8)))
% 8.86/9.10          | ~ (v1_relat_1 @ X8)
% 8.86/9.10          | ~ (v1_relat_1 @ X7))),
% 8.86/9.10      inference('cnf', [status(esa)], [t55_relat_1])).
% 8.86/9.10  thf('253', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (((k5_relat_1 @ sk_C @ X0)
% 8.86/9.10            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ 
% 8.86/9.10               (k5_relat_1 @ sk_C @ X0)))
% 8.86/9.10          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 8.86/9.10          | ~ (v1_relat_1 @ X0)
% 8.86/9.10          | ~ (v1_relat_1 @ sk_C))),
% 8.86/9.10      inference('sup+', [status(thm)], ['251', '252'])).
% 8.86/9.10  thf('254', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 8.86/9.10      inference('sup-', [status(thm)], ['99', '100'])).
% 8.86/9.10  thf('255', plain, ((v1_relat_1 @ sk_C)),
% 8.86/9.10      inference('sup-', [status(thm)], ['213', '214'])).
% 8.86/9.10  thf('256', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (((k5_relat_1 @ sk_C @ X0)
% 8.86/9.10            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ 
% 8.86/9.10               (k5_relat_1 @ sk_C @ X0)))
% 8.86/9.10          | ~ (v1_relat_1 @ X0))),
% 8.86/9.10      inference('demod', [status(thm)], ['253', '254', '255'])).
% 8.86/9.10  thf('257', plain,
% 8.86/9.10      ((((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 8.86/9.10          = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ 
% 8.86/9.10             (k6_partfun1 @ (k1_relat_1 @ sk_C))))
% 8.86/9.10        | ~ (v1_relat_1 @ sk_C)
% 8.86/9.10        | ~ (v1_funct_1 @ sk_C)
% 8.86/9.10        | ~ (v2_funct_1 @ sk_C)
% 8.86/9.10        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 8.86/9.10      inference('sup+', [status(thm)], ['240', '256'])).
% 8.86/9.10  thf('258', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 8.86/9.10           = (k6_partfun1 @ X0))),
% 8.86/9.10      inference('demod', [status(thm)], ['133', '134'])).
% 8.86/9.10  thf('259', plain, ((v1_relat_1 @ sk_C)),
% 8.86/9.10      inference('sup-', [status(thm)], ['213', '214'])).
% 8.86/9.10  thf('260', plain, ((v1_funct_1 @ sk_C)),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('261', plain, ((v2_funct_1 @ sk_C)),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('262', plain,
% 8.86/9.10      ((((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 8.86/9.10          = (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 8.86/9.10        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 8.86/9.10      inference('demod', [status(thm)], ['257', '258', '259', '260', '261'])).
% 8.86/9.10  thf('263', plain,
% 8.86/9.10      ((~ (v1_relat_1 @ sk_C)
% 8.86/9.10        | ~ (v1_funct_1 @ sk_C)
% 8.86/9.10        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 8.86/9.10            = (k6_partfun1 @ (k1_relat_1 @ sk_C))))),
% 8.86/9.10      inference('sup-', [status(thm)], ['239', '262'])).
% 8.86/9.10  thf('264', plain, ((v1_relat_1 @ sk_C)),
% 8.86/9.10      inference('sup-', [status(thm)], ['213', '214'])).
% 8.86/9.10  thf('265', plain, ((v1_funct_1 @ sk_C)),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('266', plain,
% 8.86/9.10      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 8.86/9.10         = (k6_partfun1 @ (k1_relat_1 @ sk_C)))),
% 8.86/9.10      inference('demod', [status(thm)], ['263', '264', '265'])).
% 8.86/9.10  thf('267', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('268', plain, ((v1_funct_1 @ sk_C)),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('269', plain,
% 8.86/9.10      ((((sk_B) != (sk_B))
% 8.86/9.10        | ((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A_1))
% 8.86/9.10        | ((sk_B) = (k1_xboole_0)))),
% 8.86/9.10      inference('demod', [status(thm)],
% 8.86/9.10                ['236', '237', '238', '266', '267', '268'])).
% 8.86/9.10  thf('270', plain,
% 8.86/9.10      ((((sk_B) = (k1_xboole_0))
% 8.86/9.10        | ((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A_1)))),
% 8.86/9.10      inference('simplify', [status(thm)], ['269'])).
% 8.86/9.10  thf('271', plain, (((sk_B) != (k1_xboole_0))),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('272', plain,
% 8.86/9.10      (((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A_1))),
% 8.86/9.10      inference('simplify_reflect-', [status(thm)], ['270', '271'])).
% 8.86/9.10  thf('273', plain,
% 8.86/9.10      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A_1))
% 8.86/9.10         = (k2_funct_1 @ sk_C))),
% 8.86/9.10      inference('demod', [status(thm)], ['233', '272'])).
% 8.86/9.10  thf('274', plain, ((v1_relat_1 @ sk_C)),
% 8.86/9.10      inference('sup-', [status(thm)], ['213', '214'])).
% 8.86/9.10  thf('275', plain, ((v1_funct_1 @ sk_C)),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('276', plain, ((v2_funct_1 @ sk_C)),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('277', plain,
% 8.86/9.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('278', plain,
% 8.86/9.10      (![X19 : $i, X20 : $i, X21 : $i]:
% 8.86/9.10         ((v1_relat_1 @ X19)
% 8.86/9.10          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 8.86/9.10      inference('cnf', [status(esa)], [cc1_relset_1])).
% 8.86/9.10  thf('279', plain, ((v1_relat_1 @ sk_D)),
% 8.86/9.10      inference('sup-', [status(thm)], ['277', '278'])).
% 8.86/9.10  thf('280', plain,
% 8.86/9.10      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (k2_funct_1 @ sk_C))),
% 8.86/9.10      inference('demod', [status(thm)],
% 8.86/9.10                ['192', '197', '273', '274', '275', '276', '279'])).
% 8.86/9.10  thf('281', plain, (((k2_relat_1 @ sk_D) = (sk_A_1))),
% 8.86/9.10      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 8.86/9.10  thf('282', plain, (((k2_relat_1 @ sk_D) = (sk_A_1))),
% 8.86/9.10      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 8.86/9.10  thf('283', plain,
% 8.86/9.10      (![X0 : $i]:
% 8.86/9.10         (~ (v1_relat_1 @ X0)
% 8.86/9.10          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) = (X0)))),
% 8.86/9.10      inference('sup-', [status(thm)], ['90', '93'])).
% 8.86/9.10  thf('284', plain,
% 8.86/9.10      ((((k5_relat_1 @ sk_D @ (k6_partfun1 @ sk_A_1)) = (sk_D))
% 8.86/9.10        | ~ (v1_relat_1 @ sk_D))),
% 8.86/9.10      inference('sup+', [status(thm)], ['282', '283'])).
% 8.86/9.10  thf('285', plain, ((v1_relat_1 @ sk_D)),
% 8.86/9.10      inference('sup-', [status(thm)], ['277', '278'])).
% 8.86/9.10  thf('286', plain, (((k5_relat_1 @ sk_D @ (k6_partfun1 @ sk_A_1)) = (sk_D))),
% 8.86/9.10      inference('demod', [status(thm)], ['284', '285'])).
% 8.86/9.10  thf('287', plain, ((v1_relat_1 @ sk_D)),
% 8.86/9.10      inference('sup-', [status(thm)], ['277', '278'])).
% 8.86/9.10  thf('288', plain, ((v1_funct_1 @ sk_D)),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('289', plain, ((v2_funct_1 @ sk_D)),
% 8.86/9.10      inference('sup-', [status(thm)], ['75', '76'])).
% 8.86/9.10  thf('290', plain, (((k2_funct_1 @ sk_C) = (sk_D))),
% 8.86/9.10      inference('demod', [status(thm)],
% 8.86/9.10                ['183', '280', '281', '286', '287', '288', '289'])).
% 8.86/9.10  thf('291', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 8.86/9.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.86/9.10  thf('292', plain, ($false),
% 8.86/9.10      inference('simplify_reflect-', [status(thm)], ['290', '291'])).
% 8.86/9.10  
% 8.86/9.10  % SZS output end Refutation
% 8.86/9.10  
% 8.86/9.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

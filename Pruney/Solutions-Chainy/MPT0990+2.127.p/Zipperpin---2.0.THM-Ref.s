%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Krhk0kbxLQ

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:16 EST 2020

% Result     : Theorem 2.83s
% Output     : Refutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :  304 (1014 expanded)
%              Number of leaves         :   53 ( 324 expanded)
%              Depth                    :   29
%              Number of atoms          : 2779 (22653 expanded)
%              Number of equality atoms :  181 (1551 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k1_relat_1 @ X18 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('6',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
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

thf('9',plain,(
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

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('20',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['6','19'])).

thf('21',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','20','21','22'])).

thf('24',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
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

thf('29',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( ( k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39 )
        = ( k5_relat_1 @ X36 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('38',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

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
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X35 ) ) ) ) ),
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
    inference(demod,[status(thm)],['33','34'])).

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
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( X25 = X28 )
      | ~ ( r2_relset_1 @ X26 @ X27 @ X25 @ X28 ) ) ),
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
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('53',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('54',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['35','55'])).

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
    ! [X17: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('65',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('66',plain,(
    ! [X17: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X17 ) ) ),
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
    ! [X49: $i,X50: $i] :
      ( ( X49 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X49 @ X50 ) ) ),
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
    ! [X47: $i,X48: $i] :
      ( ( v2_funct_1 @ X48 )
      | ~ ( zip_tseitin_0 @ X48 @ X47 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('78',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['26','78'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('80',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('81',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('82',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('83',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relat_1 @ X18 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('84',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('85',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v4_relat_1 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('87',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v4_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k6_partfun1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('90',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('91',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X16 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('92',plain,(
    ! [X11: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('93',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('94',plain,(
    ! [X11: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X11 ) )
      = X11 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['88','91','94'])).

thf('96',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ( v4_relat_1 @ X2 @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['83','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['82','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v4_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf(t47_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('105',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X6 @ X7 ) )
        = ( k2_relat_1 @ X7 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X7 ) @ ( k2_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['80','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ sk_B ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['79','109'])).

thf('111',plain,(
    ! [X12: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('112',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('113',plain,(
    ! [X12: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X12 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('116',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('117',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('118',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['76','77'])).

thf('121',plain,
    ( sk_B
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['110','113','118','119','120'])).

thf('122',plain,
    ( ( sk_B
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['0','121'])).

thf('123',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['116','117'])).

thf('124',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['76','77'])).

thf('126',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['122','123','124','125'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('127',plain,(
    ! [X13: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X13 ) ) @ X13 )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('128',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('129',plain,(
    ! [X13: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X13 ) ) @ X13 )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['126','129'])).

thf('131',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('132',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('133',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ( X56 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X57 )
      | ~ ( v1_funct_2 @ X57 @ X58 @ X56 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X56 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X57 ) @ X57 )
        = ( k6_partfun1 @ X56 ) )
      | ~ ( v2_funct_1 @ X57 )
      | ( ( k2_relset_1 @ X58 @ X56 @ X57 )
       != X56 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('135',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['135','136','137','138','139'])).

thf('141',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['141','142'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('144',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) @ X10 )
        = ( k5_relat_1 @ X9 @ ( k5_relat_1 @ X8 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('148',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('150',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['145','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['132','151'])).

thf('153',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['148','149'])).

thf('154',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['152','153','154'])).

thf('156',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['131','155'])).

thf('157',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k1_relat_1 @ X18 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('158',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('159',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relat_1 @ X18 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('160',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('161',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('163',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('167',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['165','166'])).

thf('168',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['148','149'])).

thf('169',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['167','168','169','170'])).

thf('172',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v4_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('173',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['160','173'])).

thf('175',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['148','149'])).

thf('176',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['174','175','176'])).

thf('178',plain,(
    ! [X12: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X12 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('179',plain,(
    ! [X11: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X11 ) )
      = X11 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('180',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X6 @ X7 ) )
        = ( k2_relat_1 @ X7 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X7 ) @ ( k2_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X16 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('183',plain,(
    ! [X12: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X12 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('184',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_relat_1 @ X1 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['181','182','183'])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X1 ) ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['178','184'])).

thf('186',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X16 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X1 ) ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['185','186'])).

thf('188',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['177','187'])).

thf('189',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) ) )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['159','188'])).

thf('190',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['163','164'])).

thf('191',plain,(
    ! [X11: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X11 ) )
      = X11 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('192',plain,(
    ! [X13: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X13 ) ) @ X13 )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['191','192'])).

thf('194',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X16 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X12: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X12 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('197',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['148','149'])).

thf('198',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['189','190','195','196','197','198','199'])).

thf('201',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['163','164'])).

thf('202',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X6 @ X7 ) )
        = ( k2_relat_1 @ X7 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X7 ) @ ( k2_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('203',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['148','149'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['203','204'])).

thf('206',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['200','205'])).

thf('207',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['88','91','94'])).

thf('208',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['206','207'])).

thf('209',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['158','208'])).

thf('210',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['148','149'])).

thf('211',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['209','210','211'])).

thf('213',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
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

thf('215',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['215','216','217','218','219'])).

thf('221',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['220'])).

thf('222',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['221','222'])).

thf('224',plain,(
    ! [X12: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X12 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('225',plain,
    ( sk_A
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['212','223','224'])).

thf('226',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['157','225'])).

thf('227',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['148','149'])).

thf('228',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['226','227','228','229'])).

thf('231',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('232',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k1_relat_1 @ X18 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('233',plain,(
    ! [X14: $i] :
      ( ( ( k5_relat_1 @ X14 @ ( k6_relat_1 @ ( k2_relat_1 @ X14 ) ) )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('234',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('235',plain,(
    ! [X14: $i] :
      ( ( ( k5_relat_1 @ X14 @ ( k6_partfun1 @ ( k2_relat_1 @ X14 ) ) )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['233','234'])).

thf('236',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['232','235'])).

thf('237',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['231','236'])).

thf('238',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['237'])).

thf('239',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['230','238'])).

thf('240',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['148','149'])).

thf('241',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['239','240','241','242'])).

thf('244',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['116','117'])).

thf('245',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['156','243','244'])).

thf('246',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['116','117'])).

thf('247',plain,
    ( ( k2_funct_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['130','245','246'])).

thf('248',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['247','248'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Krhk0kbxLQ
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:36:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.83/3.03  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.83/3.03  % Solved by: fo/fo7.sh
% 2.83/3.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.83/3.03  % done 1775 iterations in 2.568s
% 2.83/3.03  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.83/3.03  % SZS output start Refutation
% 2.83/3.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.83/3.03  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.83/3.03  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.83/3.03  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.83/3.03  thf(sk_D_type, type, sk_D: $i).
% 2.83/3.03  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.83/3.03  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.83/3.03  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.83/3.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.83/3.03  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.83/3.03  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.83/3.03  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.83/3.03  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.83/3.03  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.83/3.03  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.83/3.03  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.83/3.03  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.83/3.03  thf(sk_B_type, type, sk_B: $i).
% 2.83/3.03  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.83/3.03  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.83/3.03  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.83/3.03  thf(sk_C_type, type, sk_C: $i).
% 2.83/3.03  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.83/3.03  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.83/3.03  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 2.83/3.03  thf(sk_A_type, type, sk_A: $i).
% 2.83/3.03  thf(t55_funct_1, axiom,
% 2.83/3.03    (![A:$i]:
% 2.83/3.03     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.83/3.03       ( ( v2_funct_1 @ A ) =>
% 2.83/3.03         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 2.83/3.03           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.83/3.03  thf('0', plain,
% 2.83/3.03      (![X18 : $i]:
% 2.83/3.03         (~ (v2_funct_1 @ X18)
% 2.83/3.03          | ((k1_relat_1 @ X18) = (k2_relat_1 @ (k2_funct_1 @ X18)))
% 2.83/3.03          | ~ (v1_funct_1 @ X18)
% 2.83/3.03          | ~ (v1_relat_1 @ X18))),
% 2.83/3.03      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.83/3.03  thf(t36_funct_2, conjecture,
% 2.83/3.03    (![A:$i,B:$i,C:$i]:
% 2.83/3.03     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.83/3.03         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.83/3.03       ( ![D:$i]:
% 2.83/3.03         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.83/3.03             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.83/3.03           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.83/3.03               ( r2_relset_1 @
% 2.83/3.03                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.83/3.03                 ( k6_partfun1 @ A ) ) & 
% 2.83/3.03               ( v2_funct_1 @ C ) ) =>
% 2.83/3.03             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.83/3.03               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 2.83/3.03  thf(zf_stmt_0, negated_conjecture,
% 2.83/3.03    (~( ![A:$i,B:$i,C:$i]:
% 2.83/3.03        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.83/3.03            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.83/3.03          ( ![D:$i]:
% 2.83/3.03            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.83/3.03                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.83/3.03              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.83/3.03                  ( r2_relset_1 @
% 2.83/3.03                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.83/3.03                    ( k6_partfun1 @ A ) ) & 
% 2.83/3.03                  ( v2_funct_1 @ C ) ) =>
% 2.83/3.03                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.83/3.03                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 2.83/3.03    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 2.83/3.03  thf('1', plain,
% 2.83/3.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf(t35_funct_2, axiom,
% 2.83/3.03    (![A:$i,B:$i,C:$i]:
% 2.83/3.03     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.83/3.03         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.83/3.03       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 2.83/3.03         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.83/3.03           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 2.83/3.03             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 2.83/3.03  thf('2', plain,
% 2.83/3.03      (![X56 : $i, X57 : $i, X58 : $i]:
% 2.83/3.03         (((X56) = (k1_xboole_0))
% 2.83/3.03          | ~ (v1_funct_1 @ X57)
% 2.83/3.03          | ~ (v1_funct_2 @ X57 @ X58 @ X56)
% 2.83/3.03          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X56)))
% 2.83/3.03          | ((k5_relat_1 @ X57 @ (k2_funct_1 @ X57)) = (k6_partfun1 @ X58))
% 2.83/3.03          | ~ (v2_funct_1 @ X57)
% 2.83/3.03          | ((k2_relset_1 @ X58 @ X56 @ X57) != (X56)))),
% 2.83/3.03      inference('cnf', [status(esa)], [t35_funct_2])).
% 2.83/3.03  thf('3', plain,
% 2.83/3.03      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 2.83/3.03        | ~ (v2_funct_1 @ sk_D)
% 2.83/3.03        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 2.83/3.03        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.83/3.03        | ~ (v1_funct_1 @ sk_D)
% 2.83/3.03        | ((sk_A) = (k1_xboole_0)))),
% 2.83/3.03      inference('sup-', [status(thm)], ['1', '2'])).
% 2.83/3.03  thf('4', plain,
% 2.83/3.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf(redefinition_k2_relset_1, axiom,
% 2.83/3.03    (![A:$i,B:$i,C:$i]:
% 2.83/3.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.83/3.03       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.83/3.03  thf('5', plain,
% 2.83/3.03      (![X22 : $i, X23 : $i, X24 : $i]:
% 2.83/3.03         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 2.83/3.03          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 2.83/3.03      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.83/3.03  thf('6', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.83/3.03      inference('sup-', [status(thm)], ['4', '5'])).
% 2.83/3.03  thf('7', plain,
% 2.83/3.03      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.83/3.03        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.83/3.03        (k6_partfun1 @ sk_A))),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('8', plain,
% 2.83/3.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf(t24_funct_2, axiom,
% 2.83/3.03    (![A:$i,B:$i,C:$i]:
% 2.83/3.03     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.83/3.03         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.83/3.03       ( ![D:$i]:
% 2.83/3.03         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.83/3.03             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.83/3.03           ( ( r2_relset_1 @
% 2.83/3.03               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 2.83/3.03               ( k6_partfun1 @ B ) ) =>
% 2.83/3.03             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 2.83/3.03  thf('9', plain,
% 2.83/3.03      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 2.83/3.03         (~ (v1_funct_1 @ X43)
% 2.83/3.03          | ~ (v1_funct_2 @ X43 @ X44 @ X45)
% 2.83/3.03          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 2.83/3.03          | ~ (r2_relset_1 @ X44 @ X44 @ 
% 2.83/3.03               (k1_partfun1 @ X44 @ X45 @ X45 @ X44 @ X43 @ X46) @ 
% 2.83/3.03               (k6_partfun1 @ X44))
% 2.83/3.03          | ((k2_relset_1 @ X45 @ X44 @ X46) = (X44))
% 2.83/3.03          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 2.83/3.03          | ~ (v1_funct_2 @ X46 @ X45 @ X44)
% 2.83/3.03          | ~ (v1_funct_1 @ X46))),
% 2.83/3.03      inference('cnf', [status(esa)], [t24_funct_2])).
% 2.83/3.03  thf('10', plain,
% 2.83/3.03      (![X0 : $i]:
% 2.83/3.03         (~ (v1_funct_1 @ X0)
% 2.83/3.03          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.83/3.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.83/3.03          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.83/3.03          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.83/3.03               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.83/3.03               (k6_partfun1 @ sk_A))
% 2.83/3.03          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.83/3.03          | ~ (v1_funct_1 @ sk_C))),
% 2.83/3.03      inference('sup-', [status(thm)], ['8', '9'])).
% 2.83/3.03  thf('11', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('12', plain, ((v1_funct_1 @ sk_C)),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('13', plain,
% 2.83/3.03      (![X0 : $i]:
% 2.83/3.03         (~ (v1_funct_1 @ X0)
% 2.83/3.03          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.83/3.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.83/3.03          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.83/3.03          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.83/3.03               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.83/3.03               (k6_partfun1 @ sk_A)))),
% 2.83/3.03      inference('demod', [status(thm)], ['10', '11', '12'])).
% 2.83/3.03  thf('14', plain,
% 2.83/3.03      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 2.83/3.03        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.83/3.03        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.83/3.03        | ~ (v1_funct_1 @ sk_D))),
% 2.83/3.03      inference('sup-', [status(thm)], ['7', '13'])).
% 2.83/3.03  thf('15', plain,
% 2.83/3.03      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.83/3.03      inference('sup-', [status(thm)], ['4', '5'])).
% 2.83/3.03  thf('16', plain,
% 2.83/3.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('17', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('19', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.83/3.03      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 2.83/3.03  thf('20', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))),
% 2.83/3.03      inference('demod', [status(thm)], ['6', '19'])).
% 2.83/3.03  thf('21', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('22', plain, ((v1_funct_1 @ sk_D)),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('23', plain,
% 2.83/3.03      ((((sk_A) != (sk_A))
% 2.83/3.03        | ~ (v2_funct_1 @ sk_D)
% 2.83/3.03        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 2.83/3.03        | ((sk_A) = (k1_xboole_0)))),
% 2.83/3.03      inference('demod', [status(thm)], ['3', '20', '21', '22'])).
% 2.83/3.03  thf('24', plain,
% 2.83/3.03      ((((sk_A) = (k1_xboole_0))
% 2.83/3.03        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 2.83/3.03        | ~ (v2_funct_1 @ sk_D))),
% 2.83/3.03      inference('simplify', [status(thm)], ['23'])).
% 2.83/3.03  thf('25', plain, (((sk_A) != (k1_xboole_0))),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('26', plain,
% 2.83/3.03      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 2.83/3.03        | ~ (v2_funct_1 @ sk_D))),
% 2.83/3.03      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 2.83/3.03  thf('27', plain,
% 2.83/3.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('28', plain,
% 2.83/3.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf(redefinition_k1_partfun1, axiom,
% 2.83/3.03    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.83/3.03     ( ( ( v1_funct_1 @ E ) & 
% 2.83/3.03         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.83/3.03         ( v1_funct_1 @ F ) & 
% 2.83/3.03         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.83/3.03       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.83/3.03  thf('29', plain,
% 2.83/3.03      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 2.83/3.03         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 2.83/3.03          | ~ (v1_funct_1 @ X36)
% 2.83/3.03          | ~ (v1_funct_1 @ X39)
% 2.83/3.03          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 2.83/3.03          | ((k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39)
% 2.83/3.03              = (k5_relat_1 @ X36 @ X39)))),
% 2.83/3.03      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 2.83/3.03  thf('30', plain,
% 2.83/3.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.83/3.03         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.83/3.03            = (k5_relat_1 @ sk_C @ X0))
% 2.83/3.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.83/3.03          | ~ (v1_funct_1 @ X0)
% 2.83/3.03          | ~ (v1_funct_1 @ sk_C))),
% 2.83/3.03      inference('sup-', [status(thm)], ['28', '29'])).
% 2.83/3.03  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('32', plain,
% 2.83/3.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.83/3.03         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.83/3.03            = (k5_relat_1 @ sk_C @ X0))
% 2.83/3.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.83/3.03          | ~ (v1_funct_1 @ X0))),
% 2.83/3.03      inference('demod', [status(thm)], ['30', '31'])).
% 2.83/3.03  thf('33', plain,
% 2.83/3.03      ((~ (v1_funct_1 @ sk_D)
% 2.83/3.03        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.83/3.03            = (k5_relat_1 @ sk_C @ sk_D)))),
% 2.83/3.03      inference('sup-', [status(thm)], ['27', '32'])).
% 2.83/3.03  thf('34', plain, ((v1_funct_1 @ sk_D)),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('35', plain,
% 2.83/3.03      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.83/3.03         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.83/3.03      inference('demod', [status(thm)], ['33', '34'])).
% 2.83/3.03  thf('36', plain,
% 2.83/3.03      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.83/3.03        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.83/3.03        (k6_partfun1 @ sk_A))),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('37', plain,
% 2.83/3.03      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.83/3.03         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.83/3.03      inference('demod', [status(thm)], ['33', '34'])).
% 2.83/3.03  thf('38', plain,
% 2.83/3.03      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 2.83/3.03        (k6_partfun1 @ sk_A))),
% 2.83/3.03      inference('demod', [status(thm)], ['36', '37'])).
% 2.83/3.03  thf('39', plain,
% 2.83/3.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('40', plain,
% 2.83/3.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf(dt_k1_partfun1, axiom,
% 2.83/3.03    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.83/3.03     ( ( ( v1_funct_1 @ E ) & 
% 2.83/3.03         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.83/3.03         ( v1_funct_1 @ F ) & 
% 2.83/3.03         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.83/3.03       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.83/3.03         ( m1_subset_1 @
% 2.83/3.03           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.83/3.03           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.83/3.03  thf('41', plain,
% 2.83/3.03      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 2.83/3.03         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 2.83/3.03          | ~ (v1_funct_1 @ X30)
% 2.83/3.03          | ~ (v1_funct_1 @ X33)
% 2.83/3.03          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 2.83/3.03          | (m1_subset_1 @ (k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33) @ 
% 2.83/3.03             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X35))))),
% 2.83/3.03      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.83/3.03  thf('42', plain,
% 2.83/3.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.83/3.03         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.83/3.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.83/3.03          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.83/3.03          | ~ (v1_funct_1 @ X1)
% 2.83/3.03          | ~ (v1_funct_1 @ sk_C))),
% 2.83/3.03      inference('sup-', [status(thm)], ['40', '41'])).
% 2.83/3.03  thf('43', plain, ((v1_funct_1 @ sk_C)),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('44', plain,
% 2.83/3.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.83/3.03         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.83/3.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.83/3.03          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.83/3.03          | ~ (v1_funct_1 @ X1))),
% 2.83/3.03      inference('demod', [status(thm)], ['42', '43'])).
% 2.83/3.03  thf('45', plain,
% 2.83/3.03      ((~ (v1_funct_1 @ sk_D)
% 2.83/3.03        | (m1_subset_1 @ 
% 2.83/3.03           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.83/3.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.83/3.03      inference('sup-', [status(thm)], ['39', '44'])).
% 2.83/3.03  thf('46', plain, ((v1_funct_1 @ sk_D)),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('47', plain,
% 2.83/3.03      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.83/3.03         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.83/3.03      inference('demod', [status(thm)], ['33', '34'])).
% 2.83/3.03  thf('48', plain,
% 2.83/3.03      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 2.83/3.03        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.83/3.03      inference('demod', [status(thm)], ['45', '46', '47'])).
% 2.83/3.03  thf(redefinition_r2_relset_1, axiom,
% 2.83/3.03    (![A:$i,B:$i,C:$i,D:$i]:
% 2.83/3.03     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.83/3.03         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.83/3.03       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.83/3.03  thf('49', plain,
% 2.83/3.03      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 2.83/3.03         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 2.83/3.03          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 2.83/3.03          | ((X25) = (X28))
% 2.83/3.03          | ~ (r2_relset_1 @ X26 @ X27 @ X25 @ X28))),
% 2.83/3.03      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.83/3.03  thf('50', plain,
% 2.83/3.03      (![X0 : $i]:
% 2.83/3.03         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 2.83/3.03          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 2.83/3.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.83/3.03      inference('sup-', [status(thm)], ['48', '49'])).
% 2.83/3.03  thf('51', plain,
% 2.83/3.03      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 2.83/3.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.83/3.03        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 2.83/3.03      inference('sup-', [status(thm)], ['38', '50'])).
% 2.83/3.03  thf(t29_relset_1, axiom,
% 2.83/3.03    (![A:$i]:
% 2.83/3.03     ( m1_subset_1 @
% 2.83/3.03       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 2.83/3.03  thf('52', plain,
% 2.83/3.03      (![X29 : $i]:
% 2.83/3.03         (m1_subset_1 @ (k6_relat_1 @ X29) @ 
% 2.83/3.03          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 2.83/3.03      inference('cnf', [status(esa)], [t29_relset_1])).
% 2.83/3.03  thf(redefinition_k6_partfun1, axiom,
% 2.83/3.03    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.83/3.03  thf('53', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 2.83/3.03      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.83/3.03  thf('54', plain,
% 2.83/3.03      (![X29 : $i]:
% 2.83/3.03         (m1_subset_1 @ (k6_partfun1 @ X29) @ 
% 2.83/3.03          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 2.83/3.03      inference('demod', [status(thm)], ['52', '53'])).
% 2.83/3.03  thf('55', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 2.83/3.03      inference('demod', [status(thm)], ['51', '54'])).
% 2.83/3.03  thf('56', plain,
% 2.83/3.03      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.83/3.03         = (k6_partfun1 @ sk_A))),
% 2.83/3.03      inference('demod', [status(thm)], ['35', '55'])).
% 2.83/3.03  thf('57', plain,
% 2.83/3.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf(t30_funct_2, axiom,
% 2.83/3.03    (![A:$i,B:$i,C:$i,D:$i]:
% 2.83/3.03     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.83/3.03         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 2.83/3.03       ( ![E:$i]:
% 2.83/3.03         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 2.83/3.03             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 2.83/3.03           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 2.83/3.03               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 2.83/3.03             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 2.83/3.03               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 2.83/3.03  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 2.83/3.03  thf(zf_stmt_2, axiom,
% 2.83/3.03    (![C:$i,B:$i]:
% 2.83/3.03     ( ( zip_tseitin_1 @ C @ B ) =>
% 2.83/3.03       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 2.83/3.03  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 2.83/3.03  thf(zf_stmt_4, axiom,
% 2.83/3.03    (![E:$i,D:$i]:
% 2.83/3.03     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 2.83/3.03  thf(zf_stmt_5, axiom,
% 2.83/3.03    (![A:$i,B:$i,C:$i,D:$i]:
% 2.83/3.03     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.83/3.03         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.83/3.03       ( ![E:$i]:
% 2.83/3.03         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.83/3.03             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.83/3.03           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 2.83/3.03               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 2.83/3.03             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 2.83/3.03  thf('58', plain,
% 2.83/3.03      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 2.83/3.03         (~ (v1_funct_1 @ X51)
% 2.83/3.03          | ~ (v1_funct_2 @ X51 @ X52 @ X53)
% 2.83/3.03          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53)))
% 2.83/3.03          | (zip_tseitin_0 @ X51 @ X54)
% 2.83/3.03          | ~ (v2_funct_1 @ (k1_partfun1 @ X55 @ X52 @ X52 @ X53 @ X54 @ X51))
% 2.83/3.03          | (zip_tseitin_1 @ X53 @ X52)
% 2.83/3.03          | ((k2_relset_1 @ X55 @ X52 @ X54) != (X52))
% 2.83/3.03          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X52)))
% 2.83/3.03          | ~ (v1_funct_2 @ X54 @ X55 @ X52)
% 2.83/3.03          | ~ (v1_funct_1 @ X54))),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.83/3.03  thf('59', plain,
% 2.83/3.03      (![X0 : $i, X1 : $i]:
% 2.83/3.03         (~ (v1_funct_1 @ X0)
% 2.83/3.03          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.83/3.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.83/3.03          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 2.83/3.03          | (zip_tseitin_1 @ sk_A @ sk_B)
% 2.83/3.03          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 2.83/3.03          | (zip_tseitin_0 @ sk_D @ X0)
% 2.83/3.03          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.83/3.03          | ~ (v1_funct_1 @ sk_D))),
% 2.83/3.03      inference('sup-', [status(thm)], ['57', '58'])).
% 2.83/3.03  thf('60', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('61', plain, ((v1_funct_1 @ sk_D)),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('62', plain,
% 2.83/3.03      (![X0 : $i, X1 : $i]:
% 2.83/3.03         (~ (v1_funct_1 @ X0)
% 2.83/3.03          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.83/3.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.83/3.03          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 2.83/3.03          | (zip_tseitin_1 @ sk_A @ sk_B)
% 2.83/3.03          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 2.83/3.03          | (zip_tseitin_0 @ sk_D @ X0))),
% 2.83/3.03      inference('demod', [status(thm)], ['59', '60', '61'])).
% 2.83/3.03  thf('63', plain,
% 2.83/3.03      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 2.83/3.03        | (zip_tseitin_0 @ sk_D @ sk_C)
% 2.83/3.03        | (zip_tseitin_1 @ sk_A @ sk_B)
% 2.83/3.03        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 2.83/3.03        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 2.83/3.03        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.83/3.03        | ~ (v1_funct_1 @ sk_C))),
% 2.83/3.03      inference('sup-', [status(thm)], ['56', '62'])).
% 2.83/3.03  thf(fc4_funct_1, axiom,
% 2.83/3.03    (![A:$i]:
% 2.83/3.03     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 2.83/3.03       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 2.83/3.03  thf('64', plain, (![X17 : $i]: (v2_funct_1 @ (k6_relat_1 @ X17))),
% 2.83/3.03      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.83/3.03  thf('65', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 2.83/3.03      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.83/3.03  thf('66', plain, (![X17 : $i]: (v2_funct_1 @ (k6_partfun1 @ X17))),
% 2.83/3.03      inference('demod', [status(thm)], ['64', '65'])).
% 2.83/3.03  thf('67', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('68', plain,
% 2.83/3.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('69', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('70', plain, ((v1_funct_1 @ sk_C)),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('71', plain,
% 2.83/3.03      (((zip_tseitin_0 @ sk_D @ sk_C)
% 2.83/3.03        | (zip_tseitin_1 @ sk_A @ sk_B)
% 2.83/3.03        | ((sk_B) != (sk_B)))),
% 2.83/3.03      inference('demod', [status(thm)], ['63', '66', '67', '68', '69', '70'])).
% 2.83/3.03  thf('72', plain,
% 2.83/3.03      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 2.83/3.03      inference('simplify', [status(thm)], ['71'])).
% 2.83/3.03  thf('73', plain,
% 2.83/3.03      (![X49 : $i, X50 : $i]:
% 2.83/3.03         (((X49) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X49 @ X50))),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.83/3.03  thf('74', plain,
% 2.83/3.03      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 2.83/3.03      inference('sup-', [status(thm)], ['72', '73'])).
% 2.83/3.03  thf('75', plain, (((sk_A) != (k1_xboole_0))),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('76', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 2.83/3.03      inference('simplify_reflect-', [status(thm)], ['74', '75'])).
% 2.83/3.03  thf('77', plain,
% 2.83/3.03      (![X47 : $i, X48 : $i]:
% 2.83/3.03         ((v2_funct_1 @ X48) | ~ (zip_tseitin_0 @ X48 @ X47))),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_4])).
% 2.83/3.03  thf('78', plain, ((v2_funct_1 @ sk_D)),
% 2.83/3.03      inference('sup-', [status(thm)], ['76', '77'])).
% 2.83/3.03  thf('79', plain,
% 2.83/3.03      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 2.83/3.03      inference('demod', [status(thm)], ['26', '78'])).
% 2.83/3.03  thf(dt_k2_funct_1, axiom,
% 2.83/3.03    (![A:$i]:
% 2.83/3.03     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.83/3.03       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 2.83/3.03         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 2.83/3.03  thf('80', plain,
% 2.83/3.03      (![X15 : $i]:
% 2.83/3.03         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 2.83/3.03          | ~ (v1_funct_1 @ X15)
% 2.83/3.03          | ~ (v1_relat_1 @ X15))),
% 2.83/3.03      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.83/3.03  thf('81', plain,
% 2.83/3.03      (![X15 : $i]:
% 2.83/3.03         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 2.83/3.03          | ~ (v1_funct_1 @ X15)
% 2.83/3.03          | ~ (v1_relat_1 @ X15))),
% 2.83/3.03      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.83/3.03  thf('82', plain,
% 2.83/3.03      (![X15 : $i]:
% 2.83/3.03         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 2.83/3.03          | ~ (v1_funct_1 @ X15)
% 2.83/3.03          | ~ (v1_relat_1 @ X15))),
% 2.83/3.03      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.83/3.03  thf('83', plain,
% 2.83/3.03      (![X18 : $i]:
% 2.83/3.03         (~ (v2_funct_1 @ X18)
% 2.83/3.03          | ((k2_relat_1 @ X18) = (k1_relat_1 @ (k2_funct_1 @ X18)))
% 2.83/3.03          | ~ (v1_funct_1 @ X18)
% 2.83/3.03          | ~ (v1_relat_1 @ X18))),
% 2.83/3.03      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.83/3.03  thf('84', plain,
% 2.83/3.03      (![X29 : $i]:
% 2.83/3.03         (m1_subset_1 @ (k6_partfun1 @ X29) @ 
% 2.83/3.03          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 2.83/3.03      inference('demod', [status(thm)], ['52', '53'])).
% 2.83/3.03  thf(cc2_relset_1, axiom,
% 2.83/3.03    (![A:$i,B:$i,C:$i]:
% 2.83/3.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.83/3.03       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.83/3.03  thf('85', plain,
% 2.83/3.03      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.83/3.03         ((v4_relat_1 @ X19 @ X20)
% 2.83/3.03          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 2.83/3.03      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.83/3.03  thf('86', plain, (![X0 : $i]: (v4_relat_1 @ (k6_partfun1 @ X0) @ X0)),
% 2.83/3.03      inference('sup-', [status(thm)], ['84', '85'])).
% 2.83/3.03  thf(d18_relat_1, axiom,
% 2.83/3.03    (![A:$i,B:$i]:
% 2.83/3.03     ( ( v1_relat_1 @ B ) =>
% 2.83/3.03       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 2.83/3.03  thf('87', plain,
% 2.83/3.03      (![X2 : $i, X3 : $i]:
% 2.83/3.03         (~ (v4_relat_1 @ X2 @ X3)
% 2.83/3.03          | (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 2.83/3.03          | ~ (v1_relat_1 @ X2))),
% 2.83/3.03      inference('cnf', [status(esa)], [d18_relat_1])).
% 2.83/3.03  thf('88', plain,
% 2.83/3.03      (![X0 : $i]:
% 2.83/3.03         (~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 2.83/3.03          | (r1_tarski @ (k1_relat_1 @ (k6_partfun1 @ X0)) @ X0))),
% 2.83/3.03      inference('sup-', [status(thm)], ['86', '87'])).
% 2.83/3.03  thf('89', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 2.83/3.03      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.83/3.03  thf('90', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 2.83/3.03      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.83/3.03  thf('91', plain, (![X16 : $i]: (v1_relat_1 @ (k6_partfun1 @ X16))),
% 2.83/3.03      inference('demod', [status(thm)], ['89', '90'])).
% 2.83/3.03  thf(t71_relat_1, axiom,
% 2.83/3.03    (![A:$i]:
% 2.83/3.03     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 2.83/3.03       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 2.83/3.03  thf('92', plain, (![X11 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 2.83/3.03      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.83/3.03  thf('93', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 2.83/3.03      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.83/3.03  thf('94', plain, (![X11 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X11)) = (X11))),
% 2.83/3.03      inference('demod', [status(thm)], ['92', '93'])).
% 2.83/3.03  thf('95', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 2.83/3.03      inference('demod', [status(thm)], ['88', '91', '94'])).
% 2.83/3.03  thf('96', plain,
% 2.83/3.03      (![X2 : $i, X3 : $i]:
% 2.83/3.03         (~ (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 2.83/3.03          | (v4_relat_1 @ X2 @ X3)
% 2.83/3.03          | ~ (v1_relat_1 @ X2))),
% 2.83/3.03      inference('cnf', [status(esa)], [d18_relat_1])).
% 2.83/3.03  thf('97', plain,
% 2.83/3.03      (![X0 : $i]:
% 2.83/3.03         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 2.83/3.03      inference('sup-', [status(thm)], ['95', '96'])).
% 2.83/3.03  thf('98', plain,
% 2.83/3.03      (![X0 : $i]:
% 2.83/3.03         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 2.83/3.03          | ~ (v1_relat_1 @ X0)
% 2.83/3.03          | ~ (v1_funct_1 @ X0)
% 2.83/3.03          | ~ (v2_funct_1 @ X0)
% 2.83/3.03          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 2.83/3.03      inference('sup+', [status(thm)], ['83', '97'])).
% 2.83/3.03  thf('99', plain,
% 2.83/3.03      (![X0 : $i]:
% 2.83/3.03         (~ (v1_relat_1 @ X0)
% 2.83/3.03          | ~ (v1_funct_1 @ X0)
% 2.83/3.03          | ~ (v2_funct_1 @ X0)
% 2.83/3.03          | ~ (v1_funct_1 @ X0)
% 2.83/3.03          | ~ (v1_relat_1 @ X0)
% 2.83/3.03          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 2.83/3.03      inference('sup-', [status(thm)], ['82', '98'])).
% 2.83/3.03  thf('100', plain,
% 2.83/3.03      (![X0 : $i]:
% 2.83/3.03         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 2.83/3.03          | ~ (v2_funct_1 @ X0)
% 2.83/3.03          | ~ (v1_funct_1 @ X0)
% 2.83/3.03          | ~ (v1_relat_1 @ X0))),
% 2.83/3.03      inference('simplify', [status(thm)], ['99'])).
% 2.83/3.03  thf('101', plain,
% 2.83/3.03      (![X2 : $i, X3 : $i]:
% 2.83/3.03         (~ (v4_relat_1 @ X2 @ X3)
% 2.83/3.03          | (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 2.83/3.03          | ~ (v1_relat_1 @ X2))),
% 2.83/3.03      inference('cnf', [status(esa)], [d18_relat_1])).
% 2.83/3.03  thf('102', plain,
% 2.83/3.03      (![X0 : $i]:
% 2.83/3.03         (~ (v1_relat_1 @ X0)
% 2.83/3.03          | ~ (v1_funct_1 @ X0)
% 2.83/3.03          | ~ (v2_funct_1 @ X0)
% 2.83/3.03          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.83/3.03          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0)))),
% 2.83/3.03      inference('sup-', [status(thm)], ['100', '101'])).
% 2.83/3.03  thf('103', plain,
% 2.83/3.03      (![X0 : $i]:
% 2.83/3.03         (~ (v1_relat_1 @ X0)
% 2.83/3.03          | ~ (v1_funct_1 @ X0)
% 2.83/3.03          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 2.83/3.03          | ~ (v2_funct_1 @ X0)
% 2.83/3.03          | ~ (v1_funct_1 @ X0)
% 2.83/3.03          | ~ (v1_relat_1 @ X0))),
% 2.83/3.03      inference('sup-', [status(thm)], ['81', '102'])).
% 2.83/3.03  thf('104', plain,
% 2.83/3.03      (![X0 : $i]:
% 2.83/3.03         (~ (v2_funct_1 @ X0)
% 2.83/3.03          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 2.83/3.03          | ~ (v1_funct_1 @ X0)
% 2.83/3.03          | ~ (v1_relat_1 @ X0))),
% 2.83/3.03      inference('simplify', [status(thm)], ['103'])).
% 2.83/3.03  thf(t47_relat_1, axiom,
% 2.83/3.03    (![A:$i]:
% 2.83/3.03     ( ( v1_relat_1 @ A ) =>
% 2.83/3.03       ( ![B:$i]:
% 2.83/3.03         ( ( v1_relat_1 @ B ) =>
% 2.83/3.03           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 2.83/3.03             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 2.83/3.03  thf('105', plain,
% 2.83/3.03      (![X6 : $i, X7 : $i]:
% 2.83/3.03         (~ (v1_relat_1 @ X6)
% 2.83/3.03          | ((k2_relat_1 @ (k5_relat_1 @ X6 @ X7)) = (k2_relat_1 @ X7))
% 2.83/3.03          | ~ (r1_tarski @ (k1_relat_1 @ X7) @ (k2_relat_1 @ X6))
% 2.83/3.03          | ~ (v1_relat_1 @ X7))),
% 2.83/3.03      inference('cnf', [status(esa)], [t47_relat_1])).
% 2.83/3.03  thf('106', plain,
% 2.83/3.03      (![X0 : $i]:
% 2.83/3.03         (~ (v1_relat_1 @ X0)
% 2.83/3.03          | ~ (v1_funct_1 @ X0)
% 2.83/3.03          | ~ (v2_funct_1 @ X0)
% 2.83/3.03          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.83/3.03          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 2.83/3.03              = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.83/3.03          | ~ (v1_relat_1 @ X0))),
% 2.83/3.03      inference('sup-', [status(thm)], ['104', '105'])).
% 2.83/3.03  thf('107', plain,
% 2.83/3.03      (![X0 : $i]:
% 2.83/3.03         (((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 2.83/3.03            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.83/3.03          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.83/3.03          | ~ (v2_funct_1 @ X0)
% 2.83/3.03          | ~ (v1_funct_1 @ X0)
% 2.83/3.03          | ~ (v1_relat_1 @ X0))),
% 2.83/3.03      inference('simplify', [status(thm)], ['106'])).
% 2.83/3.03  thf('108', plain,
% 2.83/3.03      (![X0 : $i]:
% 2.83/3.03         (~ (v1_relat_1 @ X0)
% 2.83/3.03          | ~ (v1_funct_1 @ X0)
% 2.83/3.03          | ~ (v1_relat_1 @ X0)
% 2.83/3.03          | ~ (v1_funct_1 @ X0)
% 2.83/3.03          | ~ (v2_funct_1 @ X0)
% 2.83/3.03          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 2.83/3.03              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 2.83/3.03      inference('sup-', [status(thm)], ['80', '107'])).
% 2.83/3.03  thf('109', plain,
% 2.83/3.03      (![X0 : $i]:
% 2.83/3.03         (((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 2.83/3.03            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.83/3.03          | ~ (v2_funct_1 @ X0)
% 2.83/3.03          | ~ (v1_funct_1 @ X0)
% 2.83/3.03          | ~ (v1_relat_1 @ X0))),
% 2.83/3.03      inference('simplify', [status(thm)], ['108'])).
% 2.83/3.03  thf('110', plain,
% 2.83/3.03      ((((k2_relat_1 @ (k6_partfun1 @ sk_B))
% 2.83/3.03          = (k2_relat_1 @ (k2_funct_1 @ sk_D)))
% 2.83/3.03        | ~ (v1_relat_1 @ sk_D)
% 2.83/3.03        | ~ (v1_funct_1 @ sk_D)
% 2.83/3.03        | ~ (v2_funct_1 @ sk_D))),
% 2.83/3.03      inference('sup+', [status(thm)], ['79', '109'])).
% 2.83/3.03  thf('111', plain, (![X12 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 2.83/3.03      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.83/3.03  thf('112', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 2.83/3.03      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.83/3.03  thf('113', plain,
% 2.83/3.03      (![X12 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X12)) = (X12))),
% 2.83/3.03      inference('demod', [status(thm)], ['111', '112'])).
% 2.83/3.03  thf('114', plain,
% 2.83/3.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf(cc2_relat_1, axiom,
% 2.83/3.03    (![A:$i]:
% 2.83/3.03     ( ( v1_relat_1 @ A ) =>
% 2.83/3.03       ( ![B:$i]:
% 2.83/3.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.83/3.03  thf('115', plain,
% 2.83/3.03      (![X0 : $i, X1 : $i]:
% 2.83/3.03         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 2.83/3.03          | (v1_relat_1 @ X0)
% 2.83/3.03          | ~ (v1_relat_1 @ X1))),
% 2.83/3.03      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.83/3.03  thf('116', plain,
% 2.83/3.03      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 2.83/3.03      inference('sup-', [status(thm)], ['114', '115'])).
% 2.83/3.03  thf(fc6_relat_1, axiom,
% 2.83/3.03    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.83/3.03  thf('117', plain,
% 2.83/3.03      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 2.83/3.03      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.83/3.03  thf('118', plain, ((v1_relat_1 @ sk_D)),
% 2.83/3.03      inference('demod', [status(thm)], ['116', '117'])).
% 2.83/3.03  thf('119', plain, ((v1_funct_1 @ sk_D)),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('120', plain, ((v2_funct_1 @ sk_D)),
% 2.83/3.03      inference('sup-', [status(thm)], ['76', '77'])).
% 2.83/3.03  thf('121', plain, (((sk_B) = (k2_relat_1 @ (k2_funct_1 @ sk_D)))),
% 2.83/3.03      inference('demod', [status(thm)], ['110', '113', '118', '119', '120'])).
% 2.83/3.03  thf('122', plain,
% 2.83/3.03      ((((sk_B) = (k1_relat_1 @ sk_D))
% 2.83/3.03        | ~ (v1_relat_1 @ sk_D)
% 2.83/3.03        | ~ (v1_funct_1 @ sk_D)
% 2.83/3.03        | ~ (v2_funct_1 @ sk_D))),
% 2.83/3.03      inference('sup+', [status(thm)], ['0', '121'])).
% 2.83/3.03  thf('123', plain, ((v1_relat_1 @ sk_D)),
% 2.83/3.03      inference('demod', [status(thm)], ['116', '117'])).
% 2.83/3.03  thf('124', plain, ((v1_funct_1 @ sk_D)),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('125', plain, ((v2_funct_1 @ sk_D)),
% 2.83/3.03      inference('sup-', [status(thm)], ['76', '77'])).
% 2.83/3.03  thf('126', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 2.83/3.03      inference('demod', [status(thm)], ['122', '123', '124', '125'])).
% 2.83/3.03  thf(t78_relat_1, axiom,
% 2.83/3.03    (![A:$i]:
% 2.83/3.03     ( ( v1_relat_1 @ A ) =>
% 2.83/3.03       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 2.83/3.03  thf('127', plain,
% 2.83/3.03      (![X13 : $i]:
% 2.83/3.03         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X13)) @ X13) = (X13))
% 2.83/3.03          | ~ (v1_relat_1 @ X13))),
% 2.83/3.03      inference('cnf', [status(esa)], [t78_relat_1])).
% 2.83/3.03  thf('128', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 2.83/3.03      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.83/3.03  thf('129', plain,
% 2.83/3.03      (![X13 : $i]:
% 2.83/3.03         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X13)) @ X13) = (X13))
% 2.83/3.03          | ~ (v1_relat_1 @ X13))),
% 2.83/3.03      inference('demod', [status(thm)], ['127', '128'])).
% 2.83/3.03  thf('130', plain,
% 2.83/3.03      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))
% 2.83/3.03        | ~ (v1_relat_1 @ sk_D))),
% 2.83/3.03      inference('sup+', [status(thm)], ['126', '129'])).
% 2.83/3.03  thf('131', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 2.83/3.03      inference('demod', [status(thm)], ['51', '54'])).
% 2.83/3.03  thf('132', plain,
% 2.83/3.03      (![X15 : $i]:
% 2.83/3.03         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 2.83/3.03          | ~ (v1_funct_1 @ X15)
% 2.83/3.03          | ~ (v1_relat_1 @ X15))),
% 2.83/3.03      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.83/3.03  thf('133', plain,
% 2.83/3.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('134', plain,
% 2.83/3.03      (![X56 : $i, X57 : $i, X58 : $i]:
% 2.83/3.03         (((X56) = (k1_xboole_0))
% 2.83/3.03          | ~ (v1_funct_1 @ X57)
% 2.83/3.03          | ~ (v1_funct_2 @ X57 @ X58 @ X56)
% 2.83/3.03          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X56)))
% 2.83/3.03          | ((k5_relat_1 @ (k2_funct_1 @ X57) @ X57) = (k6_partfun1 @ X56))
% 2.83/3.03          | ~ (v2_funct_1 @ X57)
% 2.83/3.03          | ((k2_relset_1 @ X58 @ X56 @ X57) != (X56)))),
% 2.83/3.03      inference('cnf', [status(esa)], [t35_funct_2])).
% 2.83/3.03  thf('135', plain,
% 2.83/3.03      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 2.83/3.03        | ~ (v2_funct_1 @ sk_C)
% 2.83/3.03        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 2.83/3.03        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.83/3.03        | ~ (v1_funct_1 @ sk_C)
% 2.83/3.03        | ((sk_B) = (k1_xboole_0)))),
% 2.83/3.03      inference('sup-', [status(thm)], ['133', '134'])).
% 2.83/3.03  thf('136', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('137', plain, ((v2_funct_1 @ sk_C)),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('138', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('139', plain, ((v1_funct_1 @ sk_C)),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('140', plain,
% 2.83/3.03      ((((sk_B) != (sk_B))
% 2.83/3.03        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 2.83/3.03        | ((sk_B) = (k1_xboole_0)))),
% 2.83/3.03      inference('demod', [status(thm)], ['135', '136', '137', '138', '139'])).
% 2.83/3.03  thf('141', plain,
% 2.83/3.03      ((((sk_B) = (k1_xboole_0))
% 2.83/3.03        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 2.83/3.03      inference('simplify', [status(thm)], ['140'])).
% 2.83/3.03  thf('142', plain, (((sk_B) != (k1_xboole_0))),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('143', plain,
% 2.83/3.03      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 2.83/3.03      inference('simplify_reflect-', [status(thm)], ['141', '142'])).
% 2.83/3.03  thf(t55_relat_1, axiom,
% 2.83/3.03    (![A:$i]:
% 2.83/3.03     ( ( v1_relat_1 @ A ) =>
% 2.83/3.03       ( ![B:$i]:
% 2.83/3.03         ( ( v1_relat_1 @ B ) =>
% 2.83/3.03           ( ![C:$i]:
% 2.83/3.03             ( ( v1_relat_1 @ C ) =>
% 2.83/3.03               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 2.83/3.03                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 2.83/3.03  thf('144', plain,
% 2.83/3.03      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.83/3.03         (~ (v1_relat_1 @ X8)
% 2.83/3.03          | ((k5_relat_1 @ (k5_relat_1 @ X9 @ X8) @ X10)
% 2.83/3.03              = (k5_relat_1 @ X9 @ (k5_relat_1 @ X8 @ X10)))
% 2.83/3.03          | ~ (v1_relat_1 @ X10)
% 2.83/3.03          | ~ (v1_relat_1 @ X9))),
% 2.83/3.03      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.83/3.03  thf('145', plain,
% 2.83/3.03      (![X0 : $i]:
% 2.83/3.03         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 2.83/3.03            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 2.83/3.03          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.83/3.03          | ~ (v1_relat_1 @ X0)
% 2.83/3.03          | ~ (v1_relat_1 @ sk_C))),
% 2.83/3.03      inference('sup+', [status(thm)], ['143', '144'])).
% 2.83/3.03  thf('146', plain,
% 2.83/3.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('147', plain,
% 2.83/3.03      (![X0 : $i, X1 : $i]:
% 2.83/3.03         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 2.83/3.03          | (v1_relat_1 @ X0)
% 2.83/3.03          | ~ (v1_relat_1 @ X1))),
% 2.83/3.03      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.83/3.03  thf('148', plain,
% 2.83/3.03      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 2.83/3.03      inference('sup-', [status(thm)], ['146', '147'])).
% 2.83/3.03  thf('149', plain,
% 2.83/3.03      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 2.83/3.03      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.83/3.03  thf('150', plain, ((v1_relat_1 @ sk_C)),
% 2.83/3.03      inference('demod', [status(thm)], ['148', '149'])).
% 2.83/3.03  thf('151', plain,
% 2.83/3.03      (![X0 : $i]:
% 2.83/3.03         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 2.83/3.03            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 2.83/3.03          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.83/3.03          | ~ (v1_relat_1 @ X0))),
% 2.83/3.03      inference('demod', [status(thm)], ['145', '150'])).
% 2.83/3.03  thf('152', plain,
% 2.83/3.03      (![X0 : $i]:
% 2.83/3.03         (~ (v1_relat_1 @ sk_C)
% 2.83/3.03          | ~ (v1_funct_1 @ sk_C)
% 2.83/3.03          | ~ (v1_relat_1 @ X0)
% 2.83/3.03          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 2.83/3.03              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 2.83/3.03      inference('sup-', [status(thm)], ['132', '151'])).
% 2.83/3.03  thf('153', plain, ((v1_relat_1 @ sk_C)),
% 2.83/3.03      inference('demod', [status(thm)], ['148', '149'])).
% 2.83/3.03  thf('154', plain, ((v1_funct_1 @ sk_C)),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('155', plain,
% 2.83/3.03      (![X0 : $i]:
% 2.83/3.03         (~ (v1_relat_1 @ X0)
% 2.83/3.03          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 2.83/3.03              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 2.83/3.03      inference('demod', [status(thm)], ['152', '153', '154'])).
% 2.83/3.03  thf('156', plain,
% 2.83/3.03      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 2.83/3.03          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 2.83/3.03        | ~ (v1_relat_1 @ sk_D))),
% 2.83/3.03      inference('sup+', [status(thm)], ['131', '155'])).
% 2.83/3.03  thf('157', plain,
% 2.83/3.03      (![X18 : $i]:
% 2.83/3.03         (~ (v2_funct_1 @ X18)
% 2.83/3.03          | ((k1_relat_1 @ X18) = (k2_relat_1 @ (k2_funct_1 @ X18)))
% 2.83/3.03          | ~ (v1_funct_1 @ X18)
% 2.83/3.03          | ~ (v1_relat_1 @ X18))),
% 2.83/3.03      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.83/3.03  thf('158', plain,
% 2.83/3.03      (![X15 : $i]:
% 2.83/3.03         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 2.83/3.03          | ~ (v1_funct_1 @ X15)
% 2.83/3.03          | ~ (v1_relat_1 @ X15))),
% 2.83/3.03      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.83/3.03  thf('159', plain,
% 2.83/3.03      (![X18 : $i]:
% 2.83/3.03         (~ (v2_funct_1 @ X18)
% 2.83/3.03          | ((k2_relat_1 @ X18) = (k1_relat_1 @ (k2_funct_1 @ X18)))
% 2.83/3.03          | ~ (v1_funct_1 @ X18)
% 2.83/3.03          | ~ (v1_relat_1 @ X18))),
% 2.83/3.03      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.83/3.03  thf('160', plain,
% 2.83/3.03      (![X15 : $i]:
% 2.83/3.03         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 2.83/3.03          | ~ (v1_funct_1 @ X15)
% 2.83/3.03          | ~ (v1_relat_1 @ X15))),
% 2.83/3.03      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.83/3.03  thf('161', plain,
% 2.83/3.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('162', plain,
% 2.83/3.03      (![X22 : $i, X23 : $i, X24 : $i]:
% 2.83/3.03         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 2.83/3.03          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 2.83/3.03      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.83/3.03  thf('163', plain,
% 2.83/3.03      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 2.83/3.03      inference('sup-', [status(thm)], ['161', '162'])).
% 2.83/3.03  thf('164', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('165', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.83/3.03      inference('sup+', [status(thm)], ['163', '164'])).
% 2.83/3.03  thf('166', plain,
% 2.83/3.03      (![X0 : $i]:
% 2.83/3.03         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 2.83/3.03          | ~ (v2_funct_1 @ X0)
% 2.83/3.03          | ~ (v1_funct_1 @ X0)
% 2.83/3.03          | ~ (v1_relat_1 @ X0))),
% 2.83/3.03      inference('simplify', [status(thm)], ['99'])).
% 2.83/3.03  thf('167', plain,
% 2.83/3.03      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)
% 2.83/3.03        | ~ (v1_relat_1 @ sk_C)
% 2.83/3.03        | ~ (v1_funct_1 @ sk_C)
% 2.83/3.03        | ~ (v2_funct_1 @ sk_C))),
% 2.83/3.03      inference('sup+', [status(thm)], ['165', '166'])).
% 2.83/3.03  thf('168', plain, ((v1_relat_1 @ sk_C)),
% 2.83/3.03      inference('demod', [status(thm)], ['148', '149'])).
% 2.83/3.03  thf('169', plain, ((v1_funct_1 @ sk_C)),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('170', plain, ((v2_funct_1 @ sk_C)),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('171', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)),
% 2.83/3.03      inference('demod', [status(thm)], ['167', '168', '169', '170'])).
% 2.83/3.03  thf('172', plain,
% 2.83/3.03      (![X2 : $i, X3 : $i]:
% 2.83/3.03         (~ (v4_relat_1 @ X2 @ X3)
% 2.83/3.03          | (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 2.83/3.03          | ~ (v1_relat_1 @ X2))),
% 2.83/3.03      inference('cnf', [status(esa)], [d18_relat_1])).
% 2.83/3.03  thf('173', plain,
% 2.83/3.03      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.83/3.03        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 2.83/3.03      inference('sup-', [status(thm)], ['171', '172'])).
% 2.83/3.03  thf('174', plain,
% 2.83/3.03      ((~ (v1_relat_1 @ sk_C)
% 2.83/3.03        | ~ (v1_funct_1 @ sk_C)
% 2.83/3.03        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 2.83/3.03      inference('sup-', [status(thm)], ['160', '173'])).
% 2.83/3.03  thf('175', plain, ((v1_relat_1 @ sk_C)),
% 2.83/3.03      inference('demod', [status(thm)], ['148', '149'])).
% 2.83/3.03  thf('176', plain, ((v1_funct_1 @ sk_C)),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('177', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B)),
% 2.83/3.03      inference('demod', [status(thm)], ['174', '175', '176'])).
% 2.83/3.03  thf('178', plain,
% 2.83/3.03      (![X12 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X12)) = (X12))),
% 2.83/3.03      inference('demod', [status(thm)], ['111', '112'])).
% 2.83/3.03  thf('179', plain,
% 2.83/3.03      (![X11 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X11)) = (X11))),
% 2.83/3.03      inference('demod', [status(thm)], ['92', '93'])).
% 2.83/3.03  thf('180', plain,
% 2.83/3.03      (![X6 : $i, X7 : $i]:
% 2.83/3.03         (~ (v1_relat_1 @ X6)
% 2.83/3.03          | ((k2_relat_1 @ (k5_relat_1 @ X6 @ X7)) = (k2_relat_1 @ X7))
% 2.83/3.03          | ~ (r1_tarski @ (k1_relat_1 @ X7) @ (k2_relat_1 @ X6))
% 2.83/3.03          | ~ (v1_relat_1 @ X7))),
% 2.83/3.03      inference('cnf', [status(esa)], [t47_relat_1])).
% 2.83/3.03  thf('181', plain,
% 2.83/3.03      (![X0 : $i, X1 : $i]:
% 2.83/3.03         (~ (r1_tarski @ X0 @ (k2_relat_1 @ X1))
% 2.83/3.03          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 2.83/3.03          | ((k2_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 2.83/3.03              = (k2_relat_1 @ (k6_partfun1 @ X0)))
% 2.83/3.03          | ~ (v1_relat_1 @ X1))),
% 2.83/3.03      inference('sup-', [status(thm)], ['179', '180'])).
% 2.83/3.03  thf('182', plain, (![X16 : $i]: (v1_relat_1 @ (k6_partfun1 @ X16))),
% 2.83/3.03      inference('demod', [status(thm)], ['89', '90'])).
% 2.83/3.03  thf('183', plain,
% 2.83/3.03      (![X12 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X12)) = (X12))),
% 2.83/3.03      inference('demod', [status(thm)], ['111', '112'])).
% 2.83/3.03  thf('184', plain,
% 2.83/3.03      (![X0 : $i, X1 : $i]:
% 2.83/3.03         (~ (r1_tarski @ X0 @ (k2_relat_1 @ X1))
% 2.83/3.03          | ((k2_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0))) = (X0))
% 2.83/3.03          | ~ (v1_relat_1 @ X1))),
% 2.83/3.03      inference('demod', [status(thm)], ['181', '182', '183'])).
% 2.83/3.03  thf('185', plain,
% 2.83/3.03      (![X0 : $i, X1 : $i]:
% 2.83/3.03         (~ (r1_tarski @ X1 @ X0)
% 2.83/3.03          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 2.83/3.03          | ((k2_relat_1 @ 
% 2.83/3.03              (k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X1))) = (
% 2.83/3.03              X1)))),
% 2.83/3.03      inference('sup-', [status(thm)], ['178', '184'])).
% 2.83/3.03  thf('186', plain, (![X16 : $i]: (v1_relat_1 @ (k6_partfun1 @ X16))),
% 2.83/3.03      inference('demod', [status(thm)], ['89', '90'])).
% 2.83/3.03  thf('187', plain,
% 2.83/3.03      (![X0 : $i, X1 : $i]:
% 2.83/3.03         (~ (r1_tarski @ X1 @ X0)
% 2.83/3.03          | ((k2_relat_1 @ 
% 2.83/3.03              (k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X1))) = (
% 2.83/3.03              X1)))),
% 2.83/3.03      inference('demod', [status(thm)], ['185', '186'])).
% 2.83/3.03  thf('188', plain,
% 2.83/3.03      (((k2_relat_1 @ 
% 2.83/3.03         (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 2.83/3.03          (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))))
% 2.83/3.03         = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 2.83/3.03      inference('sup-', [status(thm)], ['177', '187'])).
% 2.83/3.03  thf('189', plain,
% 2.83/3.03      ((((k2_relat_1 @ 
% 2.83/3.03          (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 2.83/3.03           (k6_partfun1 @ (k2_relat_1 @ sk_C))))
% 2.83/3.03          = (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 2.83/3.03        | ~ (v1_relat_1 @ sk_C)
% 2.83/3.03        | ~ (v1_funct_1 @ sk_C)
% 2.83/3.03        | ~ (v2_funct_1 @ sk_C))),
% 2.83/3.03      inference('sup+', [status(thm)], ['159', '188'])).
% 2.83/3.03  thf('190', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.83/3.03      inference('sup+', [status(thm)], ['163', '164'])).
% 2.83/3.03  thf('191', plain,
% 2.83/3.03      (![X11 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X11)) = (X11))),
% 2.83/3.03      inference('demod', [status(thm)], ['92', '93'])).
% 2.83/3.03  thf('192', plain,
% 2.83/3.03      (![X13 : $i]:
% 2.83/3.03         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X13)) @ X13) = (X13))
% 2.83/3.03          | ~ (v1_relat_1 @ X13))),
% 2.83/3.03      inference('demod', [status(thm)], ['127', '128'])).
% 2.83/3.03  thf('193', plain,
% 2.83/3.03      (![X0 : $i]:
% 2.83/3.03         (((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 2.83/3.03            = (k6_partfun1 @ X0))
% 2.83/3.03          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 2.83/3.03      inference('sup+', [status(thm)], ['191', '192'])).
% 2.83/3.03  thf('194', plain, (![X16 : $i]: (v1_relat_1 @ (k6_partfun1 @ X16))),
% 2.83/3.03      inference('demod', [status(thm)], ['89', '90'])).
% 2.83/3.03  thf('195', plain,
% 2.83/3.03      (![X0 : $i]:
% 2.83/3.03         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 2.83/3.03           = (k6_partfun1 @ X0))),
% 2.83/3.03      inference('demod', [status(thm)], ['193', '194'])).
% 2.83/3.03  thf('196', plain,
% 2.83/3.03      (![X12 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X12)) = (X12))),
% 2.83/3.03      inference('demod', [status(thm)], ['111', '112'])).
% 2.83/3.03  thf('197', plain, ((v1_relat_1 @ sk_C)),
% 2.83/3.03      inference('demod', [status(thm)], ['148', '149'])).
% 2.83/3.03  thf('198', plain, ((v1_funct_1 @ sk_C)),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('199', plain, ((v2_funct_1 @ sk_C)),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('200', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 2.83/3.03      inference('demod', [status(thm)],
% 2.83/3.03                ['189', '190', '195', '196', '197', '198', '199'])).
% 2.83/3.03  thf('201', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.83/3.03      inference('sup+', [status(thm)], ['163', '164'])).
% 2.83/3.03  thf('202', plain,
% 2.83/3.03      (![X6 : $i, X7 : $i]:
% 2.83/3.03         (~ (v1_relat_1 @ X6)
% 2.83/3.03          | ((k2_relat_1 @ (k5_relat_1 @ X6 @ X7)) = (k2_relat_1 @ X7))
% 2.83/3.03          | ~ (r1_tarski @ (k1_relat_1 @ X7) @ (k2_relat_1 @ X6))
% 2.83/3.03          | ~ (v1_relat_1 @ X7))),
% 2.83/3.03      inference('cnf', [status(esa)], [t47_relat_1])).
% 2.83/3.03  thf('203', plain,
% 2.83/3.03      (![X0 : $i]:
% 2.83/3.03         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_B)
% 2.83/3.03          | ~ (v1_relat_1 @ X0)
% 2.83/3.03          | ((k2_relat_1 @ (k5_relat_1 @ sk_C @ X0)) = (k2_relat_1 @ X0))
% 2.83/3.03          | ~ (v1_relat_1 @ sk_C))),
% 2.83/3.03      inference('sup-', [status(thm)], ['201', '202'])).
% 2.83/3.03  thf('204', plain, ((v1_relat_1 @ sk_C)),
% 2.83/3.03      inference('demod', [status(thm)], ['148', '149'])).
% 2.83/3.03  thf('205', plain,
% 2.83/3.03      (![X0 : $i]:
% 2.83/3.03         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_B)
% 2.83/3.03          | ~ (v1_relat_1 @ X0)
% 2.83/3.03          | ((k2_relat_1 @ (k5_relat_1 @ sk_C @ X0)) = (k2_relat_1 @ X0)))),
% 2.83/3.03      inference('demod', [status(thm)], ['203', '204'])).
% 2.83/3.03  thf('206', plain,
% 2.83/3.03      ((~ (r1_tarski @ sk_B @ sk_B)
% 2.83/3.03        | ((k2_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 2.83/3.03            = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 2.83/3.03        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 2.83/3.03      inference('sup-', [status(thm)], ['200', '205'])).
% 2.83/3.03  thf('207', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 2.83/3.03      inference('demod', [status(thm)], ['88', '91', '94'])).
% 2.83/3.03  thf('208', plain,
% 2.83/3.03      ((((k2_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 2.83/3.03          = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 2.83/3.03        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 2.83/3.03      inference('demod', [status(thm)], ['206', '207'])).
% 2.83/3.03  thf('209', plain,
% 2.83/3.03      ((~ (v1_relat_1 @ sk_C)
% 2.83/3.03        | ~ (v1_funct_1 @ sk_C)
% 2.83/3.03        | ((k2_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 2.83/3.03            = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 2.83/3.03      inference('sup-', [status(thm)], ['158', '208'])).
% 2.83/3.03  thf('210', plain, ((v1_relat_1 @ sk_C)),
% 2.83/3.03      inference('demod', [status(thm)], ['148', '149'])).
% 2.83/3.03  thf('211', plain, ((v1_funct_1 @ sk_C)),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('212', plain,
% 2.83/3.03      (((k2_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 2.83/3.03         = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 2.83/3.03      inference('demod', [status(thm)], ['209', '210', '211'])).
% 2.83/3.03  thf('213', plain,
% 2.83/3.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('214', plain,
% 2.83/3.03      (![X56 : $i, X57 : $i, X58 : $i]:
% 2.83/3.03         (((X56) = (k1_xboole_0))
% 2.83/3.03          | ~ (v1_funct_1 @ X57)
% 2.83/3.03          | ~ (v1_funct_2 @ X57 @ X58 @ X56)
% 2.83/3.03          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X56)))
% 2.83/3.03          | ((k5_relat_1 @ X57 @ (k2_funct_1 @ X57)) = (k6_partfun1 @ X58))
% 2.83/3.03          | ~ (v2_funct_1 @ X57)
% 2.83/3.03          | ((k2_relset_1 @ X58 @ X56 @ X57) != (X56)))),
% 2.83/3.03      inference('cnf', [status(esa)], [t35_funct_2])).
% 2.83/3.03  thf('215', plain,
% 2.83/3.03      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 2.83/3.03        | ~ (v2_funct_1 @ sk_C)
% 2.83/3.03        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 2.83/3.03        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.83/3.03        | ~ (v1_funct_1 @ sk_C)
% 2.83/3.03        | ((sk_B) = (k1_xboole_0)))),
% 2.83/3.03      inference('sup-', [status(thm)], ['213', '214'])).
% 2.83/3.03  thf('216', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('217', plain, ((v2_funct_1 @ sk_C)),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('218', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('219', plain, ((v1_funct_1 @ sk_C)),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('220', plain,
% 2.83/3.03      ((((sk_B) != (sk_B))
% 2.83/3.03        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 2.83/3.03        | ((sk_B) = (k1_xboole_0)))),
% 2.83/3.03      inference('demod', [status(thm)], ['215', '216', '217', '218', '219'])).
% 2.83/3.03  thf('221', plain,
% 2.83/3.03      ((((sk_B) = (k1_xboole_0))
% 2.83/3.03        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 2.83/3.03      inference('simplify', [status(thm)], ['220'])).
% 2.83/3.03  thf('222', plain, (((sk_B) != (k1_xboole_0))),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('223', plain,
% 2.83/3.03      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 2.83/3.03      inference('simplify_reflect-', [status(thm)], ['221', '222'])).
% 2.83/3.03  thf('224', plain,
% 2.83/3.03      (![X12 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X12)) = (X12))),
% 2.83/3.03      inference('demod', [status(thm)], ['111', '112'])).
% 2.83/3.03  thf('225', plain, (((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 2.83/3.03      inference('demod', [status(thm)], ['212', '223', '224'])).
% 2.83/3.03  thf('226', plain,
% 2.83/3.03      ((((sk_A) = (k1_relat_1 @ sk_C))
% 2.83/3.03        | ~ (v1_relat_1 @ sk_C)
% 2.83/3.03        | ~ (v1_funct_1 @ sk_C)
% 2.83/3.03        | ~ (v2_funct_1 @ sk_C))),
% 2.83/3.03      inference('sup+', [status(thm)], ['157', '225'])).
% 2.83/3.03  thf('227', plain, ((v1_relat_1 @ sk_C)),
% 2.83/3.03      inference('demod', [status(thm)], ['148', '149'])).
% 2.83/3.03  thf('228', plain, ((v1_funct_1 @ sk_C)),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('229', plain, ((v2_funct_1 @ sk_C)),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('230', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 2.83/3.03      inference('demod', [status(thm)], ['226', '227', '228', '229'])).
% 2.83/3.03  thf('231', plain,
% 2.83/3.03      (![X15 : $i]:
% 2.83/3.03         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 2.83/3.03          | ~ (v1_funct_1 @ X15)
% 2.83/3.03          | ~ (v1_relat_1 @ X15))),
% 2.83/3.03      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.83/3.03  thf('232', plain,
% 2.83/3.03      (![X18 : $i]:
% 2.83/3.03         (~ (v2_funct_1 @ X18)
% 2.83/3.03          | ((k1_relat_1 @ X18) = (k2_relat_1 @ (k2_funct_1 @ X18)))
% 2.83/3.03          | ~ (v1_funct_1 @ X18)
% 2.83/3.03          | ~ (v1_relat_1 @ X18))),
% 2.83/3.03      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.83/3.03  thf(t80_relat_1, axiom,
% 2.83/3.03    (![A:$i]:
% 2.83/3.03     ( ( v1_relat_1 @ A ) =>
% 2.83/3.03       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 2.83/3.03  thf('233', plain,
% 2.83/3.03      (![X14 : $i]:
% 2.83/3.03         (((k5_relat_1 @ X14 @ (k6_relat_1 @ (k2_relat_1 @ X14))) = (X14))
% 2.83/3.03          | ~ (v1_relat_1 @ X14))),
% 2.83/3.03      inference('cnf', [status(esa)], [t80_relat_1])).
% 2.83/3.03  thf('234', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 2.83/3.03      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.83/3.03  thf('235', plain,
% 2.83/3.03      (![X14 : $i]:
% 2.83/3.03         (((k5_relat_1 @ X14 @ (k6_partfun1 @ (k2_relat_1 @ X14))) = (X14))
% 2.83/3.03          | ~ (v1_relat_1 @ X14))),
% 2.83/3.03      inference('demod', [status(thm)], ['233', '234'])).
% 2.83/3.03  thf('236', plain,
% 2.83/3.03      (![X0 : $i]:
% 2.83/3.03         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 2.83/3.03            = (k2_funct_1 @ X0))
% 2.83/3.03          | ~ (v1_relat_1 @ X0)
% 2.83/3.03          | ~ (v1_funct_1 @ X0)
% 2.83/3.03          | ~ (v2_funct_1 @ X0)
% 2.83/3.03          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 2.83/3.03      inference('sup+', [status(thm)], ['232', '235'])).
% 2.83/3.03  thf('237', plain,
% 2.83/3.03      (![X0 : $i]:
% 2.83/3.03         (~ (v1_relat_1 @ X0)
% 2.83/3.03          | ~ (v1_funct_1 @ X0)
% 2.83/3.03          | ~ (v2_funct_1 @ X0)
% 2.83/3.03          | ~ (v1_funct_1 @ X0)
% 2.83/3.03          | ~ (v1_relat_1 @ X0)
% 2.83/3.03          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 2.83/3.03              (k6_partfun1 @ (k1_relat_1 @ X0))) = (k2_funct_1 @ X0)))),
% 2.83/3.03      inference('sup-', [status(thm)], ['231', '236'])).
% 2.83/3.03  thf('238', plain,
% 2.83/3.03      (![X0 : $i]:
% 2.83/3.03         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 2.83/3.03            = (k2_funct_1 @ X0))
% 2.83/3.03          | ~ (v2_funct_1 @ X0)
% 2.83/3.03          | ~ (v1_funct_1 @ X0)
% 2.83/3.03          | ~ (v1_relat_1 @ X0))),
% 2.83/3.03      inference('simplify', [status(thm)], ['237'])).
% 2.83/3.03  thf('239', plain,
% 2.83/3.03      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 2.83/3.03          = (k2_funct_1 @ sk_C))
% 2.83/3.03        | ~ (v1_relat_1 @ sk_C)
% 2.83/3.03        | ~ (v1_funct_1 @ sk_C)
% 2.83/3.03        | ~ (v2_funct_1 @ sk_C))),
% 2.83/3.03      inference('sup+', [status(thm)], ['230', '238'])).
% 2.83/3.03  thf('240', plain, ((v1_relat_1 @ sk_C)),
% 2.83/3.03      inference('demod', [status(thm)], ['148', '149'])).
% 2.83/3.03  thf('241', plain, ((v1_funct_1 @ sk_C)),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('242', plain, ((v2_funct_1 @ sk_C)),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('243', plain,
% 2.83/3.03      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 2.83/3.03         = (k2_funct_1 @ sk_C))),
% 2.83/3.03      inference('demod', [status(thm)], ['239', '240', '241', '242'])).
% 2.83/3.03  thf('244', plain, ((v1_relat_1 @ sk_D)),
% 2.83/3.03      inference('demod', [status(thm)], ['116', '117'])).
% 2.83/3.03  thf('245', plain,
% 2.83/3.03      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (k2_funct_1 @ sk_C))),
% 2.83/3.03      inference('demod', [status(thm)], ['156', '243', '244'])).
% 2.83/3.03  thf('246', plain, ((v1_relat_1 @ sk_D)),
% 2.83/3.03      inference('demod', [status(thm)], ['116', '117'])).
% 2.83/3.03  thf('247', plain, (((k2_funct_1 @ sk_C) = (sk_D))),
% 2.83/3.03      inference('demod', [status(thm)], ['130', '245', '246'])).
% 2.83/3.03  thf('248', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 2.83/3.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.83/3.03  thf('249', plain, ($false),
% 2.83/3.03      inference('simplify_reflect-', [status(thm)], ['247', '248'])).
% 2.83/3.03  
% 2.83/3.03  % SZS output end Refutation
% 2.83/3.03  
% 2.83/3.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

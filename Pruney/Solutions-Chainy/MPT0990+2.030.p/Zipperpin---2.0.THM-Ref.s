%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.l7DmZbZQ2T

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:59 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 246 expanded)
%              Number of leaves         :   45 (  92 expanded)
%              Depth                    :   13
%              Number of atoms          : 1379 (5438 expanded)
%              Number of equality atoms :   97 ( 391 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

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
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
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
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( ( k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42 )
        = ( k5_relat_1 @ X39 @ X42 ) ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X32 @ X33 @ X35 @ X36 @ X31 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X36 ) ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( X19 = X22 )
      | ~ ( r2_relset_1 @ X20 @ X21 @ X19 @ X22 ) ) ),
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
    ! [X38: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('27',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
    ! [X38: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X38 ) ) ) ),
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
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( X46 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ X48 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X46 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X47 ) @ X47 )
        = ( k6_partfun1 @ X46 ) )
      | ~ ( v2_funct_1 @ X47 )
      | ( ( k2_relset_1 @ X48 @ X46 @ X47 )
       != X46 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('33',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('34',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( X46 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ X48 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X46 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X47 ) @ X47 )
        = ( k6_relat_1 @ X46 ) )
      | ~ ( v2_funct_1 @ X47 )
      | ( ( k2_relset_1 @ X48 @ X46 @ X47 )
       != X46 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('77',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.l7DmZbZQ2T
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:01:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.90/1.14  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.90/1.14  % Solved by: fo/fo7.sh
% 0.90/1.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.14  % done 307 iterations in 0.684s
% 0.90/1.14  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.90/1.14  % SZS output start Refutation
% 0.90/1.14  thf(sk_D_type, type, sk_D: $i).
% 0.90/1.14  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.90/1.14  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.14  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.90/1.14  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.90/1.14  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.90/1.14  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.90/1.14  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.90/1.14  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.90/1.14  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.90/1.14  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.90/1.14  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.90/1.14  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.90/1.14  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.90/1.14  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.90/1.14  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.90/1.14  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.90/1.14  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.14  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.14  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.90/1.14  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.14  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.90/1.14  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.90/1.14  thf(sk_C_type, type, sk_C: $i).
% 0.90/1.14  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.90/1.14  thf(t36_funct_2, conjecture,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.90/1.14         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.90/1.14       ( ![D:$i]:
% 0.90/1.14         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.90/1.14             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.90/1.14           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.90/1.14               ( r2_relset_1 @
% 0.90/1.14                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.90/1.14                 ( k6_partfun1 @ A ) ) & 
% 0.90/1.14               ( v2_funct_1 @ C ) ) =>
% 0.90/1.14             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.90/1.14               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.90/1.14  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.14    (~( ![A:$i,B:$i,C:$i]:
% 0.90/1.14        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.90/1.14            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.90/1.14          ( ![D:$i]:
% 0.90/1.14            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.90/1.14                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.90/1.14              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.90/1.14                  ( r2_relset_1 @
% 0.90/1.14                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.90/1.14                    ( k6_partfun1 @ A ) ) & 
% 0.90/1.14                  ( v2_funct_1 @ C ) ) =>
% 0.90/1.14                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.90/1.14                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.90/1.14    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.90/1.14  thf('0', plain,
% 0.90/1.14      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.14        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.90/1.14        (k6_partfun1 @ sk_A))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(redefinition_k6_partfun1, axiom,
% 0.90/1.14    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.90/1.14  thf('1', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 0.90/1.14      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.90/1.14  thf('2', plain,
% 0.90/1.14      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.14        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.90/1.14        (k6_relat_1 @ sk_A))),
% 0.90/1.14      inference('demod', [status(thm)], ['0', '1'])).
% 0.90/1.14  thf('3', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('4', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(redefinition_k1_partfun1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.90/1.14     ( ( ( v1_funct_1 @ E ) & 
% 0.90/1.14         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.90/1.14         ( v1_funct_1 @ F ) & 
% 0.90/1.14         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.90/1.14       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.90/1.14  thf('5', plain,
% 0.90/1.14      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.90/1.14         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.90/1.14          | ~ (v1_funct_1 @ X39)
% 0.90/1.14          | ~ (v1_funct_1 @ X42)
% 0.90/1.14          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 0.90/1.14          | ((k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42)
% 0.90/1.14              = (k5_relat_1 @ X39 @ X42)))),
% 0.90/1.14      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.90/1.14  thf('6', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.14         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.90/1.14            = (k5_relat_1 @ sk_C @ X0))
% 0.90/1.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.90/1.14          | ~ (v1_funct_1 @ X0)
% 0.90/1.14          | ~ (v1_funct_1 @ sk_C))),
% 0.90/1.14      inference('sup-', [status(thm)], ['4', '5'])).
% 0.90/1.14  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('8', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.14         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.90/1.14            = (k5_relat_1 @ sk_C @ X0))
% 0.90/1.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.90/1.14          | ~ (v1_funct_1 @ X0))),
% 0.90/1.14      inference('demod', [status(thm)], ['6', '7'])).
% 0.90/1.14  thf('9', plain,
% 0.90/1.14      ((~ (v1_funct_1 @ sk_D)
% 0.90/1.14        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.90/1.14            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['3', '8'])).
% 0.90/1.14  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('11', plain,
% 0.90/1.14      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.90/1.14         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['9', '10'])).
% 0.90/1.14  thf('12', plain,
% 0.90/1.14      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.90/1.14        (k6_relat_1 @ sk_A))),
% 0.90/1.14      inference('demod', [status(thm)], ['2', '11'])).
% 0.90/1.14  thf('13', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('14', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(dt_k1_partfun1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.90/1.14     ( ( ( v1_funct_1 @ E ) & 
% 0.90/1.14         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.90/1.14         ( v1_funct_1 @ F ) & 
% 0.90/1.14         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.90/1.14       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.90/1.14         ( m1_subset_1 @
% 0.90/1.14           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.90/1.14           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.90/1.14  thf('15', plain,
% 0.90/1.14      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.90/1.14         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.90/1.14          | ~ (v1_funct_1 @ X31)
% 0.90/1.14          | ~ (v1_funct_1 @ X34)
% 0.90/1.14          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.90/1.14          | (m1_subset_1 @ (k1_partfun1 @ X32 @ X33 @ X35 @ X36 @ X31 @ X34) @ 
% 0.90/1.14             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X36))))),
% 0.90/1.14      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.90/1.14  thf('16', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.14         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.90/1.14           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.90/1.14          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.90/1.14          | ~ (v1_funct_1 @ X1)
% 0.90/1.14          | ~ (v1_funct_1 @ sk_C))),
% 0.90/1.14      inference('sup-', [status(thm)], ['14', '15'])).
% 0.90/1.14  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('18', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.14         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.90/1.14           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.90/1.14          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.90/1.14          | ~ (v1_funct_1 @ X1))),
% 0.90/1.14      inference('demod', [status(thm)], ['16', '17'])).
% 0.90/1.14  thf('19', plain,
% 0.90/1.14      ((~ (v1_funct_1 @ sk_D)
% 0.90/1.14        | (m1_subset_1 @ 
% 0.90/1.14           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.90/1.14           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['13', '18'])).
% 0.90/1.14  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('21', plain,
% 0.90/1.14      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.90/1.14         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['9', '10'])).
% 0.90/1.14  thf('22', plain,
% 0.90/1.14      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.90/1.14        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.14      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.90/1.14  thf(redefinition_r2_relset_1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.14     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.90/1.14         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.90/1.14       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.90/1.14  thf('23', plain,
% 0.90/1.14      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.90/1.14         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.90/1.14          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.90/1.14          | ((X19) = (X22))
% 0.90/1.14          | ~ (r2_relset_1 @ X20 @ X21 @ X19 @ X22))),
% 0.90/1.14      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.90/1.14  thf('24', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 0.90/1.14          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 0.90/1.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['22', '23'])).
% 0.90/1.14  thf('25', plain,
% 0.90/1.14      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 0.90/1.14           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.90/1.14        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['12', '24'])).
% 0.90/1.14  thf(dt_k6_partfun1, axiom,
% 0.90/1.14    (![A:$i]:
% 0.90/1.14     ( ( m1_subset_1 @
% 0.90/1.14         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.90/1.14       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.90/1.14  thf('26', plain,
% 0.90/1.14      (![X38 : $i]:
% 0.90/1.14         (m1_subset_1 @ (k6_partfun1 @ X38) @ 
% 0.90/1.14          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X38)))),
% 0.90/1.14      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.90/1.14  thf('27', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 0.90/1.14      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.90/1.14  thf('28', plain,
% 0.90/1.14      (![X38 : $i]:
% 0.90/1.14         (m1_subset_1 @ (k6_relat_1 @ X38) @ 
% 0.90/1.14          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X38)))),
% 0.90/1.14      inference('demod', [status(thm)], ['26', '27'])).
% 0.90/1.14  thf('29', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 0.90/1.14      inference('demod', [status(thm)], ['25', '28'])).
% 0.90/1.14  thf(dt_k2_funct_1, axiom,
% 0.90/1.14    (![A:$i]:
% 0.90/1.14     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.90/1.14       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.90/1.14         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.90/1.14  thf('30', plain,
% 0.90/1.14      (![X7 : $i]:
% 0.90/1.14         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 0.90/1.14          | ~ (v1_funct_1 @ X7)
% 0.90/1.14          | ~ (v1_relat_1 @ X7))),
% 0.90/1.14      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.90/1.14  thf('31', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(t35_funct_2, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.90/1.14         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.90/1.14       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.90/1.14         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.90/1.14           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.90/1.14             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.90/1.14  thf('32', plain,
% 0.90/1.14      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.90/1.14         (((X46) = (k1_xboole_0))
% 0.90/1.14          | ~ (v1_funct_1 @ X47)
% 0.90/1.14          | ~ (v1_funct_2 @ X47 @ X48 @ X46)
% 0.90/1.14          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X46)))
% 0.90/1.14          | ((k5_relat_1 @ (k2_funct_1 @ X47) @ X47) = (k6_partfun1 @ X46))
% 0.90/1.14          | ~ (v2_funct_1 @ X47)
% 0.90/1.14          | ((k2_relset_1 @ X48 @ X46 @ X47) != (X46)))),
% 0.90/1.14      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.90/1.14  thf('33', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 0.90/1.14      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.90/1.14  thf('34', plain,
% 0.90/1.14      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.90/1.14         (((X46) = (k1_xboole_0))
% 0.90/1.14          | ~ (v1_funct_1 @ X47)
% 0.90/1.14          | ~ (v1_funct_2 @ X47 @ X48 @ X46)
% 0.90/1.14          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X46)))
% 0.90/1.14          | ((k5_relat_1 @ (k2_funct_1 @ X47) @ X47) = (k6_relat_1 @ X46))
% 0.90/1.14          | ~ (v2_funct_1 @ X47)
% 0.90/1.14          | ((k2_relset_1 @ X48 @ X46 @ X47) != (X46)))),
% 0.90/1.14      inference('demod', [status(thm)], ['32', '33'])).
% 0.90/1.14  thf('35', plain,
% 0.90/1.14      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.90/1.14        | ~ (v2_funct_1 @ sk_C)
% 0.90/1.14        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 0.90/1.14        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.90/1.14        | ~ (v1_funct_1 @ sk_C)
% 0.90/1.14        | ((sk_B) = (k1_xboole_0)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['31', '34'])).
% 0.90/1.14  thf('36', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('37', plain, ((v2_funct_1 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('38', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('39', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('40', plain,
% 0.90/1.14      ((((sk_B) != (sk_B))
% 0.90/1.14        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 0.90/1.14        | ((sk_B) = (k1_xboole_0)))),
% 0.90/1.14      inference('demod', [status(thm)], ['35', '36', '37', '38', '39'])).
% 0.90/1.14  thf('41', plain,
% 0.90/1.14      ((((sk_B) = (k1_xboole_0))
% 0.90/1.14        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B)))),
% 0.90/1.14      inference('simplify', [status(thm)], ['40'])).
% 0.90/1.14  thf('42', plain, (((sk_B) != (k1_xboole_0))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('43', plain,
% 0.90/1.14      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))),
% 0.90/1.14      inference('simplify_reflect-', [status(thm)], ['41', '42'])).
% 0.90/1.14  thf(t55_relat_1, axiom,
% 0.90/1.14    (![A:$i]:
% 0.90/1.14     ( ( v1_relat_1 @ A ) =>
% 0.90/1.14       ( ![B:$i]:
% 0.90/1.14         ( ( v1_relat_1 @ B ) =>
% 0.90/1.14           ( ![C:$i]:
% 0.90/1.14             ( ( v1_relat_1 @ C ) =>
% 0.90/1.14               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.90/1.14                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.90/1.14  thf('44', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.14         (~ (v1_relat_1 @ X0)
% 0.90/1.14          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 0.90/1.14              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 0.90/1.14          | ~ (v1_relat_1 @ X2)
% 0.90/1.14          | ~ (v1_relat_1 @ X1))),
% 0.90/1.14      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.90/1.14  thf('45', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 0.90/1.14            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 0.90/1.14          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.90/1.14          | ~ (v1_relat_1 @ X0)
% 0.90/1.14          | ~ (v1_relat_1 @ sk_C))),
% 0.90/1.14      inference('sup+', [status(thm)], ['43', '44'])).
% 0.90/1.14  thf('46', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(cc1_relset_1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.14       ( v1_relat_1 @ C ) ))).
% 0.90/1.14  thf('47', plain,
% 0.90/1.14      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.90/1.14         ((v1_relat_1 @ X10)
% 0.90/1.14          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.90/1.14      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.90/1.14  thf('48', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.14      inference('sup-', [status(thm)], ['46', '47'])).
% 0.90/1.14  thf('49', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 0.90/1.14            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 0.90/1.14          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.90/1.14          | ~ (v1_relat_1 @ X0))),
% 0.90/1.14      inference('demod', [status(thm)], ['45', '48'])).
% 0.90/1.14  thf('50', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (~ (v1_relat_1 @ sk_C)
% 0.90/1.14          | ~ (v1_funct_1 @ sk_C)
% 0.90/1.14          | ~ (v1_relat_1 @ X0)
% 0.90/1.14          | ((k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 0.90/1.14              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['30', '49'])).
% 0.90/1.14  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.14      inference('sup-', [status(thm)], ['46', '47'])).
% 0.90/1.14  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('53', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (~ (v1_relat_1 @ X0)
% 0.90/1.14          | ((k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 0.90/1.14              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 0.90/1.14      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.90/1.14  thf('54', plain,
% 0.90/1.14      ((((k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_D)
% 0.90/1.14          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_relat_1 @ sk_A)))
% 0.90/1.14        | ~ (v1_relat_1 @ sk_D))),
% 0.90/1.14      inference('sup+', [status(thm)], ['29', '53'])).
% 0.90/1.14  thf('55', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(d1_funct_2, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.14       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.90/1.14           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.90/1.14             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.90/1.14         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.90/1.14           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.90/1.14             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.90/1.14  thf(zf_stmt_1, axiom,
% 0.90/1.14    (![C:$i,B:$i,A:$i]:
% 0.90/1.14     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.90/1.14       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.90/1.14  thf('56', plain,
% 0.90/1.14      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.90/1.14         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 0.90/1.14          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 0.90/1.14          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.90/1.14  thf('57', plain,
% 0.90/1.14      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 0.90/1.14        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['55', '56'])).
% 0.90/1.14  thf(zf_stmt_2, axiom,
% 0.90/1.14    (![B:$i,A:$i]:
% 0.90/1.14     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.90/1.14       ( zip_tseitin_0 @ B @ A ) ))).
% 0.90/1.14  thf('58', plain,
% 0.90/1.14      (![X23 : $i, X24 : $i]:
% 0.90/1.14         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.90/1.14  thf('59', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.90/1.14  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.90/1.14  thf(zf_stmt_5, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.14       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.90/1.14         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.90/1.14           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.90/1.14             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.90/1.14  thf('60', plain,
% 0.90/1.14      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.90/1.14         (~ (zip_tseitin_0 @ X28 @ X29)
% 0.90/1.14          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 0.90/1.14          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.90/1.14  thf('61', plain,
% 0.90/1.14      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 0.90/1.14      inference('sup-', [status(thm)], ['59', '60'])).
% 0.90/1.14  thf('62', plain,
% 0.90/1.14      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 0.90/1.14      inference('sup-', [status(thm)], ['58', '61'])).
% 0.90/1.14  thf('63', plain, (((sk_A) != (k1_xboole_0))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('64', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 0.90/1.14      inference('simplify_reflect-', [status(thm)], ['62', '63'])).
% 0.90/1.14  thf('65', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(redefinition_k1_relset_1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.14       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.90/1.14  thf('66', plain,
% 0.90/1.14      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.90/1.14         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 0.90/1.14          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.90/1.14      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.90/1.14  thf('67', plain,
% 0.90/1.14      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.90/1.14      inference('sup-', [status(thm)], ['65', '66'])).
% 0.90/1.14  thf('68', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['57', '64', '67'])).
% 0.90/1.14  thf(t78_relat_1, axiom,
% 0.90/1.14    (![A:$i]:
% 0.90/1.14     ( ( v1_relat_1 @ A ) =>
% 0.90/1.14       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 0.90/1.14  thf('69', plain,
% 0.90/1.14      (![X5 : $i]:
% 0.90/1.14         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X5)) @ X5) = (X5))
% 0.90/1.14          | ~ (v1_relat_1 @ X5))),
% 0.90/1.14      inference('cnf', [status(esa)], [t78_relat_1])).
% 0.90/1.14  thf('70', plain,
% 0.90/1.14      ((((k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_D) = (sk_D))
% 0.90/1.14        | ~ (v1_relat_1 @ sk_D))),
% 0.90/1.14      inference('sup+', [status(thm)], ['68', '69'])).
% 0.90/1.14  thf('71', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('72', plain,
% 0.90/1.14      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.90/1.14         ((v1_relat_1 @ X10)
% 0.90/1.14          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.90/1.14      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.90/1.14  thf('73', plain, ((v1_relat_1 @ sk_D)),
% 0.90/1.14      inference('sup-', [status(thm)], ['71', '72'])).
% 0.90/1.14  thf('74', plain, (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_D) = (sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['70', '73'])).
% 0.90/1.14  thf('75', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('76', plain,
% 0.90/1.14      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.90/1.14         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 0.90/1.14          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 0.90/1.14          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.90/1.14  thf('77', plain,
% 0.90/1.14      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.90/1.14        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['75', '76'])).
% 0.90/1.14  thf('78', plain,
% 0.90/1.14      (![X23 : $i, X24 : $i]:
% 0.90/1.14         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.90/1.14  thf('79', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('80', plain,
% 0.90/1.14      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.90/1.14         (~ (zip_tseitin_0 @ X28 @ X29)
% 0.90/1.14          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 0.90/1.14          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.90/1.14  thf('81', plain,
% 0.90/1.14      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.90/1.14      inference('sup-', [status(thm)], ['79', '80'])).
% 0.90/1.14  thf('82', plain,
% 0.90/1.14      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.90/1.14      inference('sup-', [status(thm)], ['78', '81'])).
% 0.90/1.14  thf('83', plain, (((sk_B) != (k1_xboole_0))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('84', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.90/1.14      inference('simplify_reflect-', [status(thm)], ['82', '83'])).
% 0.90/1.14  thf('85', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('86', plain,
% 0.90/1.14      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.90/1.14         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 0.90/1.14          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.90/1.14      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.90/1.14  thf('87', plain,
% 0.90/1.14      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.90/1.14      inference('sup-', [status(thm)], ['85', '86'])).
% 0.90/1.14  thf('88', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['77', '84', '87'])).
% 0.90/1.14  thf('89', plain,
% 0.90/1.14      (![X7 : $i]:
% 0.90/1.14         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 0.90/1.14          | ~ (v1_funct_1 @ X7)
% 0.90/1.14          | ~ (v1_relat_1 @ X7))),
% 0.90/1.14      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.90/1.14  thf(t55_funct_1, axiom,
% 0.90/1.14    (![A:$i]:
% 0.90/1.14     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.90/1.14       ( ( v2_funct_1 @ A ) =>
% 0.90/1.14         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.90/1.14           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.90/1.14  thf('90', plain,
% 0.90/1.14      (![X8 : $i]:
% 0.90/1.14         (~ (v2_funct_1 @ X8)
% 0.90/1.14          | ((k1_relat_1 @ X8) = (k2_relat_1 @ (k2_funct_1 @ X8)))
% 0.90/1.14          | ~ (v1_funct_1 @ X8)
% 0.90/1.14          | ~ (v1_relat_1 @ X8))),
% 0.90/1.14      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.90/1.14  thf(t80_relat_1, axiom,
% 0.90/1.14    (![A:$i]:
% 0.90/1.14     ( ( v1_relat_1 @ A ) =>
% 0.90/1.14       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.90/1.14  thf('91', plain,
% 0.90/1.14      (![X6 : $i]:
% 0.90/1.14         (((k5_relat_1 @ X6 @ (k6_relat_1 @ (k2_relat_1 @ X6))) = (X6))
% 0.90/1.14          | ~ (v1_relat_1 @ X6))),
% 0.90/1.14      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.90/1.14  thf('92', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.90/1.14            = (k2_funct_1 @ X0))
% 0.90/1.14          | ~ (v1_relat_1 @ X0)
% 0.90/1.14          | ~ (v1_funct_1 @ X0)
% 0.90/1.14          | ~ (v2_funct_1 @ X0)
% 0.90/1.14          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.90/1.14      inference('sup+', [status(thm)], ['90', '91'])).
% 0.90/1.14  thf('93', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (~ (v1_relat_1 @ X0)
% 0.90/1.14          | ~ (v1_funct_1 @ X0)
% 0.90/1.14          | ~ (v2_funct_1 @ X0)
% 0.90/1.14          | ~ (v1_funct_1 @ X0)
% 0.90/1.14          | ~ (v1_relat_1 @ X0)
% 0.90/1.14          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.90/1.14              = (k2_funct_1 @ X0)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['89', '92'])).
% 0.90/1.14  thf('94', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.90/1.14            = (k2_funct_1 @ X0))
% 0.90/1.14          | ~ (v2_funct_1 @ X0)
% 0.90/1.14          | ~ (v1_funct_1 @ X0)
% 0.90/1.14          | ~ (v1_relat_1 @ X0))),
% 0.90/1.14      inference('simplify', [status(thm)], ['93'])).
% 0.90/1.14  thf('95', plain,
% 0.90/1.14      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_relat_1 @ sk_A))
% 0.90/1.14          = (k2_funct_1 @ sk_C))
% 0.90/1.14        | ~ (v1_relat_1 @ sk_C)
% 0.90/1.14        | ~ (v1_funct_1 @ sk_C)
% 0.90/1.14        | ~ (v2_funct_1 @ sk_C))),
% 0.90/1.14      inference('sup+', [status(thm)], ['88', '94'])).
% 0.90/1.14  thf('96', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.14      inference('sup-', [status(thm)], ['46', '47'])).
% 0.90/1.14  thf('97', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('98', plain, ((v2_funct_1 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('99', plain,
% 0.90/1.14      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_relat_1 @ sk_A))
% 0.90/1.14         = (k2_funct_1 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['95', '96', '97', '98'])).
% 0.90/1.14  thf('100', plain, ((v1_relat_1 @ sk_D)),
% 0.90/1.14      inference('sup-', [status(thm)], ['71', '72'])).
% 0.90/1.14  thf('101', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['54', '74', '99', '100'])).
% 0.90/1.14  thf('102', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('103', plain, ($false),
% 0.90/1.14      inference('simplify_reflect-', [status(thm)], ['101', '102'])).
% 0.90/1.14  
% 0.90/1.14  % SZS output end Refutation
% 0.90/1.14  
% 0.90/1.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

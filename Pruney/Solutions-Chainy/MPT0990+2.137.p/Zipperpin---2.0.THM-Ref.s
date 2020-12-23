%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1m2CcGW7Ry

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:18 EST 2020

% Result     : Theorem 2.73s
% Output     : Refutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :  208 (1117 expanded)
%              Number of leaves         :   52 ( 343 expanded)
%              Depth                    :   27
%              Number of atoms          : 1988 (29238 expanded)
%              Number of equality atoms :  138 (1944 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
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
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( ( k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41 )
        = ( k5_relat_1 @ X38 @ X41 ) ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X35 ) ) ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( X26 = X29 )
      | ~ ( r2_relset_1 @ X27 @ X28 @ X26 @ X29 ) ) ),
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
    ! [X37: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('27',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','28'])).

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

thf('30',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ( X21
        = ( k2_funct_1 @ X22 ) )
      | ( ( k5_relat_1 @ X21 @ X22 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X22 ) ) )
      | ( ( k2_relat_1 @ X21 )
       != ( k1_relat_1 @ X22 ) )
      | ~ ( v2_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('31',plain,
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
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('33',plain,(
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

thf('34',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( r2_relset_1 @ X46 @ X46 @ ( k1_partfun1 @ X46 @ X47 @ X47 @ X46 @ X45 @ X48 ) @ ( k6_partfun1 @ X46 ) )
      | ( ( k2_relset_1 @ X47 @ X46 @ X48 )
        = X46 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) )
      | ~ ( v1_funct_2 @ X48 @ X47 @ X46 )
      | ~ ( v1_funct_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('35',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('36',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( r2_relset_1 @ X46 @ X46 @ ( k1_partfun1 @ X46 @ X47 @ X47 @ X46 @ X45 @ X48 ) @ ( k6_relat_1 @ X46 ) )
      | ( ( k2_relset_1 @ X47 @ X46 @ X48 )
        = X46 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) )
      | ~ ( v1_funct_2 @ X48 @ X47 @ X46 )
      | ~ ( v1_funct_1 @ X48 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['32','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('43',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('44',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['41','44','45','46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('50',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('52',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('53',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('57',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('63',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('65',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['31','48','53','54','59','60','65'])).

thf('67',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('69',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('70',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
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

thf('72',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_funct_2 @ X53 @ X54 @ X55 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X55 ) ) )
      | ( zip_tseitin_0 @ X53 @ X56 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X57 @ X54 @ X54 @ X55 @ X56 @ X53 ) )
      | ( zip_tseitin_1 @ X55 @ X54 )
      | ( ( k2_relset_1 @ X57 @ X54 @ X56 )
       != X54 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X54 ) ) )
      | ~ ( v1_funct_2 @ X56 @ X57 @ X54 )
      | ~ ( v1_funct_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('73',plain,(
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
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['70','76'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('78',plain,(
    ! [X18: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('79',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['77','78','79','80','81','82'])).

thf('84',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X51: $i,X52: $i] :
      ( ( X51 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('86',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X49: $i,X50: $i] :
      ( ( v2_funct_1 @ X50 )
      | ~ ( zip_tseitin_0 @ X50 @ X49 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('90',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['67','90'])).

thf('92',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('93',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k2_funct_1 @ X15 )
        = ( k4_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('94',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k2_funct_1 @ sk_D )
      = ( k4_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['51','52'])).

thf('96',plain,
    ( ( ( k2_funct_1 @ sk_D )
      = ( k4_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['88','89'])).

thf('98',plain,
    ( ( k2_funct_1 @ sk_D )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( sk_C
      = ( k4_relat_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['91','98'])).

thf('100',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['41','44','45','46','47'])).

thf('101',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['41','44','45','46','47'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('102',plain,(
    ! [X10: $i] :
      ( ( ( k2_relat_1 @ X10 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('103',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X12 ) @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ sk_D @ ( k4_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['101','104'])).

thf('106',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['51','52'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ sk_D @ ( k4_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ ( k5_relat_1 @ sk_D @ ( k4_relat_1 @ sk_D ) ) )
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['100','107'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('110',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['51','52'])).

thf('112',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_D @ ( k4_relat_1 @ sk_D ) ) )
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['108','110','111'])).

thf('113',plain,
    ( ( k2_funct_1 @ sk_D )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['96','97'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('114',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('115',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['51','52'])).

thf('117',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('119',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_D @ ( k4_relat_1 @ sk_D ) ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['112','118'])).

thf('120',plain,(
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

thf('121',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ( X58 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X59 )
      | ~ ( v1_funct_2 @ X59 @ X60 @ X58 )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X58 ) ) )
      | ( ( k5_relat_1 @ X59 @ ( k2_funct_1 @ X59 ) )
        = ( k6_partfun1 @ X60 ) )
      | ~ ( v2_funct_1 @ X59 )
      | ( ( k2_relset_1 @ X60 @ X58 @ X59 )
       != X58 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('122',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('123',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ( X58 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X59 )
      | ~ ( v1_funct_2 @ X59 @ X60 @ X58 )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X58 ) ) )
      | ( ( k5_relat_1 @ X59 @ ( k2_funct_1 @ X59 ) )
        = ( k6_relat_1 @ X60 ) )
      | ~ ( v2_funct_1 @ X59 )
      | ( ( k2_relset_1 @ X60 @ X58 @ X59 )
       != X58 ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['120','123'])).

thf('125',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('126',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['41','44','45','46','47'])).

thf('127',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['124','127','128','129'])).

thf('131',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['131','132'])).

thf('134',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['88','89'])).

thf('135',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,
    ( ( k2_funct_1 @ sk_D )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('137',plain,
    ( ( k5_relat_1 @ sk_D @ ( k4_relat_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['135','136'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('138',plain,(
    ! [X13: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('139',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['119','137','138'])).

thf('140',plain,
    ( ( sk_C
      = ( k4_relat_1 @ sk_D ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['99','139'])).

thf('141',plain,
    ( sk_C
    = ( k4_relat_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['140'])).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('142',plain,(
    ! [X7: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X7 ) )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('143',plain,
    ( ( ( k4_relat_1 @ sk_C )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['141','142'])).

thf('144',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['51','52'])).

thf('145',plain,
    ( ( k4_relat_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k2_funct_1 @ X15 )
        = ( k4_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('149',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['63','64'])).

thf('151',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['149','150','151'])).

thf('153',plain,(
    sk_D
 != ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['146','152'])).

thf('154',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['145','153'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1m2CcGW7Ry
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:57:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.73/2.94  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.73/2.94  % Solved by: fo/fo7.sh
% 2.73/2.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.73/2.94  % done 1772 iterations in 2.480s
% 2.73/2.94  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.73/2.94  % SZS output start Refutation
% 2.73/2.94  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.73/2.94  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 2.73/2.94  thf(sk_C_type, type, sk_C: $i).
% 2.73/2.94  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 2.73/2.94  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.73/2.94  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.73/2.94  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.73/2.94  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.73/2.94  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.73/2.94  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.73/2.94  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.73/2.94  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.73/2.94  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 2.73/2.94  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.73/2.94  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.73/2.94  thf(sk_A_type, type, sk_A: $i).
% 2.73/2.94  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.73/2.94  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.73/2.94  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.73/2.94  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.73/2.94  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.73/2.94  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.73/2.94  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.73/2.94  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.73/2.94  thf(sk_D_type, type, sk_D: $i).
% 2.73/2.94  thf(sk_B_type, type, sk_B: $i).
% 2.73/2.94  thf(t36_funct_2, conjecture,
% 2.73/2.94    (![A:$i,B:$i,C:$i]:
% 2.73/2.94     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.73/2.94         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.73/2.94       ( ![D:$i]:
% 2.73/2.94         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.73/2.94             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.73/2.94           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.73/2.94               ( r2_relset_1 @
% 2.73/2.94                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.73/2.94                 ( k6_partfun1 @ A ) ) & 
% 2.73/2.94               ( v2_funct_1 @ C ) ) =>
% 2.73/2.94             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.73/2.94               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 2.73/2.94  thf(zf_stmt_0, negated_conjecture,
% 2.73/2.94    (~( ![A:$i,B:$i,C:$i]:
% 2.73/2.94        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.73/2.94            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.73/2.94          ( ![D:$i]:
% 2.73/2.94            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.73/2.94                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.73/2.94              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.73/2.94                  ( r2_relset_1 @
% 2.73/2.94                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.73/2.94                    ( k6_partfun1 @ A ) ) & 
% 2.73/2.94                  ( v2_funct_1 @ C ) ) =>
% 2.73/2.94                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.73/2.94                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 2.73/2.94    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 2.73/2.94  thf('0', plain,
% 2.73/2.94      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.73/2.94        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.73/2.94        (k6_partfun1 @ sk_A))),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf(redefinition_k6_partfun1, axiom,
% 2.73/2.94    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.73/2.94  thf('1', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 2.73/2.94      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.73/2.94  thf('2', plain,
% 2.73/2.94      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.73/2.94        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.73/2.94        (k6_relat_1 @ sk_A))),
% 2.73/2.94      inference('demod', [status(thm)], ['0', '1'])).
% 2.73/2.94  thf('3', plain,
% 2.73/2.94      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('4', plain,
% 2.73/2.94      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf(redefinition_k1_partfun1, axiom,
% 2.73/2.94    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.73/2.94     ( ( ( v1_funct_1 @ E ) & 
% 2.73/2.94         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.73/2.94         ( v1_funct_1 @ F ) & 
% 2.73/2.94         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.73/2.94       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.73/2.94  thf('5', plain,
% 2.73/2.94      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 2.73/2.94         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 2.73/2.94          | ~ (v1_funct_1 @ X38)
% 2.73/2.94          | ~ (v1_funct_1 @ X41)
% 2.73/2.94          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 2.73/2.94          | ((k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41)
% 2.73/2.94              = (k5_relat_1 @ X38 @ X41)))),
% 2.73/2.94      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 2.73/2.94  thf('6', plain,
% 2.73/2.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.73/2.94         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.73/2.94            = (k5_relat_1 @ sk_C @ X0))
% 2.73/2.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.73/2.94          | ~ (v1_funct_1 @ X0)
% 2.73/2.94          | ~ (v1_funct_1 @ sk_C))),
% 2.73/2.94      inference('sup-', [status(thm)], ['4', '5'])).
% 2.73/2.94  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('8', plain,
% 2.73/2.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.73/2.94         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.73/2.94            = (k5_relat_1 @ sk_C @ X0))
% 2.73/2.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.73/2.94          | ~ (v1_funct_1 @ X0))),
% 2.73/2.94      inference('demod', [status(thm)], ['6', '7'])).
% 2.73/2.94  thf('9', plain,
% 2.73/2.94      ((~ (v1_funct_1 @ sk_D)
% 2.73/2.94        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.73/2.94            = (k5_relat_1 @ sk_C @ sk_D)))),
% 2.73/2.94      inference('sup-', [status(thm)], ['3', '8'])).
% 2.73/2.94  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('11', plain,
% 2.73/2.94      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.73/2.94         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.73/2.94      inference('demod', [status(thm)], ['9', '10'])).
% 2.73/2.94  thf('12', plain,
% 2.73/2.94      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 2.73/2.94        (k6_relat_1 @ sk_A))),
% 2.73/2.94      inference('demod', [status(thm)], ['2', '11'])).
% 2.73/2.94  thf('13', plain,
% 2.73/2.94      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('14', plain,
% 2.73/2.94      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf(dt_k1_partfun1, axiom,
% 2.73/2.94    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.73/2.94     ( ( ( v1_funct_1 @ E ) & 
% 2.73/2.94         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.73/2.94         ( v1_funct_1 @ F ) & 
% 2.73/2.94         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.73/2.94       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.73/2.94         ( m1_subset_1 @
% 2.73/2.94           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.73/2.94           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.73/2.94  thf('15', plain,
% 2.73/2.94      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 2.73/2.94         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 2.73/2.94          | ~ (v1_funct_1 @ X30)
% 2.73/2.94          | ~ (v1_funct_1 @ X33)
% 2.73/2.94          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 2.73/2.94          | (m1_subset_1 @ (k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33) @ 
% 2.73/2.94             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X35))))),
% 2.73/2.94      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.73/2.94  thf('16', plain,
% 2.73/2.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.73/2.94         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.73/2.94           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.73/2.94          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.73/2.94          | ~ (v1_funct_1 @ X1)
% 2.73/2.94          | ~ (v1_funct_1 @ sk_C))),
% 2.73/2.94      inference('sup-', [status(thm)], ['14', '15'])).
% 2.73/2.94  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('18', plain,
% 2.73/2.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.73/2.94         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.73/2.94           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.73/2.94          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.73/2.94          | ~ (v1_funct_1 @ X1))),
% 2.73/2.94      inference('demod', [status(thm)], ['16', '17'])).
% 2.73/2.94  thf('19', plain,
% 2.73/2.94      ((~ (v1_funct_1 @ sk_D)
% 2.73/2.94        | (m1_subset_1 @ 
% 2.73/2.94           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.73/2.94           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.73/2.94      inference('sup-', [status(thm)], ['13', '18'])).
% 2.73/2.94  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('21', plain,
% 2.73/2.94      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.73/2.94         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.73/2.94      inference('demod', [status(thm)], ['9', '10'])).
% 2.73/2.94  thf('22', plain,
% 2.73/2.94      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 2.73/2.94        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.73/2.94      inference('demod', [status(thm)], ['19', '20', '21'])).
% 2.73/2.94  thf(redefinition_r2_relset_1, axiom,
% 2.73/2.94    (![A:$i,B:$i,C:$i,D:$i]:
% 2.73/2.94     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.73/2.94         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.73/2.94       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.73/2.94  thf('23', plain,
% 2.73/2.94      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 2.73/2.94         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 2.73/2.94          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 2.73/2.94          | ((X26) = (X29))
% 2.73/2.94          | ~ (r2_relset_1 @ X27 @ X28 @ X26 @ X29))),
% 2.73/2.94      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.73/2.94  thf('24', plain,
% 2.73/2.94      (![X0 : $i]:
% 2.73/2.94         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 2.73/2.94          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 2.73/2.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.73/2.94      inference('sup-', [status(thm)], ['22', '23'])).
% 2.73/2.94  thf('25', plain,
% 2.73/2.94      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 2.73/2.94           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.73/2.94        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A)))),
% 2.73/2.94      inference('sup-', [status(thm)], ['12', '24'])).
% 2.73/2.94  thf(dt_k6_partfun1, axiom,
% 2.73/2.94    (![A:$i]:
% 2.73/2.94     ( ( m1_subset_1 @
% 2.73/2.94         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 2.73/2.94       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 2.73/2.94  thf('26', plain,
% 2.73/2.94      (![X37 : $i]:
% 2.73/2.94         (m1_subset_1 @ (k6_partfun1 @ X37) @ 
% 2.73/2.94          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))),
% 2.73/2.94      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 2.73/2.94  thf('27', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 2.73/2.94      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.73/2.94  thf('28', plain,
% 2.73/2.94      (![X37 : $i]:
% 2.73/2.94         (m1_subset_1 @ (k6_relat_1 @ X37) @ 
% 2.73/2.94          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))),
% 2.73/2.94      inference('demod', [status(thm)], ['26', '27'])).
% 2.73/2.94  thf('29', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 2.73/2.94      inference('demod', [status(thm)], ['25', '28'])).
% 2.73/2.94  thf(t64_funct_1, axiom,
% 2.73/2.94    (![A:$i]:
% 2.73/2.94     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.73/2.94       ( ![B:$i]:
% 2.73/2.94         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.73/2.94           ( ( ( v2_funct_1 @ A ) & 
% 2.73/2.94               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 2.73/2.94               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 2.73/2.94             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.73/2.94  thf('30', plain,
% 2.73/2.94      (![X21 : $i, X22 : $i]:
% 2.73/2.94         (~ (v1_relat_1 @ X21)
% 2.73/2.94          | ~ (v1_funct_1 @ X21)
% 2.73/2.94          | ((X21) = (k2_funct_1 @ X22))
% 2.73/2.94          | ((k5_relat_1 @ X21 @ X22) != (k6_relat_1 @ (k2_relat_1 @ X22)))
% 2.73/2.94          | ((k2_relat_1 @ X21) != (k1_relat_1 @ X22))
% 2.73/2.94          | ~ (v2_funct_1 @ X22)
% 2.73/2.94          | ~ (v1_funct_1 @ X22)
% 2.73/2.94          | ~ (v1_relat_1 @ X22))),
% 2.73/2.94      inference('cnf', [status(esa)], [t64_funct_1])).
% 2.73/2.94  thf('31', plain,
% 2.73/2.94      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ (k2_relat_1 @ sk_D)))
% 2.73/2.94        | ~ (v1_relat_1 @ sk_D)
% 2.73/2.94        | ~ (v1_funct_1 @ sk_D)
% 2.73/2.94        | ~ (v2_funct_1 @ sk_D)
% 2.73/2.94        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 2.73/2.94        | ((sk_C) = (k2_funct_1 @ sk_D))
% 2.73/2.94        | ~ (v1_funct_1 @ sk_C)
% 2.73/2.94        | ~ (v1_relat_1 @ sk_C))),
% 2.73/2.94      inference('sup-', [status(thm)], ['29', '30'])).
% 2.73/2.94  thf('32', plain,
% 2.73/2.94      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.73/2.94        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.73/2.94        (k6_relat_1 @ sk_A))),
% 2.73/2.94      inference('demod', [status(thm)], ['0', '1'])).
% 2.73/2.94  thf('33', plain,
% 2.73/2.94      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf(t24_funct_2, axiom,
% 2.73/2.94    (![A:$i,B:$i,C:$i]:
% 2.73/2.94     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.73/2.94         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.73/2.94       ( ![D:$i]:
% 2.73/2.94         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.73/2.94             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.73/2.94           ( ( r2_relset_1 @
% 2.73/2.94               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 2.73/2.94               ( k6_partfun1 @ B ) ) =>
% 2.73/2.94             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 2.73/2.94  thf('34', plain,
% 2.73/2.94      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 2.73/2.94         (~ (v1_funct_1 @ X45)
% 2.73/2.94          | ~ (v1_funct_2 @ X45 @ X46 @ X47)
% 2.73/2.94          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 2.73/2.94          | ~ (r2_relset_1 @ X46 @ X46 @ 
% 2.73/2.94               (k1_partfun1 @ X46 @ X47 @ X47 @ X46 @ X45 @ X48) @ 
% 2.73/2.94               (k6_partfun1 @ X46))
% 2.73/2.94          | ((k2_relset_1 @ X47 @ X46 @ X48) = (X46))
% 2.73/2.94          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46)))
% 2.73/2.94          | ~ (v1_funct_2 @ X48 @ X47 @ X46)
% 2.73/2.94          | ~ (v1_funct_1 @ X48))),
% 2.73/2.94      inference('cnf', [status(esa)], [t24_funct_2])).
% 2.73/2.94  thf('35', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 2.73/2.94      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.73/2.94  thf('36', plain,
% 2.73/2.94      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 2.73/2.94         (~ (v1_funct_1 @ X45)
% 2.73/2.94          | ~ (v1_funct_2 @ X45 @ X46 @ X47)
% 2.73/2.94          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 2.73/2.94          | ~ (r2_relset_1 @ X46 @ X46 @ 
% 2.73/2.94               (k1_partfun1 @ X46 @ X47 @ X47 @ X46 @ X45 @ X48) @ 
% 2.73/2.94               (k6_relat_1 @ X46))
% 2.73/2.94          | ((k2_relset_1 @ X47 @ X46 @ X48) = (X46))
% 2.73/2.94          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46)))
% 2.73/2.94          | ~ (v1_funct_2 @ X48 @ X47 @ X46)
% 2.73/2.94          | ~ (v1_funct_1 @ X48))),
% 2.73/2.94      inference('demod', [status(thm)], ['34', '35'])).
% 2.73/2.94  thf('37', plain,
% 2.73/2.94      (![X0 : $i]:
% 2.73/2.94         (~ (v1_funct_1 @ X0)
% 2.73/2.94          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.73/2.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.73/2.94          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.73/2.94          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.73/2.94               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.73/2.94               (k6_relat_1 @ sk_A))
% 2.73/2.94          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.73/2.94          | ~ (v1_funct_1 @ sk_C))),
% 2.73/2.94      inference('sup-', [status(thm)], ['33', '36'])).
% 2.73/2.94  thf('38', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('39', plain, ((v1_funct_1 @ sk_C)),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('40', plain,
% 2.73/2.94      (![X0 : $i]:
% 2.73/2.94         (~ (v1_funct_1 @ X0)
% 2.73/2.94          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.73/2.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.73/2.94          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.73/2.94          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.73/2.94               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.73/2.94               (k6_relat_1 @ sk_A)))),
% 2.73/2.94      inference('demod', [status(thm)], ['37', '38', '39'])).
% 2.73/2.94  thf('41', plain,
% 2.73/2.94      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 2.73/2.94        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.73/2.94        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.73/2.94        | ~ (v1_funct_1 @ sk_D))),
% 2.73/2.94      inference('sup-', [status(thm)], ['32', '40'])).
% 2.73/2.94  thf('42', plain,
% 2.73/2.94      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf(redefinition_k2_relset_1, axiom,
% 2.73/2.94    (![A:$i,B:$i,C:$i]:
% 2.73/2.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.73/2.94       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.73/2.94  thf('43', plain,
% 2.73/2.94      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.73/2.94         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 2.73/2.94          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 2.73/2.94      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.73/2.94  thf('44', plain,
% 2.73/2.94      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.73/2.94      inference('sup-', [status(thm)], ['42', '43'])).
% 2.73/2.94  thf('45', plain,
% 2.73/2.94      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('46', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('47', plain, ((v1_funct_1 @ sk_D)),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('48', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.73/2.94      inference('demod', [status(thm)], ['41', '44', '45', '46', '47'])).
% 2.73/2.94  thf('49', plain,
% 2.73/2.94      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf(cc2_relat_1, axiom,
% 2.73/2.94    (![A:$i]:
% 2.73/2.94     ( ( v1_relat_1 @ A ) =>
% 2.73/2.94       ( ![B:$i]:
% 2.73/2.94         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.73/2.94  thf('50', plain,
% 2.73/2.94      (![X3 : $i, X4 : $i]:
% 2.73/2.94         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 2.73/2.94          | (v1_relat_1 @ X3)
% 2.73/2.94          | ~ (v1_relat_1 @ X4))),
% 2.73/2.94      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.73/2.94  thf('51', plain,
% 2.73/2.94      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 2.73/2.94      inference('sup-', [status(thm)], ['49', '50'])).
% 2.73/2.94  thf(fc6_relat_1, axiom,
% 2.73/2.94    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.73/2.94  thf('52', plain,
% 2.73/2.94      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 2.73/2.94      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.73/2.94  thf('53', plain, ((v1_relat_1 @ sk_D)),
% 2.73/2.94      inference('demod', [status(thm)], ['51', '52'])).
% 2.73/2.94  thf('54', plain, ((v1_funct_1 @ sk_D)),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('55', plain,
% 2.73/2.94      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('56', plain,
% 2.73/2.94      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.73/2.94         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 2.73/2.94          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 2.73/2.94      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.73/2.94  thf('57', plain,
% 2.73/2.94      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 2.73/2.94      inference('sup-', [status(thm)], ['55', '56'])).
% 2.73/2.94  thf('58', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('59', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.73/2.94      inference('sup+', [status(thm)], ['57', '58'])).
% 2.73/2.94  thf('60', plain, ((v1_funct_1 @ sk_C)),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('61', plain,
% 2.73/2.94      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('62', plain,
% 2.73/2.94      (![X3 : $i, X4 : $i]:
% 2.73/2.94         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 2.73/2.94          | (v1_relat_1 @ X3)
% 2.73/2.94          | ~ (v1_relat_1 @ X4))),
% 2.73/2.94      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.73/2.94  thf('63', plain,
% 2.73/2.94      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 2.73/2.94      inference('sup-', [status(thm)], ['61', '62'])).
% 2.73/2.94  thf('64', plain,
% 2.73/2.94      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 2.73/2.94      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.73/2.94  thf('65', plain, ((v1_relat_1 @ sk_C)),
% 2.73/2.94      inference('demod', [status(thm)], ['63', '64'])).
% 2.73/2.94  thf('66', plain,
% 2.73/2.94      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ sk_A))
% 2.73/2.94        | ~ (v2_funct_1 @ sk_D)
% 2.73/2.94        | ((sk_B) != (k1_relat_1 @ sk_D))
% 2.73/2.94        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 2.73/2.94      inference('demod', [status(thm)],
% 2.73/2.94                ['31', '48', '53', '54', '59', '60', '65'])).
% 2.73/2.94  thf('67', plain,
% 2.73/2.94      ((((sk_C) = (k2_funct_1 @ sk_D))
% 2.73/2.94        | ((sk_B) != (k1_relat_1 @ sk_D))
% 2.73/2.94        | ~ (v2_funct_1 @ sk_D))),
% 2.73/2.94      inference('simplify', [status(thm)], ['66'])).
% 2.73/2.94  thf('68', plain,
% 2.73/2.94      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.73/2.94         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.73/2.94      inference('demod', [status(thm)], ['9', '10'])).
% 2.73/2.94  thf('69', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 2.73/2.94      inference('demod', [status(thm)], ['25', '28'])).
% 2.73/2.94  thf('70', plain,
% 2.73/2.94      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.73/2.94         = (k6_relat_1 @ sk_A))),
% 2.73/2.94      inference('demod', [status(thm)], ['68', '69'])).
% 2.73/2.94  thf('71', plain,
% 2.73/2.94      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf(t30_funct_2, axiom,
% 2.73/2.94    (![A:$i,B:$i,C:$i,D:$i]:
% 2.73/2.94     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.73/2.94         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 2.73/2.94       ( ![E:$i]:
% 2.73/2.94         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 2.73/2.94             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 2.73/2.94           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 2.73/2.94               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 2.73/2.94             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 2.73/2.94               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 2.73/2.94  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 2.73/2.94  thf(zf_stmt_2, axiom,
% 2.73/2.94    (![C:$i,B:$i]:
% 2.73/2.94     ( ( zip_tseitin_1 @ C @ B ) =>
% 2.73/2.94       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 2.73/2.94  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 2.73/2.94  thf(zf_stmt_4, axiom,
% 2.73/2.94    (![E:$i,D:$i]:
% 2.73/2.94     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 2.73/2.94  thf(zf_stmt_5, axiom,
% 2.73/2.94    (![A:$i,B:$i,C:$i,D:$i]:
% 2.73/2.94     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.73/2.94         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.73/2.94       ( ![E:$i]:
% 2.73/2.94         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.73/2.94             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.73/2.94           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 2.73/2.94               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 2.73/2.94             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 2.73/2.94  thf('72', plain,
% 2.73/2.94      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 2.73/2.94         (~ (v1_funct_1 @ X53)
% 2.73/2.94          | ~ (v1_funct_2 @ X53 @ X54 @ X55)
% 2.73/2.94          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X55)))
% 2.73/2.94          | (zip_tseitin_0 @ X53 @ X56)
% 2.73/2.94          | ~ (v2_funct_1 @ (k1_partfun1 @ X57 @ X54 @ X54 @ X55 @ X56 @ X53))
% 2.73/2.94          | (zip_tseitin_1 @ X55 @ X54)
% 2.73/2.94          | ((k2_relset_1 @ X57 @ X54 @ X56) != (X54))
% 2.73/2.94          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X54)))
% 2.73/2.94          | ~ (v1_funct_2 @ X56 @ X57 @ X54)
% 2.73/2.94          | ~ (v1_funct_1 @ X56))),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.73/2.94  thf('73', plain,
% 2.73/2.94      (![X0 : $i, X1 : $i]:
% 2.73/2.94         (~ (v1_funct_1 @ X0)
% 2.73/2.94          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.73/2.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.73/2.94          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 2.73/2.94          | (zip_tseitin_1 @ sk_A @ sk_B)
% 2.73/2.94          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 2.73/2.94          | (zip_tseitin_0 @ sk_D @ X0)
% 2.73/2.94          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.73/2.94          | ~ (v1_funct_1 @ sk_D))),
% 2.73/2.94      inference('sup-', [status(thm)], ['71', '72'])).
% 2.73/2.94  thf('74', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('75', plain, ((v1_funct_1 @ sk_D)),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('76', plain,
% 2.73/2.94      (![X0 : $i, X1 : $i]:
% 2.73/2.94         (~ (v1_funct_1 @ X0)
% 2.73/2.94          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.73/2.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.73/2.94          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 2.73/2.94          | (zip_tseitin_1 @ sk_A @ sk_B)
% 2.73/2.94          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 2.73/2.94          | (zip_tseitin_0 @ sk_D @ X0))),
% 2.73/2.94      inference('demod', [status(thm)], ['73', '74', '75'])).
% 2.73/2.94  thf('77', plain,
% 2.73/2.94      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 2.73/2.94        | (zip_tseitin_0 @ sk_D @ sk_C)
% 2.73/2.94        | (zip_tseitin_1 @ sk_A @ sk_B)
% 2.73/2.94        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 2.73/2.94        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 2.73/2.94        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.73/2.94        | ~ (v1_funct_1 @ sk_C))),
% 2.73/2.94      inference('sup-', [status(thm)], ['70', '76'])).
% 2.73/2.94  thf(fc4_funct_1, axiom,
% 2.73/2.94    (![A:$i]:
% 2.73/2.94     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 2.73/2.94       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 2.73/2.94  thf('78', plain, (![X18 : $i]: (v2_funct_1 @ (k6_relat_1 @ X18))),
% 2.73/2.94      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.73/2.94  thf('79', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('80', plain,
% 2.73/2.94      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('81', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('82', plain, ((v1_funct_1 @ sk_C)),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('83', plain,
% 2.73/2.94      (((zip_tseitin_0 @ sk_D @ sk_C)
% 2.73/2.94        | (zip_tseitin_1 @ sk_A @ sk_B)
% 2.73/2.94        | ((sk_B) != (sk_B)))),
% 2.73/2.94      inference('demod', [status(thm)], ['77', '78', '79', '80', '81', '82'])).
% 2.73/2.94  thf('84', plain,
% 2.73/2.94      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 2.73/2.94      inference('simplify', [status(thm)], ['83'])).
% 2.73/2.94  thf('85', plain,
% 2.73/2.94      (![X51 : $i, X52 : $i]:
% 2.73/2.94         (((X51) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X51 @ X52))),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.73/2.94  thf('86', plain,
% 2.73/2.94      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 2.73/2.94      inference('sup-', [status(thm)], ['84', '85'])).
% 2.73/2.94  thf('87', plain, (((sk_A) != (k1_xboole_0))),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('88', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 2.73/2.94      inference('simplify_reflect-', [status(thm)], ['86', '87'])).
% 2.73/2.94  thf('89', plain,
% 2.73/2.94      (![X49 : $i, X50 : $i]:
% 2.73/2.94         ((v2_funct_1 @ X50) | ~ (zip_tseitin_0 @ X50 @ X49))),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_4])).
% 2.73/2.94  thf('90', plain, ((v2_funct_1 @ sk_D)),
% 2.73/2.94      inference('sup-', [status(thm)], ['88', '89'])).
% 2.73/2.94  thf('91', plain,
% 2.73/2.94      ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (k1_relat_1 @ sk_D)))),
% 2.73/2.94      inference('demod', [status(thm)], ['67', '90'])).
% 2.73/2.94  thf('92', plain, ((v1_funct_1 @ sk_D)),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf(d9_funct_1, axiom,
% 2.73/2.94    (![A:$i]:
% 2.73/2.94     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.73/2.94       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 2.73/2.94  thf('93', plain,
% 2.73/2.94      (![X15 : $i]:
% 2.73/2.94         (~ (v2_funct_1 @ X15)
% 2.73/2.94          | ((k2_funct_1 @ X15) = (k4_relat_1 @ X15))
% 2.73/2.94          | ~ (v1_funct_1 @ X15)
% 2.73/2.94          | ~ (v1_relat_1 @ X15))),
% 2.73/2.94      inference('cnf', [status(esa)], [d9_funct_1])).
% 2.73/2.94  thf('94', plain,
% 2.73/2.94      ((~ (v1_relat_1 @ sk_D)
% 2.73/2.94        | ((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))
% 2.73/2.94        | ~ (v2_funct_1 @ sk_D))),
% 2.73/2.94      inference('sup-', [status(thm)], ['92', '93'])).
% 2.73/2.94  thf('95', plain, ((v1_relat_1 @ sk_D)),
% 2.73/2.94      inference('demod', [status(thm)], ['51', '52'])).
% 2.73/2.94  thf('96', plain,
% 2.73/2.94      ((((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 2.73/2.94      inference('demod', [status(thm)], ['94', '95'])).
% 2.73/2.94  thf('97', plain, ((v2_funct_1 @ sk_D)),
% 2.73/2.94      inference('sup-', [status(thm)], ['88', '89'])).
% 2.73/2.94  thf('98', plain, (((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))),
% 2.73/2.94      inference('demod', [status(thm)], ['96', '97'])).
% 2.73/2.94  thf('99', plain,
% 2.73/2.94      ((((sk_C) = (k4_relat_1 @ sk_D)) | ((sk_B) != (k1_relat_1 @ sk_D)))),
% 2.73/2.94      inference('demod', [status(thm)], ['91', '98'])).
% 2.73/2.94  thf('100', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.73/2.94      inference('demod', [status(thm)], ['41', '44', '45', '46', '47'])).
% 2.73/2.94  thf('101', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.73/2.94      inference('demod', [status(thm)], ['41', '44', '45', '46', '47'])).
% 2.73/2.94  thf(t37_relat_1, axiom,
% 2.73/2.94    (![A:$i]:
% 2.73/2.94     ( ( v1_relat_1 @ A ) =>
% 2.73/2.94       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 2.73/2.94         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 2.73/2.94  thf('102', plain,
% 2.73/2.94      (![X10 : $i]:
% 2.73/2.94         (((k2_relat_1 @ X10) = (k1_relat_1 @ (k4_relat_1 @ X10)))
% 2.73/2.94          | ~ (v1_relat_1 @ X10))),
% 2.73/2.94      inference('cnf', [status(esa)], [t37_relat_1])).
% 2.73/2.94  thf(t46_relat_1, axiom,
% 2.73/2.94    (![A:$i]:
% 2.73/2.94     ( ( v1_relat_1 @ A ) =>
% 2.73/2.94       ( ![B:$i]:
% 2.73/2.94         ( ( v1_relat_1 @ B ) =>
% 2.73/2.94           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 2.73/2.94             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 2.73/2.94  thf('103', plain,
% 2.73/2.94      (![X11 : $i, X12 : $i]:
% 2.73/2.94         (~ (v1_relat_1 @ X11)
% 2.73/2.94          | ((k1_relat_1 @ (k5_relat_1 @ X12 @ X11)) = (k1_relat_1 @ X12))
% 2.73/2.94          | ~ (r1_tarski @ (k2_relat_1 @ X12) @ (k1_relat_1 @ X11))
% 2.73/2.94          | ~ (v1_relat_1 @ X12))),
% 2.73/2.94      inference('cnf', [status(esa)], [t46_relat_1])).
% 2.73/2.94  thf('104', plain,
% 2.73/2.94      (![X0 : $i, X1 : $i]:
% 2.73/2.94         (~ (r1_tarski @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0))
% 2.73/2.94          | ~ (v1_relat_1 @ X0)
% 2.73/2.94          | ~ (v1_relat_1 @ X1)
% 2.73/2.94          | ((k1_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0)))
% 2.73/2.94              = (k1_relat_1 @ X1))
% 2.73/2.94          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 2.73/2.94      inference('sup-', [status(thm)], ['102', '103'])).
% 2.73/2.94  thf('105', plain,
% 2.73/2.94      (![X0 : $i]:
% 2.73/2.94         (~ (r1_tarski @ sk_A @ (k2_relat_1 @ X0))
% 2.73/2.94          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 2.73/2.94          | ((k1_relat_1 @ (k5_relat_1 @ sk_D @ (k4_relat_1 @ X0)))
% 2.73/2.94              = (k1_relat_1 @ sk_D))
% 2.73/2.94          | ~ (v1_relat_1 @ sk_D)
% 2.73/2.94          | ~ (v1_relat_1 @ X0))),
% 2.73/2.94      inference('sup-', [status(thm)], ['101', '104'])).
% 2.73/2.94  thf('106', plain, ((v1_relat_1 @ sk_D)),
% 2.73/2.94      inference('demod', [status(thm)], ['51', '52'])).
% 2.73/2.94  thf('107', plain,
% 2.73/2.94      (![X0 : $i]:
% 2.73/2.94         (~ (r1_tarski @ sk_A @ (k2_relat_1 @ X0))
% 2.73/2.94          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 2.73/2.94          | ((k1_relat_1 @ (k5_relat_1 @ sk_D @ (k4_relat_1 @ X0)))
% 2.73/2.94              = (k1_relat_1 @ sk_D))
% 2.73/2.94          | ~ (v1_relat_1 @ X0))),
% 2.73/2.94      inference('demod', [status(thm)], ['105', '106'])).
% 2.73/2.94  thf('108', plain,
% 2.73/2.94      ((~ (r1_tarski @ sk_A @ sk_A)
% 2.73/2.94        | ~ (v1_relat_1 @ sk_D)
% 2.73/2.94        | ((k1_relat_1 @ (k5_relat_1 @ sk_D @ (k4_relat_1 @ sk_D)))
% 2.73/2.94            = (k1_relat_1 @ sk_D))
% 2.73/2.94        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_D)))),
% 2.73/2.94      inference('sup-', [status(thm)], ['100', '107'])).
% 2.73/2.94  thf(d10_xboole_0, axiom,
% 2.73/2.94    (![A:$i,B:$i]:
% 2.73/2.94     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.73/2.94  thf('109', plain,
% 2.73/2.94      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 2.73/2.94      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.73/2.94  thf('110', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.73/2.94      inference('simplify', [status(thm)], ['109'])).
% 2.73/2.94  thf('111', plain, ((v1_relat_1 @ sk_D)),
% 2.73/2.94      inference('demod', [status(thm)], ['51', '52'])).
% 2.73/2.94  thf('112', plain,
% 2.73/2.94      ((((k1_relat_1 @ (k5_relat_1 @ sk_D @ (k4_relat_1 @ sk_D)))
% 2.73/2.94          = (k1_relat_1 @ sk_D))
% 2.73/2.94        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_D)))),
% 2.73/2.94      inference('demod', [status(thm)], ['108', '110', '111'])).
% 2.73/2.94  thf('113', plain, (((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))),
% 2.73/2.94      inference('demod', [status(thm)], ['96', '97'])).
% 2.73/2.94  thf(dt_k2_funct_1, axiom,
% 2.73/2.94    (![A:$i]:
% 2.73/2.94     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.73/2.94       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 2.73/2.94         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 2.73/2.94  thf('114', plain,
% 2.73/2.94      (![X16 : $i]:
% 2.73/2.94         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 2.73/2.94          | ~ (v1_funct_1 @ X16)
% 2.73/2.94          | ~ (v1_relat_1 @ X16))),
% 2.73/2.94      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.73/2.94  thf('115', plain,
% 2.73/2.94      (((v1_relat_1 @ (k4_relat_1 @ sk_D))
% 2.73/2.94        | ~ (v1_relat_1 @ sk_D)
% 2.73/2.94        | ~ (v1_funct_1 @ sk_D))),
% 2.73/2.94      inference('sup+', [status(thm)], ['113', '114'])).
% 2.73/2.94  thf('116', plain, ((v1_relat_1 @ sk_D)),
% 2.73/2.94      inference('demod', [status(thm)], ['51', '52'])).
% 2.73/2.94  thf('117', plain, ((v1_funct_1 @ sk_D)),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('118', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_D))),
% 2.73/2.94      inference('demod', [status(thm)], ['115', '116', '117'])).
% 2.73/2.94  thf('119', plain,
% 2.73/2.94      (((k1_relat_1 @ (k5_relat_1 @ sk_D @ (k4_relat_1 @ sk_D)))
% 2.73/2.94         = (k1_relat_1 @ sk_D))),
% 2.73/2.94      inference('demod', [status(thm)], ['112', '118'])).
% 2.73/2.94  thf('120', plain,
% 2.73/2.94      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf(t35_funct_2, axiom,
% 2.73/2.94    (![A:$i,B:$i,C:$i]:
% 2.73/2.94     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.73/2.94         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.73/2.94       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 2.73/2.94         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.73/2.94           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 2.73/2.94             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 2.73/2.94  thf('121', plain,
% 2.73/2.94      (![X58 : $i, X59 : $i, X60 : $i]:
% 2.73/2.94         (((X58) = (k1_xboole_0))
% 2.73/2.94          | ~ (v1_funct_1 @ X59)
% 2.73/2.94          | ~ (v1_funct_2 @ X59 @ X60 @ X58)
% 2.73/2.94          | ~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X58)))
% 2.73/2.94          | ((k5_relat_1 @ X59 @ (k2_funct_1 @ X59)) = (k6_partfun1 @ X60))
% 2.73/2.94          | ~ (v2_funct_1 @ X59)
% 2.73/2.94          | ((k2_relset_1 @ X60 @ X58 @ X59) != (X58)))),
% 2.73/2.94      inference('cnf', [status(esa)], [t35_funct_2])).
% 2.73/2.94  thf('122', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 2.73/2.94      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.73/2.94  thf('123', plain,
% 2.73/2.94      (![X58 : $i, X59 : $i, X60 : $i]:
% 2.73/2.94         (((X58) = (k1_xboole_0))
% 2.73/2.94          | ~ (v1_funct_1 @ X59)
% 2.73/2.94          | ~ (v1_funct_2 @ X59 @ X60 @ X58)
% 2.73/2.94          | ~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X58)))
% 2.73/2.94          | ((k5_relat_1 @ X59 @ (k2_funct_1 @ X59)) = (k6_relat_1 @ X60))
% 2.73/2.94          | ~ (v2_funct_1 @ X59)
% 2.73/2.94          | ((k2_relset_1 @ X60 @ X58 @ X59) != (X58)))),
% 2.73/2.94      inference('demod', [status(thm)], ['121', '122'])).
% 2.73/2.94  thf('124', plain,
% 2.73/2.94      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 2.73/2.94        | ~ (v2_funct_1 @ sk_D)
% 2.73/2.94        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 2.73/2.94        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.73/2.94        | ~ (v1_funct_1 @ sk_D)
% 2.73/2.94        | ((sk_A) = (k1_xboole_0)))),
% 2.73/2.94      inference('sup-', [status(thm)], ['120', '123'])).
% 2.73/2.94  thf('125', plain,
% 2.73/2.94      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.73/2.94      inference('sup-', [status(thm)], ['42', '43'])).
% 2.73/2.94  thf('126', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.73/2.94      inference('demod', [status(thm)], ['41', '44', '45', '46', '47'])).
% 2.73/2.94  thf('127', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))),
% 2.73/2.94      inference('demod', [status(thm)], ['125', '126'])).
% 2.73/2.94  thf('128', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('129', plain, ((v1_funct_1 @ sk_D)),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('130', plain,
% 2.73/2.94      ((((sk_A) != (sk_A))
% 2.73/2.94        | ~ (v2_funct_1 @ sk_D)
% 2.73/2.94        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 2.73/2.94        | ((sk_A) = (k1_xboole_0)))),
% 2.73/2.94      inference('demod', [status(thm)], ['124', '127', '128', '129'])).
% 2.73/2.94  thf('131', plain,
% 2.73/2.94      ((((sk_A) = (k1_xboole_0))
% 2.73/2.94        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 2.73/2.94        | ~ (v2_funct_1 @ sk_D))),
% 2.73/2.94      inference('simplify', [status(thm)], ['130'])).
% 2.73/2.94  thf('132', plain, (((sk_A) != (k1_xboole_0))),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('133', plain,
% 2.73/2.94      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 2.73/2.94        | ~ (v2_funct_1 @ sk_D))),
% 2.73/2.94      inference('simplify_reflect-', [status(thm)], ['131', '132'])).
% 2.73/2.94  thf('134', plain, ((v2_funct_1 @ sk_D)),
% 2.73/2.94      inference('sup-', [status(thm)], ['88', '89'])).
% 2.73/2.94  thf('135', plain,
% 2.73/2.94      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 2.73/2.94      inference('demod', [status(thm)], ['133', '134'])).
% 2.73/2.94  thf('136', plain, (((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))),
% 2.73/2.94      inference('demod', [status(thm)], ['96', '97'])).
% 2.73/2.94  thf('137', plain,
% 2.73/2.94      (((k5_relat_1 @ sk_D @ (k4_relat_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 2.73/2.94      inference('demod', [status(thm)], ['135', '136'])).
% 2.73/2.94  thf(t71_relat_1, axiom,
% 2.73/2.94    (![A:$i]:
% 2.73/2.94     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 2.73/2.94       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 2.73/2.94  thf('138', plain, (![X13 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 2.73/2.94      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.73/2.94  thf('139', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 2.73/2.94      inference('demod', [status(thm)], ['119', '137', '138'])).
% 2.73/2.94  thf('140', plain, ((((sk_C) = (k4_relat_1 @ sk_D)) | ((sk_B) != (sk_B)))),
% 2.73/2.94      inference('demod', [status(thm)], ['99', '139'])).
% 2.73/2.94  thf('141', plain, (((sk_C) = (k4_relat_1 @ sk_D))),
% 2.73/2.94      inference('simplify', [status(thm)], ['140'])).
% 2.73/2.94  thf(involutiveness_k4_relat_1, axiom,
% 2.73/2.94    (![A:$i]:
% 2.73/2.94     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 2.73/2.94  thf('142', plain,
% 2.73/2.94      (![X7 : $i]:
% 2.73/2.94         (((k4_relat_1 @ (k4_relat_1 @ X7)) = (X7)) | ~ (v1_relat_1 @ X7))),
% 2.73/2.94      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 2.73/2.94  thf('143', plain, ((((k4_relat_1 @ sk_C) = (sk_D)) | ~ (v1_relat_1 @ sk_D))),
% 2.73/2.94      inference('sup+', [status(thm)], ['141', '142'])).
% 2.73/2.94  thf('144', plain, ((v1_relat_1 @ sk_D)),
% 2.73/2.94      inference('demod', [status(thm)], ['51', '52'])).
% 2.73/2.94  thf('145', plain, (((k4_relat_1 @ sk_C) = (sk_D))),
% 2.73/2.94      inference('demod', [status(thm)], ['143', '144'])).
% 2.73/2.94  thf('146', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('147', plain, ((v1_funct_1 @ sk_C)),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('148', plain,
% 2.73/2.94      (![X15 : $i]:
% 2.73/2.94         (~ (v2_funct_1 @ X15)
% 2.73/2.94          | ((k2_funct_1 @ X15) = (k4_relat_1 @ X15))
% 2.73/2.94          | ~ (v1_funct_1 @ X15)
% 2.73/2.94          | ~ (v1_relat_1 @ X15))),
% 2.73/2.94      inference('cnf', [status(esa)], [d9_funct_1])).
% 2.73/2.94  thf('149', plain,
% 2.73/2.94      ((~ (v1_relat_1 @ sk_C)
% 2.73/2.94        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 2.73/2.94        | ~ (v2_funct_1 @ sk_C))),
% 2.73/2.94      inference('sup-', [status(thm)], ['147', '148'])).
% 2.73/2.94  thf('150', plain, ((v1_relat_1 @ sk_C)),
% 2.73/2.94      inference('demod', [status(thm)], ['63', '64'])).
% 2.73/2.94  thf('151', plain, ((v2_funct_1 @ sk_C)),
% 2.73/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.94  thf('152', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 2.73/2.94      inference('demod', [status(thm)], ['149', '150', '151'])).
% 2.73/2.94  thf('153', plain, (((sk_D) != (k4_relat_1 @ sk_C))),
% 2.73/2.94      inference('demod', [status(thm)], ['146', '152'])).
% 2.73/2.94  thf('154', plain, ($false),
% 2.73/2.94      inference('simplify_reflect-', [status(thm)], ['145', '153'])).
% 2.73/2.94  
% 2.73/2.94  % SZS output end Refutation
% 2.73/2.94  
% 2.80/2.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

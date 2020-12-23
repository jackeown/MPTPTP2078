%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yartHSuqHO

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:00 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  174 (2107 expanded)
%              Number of leaves         :   45 ( 642 expanded)
%              Depth                    :   18
%              Number of atoms          : 1651 (54931 expanded)
%              Number of equality atoms :  116 (3775 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

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
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( ( k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38 )
        = ( k5_relat_1 @ X35 @ X38 ) ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X32 ) ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( X15 = X18 )
      | ~ ( r2_relset_1 @ X16 @ X17 @ X15 @ X18 ) ) ),
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
    ! [X34: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('27',plain,(
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
    ! [X34: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( X4
        = ( k2_funct_1 @ X5 ) )
      | ( ( k5_relat_1 @ X4 @ X5 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X5 ) ) )
      | ( ( k2_relat_1 @ X4 )
       != ( k1_relat_1 @ X5 ) )
      | ~ ( v2_funct_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
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
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( r2_relset_1 @ X43 @ X43 @ ( k1_partfun1 @ X43 @ X44 @ X44 @ X43 @ X42 @ X45 ) @ ( k6_partfun1 @ X43 ) )
      | ( ( k2_relset_1 @ X44 @ X43 @ X45 )
        = X43 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X45 @ X44 @ X43 )
      | ~ ( v1_funct_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('35',plain,(
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('36',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( r2_relset_1 @ X43 @ X43 @ ( k1_partfun1 @ X43 @ X44 @ X44 @ X43 @ X42 @ X45 ) @ ( k6_relat_1 @ X43 ) )
      | ( ( k2_relset_1 @ X44 @ X43 @ X45 )
        = X43 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X45 @ X44 @ X43 )
      | ~ ( v1_funct_1 @ X45 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
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

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('50',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('51',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('55',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
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

thf('59',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ( X21
        = ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('60',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('61',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('62',plain,(
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

thf('63',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('64',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('69',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('70',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['60','67','70'])).

thf('72',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('75',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B != sk_B )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['31','48','51','52','57','71','72','75'])).

thf('77',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','28'])).

thf(t48_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) ) )
           => ( ( v2_funct_1 @ B )
              & ( v2_funct_1 @ A ) ) ) ) ) )).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X1 )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ X1 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('80',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('81',plain,(
    ! [X2: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('82',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['49','50'])).

thf('83',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['55','56'])).

thf('85',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['60','67','70'])).

thf('86',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['73','74'])).

thf('88',plain,
    ( ( sk_B != sk_B )
    | ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['80','81','82','83','84','85','86','87'])).

thf('89',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['77','89'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('91',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k5_relat_1 @ X3 @ ( k2_funct_1 @ X3 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X3 ) ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('92',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( X4
        = ( k2_funct_1 @ X5 ) )
      | ( ( k5_relat_1 @ X4 @ X5 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X5 ) ) )
      | ( ( k2_relat_1 @ X4 )
       != ( k1_relat_1 @ X5 ) )
      | ~ ( v2_funct_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,
    ( ( ( k6_relat_1 @ ( k1_relat_1 @ sk_D ) )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ( ( k2_relat_1 @ sk_D )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_D ) ) )
    | ( sk_D
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['90','94'])).

thf('96',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['60','67','70'])).

thf('97',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['55','56'])).

thf('98',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['49','50'])).

thf('99',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['88'])).

thf('101',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['77','89'])).

thf('102',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['73','74'])).

thf('103',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['77','89'])).

thf('104',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['77','89'])).

thf('106',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['41','44','45','46','47'])).

thf('108',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['77','89'])).

thf('109',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ( X21
        = ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('111',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('113',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('115',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['112','115'])).

thf('117',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['116','117'])).

thf('119',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('121',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['111','118','121'])).

thf('123',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['77','89'])).

thf('124',plain,
    ( ( ( k6_relat_1 @ sk_B )
     != ( k6_relat_1 @ sk_B ) )
    | ( sk_A != sk_A )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['95','96','97','98','99','100','101','102','103','104','105','106','107','108','122','123'])).

thf('125',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['125','126'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yartHSuqHO
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:27:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.90/1.14  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.90/1.14  % Solved by: fo/fo7.sh
% 0.90/1.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.14  % done 437 iterations in 0.692s
% 0.90/1.14  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.90/1.14  % SZS output start Refutation
% 0.90/1.14  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.90/1.14  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.90/1.14  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.90/1.14  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.90/1.14  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.90/1.14  thf(sk_C_type, type, sk_C: $i).
% 0.90/1.14  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.90/1.14  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.90/1.14  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.14  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.90/1.14  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.90/1.14  thf(sk_D_type, type, sk_D: $i).
% 0.90/1.14  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.90/1.14  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.90/1.14  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.90/1.14  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.14  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.90/1.14  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.90/1.14  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.90/1.14  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.14  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.90/1.14  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.14  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.90/1.14  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.90/1.14  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
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
% 0.90/1.14  thf('1', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
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
% 0.90/1.14      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.90/1.14         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.90/1.14          | ~ (v1_funct_1 @ X35)
% 0.90/1.14          | ~ (v1_funct_1 @ X38)
% 0.90/1.14          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.90/1.14          | ((k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38)
% 0.90/1.14              = (k5_relat_1 @ X35 @ X38)))),
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
% 0.90/1.14      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.90/1.14         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.90/1.14          | ~ (v1_funct_1 @ X27)
% 0.90/1.14          | ~ (v1_funct_1 @ X30)
% 0.90/1.14          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.90/1.14          | (m1_subset_1 @ (k1_partfun1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30) @ 
% 0.90/1.14             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X32))))),
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
% 0.90/1.14      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.90/1.14         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.90/1.14          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.90/1.14          | ((X15) = (X18))
% 0.90/1.14          | ~ (r2_relset_1 @ X16 @ X17 @ X15 @ X18))),
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
% 0.90/1.14      (![X34 : $i]:
% 0.90/1.14         (m1_subset_1 @ (k6_partfun1 @ X34) @ 
% 0.90/1.14          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))),
% 0.90/1.14      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.90/1.14  thf('27', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 0.90/1.14      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.90/1.14  thf('28', plain,
% 0.90/1.14      (![X34 : $i]:
% 0.90/1.14         (m1_subset_1 @ (k6_relat_1 @ X34) @ 
% 0.90/1.14          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))),
% 0.90/1.14      inference('demod', [status(thm)], ['26', '27'])).
% 0.90/1.14  thf('29', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 0.90/1.14      inference('demod', [status(thm)], ['25', '28'])).
% 0.90/1.14  thf(t64_funct_1, axiom,
% 0.90/1.14    (![A:$i]:
% 0.90/1.14     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.90/1.14       ( ![B:$i]:
% 0.90/1.14         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.90/1.14           ( ( ( v2_funct_1 @ A ) & 
% 0.90/1.14               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.90/1.14               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.90/1.14             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.90/1.14  thf('30', plain,
% 0.90/1.14      (![X4 : $i, X5 : $i]:
% 0.90/1.14         (~ (v1_relat_1 @ X4)
% 0.90/1.14          | ~ (v1_funct_1 @ X4)
% 0.90/1.14          | ((X4) = (k2_funct_1 @ X5))
% 0.90/1.14          | ((k5_relat_1 @ X4 @ X5) != (k6_relat_1 @ (k2_relat_1 @ X5)))
% 0.90/1.14          | ((k2_relat_1 @ X4) != (k1_relat_1 @ X5))
% 0.90/1.14          | ~ (v2_funct_1 @ X5)
% 0.90/1.14          | ~ (v1_funct_1 @ X5)
% 0.90/1.14          | ~ (v1_relat_1 @ X5))),
% 0.90/1.14      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.90/1.14  thf('31', plain,
% 0.90/1.14      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ (k2_relat_1 @ sk_D)))
% 0.90/1.14        | ~ (v1_relat_1 @ sk_D)
% 0.90/1.14        | ~ (v1_funct_1 @ sk_D)
% 0.90/1.14        | ~ (v2_funct_1 @ sk_D)
% 0.90/1.14        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.90/1.14        | ((sk_C) = (k2_funct_1 @ sk_D))
% 0.90/1.14        | ~ (v1_funct_1 @ sk_C)
% 0.90/1.14        | ~ (v1_relat_1 @ sk_C))),
% 0.90/1.14      inference('sup-', [status(thm)], ['29', '30'])).
% 0.90/1.14  thf('32', plain,
% 0.90/1.14      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.14        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.90/1.14        (k6_relat_1 @ sk_A))),
% 0.90/1.14      inference('demod', [status(thm)], ['0', '1'])).
% 0.90/1.14  thf('33', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(t24_funct_2, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.90/1.14         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.90/1.14       ( ![D:$i]:
% 0.90/1.14         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.90/1.14             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.90/1.14           ( ( r2_relset_1 @
% 0.90/1.14               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.90/1.14               ( k6_partfun1 @ B ) ) =>
% 0.90/1.14             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.90/1.14  thf('34', plain,
% 0.90/1.14      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.90/1.14         (~ (v1_funct_1 @ X42)
% 0.90/1.14          | ~ (v1_funct_2 @ X42 @ X43 @ X44)
% 0.90/1.14          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 0.90/1.14          | ~ (r2_relset_1 @ X43 @ X43 @ 
% 0.90/1.14               (k1_partfun1 @ X43 @ X44 @ X44 @ X43 @ X42 @ X45) @ 
% 0.90/1.14               (k6_partfun1 @ X43))
% 0.90/1.14          | ((k2_relset_1 @ X44 @ X43 @ X45) = (X43))
% 0.90/1.14          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43)))
% 0.90/1.14          | ~ (v1_funct_2 @ X45 @ X44 @ X43)
% 0.90/1.14          | ~ (v1_funct_1 @ X45))),
% 0.90/1.14      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.90/1.14  thf('35', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 0.90/1.14      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.90/1.14  thf('36', plain,
% 0.90/1.14      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.90/1.14         (~ (v1_funct_1 @ X42)
% 0.90/1.14          | ~ (v1_funct_2 @ X42 @ X43 @ X44)
% 0.90/1.14          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 0.90/1.14          | ~ (r2_relset_1 @ X43 @ X43 @ 
% 0.90/1.14               (k1_partfun1 @ X43 @ X44 @ X44 @ X43 @ X42 @ X45) @ 
% 0.90/1.14               (k6_relat_1 @ X43))
% 0.90/1.14          | ((k2_relset_1 @ X44 @ X43 @ X45) = (X43))
% 0.90/1.14          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43)))
% 0.90/1.14          | ~ (v1_funct_2 @ X45 @ X44 @ X43)
% 0.90/1.14          | ~ (v1_funct_1 @ X45))),
% 0.90/1.14      inference('demod', [status(thm)], ['34', '35'])).
% 0.90/1.14  thf('37', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (~ (v1_funct_1 @ X0)
% 0.90/1.14          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.90/1.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.90/1.14          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.90/1.14          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.14               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.90/1.14               (k6_relat_1 @ sk_A))
% 0.90/1.14          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.90/1.14          | ~ (v1_funct_1 @ sk_C))),
% 0.90/1.14      inference('sup-', [status(thm)], ['33', '36'])).
% 0.90/1.14  thf('38', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('39', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('40', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (~ (v1_funct_1 @ X0)
% 0.90/1.14          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.90/1.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.90/1.14          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.90/1.14          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.14               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.90/1.14               (k6_relat_1 @ sk_A)))),
% 0.90/1.14      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.90/1.14  thf('41', plain,
% 0.90/1.14      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.90/1.14        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.90/1.14        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.90/1.14        | ~ (v1_funct_1 @ sk_D))),
% 0.90/1.14      inference('sup-', [status(thm)], ['32', '40'])).
% 0.90/1.14  thf('42', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(redefinition_k2_relset_1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.14       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.90/1.14  thf('43', plain,
% 0.90/1.14      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.90/1.14         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.90/1.14          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.90/1.14      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.90/1.14  thf('44', plain,
% 0.90/1.14      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.90/1.14      inference('sup-', [status(thm)], ['42', '43'])).
% 0.90/1.14  thf('45', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('46', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('47', plain, ((v1_funct_1 @ sk_D)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('48', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.90/1.14      inference('demod', [status(thm)], ['41', '44', '45', '46', '47'])).
% 0.90/1.14  thf('49', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(cc1_relset_1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.14       ( v1_relat_1 @ C ) ))).
% 0.90/1.14  thf('50', plain,
% 0.90/1.14      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.90/1.14         ((v1_relat_1 @ X6)
% 0.90/1.14          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.90/1.14      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.90/1.14  thf('51', plain, ((v1_relat_1 @ sk_D)),
% 0.90/1.14      inference('sup-', [status(thm)], ['49', '50'])).
% 0.90/1.14  thf('52', plain, ((v1_funct_1 @ sk_D)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('53', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('54', plain,
% 0.90/1.14      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.90/1.14         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.90/1.14          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.90/1.14      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.90/1.14  thf('55', plain,
% 0.90/1.14      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.90/1.14      inference('sup-', [status(thm)], ['53', '54'])).
% 0.90/1.14  thf('56', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('57', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.90/1.14      inference('sup+', [status(thm)], ['55', '56'])).
% 0.90/1.14  thf('58', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
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
% 0.90/1.14  thf('59', plain,
% 0.90/1.14      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.90/1.14         (~ (v1_funct_2 @ X23 @ X21 @ X22)
% 0.90/1.14          | ((X21) = (k1_relset_1 @ X21 @ X22 @ X23))
% 0.90/1.14          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.90/1.14  thf('60', plain,
% 0.90/1.14      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 0.90/1.14        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['58', '59'])).
% 0.90/1.14  thf(zf_stmt_2, axiom,
% 0.90/1.14    (![B:$i,A:$i]:
% 0.90/1.14     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.90/1.14       ( zip_tseitin_0 @ B @ A ) ))).
% 0.90/1.14  thf('61', plain,
% 0.90/1.14      (![X19 : $i, X20 : $i]:
% 0.90/1.14         ((zip_tseitin_0 @ X19 @ X20) | ((X19) = (k1_xboole_0)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.90/1.14  thf('62', plain,
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
% 0.90/1.14  thf('63', plain,
% 0.90/1.14      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.90/1.14         (~ (zip_tseitin_0 @ X24 @ X25)
% 0.90/1.14          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 0.90/1.14          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.90/1.14  thf('64', plain,
% 0.90/1.14      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 0.90/1.14      inference('sup-', [status(thm)], ['62', '63'])).
% 0.90/1.14  thf('65', plain,
% 0.90/1.14      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 0.90/1.14      inference('sup-', [status(thm)], ['61', '64'])).
% 0.90/1.14  thf('66', plain, (((sk_A) != (k1_xboole_0))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('67', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 0.90/1.14      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 0.90/1.14  thf('68', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(redefinition_k1_relset_1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.14       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.90/1.14  thf('69', plain,
% 0.90/1.14      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.90/1.14         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.90/1.14          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.90/1.14      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.90/1.14  thf('70', plain,
% 0.90/1.14      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.90/1.14      inference('sup-', [status(thm)], ['68', '69'])).
% 0.90/1.14  thf('71', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['60', '67', '70'])).
% 0.90/1.14  thf('72', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('73', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('74', plain,
% 0.90/1.14      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.90/1.14         ((v1_relat_1 @ X6)
% 0.90/1.14          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.90/1.14      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.90/1.14  thf('75', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.14      inference('sup-', [status(thm)], ['73', '74'])).
% 0.90/1.14  thf('76', plain,
% 0.90/1.14      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ sk_A))
% 0.90/1.14        | ~ (v2_funct_1 @ sk_D)
% 0.90/1.14        | ((sk_B) != (sk_B))
% 0.90/1.14        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 0.90/1.14      inference('demod', [status(thm)],
% 0.90/1.14                ['31', '48', '51', '52', '57', '71', '72', '75'])).
% 0.90/1.14  thf('77', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 0.90/1.14      inference('simplify', [status(thm)], ['76'])).
% 0.90/1.14  thf('78', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 0.90/1.14      inference('demod', [status(thm)], ['25', '28'])).
% 0.90/1.14  thf(t48_funct_1, axiom,
% 0.90/1.14    (![A:$i]:
% 0.90/1.14     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.90/1.14       ( ![B:$i]:
% 0.90/1.14         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.90/1.14           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.90/1.14               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.90/1.14             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.90/1.14  thf('79', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         (~ (v1_relat_1 @ X0)
% 0.90/1.14          | ~ (v1_funct_1 @ X0)
% 0.90/1.14          | (v2_funct_1 @ X1)
% 0.90/1.14          | ((k2_relat_1 @ X0) != (k1_relat_1 @ X1))
% 0.90/1.14          | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ X1))
% 0.90/1.14          | ~ (v1_funct_1 @ X1)
% 0.90/1.14          | ~ (v1_relat_1 @ X1))),
% 0.90/1.14      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.90/1.14  thf('80', plain,
% 0.90/1.14      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 0.90/1.14        | ~ (v1_relat_1 @ sk_D)
% 0.90/1.14        | ~ (v1_funct_1 @ sk_D)
% 0.90/1.14        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.90/1.14        | (v2_funct_1 @ sk_D)
% 0.90/1.14        | ~ (v1_funct_1 @ sk_C)
% 0.90/1.14        | ~ (v1_relat_1 @ sk_C))),
% 0.90/1.14      inference('sup-', [status(thm)], ['78', '79'])).
% 0.90/1.14  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 0.90/1.14  thf('81', plain, (![X2 : $i]: (v2_funct_1 @ (k6_relat_1 @ X2))),
% 0.90/1.14      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.90/1.14  thf('82', plain, ((v1_relat_1 @ sk_D)),
% 0.90/1.14      inference('sup-', [status(thm)], ['49', '50'])).
% 0.90/1.14  thf('83', plain, ((v1_funct_1 @ sk_D)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('84', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.90/1.14      inference('sup+', [status(thm)], ['55', '56'])).
% 0.90/1.14  thf('85', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['60', '67', '70'])).
% 0.90/1.14  thf('86', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('87', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.14      inference('sup-', [status(thm)], ['73', '74'])).
% 0.90/1.14  thf('88', plain, ((((sk_B) != (sk_B)) | (v2_funct_1 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)],
% 0.90/1.14                ['80', '81', '82', '83', '84', '85', '86', '87'])).
% 0.90/1.14  thf('89', plain, ((v2_funct_1 @ sk_D)),
% 0.90/1.14      inference('simplify', [status(thm)], ['88'])).
% 0.90/1.14  thf('90', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['77', '89'])).
% 0.90/1.14  thf(t61_funct_1, axiom,
% 0.90/1.14    (![A:$i]:
% 0.90/1.14     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.90/1.14       ( ( v2_funct_1 @ A ) =>
% 0.90/1.14         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.90/1.14             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.90/1.14           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.90/1.14             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.90/1.14  thf('91', plain,
% 0.90/1.14      (![X3 : $i]:
% 0.90/1.14         (~ (v2_funct_1 @ X3)
% 0.90/1.14          | ((k5_relat_1 @ X3 @ (k2_funct_1 @ X3))
% 0.90/1.14              = (k6_relat_1 @ (k1_relat_1 @ X3)))
% 0.90/1.14          | ~ (v1_funct_1 @ X3)
% 0.90/1.14          | ~ (v1_relat_1 @ X3))),
% 0.90/1.14      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.90/1.14  thf('92', plain,
% 0.90/1.14      (![X4 : $i, X5 : $i]:
% 0.90/1.14         (~ (v1_relat_1 @ X4)
% 0.90/1.14          | ~ (v1_funct_1 @ X4)
% 0.90/1.14          | ((X4) = (k2_funct_1 @ X5))
% 0.90/1.14          | ((k5_relat_1 @ X4 @ X5) != (k6_relat_1 @ (k2_relat_1 @ X5)))
% 0.90/1.14          | ((k2_relat_1 @ X4) != (k1_relat_1 @ X5))
% 0.90/1.14          | ~ (v2_funct_1 @ X5)
% 0.90/1.14          | ~ (v1_funct_1 @ X5)
% 0.90/1.14          | ~ (v1_relat_1 @ X5))),
% 0.90/1.14      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.90/1.14  thf('93', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (((k6_relat_1 @ (k1_relat_1 @ X0))
% 0.90/1.14            != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.90/1.14          | ~ (v1_relat_1 @ X0)
% 0.90/1.14          | ~ (v1_funct_1 @ X0)
% 0.90/1.14          | ~ (v2_funct_1 @ X0)
% 0.90/1.14          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.90/1.14          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.90/1.14          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.90/1.14          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.90/1.14          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.90/1.14          | ~ (v1_funct_1 @ X0)
% 0.90/1.14          | ~ (v1_relat_1 @ X0))),
% 0.90/1.14      inference('sup-', [status(thm)], ['91', '92'])).
% 0.90/1.14  thf('94', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.90/1.14          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.90/1.14          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.90/1.14          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.90/1.14          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.90/1.14          | ~ (v2_funct_1 @ X0)
% 0.90/1.14          | ~ (v1_funct_1 @ X0)
% 0.90/1.14          | ~ (v1_relat_1 @ X0)
% 0.90/1.14          | ((k6_relat_1 @ (k1_relat_1 @ X0))
% 0.90/1.14              != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.90/1.14      inference('simplify', [status(thm)], ['93'])).
% 0.90/1.14  thf('95', plain,
% 0.90/1.14      ((((k6_relat_1 @ (k1_relat_1 @ sk_D))
% 0.90/1.14          != (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.90/1.14        | ~ (v1_relat_1 @ sk_D)
% 0.90/1.14        | ~ (v1_funct_1 @ sk_D)
% 0.90/1.14        | ~ (v2_funct_1 @ sk_D)
% 0.90/1.14        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D))
% 0.90/1.14        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 0.90/1.14        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_D))
% 0.90/1.14        | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ (k2_funct_1 @ sk_D)))
% 0.90/1.14        | ((sk_D) = (k2_funct_1 @ (k2_funct_1 @ sk_D))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['90', '94'])).
% 0.90/1.14  thf('96', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['60', '67', '70'])).
% 0.90/1.14  thf('97', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.90/1.14      inference('sup+', [status(thm)], ['55', '56'])).
% 0.90/1.14  thf('98', plain, ((v1_relat_1 @ sk_D)),
% 0.90/1.14      inference('sup-', [status(thm)], ['49', '50'])).
% 0.90/1.14  thf('99', plain, ((v1_funct_1 @ sk_D)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('100', plain, ((v2_funct_1 @ sk_D)),
% 0.90/1.14      inference('simplify', [status(thm)], ['88'])).
% 0.90/1.14  thf('101', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['77', '89'])).
% 0.90/1.14  thf('102', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.14      inference('sup-', [status(thm)], ['73', '74'])).
% 0.90/1.14  thf('103', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['77', '89'])).
% 0.90/1.14  thf('104', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('105', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['77', '89'])).
% 0.90/1.14  thf('106', plain, ((v2_funct_1 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('107', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.90/1.14      inference('demod', [status(thm)], ['41', '44', '45', '46', '47'])).
% 0.90/1.14  thf('108', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['77', '89'])).
% 0.90/1.14  thf('109', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('110', plain,
% 0.90/1.14      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.90/1.14         (~ (v1_funct_2 @ X23 @ X21 @ X22)
% 0.90/1.14          | ((X21) = (k1_relset_1 @ X21 @ X22 @ X23))
% 0.90/1.14          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.90/1.14  thf('111', plain,
% 0.90/1.14      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.90/1.14        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['109', '110'])).
% 0.90/1.14  thf('112', plain,
% 0.90/1.14      (![X19 : $i, X20 : $i]:
% 0.90/1.14         ((zip_tseitin_0 @ X19 @ X20) | ((X19) = (k1_xboole_0)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.90/1.14  thf('113', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('114', plain,
% 0.90/1.14      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.90/1.14         (~ (zip_tseitin_0 @ X24 @ X25)
% 0.90/1.14          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 0.90/1.14          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.90/1.14  thf('115', plain,
% 0.90/1.14      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.90/1.14      inference('sup-', [status(thm)], ['113', '114'])).
% 0.90/1.14  thf('116', plain,
% 0.90/1.14      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.90/1.14      inference('sup-', [status(thm)], ['112', '115'])).
% 0.90/1.14  thf('117', plain, (((sk_B) != (k1_xboole_0))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('118', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.90/1.14      inference('simplify_reflect-', [status(thm)], ['116', '117'])).
% 0.90/1.14  thf('119', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('120', plain,
% 0.90/1.14      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.90/1.14         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.90/1.14          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.90/1.14      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.90/1.14  thf('121', plain,
% 0.90/1.14      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.90/1.14      inference('sup-', [status(thm)], ['119', '120'])).
% 0.90/1.14  thf('122', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.90/1.14      inference('demod', [status(thm)], ['111', '118', '121'])).
% 0.90/1.14  thf('123', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.90/1.14      inference('demod', [status(thm)], ['77', '89'])).
% 0.90/1.14  thf('124', plain,
% 0.90/1.14      ((((k6_relat_1 @ sk_B) != (k6_relat_1 @ sk_B))
% 0.90/1.14        | ((sk_A) != (sk_A))
% 0.90/1.14        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 0.90/1.14      inference('demod', [status(thm)],
% 0.90/1.14                ['95', '96', '97', '98', '99', '100', '101', '102', '103', 
% 0.90/1.14                 '104', '105', '106', '107', '108', '122', '123'])).
% 0.90/1.14  thf('125', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 0.90/1.14      inference('simplify', [status(thm)], ['124'])).
% 0.90/1.14  thf('126', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('127', plain, ($false),
% 0.90/1.14      inference('simplify_reflect-', [status(thm)], ['125', '126'])).
% 0.90/1.14  
% 0.90/1.14  % SZS output end Refutation
% 0.90/1.14  
% 0.90/1.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

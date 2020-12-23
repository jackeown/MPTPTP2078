%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.c3Cxh5l8Re

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:21 EST 2020

% Result     : Theorem 1.93s
% Output     : Refutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :  195 (2251 expanded)
%              Number of leaves         :   47 ( 688 expanded)
%              Depth                    :   18
%              Number of atoms          : 2017 (57012 expanded)
%              Number of equality atoms :  150 (3896 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
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
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( ( k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40 )
        = ( k5_relat_1 @ X37 @ X40 ) ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X34 ) ) ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( X17 = X20 )
      | ~ ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 ) ) ),
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
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('27',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( X9
        = ( k2_funct_1 @ X10 ) )
      | ( ( k5_relat_1 @ X9 @ X10 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X10 ) ) )
      | ( ( k2_relat_1 @ X9 )
       != ( k1_relat_1 @ X10 ) )
      | ~ ( v2_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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

thf('35',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('36',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( r2_relset_1 @ X45 @ X45 @ ( k1_partfun1 @ X45 @ X46 @ X46 @ X45 @ X44 @ X47 ) @ ( k6_relat_1 @ X45 ) )
      | ( ( k2_relset_1 @ X46 @ X45 @ X47 )
        = X45 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) )
      | ~ ( v1_funct_2 @ X47 @ X46 @ X45 )
      | ~ ( v1_funct_1 @ X47 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
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

thf('61',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ( X23
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('62',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('63',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('64',plain,(
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

thf('65',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('66',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('71',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('72',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['62','69','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('77',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('79',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B != sk_B )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['31','48','53','54','59','73','74','79'])).

thf('81',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
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

thf('83',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( v2_funct_1 @ X7 )
      | ( ( k2_relat_1 @ X6 )
       != ( k1_relat_1 @ X7 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X6 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('84',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('85',plain,(
    ! [X8: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('86',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['51','52'])).

thf('87',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['57','58'])).

thf('89',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['62','69','72'])).

thf('90',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['77','78'])).

thf('92',plain,
    ( ( sk_B != sk_B )
    | ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['84','85','86','87','88','89','90','91'])).

thf('93',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['81','93'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('95',plain,(
    ! [X51: $i] :
      ( ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X51 ) @ ( k2_relat_1 @ X51 ) ) ) )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('96',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X51: $i] :
      ( ( v1_funct_2 @ X51 @ ( k1_relat_1 @ X51 ) @ ( k2_relat_1 @ X51 ) )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('99',plain,(
    ! [X51: $i] :
      ( ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X51 ) @ ( k2_relat_1 @ X51 ) ) ) )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

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

thf('100',plain,(
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

thf('101',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('102',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( X48 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X48 ) ) )
      | ( ( k5_relat_1 @ X49 @ ( k2_funct_1 @ X49 ) )
        = ( k6_relat_1 @ X50 ) )
      | ~ ( v2_funct_1 @ X49 )
      | ( ( k2_relset_1 @ X50 @ X48 @ X49 )
       != X48 ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['99','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['98','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['97','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( X9
        = ( k2_funct_1 @ X10 ) )
      | ( ( k5_relat_1 @ X9 @ X10 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X10 ) ) )
      | ( ( k2_relat_1 @ X9 )
       != ( k1_relat_1 @ X10 ) )
      | ~ ( v2_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,
    ( ( ( k6_relat_1 @ ( k1_relat_1 @ sk_D ) )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ( ( k2_relat_1 @ sk_D )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_D ) ) )
    | ( sk_D
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['94','111'])).

thf('113',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['62','69','72'])).

thf('114',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['57','58'])).

thf('115',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['51','52'])).

thf('117',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['92'])).

thf('118',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['41','44','45','46','47'])).

thf('119',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['81','93'])).

thf('120',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['77','78'])).

thf('121',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['81','93'])).

thf('122',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['81','93'])).

thf('124',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['41','44','45','46','47'])).

thf('126',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['81','93'])).

thf('127',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ( X23
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('129',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('131',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('133',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['130','133'])).

thf('135',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['134','135'])).

thf('137',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('139',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['129','136','139'])).

thf('141',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['81','93'])).

thf('142',plain,
    ( ( ( k6_relat_1 @ sk_B )
     != ( k6_relat_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A != sk_A )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['112','113','114','115','116','117','118','119','120','121','122','123','124','125','126','140','141'])).

thf('143',plain,
    ( ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['143','144','145'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.c3Cxh5l8Re
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:50:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.93/2.12  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.93/2.12  % Solved by: fo/fo7.sh
% 1.93/2.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.93/2.12  % done 800 iterations in 1.665s
% 1.93/2.12  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.93/2.12  % SZS output start Refutation
% 1.93/2.12  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.93/2.12  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.93/2.12  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.93/2.12  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.93/2.12  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.93/2.12  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.93/2.12  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.93/2.12  thf(sk_A_type, type, sk_A: $i).
% 1.93/2.12  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.93/2.12  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.93/2.12  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.93/2.12  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.93/2.12  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.93/2.12  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.93/2.12  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.93/2.12  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.93/2.12  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.93/2.12  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.93/2.12  thf(sk_D_type, type, sk_D: $i).
% 1.93/2.12  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.93/2.12  thf(sk_C_type, type, sk_C: $i).
% 1.93/2.12  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.93/2.12  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.93/2.12  thf(sk_B_type, type, sk_B: $i).
% 1.93/2.12  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.93/2.12  thf(t36_funct_2, conjecture,
% 1.93/2.12    (![A:$i,B:$i,C:$i]:
% 1.93/2.12     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.93/2.12         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.93/2.12       ( ![D:$i]:
% 1.93/2.12         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.93/2.12             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.93/2.12           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.93/2.12               ( r2_relset_1 @
% 1.93/2.12                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.93/2.12                 ( k6_partfun1 @ A ) ) & 
% 1.93/2.12               ( v2_funct_1 @ C ) ) =>
% 1.93/2.12             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.93/2.12               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.93/2.12  thf(zf_stmt_0, negated_conjecture,
% 1.93/2.12    (~( ![A:$i,B:$i,C:$i]:
% 1.93/2.12        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.93/2.12            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.93/2.12          ( ![D:$i]:
% 1.93/2.12            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.93/2.12                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.93/2.12              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.93/2.12                  ( r2_relset_1 @
% 1.93/2.12                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.93/2.12                    ( k6_partfun1 @ A ) ) & 
% 1.93/2.12                  ( v2_funct_1 @ C ) ) =>
% 1.93/2.12                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.93/2.12                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.93/2.12    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.93/2.12  thf('0', plain,
% 1.93/2.12      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.93/2.12        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.93/2.12        (k6_partfun1 @ sk_A))),
% 1.93/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.12  thf(redefinition_k6_partfun1, axiom,
% 1.93/2.12    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.93/2.12  thf('1', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 1.93/2.12      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.93/2.12  thf('2', plain,
% 1.93/2.12      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.93/2.12        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.93/2.12        (k6_relat_1 @ sk_A))),
% 1.93/2.12      inference('demod', [status(thm)], ['0', '1'])).
% 1.93/2.12  thf('3', plain,
% 1.93/2.12      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.93/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.12  thf('4', plain,
% 1.93/2.12      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.93/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.12  thf(redefinition_k1_partfun1, axiom,
% 1.93/2.12    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.93/2.12     ( ( ( v1_funct_1 @ E ) & 
% 1.93/2.12         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.93/2.12         ( v1_funct_1 @ F ) & 
% 1.93/2.12         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.93/2.12       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.93/2.12  thf('5', plain,
% 1.93/2.12      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 1.93/2.12         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 1.93/2.12          | ~ (v1_funct_1 @ X37)
% 1.93/2.12          | ~ (v1_funct_1 @ X40)
% 1.93/2.12          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 1.93/2.12          | ((k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40)
% 1.93/2.12              = (k5_relat_1 @ X37 @ X40)))),
% 1.93/2.12      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.93/2.12  thf('6', plain,
% 1.93/2.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.93/2.12         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.93/2.12            = (k5_relat_1 @ sk_C @ X0))
% 1.93/2.12          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.93/2.12          | ~ (v1_funct_1 @ X0)
% 1.93/2.12          | ~ (v1_funct_1 @ sk_C))),
% 1.93/2.12      inference('sup-', [status(thm)], ['4', '5'])).
% 1.93/2.12  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 1.93/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.12  thf('8', plain,
% 1.93/2.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.93/2.12         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.93/2.12            = (k5_relat_1 @ sk_C @ X0))
% 1.93/2.12          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.93/2.12          | ~ (v1_funct_1 @ X0))),
% 1.93/2.12      inference('demod', [status(thm)], ['6', '7'])).
% 1.93/2.12  thf('9', plain,
% 1.93/2.12      ((~ (v1_funct_1 @ sk_D)
% 1.93/2.12        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.93/2.12            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.93/2.12      inference('sup-', [status(thm)], ['3', '8'])).
% 1.93/2.12  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 1.93/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.12  thf('11', plain,
% 1.93/2.12      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.93/2.12         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.93/2.12      inference('demod', [status(thm)], ['9', '10'])).
% 1.93/2.12  thf('12', plain,
% 1.93/2.12      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.93/2.12        (k6_relat_1 @ sk_A))),
% 1.93/2.12      inference('demod', [status(thm)], ['2', '11'])).
% 1.93/2.12  thf('13', plain,
% 1.93/2.12      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.93/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.12  thf('14', plain,
% 1.93/2.12      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.93/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.12  thf(dt_k1_partfun1, axiom,
% 1.93/2.12    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.93/2.12     ( ( ( v1_funct_1 @ E ) & 
% 1.93/2.12         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.93/2.12         ( v1_funct_1 @ F ) & 
% 1.93/2.12         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.93/2.12       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.93/2.12         ( m1_subset_1 @
% 1.93/2.12           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.93/2.12           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.93/2.12  thf('15', plain,
% 1.93/2.12      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.93/2.12         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.93/2.12          | ~ (v1_funct_1 @ X29)
% 1.93/2.12          | ~ (v1_funct_1 @ X32)
% 1.93/2.12          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 1.93/2.12          | (m1_subset_1 @ (k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32) @ 
% 1.93/2.12             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X34))))),
% 1.93/2.12      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.93/2.12  thf('16', plain,
% 1.93/2.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.93/2.12         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.93/2.12           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.93/2.12          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.93/2.12          | ~ (v1_funct_1 @ X1)
% 1.93/2.12          | ~ (v1_funct_1 @ sk_C))),
% 1.93/2.12      inference('sup-', [status(thm)], ['14', '15'])).
% 1.93/2.12  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 1.93/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.12  thf('18', plain,
% 1.93/2.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.93/2.12         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.93/2.12           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.93/2.12          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.93/2.12          | ~ (v1_funct_1 @ X1))),
% 1.93/2.12      inference('demod', [status(thm)], ['16', '17'])).
% 1.93/2.12  thf('19', plain,
% 1.93/2.12      ((~ (v1_funct_1 @ sk_D)
% 1.93/2.12        | (m1_subset_1 @ 
% 1.93/2.12           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.93/2.12           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.93/2.12      inference('sup-', [status(thm)], ['13', '18'])).
% 1.93/2.12  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 1.93/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.12  thf('21', plain,
% 1.93/2.12      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.93/2.12         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.93/2.12      inference('demod', [status(thm)], ['9', '10'])).
% 1.93/2.12  thf('22', plain,
% 1.93/2.12      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.93/2.12        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.93/2.12      inference('demod', [status(thm)], ['19', '20', '21'])).
% 1.93/2.12  thf(redefinition_r2_relset_1, axiom,
% 1.93/2.12    (![A:$i,B:$i,C:$i,D:$i]:
% 1.93/2.12     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.93/2.12         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.93/2.12       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.93/2.12  thf('23', plain,
% 1.93/2.12      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.93/2.12         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 1.93/2.12          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 1.93/2.12          | ((X17) = (X20))
% 1.93/2.12          | ~ (r2_relset_1 @ X18 @ X19 @ X17 @ X20))),
% 1.93/2.12      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.93/2.12  thf('24', plain,
% 1.93/2.12      (![X0 : $i]:
% 1.93/2.12         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 1.93/2.12          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 1.93/2.12          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.93/2.12      inference('sup-', [status(thm)], ['22', '23'])).
% 1.93/2.12  thf('25', plain,
% 1.93/2.12      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 1.93/2.12           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.93/2.12        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A)))),
% 1.93/2.12      inference('sup-', [status(thm)], ['12', '24'])).
% 1.93/2.12  thf(dt_k6_partfun1, axiom,
% 1.93/2.12    (![A:$i]:
% 1.93/2.12     ( ( m1_subset_1 @
% 1.93/2.12         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 1.93/2.12       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 1.93/2.12  thf('26', plain,
% 1.93/2.12      (![X36 : $i]:
% 1.93/2.12         (m1_subset_1 @ (k6_partfun1 @ X36) @ 
% 1.93/2.12          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 1.93/2.12      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.93/2.12  thf('27', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 1.93/2.12      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.93/2.12  thf('28', plain,
% 1.93/2.12      (![X36 : $i]:
% 1.93/2.12         (m1_subset_1 @ (k6_relat_1 @ X36) @ 
% 1.93/2.12          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 1.93/2.12      inference('demod', [status(thm)], ['26', '27'])).
% 1.93/2.12  thf('29', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 1.93/2.12      inference('demod', [status(thm)], ['25', '28'])).
% 1.93/2.12  thf(t64_funct_1, axiom,
% 1.93/2.12    (![A:$i]:
% 1.93/2.12     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.93/2.12       ( ![B:$i]:
% 1.93/2.12         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.93/2.12           ( ( ( v2_funct_1 @ A ) & 
% 1.93/2.12               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 1.93/2.12               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 1.93/2.12             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.93/2.12  thf('30', plain,
% 1.93/2.12      (![X9 : $i, X10 : $i]:
% 1.93/2.12         (~ (v1_relat_1 @ X9)
% 1.93/2.12          | ~ (v1_funct_1 @ X9)
% 1.93/2.12          | ((X9) = (k2_funct_1 @ X10))
% 1.93/2.12          | ((k5_relat_1 @ X9 @ X10) != (k6_relat_1 @ (k2_relat_1 @ X10)))
% 1.93/2.12          | ((k2_relat_1 @ X9) != (k1_relat_1 @ X10))
% 1.93/2.12          | ~ (v2_funct_1 @ X10)
% 1.93/2.12          | ~ (v1_funct_1 @ X10)
% 1.93/2.12          | ~ (v1_relat_1 @ X10))),
% 1.93/2.12      inference('cnf', [status(esa)], [t64_funct_1])).
% 1.93/2.12  thf('31', plain,
% 1.93/2.12      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ (k2_relat_1 @ sk_D)))
% 1.93/2.12        | ~ (v1_relat_1 @ sk_D)
% 1.93/2.12        | ~ (v1_funct_1 @ sk_D)
% 1.93/2.12        | ~ (v2_funct_1 @ sk_D)
% 1.93/2.12        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 1.93/2.12        | ((sk_C) = (k2_funct_1 @ sk_D))
% 1.93/2.12        | ~ (v1_funct_1 @ sk_C)
% 1.93/2.12        | ~ (v1_relat_1 @ sk_C))),
% 1.93/2.12      inference('sup-', [status(thm)], ['29', '30'])).
% 1.93/2.12  thf('32', plain,
% 1.93/2.12      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.93/2.12        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.93/2.12        (k6_relat_1 @ sk_A))),
% 1.93/2.12      inference('demod', [status(thm)], ['0', '1'])).
% 1.93/2.12  thf('33', plain,
% 1.93/2.12      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.93/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.12  thf(t24_funct_2, axiom,
% 1.93/2.12    (![A:$i,B:$i,C:$i]:
% 1.93/2.12     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.93/2.12         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.93/2.12       ( ![D:$i]:
% 1.93/2.12         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.93/2.12             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.93/2.12           ( ( r2_relset_1 @
% 1.93/2.12               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 1.93/2.12               ( k6_partfun1 @ B ) ) =>
% 1.93/2.12             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 1.93/2.12  thf('34', plain,
% 1.93/2.12      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 1.93/2.12         (~ (v1_funct_1 @ X44)
% 1.93/2.12          | ~ (v1_funct_2 @ X44 @ X45 @ X46)
% 1.93/2.12          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 1.93/2.12          | ~ (r2_relset_1 @ X45 @ X45 @ 
% 1.93/2.12               (k1_partfun1 @ X45 @ X46 @ X46 @ X45 @ X44 @ X47) @ 
% 1.93/2.12               (k6_partfun1 @ X45))
% 1.93/2.12          | ((k2_relset_1 @ X46 @ X45 @ X47) = (X45))
% 1.93/2.12          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45)))
% 1.93/2.12          | ~ (v1_funct_2 @ X47 @ X46 @ X45)
% 1.93/2.12          | ~ (v1_funct_1 @ X47))),
% 1.93/2.12      inference('cnf', [status(esa)], [t24_funct_2])).
% 1.93/2.12  thf('35', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 1.93/2.12      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.93/2.12  thf('36', plain,
% 1.93/2.12      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 1.93/2.12         (~ (v1_funct_1 @ X44)
% 1.93/2.12          | ~ (v1_funct_2 @ X44 @ X45 @ X46)
% 1.93/2.12          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 1.93/2.12          | ~ (r2_relset_1 @ X45 @ X45 @ 
% 1.93/2.12               (k1_partfun1 @ X45 @ X46 @ X46 @ X45 @ X44 @ X47) @ 
% 1.93/2.12               (k6_relat_1 @ X45))
% 1.93/2.12          | ((k2_relset_1 @ X46 @ X45 @ X47) = (X45))
% 1.93/2.12          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45)))
% 1.93/2.12          | ~ (v1_funct_2 @ X47 @ X46 @ X45)
% 1.93/2.12          | ~ (v1_funct_1 @ X47))),
% 1.93/2.12      inference('demod', [status(thm)], ['34', '35'])).
% 1.93/2.12  thf('37', plain,
% 1.93/2.12      (![X0 : $i]:
% 1.93/2.12         (~ (v1_funct_1 @ X0)
% 1.93/2.12          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.93/2.12          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.93/2.12          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.93/2.12          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.93/2.12               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.93/2.12               (k6_relat_1 @ sk_A))
% 1.93/2.12          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.93/2.12          | ~ (v1_funct_1 @ sk_C))),
% 1.93/2.12      inference('sup-', [status(thm)], ['33', '36'])).
% 1.93/2.12  thf('38', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.93/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.12  thf('39', plain, ((v1_funct_1 @ sk_C)),
% 1.93/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.12  thf('40', plain,
% 1.93/2.12      (![X0 : $i]:
% 1.93/2.12         (~ (v1_funct_1 @ X0)
% 1.93/2.12          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.93/2.12          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.93/2.12          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.93/2.12          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.93/2.12               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.93/2.12               (k6_relat_1 @ sk_A)))),
% 1.93/2.12      inference('demod', [status(thm)], ['37', '38', '39'])).
% 1.93/2.12  thf('41', plain,
% 1.93/2.12      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 1.93/2.12        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.93/2.12        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.93/2.12        | ~ (v1_funct_1 @ sk_D))),
% 1.93/2.12      inference('sup-', [status(thm)], ['32', '40'])).
% 1.93/2.12  thf('42', plain,
% 1.93/2.12      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.93/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.12  thf(redefinition_k2_relset_1, axiom,
% 1.93/2.12    (![A:$i,B:$i,C:$i]:
% 1.93/2.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.93/2.12       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.93/2.12  thf('43', plain,
% 1.93/2.12      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.93/2.12         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 1.93/2.12          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.93/2.12      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.93/2.12  thf('44', plain,
% 1.93/2.12      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.93/2.12      inference('sup-', [status(thm)], ['42', '43'])).
% 1.93/2.12  thf('45', plain,
% 1.93/2.12      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.93/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.12  thf('46', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.93/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.12  thf('47', plain, ((v1_funct_1 @ sk_D)),
% 1.93/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.12  thf('48', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.93/2.12      inference('demod', [status(thm)], ['41', '44', '45', '46', '47'])).
% 1.93/2.12  thf('49', plain,
% 1.93/2.12      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.93/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.12  thf(cc2_relat_1, axiom,
% 1.93/2.12    (![A:$i]:
% 1.93/2.12     ( ( v1_relat_1 @ A ) =>
% 1.93/2.12       ( ![B:$i]:
% 1.93/2.12         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.93/2.12  thf('50', plain,
% 1.93/2.12      (![X0 : $i, X1 : $i]:
% 1.93/2.12         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.93/2.12          | (v1_relat_1 @ X0)
% 1.93/2.12          | ~ (v1_relat_1 @ X1))),
% 1.93/2.12      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.93/2.12  thf('51', plain,
% 1.93/2.12      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 1.93/2.12      inference('sup-', [status(thm)], ['49', '50'])).
% 1.93/2.12  thf(fc6_relat_1, axiom,
% 1.93/2.12    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.93/2.12  thf('52', plain,
% 1.93/2.12      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.93/2.12      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.93/2.12  thf('53', plain, ((v1_relat_1 @ sk_D)),
% 1.93/2.12      inference('demod', [status(thm)], ['51', '52'])).
% 1.93/2.12  thf('54', plain, ((v1_funct_1 @ sk_D)),
% 1.93/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.12  thf('55', plain,
% 1.93/2.12      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.93/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.12  thf('56', plain,
% 1.93/2.12      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.93/2.12         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 1.93/2.12          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.93/2.12      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.93/2.12  thf('57', plain,
% 1.93/2.12      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.93/2.12      inference('sup-', [status(thm)], ['55', '56'])).
% 1.93/2.12  thf('58', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.93/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.12  thf('59', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.93/2.12      inference('sup+', [status(thm)], ['57', '58'])).
% 1.93/2.12  thf('60', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.93/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.12  thf(d1_funct_2, axiom,
% 1.93/2.12    (![A:$i,B:$i,C:$i]:
% 1.93/2.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.93/2.12       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.93/2.12           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.93/2.12             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.93/2.12         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.93/2.12           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.93/2.12             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.93/2.12  thf(zf_stmt_1, axiom,
% 1.93/2.12    (![C:$i,B:$i,A:$i]:
% 1.93/2.12     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.93/2.12       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.93/2.12  thf('61', plain,
% 1.93/2.12      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.93/2.12         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 1.93/2.12          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 1.93/2.12          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 1.93/2.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.93/2.12  thf('62', plain,
% 1.93/2.12      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 1.93/2.12        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 1.93/2.12      inference('sup-', [status(thm)], ['60', '61'])).
% 1.93/2.12  thf(zf_stmt_2, axiom,
% 1.93/2.12    (![B:$i,A:$i]:
% 1.93/2.12     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.93/2.12       ( zip_tseitin_0 @ B @ A ) ))).
% 1.93/2.12  thf('63', plain,
% 1.93/2.12      (![X21 : $i, X22 : $i]:
% 1.93/2.12         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 1.93/2.12      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.93/2.12  thf('64', plain,
% 1.93/2.12      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.93/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.12  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.93/2.12  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.93/2.12  thf(zf_stmt_5, axiom,
% 1.93/2.12    (![A:$i,B:$i,C:$i]:
% 1.93/2.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.93/2.12       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.93/2.12         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.93/2.12           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.93/2.12             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.93/2.12  thf('65', plain,
% 1.93/2.12      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.93/2.12         (~ (zip_tseitin_0 @ X26 @ X27)
% 1.93/2.12          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 1.93/2.12          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 1.93/2.12      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.93/2.12  thf('66', plain,
% 1.93/2.12      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 1.93/2.12      inference('sup-', [status(thm)], ['64', '65'])).
% 1.93/2.12  thf('67', plain,
% 1.93/2.12      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 1.93/2.12      inference('sup-', [status(thm)], ['63', '66'])).
% 1.93/2.12  thf('68', plain, (((sk_A) != (k1_xboole_0))),
% 1.93/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.12  thf('69', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 1.93/2.12      inference('simplify_reflect-', [status(thm)], ['67', '68'])).
% 1.93/2.12  thf('70', plain,
% 1.93/2.12      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.93/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.12  thf(redefinition_k1_relset_1, axiom,
% 1.93/2.12    (![A:$i,B:$i,C:$i]:
% 1.93/2.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.93/2.12       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.93/2.12  thf('71', plain,
% 1.93/2.12      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.93/2.12         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 1.93/2.12          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.93/2.12      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.93/2.12  thf('72', plain,
% 1.93/2.12      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.93/2.12      inference('sup-', [status(thm)], ['70', '71'])).
% 1.93/2.12  thf('73', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.93/2.12      inference('demod', [status(thm)], ['62', '69', '72'])).
% 1.93/2.12  thf('74', plain, ((v1_funct_1 @ sk_C)),
% 1.93/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.12  thf('75', plain,
% 1.93/2.12      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.93/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.12  thf('76', plain,
% 1.93/2.12      (![X0 : $i, X1 : $i]:
% 1.93/2.12         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.93/2.12          | (v1_relat_1 @ X0)
% 1.93/2.12          | ~ (v1_relat_1 @ X1))),
% 1.93/2.12      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.93/2.12  thf('77', plain,
% 1.93/2.12      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 1.93/2.12      inference('sup-', [status(thm)], ['75', '76'])).
% 1.93/2.12  thf('78', plain,
% 1.93/2.12      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.93/2.12      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.93/2.12  thf('79', plain, ((v1_relat_1 @ sk_C)),
% 1.93/2.12      inference('demod', [status(thm)], ['77', '78'])).
% 1.93/2.12  thf('80', plain,
% 1.93/2.12      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ sk_A))
% 1.93/2.12        | ~ (v2_funct_1 @ sk_D)
% 1.93/2.12        | ((sk_B) != (sk_B))
% 1.93/2.12        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 1.93/2.12      inference('demod', [status(thm)],
% 1.93/2.12                ['31', '48', '53', '54', '59', '73', '74', '79'])).
% 1.93/2.12  thf('81', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 1.93/2.12      inference('simplify', [status(thm)], ['80'])).
% 1.93/2.12  thf('82', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 1.93/2.12      inference('demod', [status(thm)], ['25', '28'])).
% 1.93/2.12  thf(t48_funct_1, axiom,
% 1.93/2.12    (![A:$i]:
% 1.93/2.12     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.93/2.12       ( ![B:$i]:
% 1.93/2.12         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.93/2.12           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 1.93/2.12               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 1.93/2.12             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 1.93/2.12  thf('83', plain,
% 1.93/2.12      (![X6 : $i, X7 : $i]:
% 1.93/2.12         (~ (v1_relat_1 @ X6)
% 1.93/2.12          | ~ (v1_funct_1 @ X6)
% 1.93/2.12          | (v2_funct_1 @ X7)
% 1.93/2.12          | ((k2_relat_1 @ X6) != (k1_relat_1 @ X7))
% 1.93/2.12          | ~ (v2_funct_1 @ (k5_relat_1 @ X6 @ X7))
% 1.93/2.12          | ~ (v1_funct_1 @ X7)
% 1.93/2.12          | ~ (v1_relat_1 @ X7))),
% 1.93/2.12      inference('cnf', [status(esa)], [t48_funct_1])).
% 1.93/2.12  thf('84', plain,
% 1.93/2.12      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 1.93/2.12        | ~ (v1_relat_1 @ sk_D)
% 1.93/2.12        | ~ (v1_funct_1 @ sk_D)
% 1.93/2.12        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 1.93/2.12        | (v2_funct_1 @ sk_D)
% 1.93/2.12        | ~ (v1_funct_1 @ sk_C)
% 1.93/2.12        | ~ (v1_relat_1 @ sk_C))),
% 1.93/2.12      inference('sup-', [status(thm)], ['82', '83'])).
% 1.93/2.12  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 1.93/2.12  thf('85', plain, (![X8 : $i]: (v2_funct_1 @ (k6_relat_1 @ X8))),
% 1.93/2.12      inference('cnf', [status(esa)], [t52_funct_1])).
% 1.93/2.12  thf('86', plain, ((v1_relat_1 @ sk_D)),
% 1.93/2.12      inference('demod', [status(thm)], ['51', '52'])).
% 1.93/2.12  thf('87', plain, ((v1_funct_1 @ sk_D)),
% 1.93/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.12  thf('88', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.93/2.12      inference('sup+', [status(thm)], ['57', '58'])).
% 1.93/2.12  thf('89', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.93/2.12      inference('demod', [status(thm)], ['62', '69', '72'])).
% 1.93/2.12  thf('90', plain, ((v1_funct_1 @ sk_C)),
% 1.93/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.12  thf('91', plain, ((v1_relat_1 @ sk_C)),
% 1.93/2.12      inference('demod', [status(thm)], ['77', '78'])).
% 1.93/2.12  thf('92', plain, ((((sk_B) != (sk_B)) | (v2_funct_1 @ sk_D))),
% 1.93/2.12      inference('demod', [status(thm)],
% 1.93/2.12                ['84', '85', '86', '87', '88', '89', '90', '91'])).
% 1.93/2.12  thf('93', plain, ((v2_funct_1 @ sk_D)),
% 1.93/2.12      inference('simplify', [status(thm)], ['92'])).
% 1.93/2.12  thf('94', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.93/2.12      inference('demod', [status(thm)], ['81', '93'])).
% 1.93/2.12  thf(t3_funct_2, axiom,
% 1.93/2.12    (![A:$i]:
% 1.93/2.12     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.93/2.12       ( ( v1_funct_1 @ A ) & 
% 1.93/2.12         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.93/2.12         ( m1_subset_1 @
% 1.93/2.12           A @ 
% 1.93/2.12           ( k1_zfmisc_1 @
% 1.93/2.12             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.93/2.12  thf('95', plain,
% 1.93/2.12      (![X51 : $i]:
% 1.93/2.12         ((m1_subset_1 @ X51 @ 
% 1.93/2.12           (k1_zfmisc_1 @ 
% 1.93/2.12            (k2_zfmisc_1 @ (k1_relat_1 @ X51) @ (k2_relat_1 @ X51))))
% 1.93/2.12          | ~ (v1_funct_1 @ X51)
% 1.93/2.12          | ~ (v1_relat_1 @ X51))),
% 1.93/2.12      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.93/2.12  thf('96', plain,
% 1.93/2.12      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.93/2.12         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 1.93/2.12          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.93/2.12      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.93/2.12  thf('97', plain,
% 1.93/2.12      (![X0 : $i]:
% 1.93/2.12         (~ (v1_relat_1 @ X0)
% 1.93/2.12          | ~ (v1_funct_1 @ X0)
% 1.93/2.12          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.93/2.12              = (k2_relat_1 @ X0)))),
% 1.93/2.12      inference('sup-', [status(thm)], ['95', '96'])).
% 1.93/2.12  thf('98', plain,
% 1.93/2.12      (![X51 : $i]:
% 1.93/2.12         ((v1_funct_2 @ X51 @ (k1_relat_1 @ X51) @ (k2_relat_1 @ X51))
% 1.93/2.12          | ~ (v1_funct_1 @ X51)
% 1.93/2.12          | ~ (v1_relat_1 @ X51))),
% 1.93/2.12      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.93/2.12  thf('99', plain,
% 1.93/2.12      (![X51 : $i]:
% 1.93/2.12         ((m1_subset_1 @ X51 @ 
% 1.93/2.12           (k1_zfmisc_1 @ 
% 1.93/2.12            (k2_zfmisc_1 @ (k1_relat_1 @ X51) @ (k2_relat_1 @ X51))))
% 1.93/2.12          | ~ (v1_funct_1 @ X51)
% 1.93/2.12          | ~ (v1_relat_1 @ X51))),
% 1.93/2.12      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.93/2.12  thf(t35_funct_2, axiom,
% 1.93/2.12    (![A:$i,B:$i,C:$i]:
% 1.93/2.12     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.93/2.12         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.93/2.12       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.93/2.12         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.93/2.12           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 1.93/2.12             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 1.93/2.12  thf('100', plain,
% 1.93/2.12      (![X48 : $i, X49 : $i, X50 : $i]:
% 1.93/2.12         (((X48) = (k1_xboole_0))
% 1.93/2.12          | ~ (v1_funct_1 @ X49)
% 1.93/2.12          | ~ (v1_funct_2 @ X49 @ X50 @ X48)
% 1.93/2.12          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X48)))
% 1.93/2.12          | ((k5_relat_1 @ X49 @ (k2_funct_1 @ X49)) = (k6_partfun1 @ X50))
% 1.93/2.12          | ~ (v2_funct_1 @ X49)
% 1.93/2.12          | ((k2_relset_1 @ X50 @ X48 @ X49) != (X48)))),
% 1.93/2.12      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.93/2.12  thf('101', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 1.93/2.12      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.93/2.12  thf('102', plain,
% 1.93/2.12      (![X48 : $i, X49 : $i, X50 : $i]:
% 1.93/2.12         (((X48) = (k1_xboole_0))
% 1.93/2.12          | ~ (v1_funct_1 @ X49)
% 1.93/2.12          | ~ (v1_funct_2 @ X49 @ X50 @ X48)
% 1.93/2.12          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X48)))
% 1.93/2.12          | ((k5_relat_1 @ X49 @ (k2_funct_1 @ X49)) = (k6_relat_1 @ X50))
% 1.93/2.12          | ~ (v2_funct_1 @ X49)
% 1.93/2.12          | ((k2_relset_1 @ X50 @ X48 @ X49) != (X48)))),
% 1.93/2.12      inference('demod', [status(thm)], ['100', '101'])).
% 1.93/2.12  thf('103', plain,
% 1.93/2.12      (![X0 : $i]:
% 1.93/2.12         (~ (v1_relat_1 @ X0)
% 1.93/2.12          | ~ (v1_funct_1 @ X0)
% 1.93/2.12          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.93/2.12              != (k2_relat_1 @ X0))
% 1.93/2.12          | ~ (v2_funct_1 @ X0)
% 1.93/2.12          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.93/2.12              = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 1.93/2.12          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 1.93/2.12          | ~ (v1_funct_1 @ X0)
% 1.93/2.12          | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 1.93/2.12      inference('sup-', [status(thm)], ['99', '102'])).
% 1.93/2.12  thf('104', plain,
% 1.93/2.12      (![X0 : $i]:
% 1.93/2.12         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.93/2.12          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 1.93/2.12          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.93/2.12              = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 1.93/2.12          | ~ (v2_funct_1 @ X0)
% 1.93/2.12          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.93/2.12              != (k2_relat_1 @ X0))
% 1.93/2.12          | ~ (v1_funct_1 @ X0)
% 1.93/2.12          | ~ (v1_relat_1 @ X0))),
% 1.93/2.12      inference('simplify', [status(thm)], ['103'])).
% 1.93/2.12  thf('105', plain,
% 1.93/2.12      (![X0 : $i]:
% 1.93/2.12         (~ (v1_relat_1 @ X0)
% 1.93/2.12          | ~ (v1_funct_1 @ X0)
% 1.93/2.12          | ~ (v1_relat_1 @ X0)
% 1.93/2.12          | ~ (v1_funct_1 @ X0)
% 1.93/2.12          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.93/2.12              != (k2_relat_1 @ X0))
% 1.93/2.12          | ~ (v2_funct_1 @ X0)
% 1.93/2.12          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.93/2.12              = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 1.93/2.12          | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 1.93/2.12      inference('sup-', [status(thm)], ['98', '104'])).
% 1.93/2.12  thf('106', plain,
% 1.93/2.12      (![X0 : $i]:
% 1.93/2.12         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.93/2.12          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.93/2.12              = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 1.93/2.12          | ~ (v2_funct_1 @ X0)
% 1.93/2.12          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.93/2.12              != (k2_relat_1 @ X0))
% 1.93/2.12          | ~ (v1_funct_1 @ X0)
% 1.93/2.12          | ~ (v1_relat_1 @ X0))),
% 1.93/2.12      inference('simplify', [status(thm)], ['105'])).
% 1.93/2.12  thf('107', plain,
% 1.93/2.12      (![X0 : $i]:
% 1.93/2.12         (((k2_relat_1 @ X0) != (k2_relat_1 @ X0))
% 1.93/2.12          | ~ (v1_funct_1 @ X0)
% 1.93/2.12          | ~ (v1_relat_1 @ X0)
% 1.93/2.12          | ~ (v1_relat_1 @ X0)
% 1.93/2.12          | ~ (v1_funct_1 @ X0)
% 1.93/2.12          | ~ (v2_funct_1 @ X0)
% 1.93/2.12          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.93/2.12              = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 1.93/2.12          | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 1.93/2.12      inference('sup-', [status(thm)], ['97', '106'])).
% 1.93/2.12  thf('108', plain,
% 1.93/2.12      (![X0 : $i]:
% 1.93/2.12         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.93/2.12          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.93/2.12              = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 1.93/2.12          | ~ (v2_funct_1 @ X0)
% 1.93/2.12          | ~ (v1_relat_1 @ X0)
% 1.93/2.12          | ~ (v1_funct_1 @ X0))),
% 1.93/2.12      inference('simplify', [status(thm)], ['107'])).
% 1.93/2.12  thf('109', plain,
% 1.93/2.12      (![X9 : $i, X10 : $i]:
% 1.93/2.12         (~ (v1_relat_1 @ X9)
% 1.93/2.12          | ~ (v1_funct_1 @ X9)
% 1.93/2.12          | ((X9) = (k2_funct_1 @ X10))
% 1.93/2.12          | ((k5_relat_1 @ X9 @ X10) != (k6_relat_1 @ (k2_relat_1 @ X10)))
% 1.93/2.12          | ((k2_relat_1 @ X9) != (k1_relat_1 @ X10))
% 1.93/2.12          | ~ (v2_funct_1 @ X10)
% 1.93/2.12          | ~ (v1_funct_1 @ X10)
% 1.93/2.12          | ~ (v1_relat_1 @ X10))),
% 1.93/2.12      inference('cnf', [status(esa)], [t64_funct_1])).
% 1.93/2.12  thf('110', plain,
% 1.93/2.12      (![X0 : $i]:
% 1.93/2.12         (((k6_relat_1 @ (k1_relat_1 @ X0))
% 1.93/2.12            != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 1.93/2.12          | ~ (v1_funct_1 @ X0)
% 1.93/2.12          | ~ (v1_relat_1 @ X0)
% 1.93/2.12          | ~ (v2_funct_1 @ X0)
% 1.93/2.12          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.93/2.12          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.93/2.12          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.93/2.12          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.93/2.12          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.93/2.12          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.93/2.12          | ~ (v1_funct_1 @ X0)
% 1.93/2.13          | ~ (v1_relat_1 @ X0))),
% 1.93/2.13      inference('sup-', [status(thm)], ['108', '109'])).
% 1.93/2.13  thf('111', plain,
% 1.93/2.13      (![X0 : $i]:
% 1.93/2.13         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.93/2.13          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.93/2.13          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.93/2.13          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.93/2.13          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.93/2.13          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.93/2.13          | ~ (v2_funct_1 @ X0)
% 1.93/2.13          | ~ (v1_relat_1 @ X0)
% 1.93/2.13          | ~ (v1_funct_1 @ X0)
% 1.93/2.13          | ((k6_relat_1 @ (k1_relat_1 @ X0))
% 1.93/2.13              != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 1.93/2.13      inference('simplify', [status(thm)], ['110'])).
% 1.93/2.13  thf('112', plain,
% 1.93/2.13      ((((k6_relat_1 @ (k1_relat_1 @ sk_D))
% 1.93/2.13          != (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 1.93/2.13        | ~ (v1_funct_1 @ sk_D)
% 1.93/2.13        | ~ (v1_relat_1 @ sk_D)
% 1.93/2.13        | ~ (v2_funct_1 @ sk_D)
% 1.93/2.13        | ((k2_relat_1 @ sk_D) = (k1_xboole_0))
% 1.93/2.13        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D))
% 1.93/2.13        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 1.93/2.13        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_D))
% 1.93/2.13        | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ (k2_funct_1 @ sk_D)))
% 1.93/2.13        | ((sk_D) = (k2_funct_1 @ (k2_funct_1 @ sk_D))))),
% 1.93/2.13      inference('sup-', [status(thm)], ['94', '111'])).
% 1.93/2.13  thf('113', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.93/2.13      inference('demod', [status(thm)], ['62', '69', '72'])).
% 1.93/2.13  thf('114', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.93/2.13      inference('sup+', [status(thm)], ['57', '58'])).
% 1.93/2.13  thf('115', plain, ((v1_funct_1 @ sk_D)),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('116', plain, ((v1_relat_1 @ sk_D)),
% 1.93/2.13      inference('demod', [status(thm)], ['51', '52'])).
% 1.93/2.13  thf('117', plain, ((v2_funct_1 @ sk_D)),
% 1.93/2.13      inference('simplify', [status(thm)], ['92'])).
% 1.93/2.13  thf('118', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.93/2.13      inference('demod', [status(thm)], ['41', '44', '45', '46', '47'])).
% 1.93/2.13  thf('119', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.93/2.13      inference('demod', [status(thm)], ['81', '93'])).
% 1.93/2.13  thf('120', plain, ((v1_relat_1 @ sk_C)),
% 1.93/2.13      inference('demod', [status(thm)], ['77', '78'])).
% 1.93/2.13  thf('121', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.93/2.13      inference('demod', [status(thm)], ['81', '93'])).
% 1.93/2.13  thf('122', plain, ((v1_funct_1 @ sk_C)),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('123', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.93/2.13      inference('demod', [status(thm)], ['81', '93'])).
% 1.93/2.13  thf('124', plain, ((v2_funct_1 @ sk_C)),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('125', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.93/2.13      inference('demod', [status(thm)], ['41', '44', '45', '46', '47'])).
% 1.93/2.13  thf('126', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.93/2.13      inference('demod', [status(thm)], ['81', '93'])).
% 1.93/2.13  thf('127', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('128', plain,
% 1.93/2.13      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.93/2.13         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 1.93/2.13          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 1.93/2.13          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.93/2.13  thf('129', plain,
% 1.93/2.13      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 1.93/2.13        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 1.93/2.13      inference('sup-', [status(thm)], ['127', '128'])).
% 1.93/2.13  thf('130', plain,
% 1.93/2.13      (![X21 : $i, X22 : $i]:
% 1.93/2.13         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.93/2.13  thf('131', plain,
% 1.93/2.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('132', plain,
% 1.93/2.13      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.93/2.13         (~ (zip_tseitin_0 @ X26 @ X27)
% 1.93/2.13          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 1.93/2.13          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.93/2.13  thf('133', plain,
% 1.93/2.13      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.93/2.13      inference('sup-', [status(thm)], ['131', '132'])).
% 1.93/2.13  thf('134', plain,
% 1.93/2.13      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 1.93/2.13      inference('sup-', [status(thm)], ['130', '133'])).
% 1.93/2.13  thf('135', plain, (((sk_B) != (k1_xboole_0))),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('136', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 1.93/2.13      inference('simplify_reflect-', [status(thm)], ['134', '135'])).
% 1.93/2.13  thf('137', plain,
% 1.93/2.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('138', plain,
% 1.93/2.13      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.93/2.13         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 1.93/2.13          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.93/2.13      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.93/2.13  thf('139', plain,
% 1.93/2.13      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 1.93/2.13      inference('sup-', [status(thm)], ['137', '138'])).
% 1.93/2.13  thf('140', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 1.93/2.13      inference('demod', [status(thm)], ['129', '136', '139'])).
% 1.93/2.13  thf('141', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.93/2.13      inference('demod', [status(thm)], ['81', '93'])).
% 1.93/2.13  thf('142', plain,
% 1.93/2.13      ((((k6_relat_1 @ sk_B) != (k6_relat_1 @ sk_B))
% 1.93/2.13        | ((sk_A) = (k1_xboole_0))
% 1.93/2.13        | ((sk_A) != (sk_A))
% 1.93/2.13        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 1.93/2.13      inference('demod', [status(thm)],
% 1.93/2.13                ['112', '113', '114', '115', '116', '117', '118', '119', 
% 1.93/2.13                 '120', '121', '122', '123', '124', '125', '126', '140', '141'])).
% 1.93/2.13  thf('143', plain,
% 1.93/2.13      ((((sk_D) = (k2_funct_1 @ sk_C)) | ((sk_A) = (k1_xboole_0)))),
% 1.93/2.13      inference('simplify', [status(thm)], ['142'])).
% 1.93/2.13  thf('144', plain, (((sk_A) != (k1_xboole_0))),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('145', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.93/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.93/2.13  thf('146', plain, ($false),
% 1.93/2.13      inference('simplify_reflect-', [status(thm)], ['143', '144', '145'])).
% 1.93/2.13  
% 1.93/2.13  % SZS output end Refutation
% 1.93/2.13  
% 1.93/2.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

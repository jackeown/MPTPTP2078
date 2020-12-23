%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oKc0TgVkEt

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:21 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  180 (1845 expanded)
%              Number of leaves         :   47 ( 567 expanded)
%              Depth                    :   18
%              Number of atoms          : 1745 (46495 expanded)
%              Number of equality atoms :  119 (3167 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X4 )
       != ( k1_relat_1 @ X5 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
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
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
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

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('95',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k1_relat_1 @ X7 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

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
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k5_relat_1 @ X8 @ ( k2_funct_1 @ X8 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('97',plain,(
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

thf('98',plain,(
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
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
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
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['95','99'])).

thf('101',plain,(
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
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ( ( k2_relat_1 @ sk_D )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_D ) ) )
    | ( sk_D
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['94','101'])).

thf('103',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['51','52'])).

thf('105',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['92'])).

thf('107',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['81','93'])).

thf('108',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['77','78'])).

thf('109',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['81','93'])).

thf('110',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['41','44','45','46','47'])).

thf('112',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['81','93'])).

thf('113',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ( X23
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('115',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('117',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('119',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['116','119'])).

thf('121',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['120','121'])).

thf('123',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('125',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['115','122','125'])).

thf('127',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['81','93'])).

thf('128',plain,
    ( ( sk_A != sk_A )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['102','103','104','105','106','107','108','109','110','111','112','126','127'])).

thf('129',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['129','130'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oKc0TgVkEt
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:39:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.69/0.88  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.69/0.88  % Solved by: fo/fo7.sh
% 0.69/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.88  % done 304 iterations in 0.417s
% 0.69/0.88  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.69/0.88  % SZS output start Refutation
% 0.69/0.88  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.69/0.88  thf(sk_C_type, type, sk_C: $i).
% 0.69/0.88  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.69/0.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.69/0.88  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.69/0.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.69/0.88  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.69/0.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.69/0.88  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.69/0.88  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.69/0.88  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.69/0.88  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.69/0.88  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.69/0.88  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.69/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.88  thf(sk_B_type, type, sk_B: $i).
% 0.69/0.88  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.69/0.88  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.69/0.88  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.69/0.88  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.69/0.88  thf(sk_D_type, type, sk_D: $i).
% 0.69/0.88  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.69/0.88  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.69/0.88  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.69/0.88  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.69/0.88  thf(t36_funct_2, conjecture,
% 0.69/0.88    (![A:$i,B:$i,C:$i]:
% 0.69/0.88     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.69/0.88         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.69/0.88       ( ![D:$i]:
% 0.69/0.88         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.69/0.88             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.69/0.88           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.69/0.88               ( r2_relset_1 @
% 0.69/0.88                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.69/0.88                 ( k6_partfun1 @ A ) ) & 
% 0.69/0.88               ( v2_funct_1 @ C ) ) =>
% 0.69/0.88             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.69/0.88               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.69/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.88    (~( ![A:$i,B:$i,C:$i]:
% 0.69/0.88        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.69/0.88            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.69/0.88          ( ![D:$i]:
% 0.69/0.88            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.69/0.88                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.69/0.88              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.69/0.88                  ( r2_relset_1 @
% 0.69/0.88                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.69/0.88                    ( k6_partfun1 @ A ) ) & 
% 0.69/0.88                  ( v2_funct_1 @ C ) ) =>
% 0.69/0.88                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.69/0.88                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.69/0.88    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.69/0.88  thf('0', plain,
% 0.69/0.88      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.69/0.88        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.69/0.88        (k6_partfun1 @ sk_A))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf(redefinition_k6_partfun1, axiom,
% 0.69/0.88    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.69/0.88  thf('1', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 0.69/0.88      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.69/0.88  thf('2', plain,
% 0.69/0.88      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.69/0.88        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.69/0.88        (k6_relat_1 @ sk_A))),
% 0.69/0.88      inference('demod', [status(thm)], ['0', '1'])).
% 0.69/0.88  thf('3', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('4', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf(redefinition_k1_partfun1, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.69/0.88     ( ( ( v1_funct_1 @ E ) & 
% 0.69/0.88         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.69/0.88         ( v1_funct_1 @ F ) & 
% 0.69/0.88         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.69/0.88       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.69/0.88  thf('5', plain,
% 0.69/0.88      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.69/0.88         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.69/0.88          | ~ (v1_funct_1 @ X37)
% 0.69/0.88          | ~ (v1_funct_1 @ X40)
% 0.69/0.88          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.69/0.88          | ((k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40)
% 0.69/0.88              = (k5_relat_1 @ X37 @ X40)))),
% 0.69/0.88      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.69/0.88  thf('6', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.88         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.69/0.88            = (k5_relat_1 @ sk_C @ X0))
% 0.69/0.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.69/0.88          | ~ (v1_funct_1 @ X0)
% 0.69/0.88          | ~ (v1_funct_1 @ sk_C))),
% 0.69/0.88      inference('sup-', [status(thm)], ['4', '5'])).
% 0.69/0.88  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('8', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.88         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.69/0.88            = (k5_relat_1 @ sk_C @ X0))
% 0.69/0.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.69/0.88          | ~ (v1_funct_1 @ X0))),
% 0.69/0.88      inference('demod', [status(thm)], ['6', '7'])).
% 0.69/0.88  thf('9', plain,
% 0.69/0.88      ((~ (v1_funct_1 @ sk_D)
% 0.69/0.88        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.69/0.88            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['3', '8'])).
% 0.69/0.88  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('11', plain,
% 0.69/0.88      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.69/0.88         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.69/0.88      inference('demod', [status(thm)], ['9', '10'])).
% 0.69/0.88  thf('12', plain,
% 0.69/0.88      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.69/0.88        (k6_relat_1 @ sk_A))),
% 0.69/0.88      inference('demod', [status(thm)], ['2', '11'])).
% 0.69/0.88  thf('13', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('14', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf(dt_k1_partfun1, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.69/0.88     ( ( ( v1_funct_1 @ E ) & 
% 0.69/0.88         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.69/0.88         ( v1_funct_1 @ F ) & 
% 0.69/0.88         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.69/0.88       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.69/0.88         ( m1_subset_1 @
% 0.69/0.88           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.69/0.88           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.69/0.88  thf('15', plain,
% 0.69/0.88      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.69/0.88         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.69/0.88          | ~ (v1_funct_1 @ X29)
% 0.69/0.88          | ~ (v1_funct_1 @ X32)
% 0.69/0.88          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.69/0.88          | (m1_subset_1 @ (k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32) @ 
% 0.69/0.88             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X34))))),
% 0.69/0.88      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.69/0.88  thf('16', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.88         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.69/0.88           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.69/0.88          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.69/0.88          | ~ (v1_funct_1 @ X1)
% 0.69/0.88          | ~ (v1_funct_1 @ sk_C))),
% 0.69/0.88      inference('sup-', [status(thm)], ['14', '15'])).
% 0.69/0.88  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('18', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.88         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.69/0.88           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.69/0.88          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.69/0.88          | ~ (v1_funct_1 @ X1))),
% 0.69/0.88      inference('demod', [status(thm)], ['16', '17'])).
% 0.69/0.88  thf('19', plain,
% 0.69/0.88      ((~ (v1_funct_1 @ sk_D)
% 0.69/0.88        | (m1_subset_1 @ 
% 0.69/0.88           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.69/0.88           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.69/0.88      inference('sup-', [status(thm)], ['13', '18'])).
% 0.69/0.88  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('21', plain,
% 0.69/0.88      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.69/0.88         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.69/0.88      inference('demod', [status(thm)], ['9', '10'])).
% 0.69/0.88  thf('22', plain,
% 0.69/0.88      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.69/0.88        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.69/0.88      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.69/0.88  thf(redefinition_r2_relset_1, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i,D:$i]:
% 0.69/0.88     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.69/0.88         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.69/0.88       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.69/0.88  thf('23', plain,
% 0.69/0.88      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.69/0.88         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.69/0.88          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.69/0.88          | ((X17) = (X20))
% 0.69/0.88          | ~ (r2_relset_1 @ X18 @ X19 @ X17 @ X20))),
% 0.69/0.88      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.69/0.88  thf('24', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 0.69/0.88          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 0.69/0.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.69/0.88      inference('sup-', [status(thm)], ['22', '23'])).
% 0.69/0.88  thf('25', plain,
% 0.69/0.88      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 0.69/0.88           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.69/0.88        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['12', '24'])).
% 0.69/0.88  thf(dt_k6_partfun1, axiom,
% 0.69/0.88    (![A:$i]:
% 0.69/0.88     ( ( m1_subset_1 @
% 0.69/0.88         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.69/0.88       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.69/0.88  thf('26', plain,
% 0.69/0.88      (![X36 : $i]:
% 0.69/0.88         (m1_subset_1 @ (k6_partfun1 @ X36) @ 
% 0.69/0.88          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 0.69/0.88      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.69/0.88  thf('27', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 0.69/0.88      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.69/0.88  thf('28', plain,
% 0.69/0.88      (![X36 : $i]:
% 0.69/0.88         (m1_subset_1 @ (k6_relat_1 @ X36) @ 
% 0.69/0.88          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 0.69/0.88      inference('demod', [status(thm)], ['26', '27'])).
% 0.69/0.88  thf('29', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 0.69/0.88      inference('demod', [status(thm)], ['25', '28'])).
% 0.69/0.88  thf(t64_funct_1, axiom,
% 0.69/0.88    (![A:$i]:
% 0.69/0.88     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.69/0.88       ( ![B:$i]:
% 0.69/0.88         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.69/0.88           ( ( ( v2_funct_1 @ A ) & 
% 0.69/0.88               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.69/0.88               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.69/0.88             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.69/0.88  thf('30', plain,
% 0.69/0.88      (![X9 : $i, X10 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X9)
% 0.69/0.88          | ~ (v1_funct_1 @ X9)
% 0.69/0.88          | ((X9) = (k2_funct_1 @ X10))
% 0.69/0.88          | ((k5_relat_1 @ X9 @ X10) != (k6_relat_1 @ (k2_relat_1 @ X10)))
% 0.69/0.88          | ((k2_relat_1 @ X9) != (k1_relat_1 @ X10))
% 0.69/0.88          | ~ (v2_funct_1 @ X10)
% 0.69/0.88          | ~ (v1_funct_1 @ X10)
% 0.69/0.88          | ~ (v1_relat_1 @ X10))),
% 0.69/0.88      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.69/0.88  thf('31', plain,
% 0.69/0.88      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ (k2_relat_1 @ sk_D)))
% 0.69/0.88        | ~ (v1_relat_1 @ sk_D)
% 0.69/0.88        | ~ (v1_funct_1 @ sk_D)
% 0.69/0.88        | ~ (v2_funct_1 @ sk_D)
% 0.69/0.88        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.69/0.88        | ((sk_C) = (k2_funct_1 @ sk_D))
% 0.69/0.88        | ~ (v1_funct_1 @ sk_C)
% 0.69/0.88        | ~ (v1_relat_1 @ sk_C))),
% 0.69/0.88      inference('sup-', [status(thm)], ['29', '30'])).
% 0.69/0.88  thf('32', plain,
% 0.69/0.88      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.69/0.88        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.69/0.88        (k6_relat_1 @ sk_A))),
% 0.69/0.88      inference('demod', [status(thm)], ['0', '1'])).
% 0.69/0.88  thf('33', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf(t24_funct_2, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i]:
% 0.69/0.88     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.69/0.88         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.69/0.88       ( ![D:$i]:
% 0.69/0.88         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.69/0.88             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.69/0.88           ( ( r2_relset_1 @
% 0.69/0.88               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.69/0.88               ( k6_partfun1 @ B ) ) =>
% 0.69/0.88             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.69/0.88  thf('34', plain,
% 0.69/0.88      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.69/0.88         (~ (v1_funct_1 @ X44)
% 0.69/0.88          | ~ (v1_funct_2 @ X44 @ X45 @ X46)
% 0.69/0.88          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 0.69/0.88          | ~ (r2_relset_1 @ X45 @ X45 @ 
% 0.69/0.88               (k1_partfun1 @ X45 @ X46 @ X46 @ X45 @ X44 @ X47) @ 
% 0.69/0.88               (k6_partfun1 @ X45))
% 0.69/0.88          | ((k2_relset_1 @ X46 @ X45 @ X47) = (X45))
% 0.69/0.88          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45)))
% 0.69/0.88          | ~ (v1_funct_2 @ X47 @ X46 @ X45)
% 0.69/0.88          | ~ (v1_funct_1 @ X47))),
% 0.69/0.88      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.69/0.88  thf('35', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 0.69/0.88      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.69/0.88  thf('36', plain,
% 0.69/0.88      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.69/0.88         (~ (v1_funct_1 @ X44)
% 0.69/0.88          | ~ (v1_funct_2 @ X44 @ X45 @ X46)
% 0.69/0.88          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 0.69/0.88          | ~ (r2_relset_1 @ X45 @ X45 @ 
% 0.69/0.88               (k1_partfun1 @ X45 @ X46 @ X46 @ X45 @ X44 @ X47) @ 
% 0.69/0.88               (k6_relat_1 @ X45))
% 0.69/0.88          | ((k2_relset_1 @ X46 @ X45 @ X47) = (X45))
% 0.69/0.88          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45)))
% 0.69/0.88          | ~ (v1_funct_2 @ X47 @ X46 @ X45)
% 0.69/0.88          | ~ (v1_funct_1 @ X47))),
% 0.69/0.88      inference('demod', [status(thm)], ['34', '35'])).
% 0.69/0.88  thf('37', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (v1_funct_1 @ X0)
% 0.69/0.88          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.69/0.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.69/0.88          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.69/0.88          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.69/0.88               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.69/0.88               (k6_relat_1 @ sk_A))
% 0.69/0.88          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.69/0.88          | ~ (v1_funct_1 @ sk_C))),
% 0.69/0.88      inference('sup-', [status(thm)], ['33', '36'])).
% 0.69/0.88  thf('38', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('39', plain, ((v1_funct_1 @ sk_C)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('40', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (v1_funct_1 @ X0)
% 0.69/0.88          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.69/0.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.69/0.88          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.69/0.88          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.69/0.88               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.69/0.88               (k6_relat_1 @ sk_A)))),
% 0.69/0.88      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.69/0.88  thf('41', plain,
% 0.69/0.88      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.69/0.88        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.69/0.88        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.69/0.88        | ~ (v1_funct_1 @ sk_D))),
% 0.69/0.88      inference('sup-', [status(thm)], ['32', '40'])).
% 0.69/0.88  thf('42', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf(redefinition_k2_relset_1, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i]:
% 0.69/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.69/0.88       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.69/0.88  thf('43', plain,
% 0.69/0.88      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.69/0.88         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.69/0.88          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.69/0.88      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.69/0.88  thf('44', plain,
% 0.69/0.88      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.69/0.88      inference('sup-', [status(thm)], ['42', '43'])).
% 0.69/0.88  thf('45', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('46', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('47', plain, ((v1_funct_1 @ sk_D)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('48', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.69/0.88      inference('demod', [status(thm)], ['41', '44', '45', '46', '47'])).
% 0.69/0.88  thf('49', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf(cc2_relat_1, axiom,
% 0.69/0.88    (![A:$i]:
% 0.69/0.88     ( ( v1_relat_1 @ A ) =>
% 0.69/0.88       ( ![B:$i]:
% 0.69/0.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.69/0.88  thf('50', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.69/0.88          | (v1_relat_1 @ X0)
% 0.69/0.88          | ~ (v1_relat_1 @ X1))),
% 0.69/0.88      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.69/0.88  thf('51', plain,
% 0.69/0.88      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.69/0.88      inference('sup-', [status(thm)], ['49', '50'])).
% 0.69/0.88  thf(fc6_relat_1, axiom,
% 0.69/0.88    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.69/0.88  thf('52', plain,
% 0.69/0.88      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.69/0.88      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.69/0.88  thf('53', plain, ((v1_relat_1 @ sk_D)),
% 0.69/0.88      inference('demod', [status(thm)], ['51', '52'])).
% 0.69/0.88  thf('54', plain, ((v1_funct_1 @ sk_D)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('55', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('56', plain,
% 0.69/0.88      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.69/0.88         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.69/0.88          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.69/0.88      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.69/0.88  thf('57', plain,
% 0.69/0.88      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.69/0.88      inference('sup-', [status(thm)], ['55', '56'])).
% 0.69/0.88  thf('58', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('59', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.69/0.88      inference('sup+', [status(thm)], ['57', '58'])).
% 0.69/0.88  thf('60', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf(d1_funct_2, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i]:
% 0.69/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.69/0.88       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.69/0.88           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.69/0.88             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.69/0.88         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.69/0.88           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.69/0.88             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.69/0.88  thf(zf_stmt_1, axiom,
% 0.69/0.88    (![C:$i,B:$i,A:$i]:
% 0.69/0.88     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.69/0.88       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.69/0.88  thf('61', plain,
% 0.69/0.88      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.69/0.88         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 0.69/0.88          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 0.69/0.88          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.69/0.88  thf('62', plain,
% 0.69/0.88      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 0.69/0.88        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['60', '61'])).
% 0.69/0.88  thf(zf_stmt_2, axiom,
% 0.69/0.88    (![B:$i,A:$i]:
% 0.69/0.88     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.69/0.88       ( zip_tseitin_0 @ B @ A ) ))).
% 0.69/0.88  thf('63', plain,
% 0.69/0.88      (![X21 : $i, X22 : $i]:
% 0.69/0.88         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.69/0.88  thf('64', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.69/0.88  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.69/0.88  thf(zf_stmt_5, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i]:
% 0.69/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.69/0.88       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.69/0.88         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.69/0.88           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.69/0.88             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.69/0.88  thf('65', plain,
% 0.69/0.88      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.69/0.88         (~ (zip_tseitin_0 @ X26 @ X27)
% 0.69/0.88          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 0.69/0.88          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.69/0.88  thf('66', plain,
% 0.69/0.88      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 0.69/0.88      inference('sup-', [status(thm)], ['64', '65'])).
% 0.69/0.88  thf('67', plain,
% 0.69/0.88      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 0.69/0.88      inference('sup-', [status(thm)], ['63', '66'])).
% 0.69/0.88  thf('68', plain, (((sk_A) != (k1_xboole_0))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('69', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 0.69/0.88      inference('simplify_reflect-', [status(thm)], ['67', '68'])).
% 0.69/0.88  thf('70', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf(redefinition_k1_relset_1, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i]:
% 0.69/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.69/0.88       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.69/0.88  thf('71', plain,
% 0.69/0.88      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.69/0.88         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 0.69/0.88          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.69/0.88      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.69/0.88  thf('72', plain,
% 0.69/0.88      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.69/0.88      inference('sup-', [status(thm)], ['70', '71'])).
% 0.69/0.88  thf('73', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.69/0.88      inference('demod', [status(thm)], ['62', '69', '72'])).
% 0.69/0.88  thf('74', plain, ((v1_funct_1 @ sk_C)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('75', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('76', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.69/0.88          | (v1_relat_1 @ X0)
% 0.69/0.88          | ~ (v1_relat_1 @ X1))),
% 0.69/0.88      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.69/0.88  thf('77', plain,
% 0.69/0.88      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.69/0.88      inference('sup-', [status(thm)], ['75', '76'])).
% 0.69/0.88  thf('78', plain,
% 0.69/0.88      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.69/0.88      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.69/0.88  thf('79', plain, ((v1_relat_1 @ sk_C)),
% 0.69/0.88      inference('demod', [status(thm)], ['77', '78'])).
% 0.69/0.88  thf('80', plain,
% 0.69/0.88      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ sk_A))
% 0.69/0.88        | ~ (v2_funct_1 @ sk_D)
% 0.69/0.88        | ((sk_B) != (sk_B))
% 0.69/0.88        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 0.69/0.88      inference('demod', [status(thm)],
% 0.69/0.88                ['31', '48', '53', '54', '59', '73', '74', '79'])).
% 0.69/0.88  thf('81', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 0.69/0.88      inference('simplify', [status(thm)], ['80'])).
% 0.69/0.88  thf('82', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 0.69/0.88      inference('demod', [status(thm)], ['25', '28'])).
% 0.69/0.88  thf(t48_funct_1, axiom,
% 0.69/0.88    (![A:$i]:
% 0.69/0.88     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.69/0.88       ( ![B:$i]:
% 0.69/0.88         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.69/0.88           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.69/0.88               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.69/0.88             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.69/0.88  thf('83', plain,
% 0.69/0.88      (![X4 : $i, X5 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X4)
% 0.69/0.88          | ~ (v1_funct_1 @ X4)
% 0.69/0.88          | (v2_funct_1 @ X5)
% 0.69/0.88          | ((k2_relat_1 @ X4) != (k1_relat_1 @ X5))
% 0.69/0.88          | ~ (v2_funct_1 @ (k5_relat_1 @ X4 @ X5))
% 0.69/0.88          | ~ (v1_funct_1 @ X5)
% 0.69/0.88          | ~ (v1_relat_1 @ X5))),
% 0.69/0.88      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.69/0.88  thf('84', plain,
% 0.69/0.88      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 0.69/0.88        | ~ (v1_relat_1 @ sk_D)
% 0.69/0.88        | ~ (v1_funct_1 @ sk_D)
% 0.69/0.88        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.69/0.88        | (v2_funct_1 @ sk_D)
% 0.69/0.88        | ~ (v1_funct_1 @ sk_C)
% 0.69/0.88        | ~ (v1_relat_1 @ sk_C))),
% 0.69/0.88      inference('sup-', [status(thm)], ['82', '83'])).
% 0.69/0.88  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 0.69/0.88  thf('85', plain, (![X6 : $i]: (v2_funct_1 @ (k6_relat_1 @ X6))),
% 0.69/0.88      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.69/0.88  thf('86', plain, ((v1_relat_1 @ sk_D)),
% 0.69/0.88      inference('demod', [status(thm)], ['51', '52'])).
% 0.69/0.88  thf('87', plain, ((v1_funct_1 @ sk_D)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('88', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.69/0.88      inference('sup+', [status(thm)], ['57', '58'])).
% 0.69/0.88  thf('89', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.69/0.88      inference('demod', [status(thm)], ['62', '69', '72'])).
% 0.69/0.88  thf('90', plain, ((v1_funct_1 @ sk_C)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('91', plain, ((v1_relat_1 @ sk_C)),
% 0.69/0.88      inference('demod', [status(thm)], ['77', '78'])).
% 0.69/0.88  thf('92', plain, ((((sk_B) != (sk_B)) | (v2_funct_1 @ sk_D))),
% 0.69/0.88      inference('demod', [status(thm)],
% 0.69/0.88                ['84', '85', '86', '87', '88', '89', '90', '91'])).
% 0.69/0.88  thf('93', plain, ((v2_funct_1 @ sk_D)),
% 0.69/0.88      inference('simplify', [status(thm)], ['92'])).
% 0.69/0.88  thf('94', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.69/0.88      inference('demod', [status(thm)], ['81', '93'])).
% 0.69/0.88  thf(t55_funct_1, axiom,
% 0.69/0.88    (![A:$i]:
% 0.69/0.88     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.69/0.88       ( ( v2_funct_1 @ A ) =>
% 0.69/0.88         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.69/0.88           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.69/0.88  thf('95', plain,
% 0.69/0.88      (![X7 : $i]:
% 0.69/0.88         (~ (v2_funct_1 @ X7)
% 0.69/0.88          | ((k1_relat_1 @ X7) = (k2_relat_1 @ (k2_funct_1 @ X7)))
% 0.69/0.88          | ~ (v1_funct_1 @ X7)
% 0.69/0.88          | ~ (v1_relat_1 @ X7))),
% 0.69/0.88      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.69/0.88  thf(t61_funct_1, axiom,
% 0.69/0.88    (![A:$i]:
% 0.69/0.88     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.69/0.88       ( ( v2_funct_1 @ A ) =>
% 0.69/0.88         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.69/0.88             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.69/0.88           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.69/0.88             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.69/0.88  thf('96', plain,
% 0.69/0.88      (![X8 : $i]:
% 0.69/0.88         (~ (v2_funct_1 @ X8)
% 0.69/0.88          | ((k5_relat_1 @ X8 @ (k2_funct_1 @ X8))
% 0.69/0.88              = (k6_relat_1 @ (k1_relat_1 @ X8)))
% 0.69/0.88          | ~ (v1_funct_1 @ X8)
% 0.69/0.88          | ~ (v1_relat_1 @ X8))),
% 0.69/0.88      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.69/0.88  thf('97', plain,
% 0.69/0.88      (![X9 : $i, X10 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X9)
% 0.69/0.88          | ~ (v1_funct_1 @ X9)
% 0.69/0.88          | ((X9) = (k2_funct_1 @ X10))
% 0.69/0.88          | ((k5_relat_1 @ X9 @ X10) != (k6_relat_1 @ (k2_relat_1 @ X10)))
% 0.69/0.88          | ((k2_relat_1 @ X9) != (k1_relat_1 @ X10))
% 0.69/0.88          | ~ (v2_funct_1 @ X10)
% 0.69/0.88          | ~ (v1_funct_1 @ X10)
% 0.69/0.88          | ~ (v1_relat_1 @ X10))),
% 0.69/0.88      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.69/0.88  thf('98', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (((k6_relat_1 @ (k1_relat_1 @ X0))
% 0.69/0.88            != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.69/0.88          | ~ (v1_relat_1 @ X0)
% 0.69/0.88          | ~ (v1_funct_1 @ X0)
% 0.69/0.88          | ~ (v2_funct_1 @ X0)
% 0.69/0.88          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.69/0.88          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.69/0.88          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.69/0.88          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.69/0.88          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.69/0.88          | ~ (v1_funct_1 @ X0)
% 0.69/0.88          | ~ (v1_relat_1 @ X0))),
% 0.69/0.88      inference('sup-', [status(thm)], ['96', '97'])).
% 0.69/0.88  thf('99', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.69/0.88          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.69/0.88          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.69/0.88          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.69/0.88          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.69/0.88          | ~ (v2_funct_1 @ X0)
% 0.69/0.88          | ~ (v1_funct_1 @ X0)
% 0.69/0.88          | ~ (v1_relat_1 @ X0)
% 0.69/0.88          | ((k6_relat_1 @ (k1_relat_1 @ X0))
% 0.69/0.88              != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.69/0.88      inference('simplify', [status(thm)], ['98'])).
% 0.69/0.88  thf('100', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (((k6_relat_1 @ (k1_relat_1 @ X0)) != (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.69/0.88          | ~ (v1_relat_1 @ X0)
% 0.69/0.88          | ~ (v1_funct_1 @ X0)
% 0.69/0.88          | ~ (v2_funct_1 @ X0)
% 0.69/0.88          | ~ (v1_relat_1 @ X0)
% 0.69/0.88          | ~ (v1_funct_1 @ X0)
% 0.69/0.88          | ~ (v2_funct_1 @ X0)
% 0.69/0.88          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.69/0.88          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.69/0.88          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.69/0.88          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.69/0.88          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.69/0.88      inference('sup-', [status(thm)], ['95', '99'])).
% 0.69/0.88  thf('101', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.69/0.88          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.69/0.88          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.69/0.88          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.69/0.88          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.69/0.88          | ~ (v2_funct_1 @ X0)
% 0.69/0.88          | ~ (v1_funct_1 @ X0)
% 0.69/0.88          | ~ (v1_relat_1 @ X0))),
% 0.69/0.88      inference('simplify', [status(thm)], ['100'])).
% 0.69/0.88  thf('102', plain,
% 0.69/0.88      ((~ (v2_funct_1 @ sk_C)
% 0.69/0.88        | ~ (v1_relat_1 @ sk_D)
% 0.69/0.88        | ~ (v1_funct_1 @ sk_D)
% 0.69/0.88        | ~ (v2_funct_1 @ sk_D)
% 0.69/0.88        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D))
% 0.69/0.88        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 0.69/0.88        | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ (k2_funct_1 @ sk_D)))
% 0.69/0.88        | ((sk_D) = (k2_funct_1 @ (k2_funct_1 @ sk_D))))),
% 0.69/0.88      inference('sup-', [status(thm)], ['94', '101'])).
% 0.69/0.88  thf('103', plain, ((v2_funct_1 @ sk_C)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('104', plain, ((v1_relat_1 @ sk_D)),
% 0.69/0.88      inference('demod', [status(thm)], ['51', '52'])).
% 0.69/0.88  thf('105', plain, ((v1_funct_1 @ sk_D)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('106', plain, ((v2_funct_1 @ sk_D)),
% 0.69/0.88      inference('simplify', [status(thm)], ['92'])).
% 0.69/0.88  thf('107', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.69/0.88      inference('demod', [status(thm)], ['81', '93'])).
% 0.69/0.88  thf('108', plain, ((v1_relat_1 @ sk_C)),
% 0.69/0.88      inference('demod', [status(thm)], ['77', '78'])).
% 0.69/0.88  thf('109', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.69/0.88      inference('demod', [status(thm)], ['81', '93'])).
% 0.69/0.88  thf('110', plain, ((v1_funct_1 @ sk_C)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('111', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.69/0.88      inference('demod', [status(thm)], ['41', '44', '45', '46', '47'])).
% 0.69/0.88  thf('112', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.69/0.88      inference('demod', [status(thm)], ['81', '93'])).
% 0.69/0.88  thf('113', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('114', plain,
% 0.69/0.88      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.69/0.88         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 0.69/0.88          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 0.69/0.88          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.69/0.88  thf('115', plain,
% 0.69/0.88      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.69/0.88        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['113', '114'])).
% 0.69/0.88  thf('116', plain,
% 0.69/0.88      (![X21 : $i, X22 : $i]:
% 0.69/0.88         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.69/0.88  thf('117', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('118', plain,
% 0.69/0.88      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.69/0.88         (~ (zip_tseitin_0 @ X26 @ X27)
% 0.69/0.88          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 0.69/0.88          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.69/0.88  thf('119', plain,
% 0.69/0.88      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.69/0.88      inference('sup-', [status(thm)], ['117', '118'])).
% 0.69/0.88  thf('120', plain,
% 0.69/0.88      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.69/0.88      inference('sup-', [status(thm)], ['116', '119'])).
% 0.69/0.88  thf('121', plain, (((sk_B) != (k1_xboole_0))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('122', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.69/0.88      inference('simplify_reflect-', [status(thm)], ['120', '121'])).
% 0.69/0.88  thf('123', plain,
% 0.69/0.88      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('124', plain,
% 0.69/0.88      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.69/0.88         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 0.69/0.88          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.69/0.88      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.69/0.88  thf('125', plain,
% 0.69/0.88      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.69/0.88      inference('sup-', [status(thm)], ['123', '124'])).
% 0.69/0.88  thf('126', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.69/0.88      inference('demod', [status(thm)], ['115', '122', '125'])).
% 0.69/0.88  thf('127', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.69/0.88      inference('demod', [status(thm)], ['81', '93'])).
% 0.69/0.88  thf('128', plain, ((((sk_A) != (sk_A)) | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 0.69/0.88      inference('demod', [status(thm)],
% 0.69/0.88                ['102', '103', '104', '105', '106', '107', '108', '109', 
% 0.69/0.88                 '110', '111', '112', '126', '127'])).
% 0.69/0.88  thf('129', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 0.69/0.88      inference('simplify', [status(thm)], ['128'])).
% 0.69/0.88  thf('130', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('131', plain, ($false),
% 0.69/0.88      inference('simplify_reflect-', [status(thm)], ['129', '130'])).
% 0.69/0.88  
% 0.69/0.88  % SZS output end Refutation
% 0.69/0.88  
% 0.69/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

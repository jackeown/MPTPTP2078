%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pmAAz8vEGm

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:21 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :  179 (2116 expanded)
%              Number of leaves         :   46 ( 645 expanded)
%              Depth                    :   18
%              Number of atoms          : 1660 (54686 expanded)
%              Number of equality atoms :  119 (3740 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

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

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( ( k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40 )
        = ( k5_relat_1 @ X37 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('20',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('21',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( X17 = X20 )
      | ~ ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','22'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('24',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('25',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

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

thf('26',plain,(
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

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('27',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( X9
        = ( k2_funct_1 @ X10 ) )
      | ( ( k5_relat_1 @ X9 @ X10 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X10 ) ) )
      | ( ( k2_relat_1 @ X9 )
       != ( k1_relat_1 @ X10 ) )
      | ~ ( v2_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
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

thf('32',plain,(
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

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('39',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('40',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['37','40','41','42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('48',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('49',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('53',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
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

thf('57',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ( X23
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('58',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('59',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('60',plain,(
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

thf('61',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('62',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['63','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('67',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('68',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['58','65','68'])).

thf('70',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('73',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('75',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B != sk_B )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['29','44','49','50','55','69','70','75'])).

thf('77',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

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

thf('80',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('81',plain,(
    ! [X5: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('82',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('83',plain,(
    ! [X5: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X5 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['47','48'])).

thf('85',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['53','54'])).

thf('87',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['58','65','68'])).

thf('88',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['73','74'])).

thf('90',plain,
    ( ( sk_B != sk_B )
    | ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['80','83','84','85','86','87','88','89'])).

thf('91',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['77','91'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('93',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k5_relat_1 @ X8 @ ( k2_funct_1 @ X8 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('94',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('95',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k5_relat_1 @ X8 @ ( k2_funct_1 @ X8 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( X9
        = ( k2_funct_1 @ X10 ) )
      | ( ( k5_relat_1 @ X9 @ X10 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X10 ) ) )
      | ( ( k2_relat_1 @ X9 )
       != ( k1_relat_1 @ X10 ) )
      | ~ ( v2_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
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
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
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
      | ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
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
    inference('sup-',[status(thm)],['92','98'])).

thf('100',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['58','65','68'])).

thf('101',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['53','54'])).

thf('102',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['47','48'])).

thf('103',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['90'])).

thf('105',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['77','91'])).

thf('106',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['73','74'])).

thf('107',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['77','91'])).

thf('108',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['77','91'])).

thf('110',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['37','40','41','42','43'])).

thf('112',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['77','91'])).

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
    inference(demod,[status(thm)],['77','91'])).

thf('128',plain,
    ( ( ( k6_partfun1 @ sk_B )
     != ( k6_partfun1 @ sk_B ) )
    | ( sk_A != sk_A )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['99','100','101','102','103','104','105','106','107','108','109','110','111','112','126','127'])).

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
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pmAAz8vEGm
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:43:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.70/0.93  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.70/0.93  % Solved by: fo/fo7.sh
% 0.70/0.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.93  % done 361 iterations in 0.478s
% 0.70/0.93  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.70/0.93  % SZS output start Refutation
% 0.70/0.93  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.70/0.93  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.70/0.93  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.70/0.93  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.70/0.93  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.70/0.93  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.70/0.93  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.70/0.93  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.70/0.93  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.70/0.93  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.70/0.93  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.70/0.93  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.70/0.93  thf(sk_C_type, type, sk_C: $i).
% 0.70/0.93  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.70/0.93  thf(sk_D_type, type, sk_D: $i).
% 0.70/0.93  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.70/0.93  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.70/0.93  thf(sk_B_type, type, sk_B: $i).
% 0.70/0.93  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.70/0.93  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.70/0.93  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.93  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.70/0.93  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.70/0.93  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.70/0.93  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.70/0.93  thf(t36_funct_2, conjecture,
% 0.70/0.93    (![A:$i,B:$i,C:$i]:
% 0.70/0.93     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.70/0.93         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.70/0.93       ( ![D:$i]:
% 0.70/0.93         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.70/0.93             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.70/0.93           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.70/0.93               ( r2_relset_1 @
% 0.70/0.93                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.70/0.93                 ( k6_partfun1 @ A ) ) & 
% 0.70/0.93               ( v2_funct_1 @ C ) ) =>
% 0.70/0.93             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.70/0.93               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.70/0.93  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.93    (~( ![A:$i,B:$i,C:$i]:
% 0.70/0.93        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.70/0.93            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.70/0.93          ( ![D:$i]:
% 0.70/0.93            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.70/0.93                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.70/0.93              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.70/0.93                  ( r2_relset_1 @
% 0.70/0.93                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.70/0.93                    ( k6_partfun1 @ A ) ) & 
% 0.70/0.93                  ( v2_funct_1 @ C ) ) =>
% 0.70/0.93                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.70/0.93                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.70/0.93    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.70/0.93  thf('0', plain,
% 0.70/0.93      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.70/0.93        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.70/0.93        (k6_partfun1 @ sk_A))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf('1', plain,
% 0.70/0.93      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf('2', plain,
% 0.70/0.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf(redefinition_k1_partfun1, axiom,
% 0.70/0.93    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.70/0.93     ( ( ( v1_funct_1 @ E ) & 
% 0.70/0.93         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.70/0.93         ( v1_funct_1 @ F ) & 
% 0.70/0.93         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.70/0.93       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.70/0.93  thf('3', plain,
% 0.70/0.93      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.70/0.93         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.70/0.93          | ~ (v1_funct_1 @ X37)
% 0.70/0.93          | ~ (v1_funct_1 @ X40)
% 0.70/0.93          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.70/0.93          | ((k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40)
% 0.70/0.93              = (k5_relat_1 @ X37 @ X40)))),
% 0.70/0.93      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.70/0.93  thf('4', plain,
% 0.70/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.93         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.70/0.93            = (k5_relat_1 @ sk_C @ X0))
% 0.70/0.93          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.70/0.93          | ~ (v1_funct_1 @ X0)
% 0.70/0.93          | ~ (v1_funct_1 @ sk_C))),
% 0.70/0.93      inference('sup-', [status(thm)], ['2', '3'])).
% 0.70/0.93  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf('6', plain,
% 0.70/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.93         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.70/0.93            = (k5_relat_1 @ sk_C @ X0))
% 0.70/0.93          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.70/0.93          | ~ (v1_funct_1 @ X0))),
% 0.70/0.93      inference('demod', [status(thm)], ['4', '5'])).
% 0.70/0.93  thf('7', plain,
% 0.70/0.93      ((~ (v1_funct_1 @ sk_D)
% 0.70/0.93        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.70/0.93            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.70/0.93      inference('sup-', [status(thm)], ['1', '6'])).
% 0.70/0.93  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf('9', plain,
% 0.70/0.93      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.70/0.93         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.70/0.93      inference('demod', [status(thm)], ['7', '8'])).
% 0.70/0.93  thf('10', plain,
% 0.70/0.93      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.70/0.93        (k6_partfun1 @ sk_A))),
% 0.70/0.93      inference('demod', [status(thm)], ['0', '9'])).
% 0.70/0.93  thf('11', plain,
% 0.70/0.93      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf('12', plain,
% 0.70/0.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf(dt_k1_partfun1, axiom,
% 0.70/0.93    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.70/0.93     ( ( ( v1_funct_1 @ E ) & 
% 0.70/0.93         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.70/0.93         ( v1_funct_1 @ F ) & 
% 0.70/0.93         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.70/0.93       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.70/0.93         ( m1_subset_1 @
% 0.70/0.93           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.70/0.93           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.70/0.93  thf('13', plain,
% 0.70/0.93      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.70/0.93         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.70/0.93          | ~ (v1_funct_1 @ X29)
% 0.70/0.93          | ~ (v1_funct_1 @ X32)
% 0.70/0.93          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.70/0.93          | (m1_subset_1 @ (k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32) @ 
% 0.70/0.93             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X34))))),
% 0.70/0.93      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.70/0.93  thf('14', plain,
% 0.70/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.93         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.70/0.93           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.70/0.93          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.70/0.93          | ~ (v1_funct_1 @ X1)
% 0.70/0.93          | ~ (v1_funct_1 @ sk_C))),
% 0.70/0.93      inference('sup-', [status(thm)], ['12', '13'])).
% 0.70/0.93  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf('16', plain,
% 0.70/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.93         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.70/0.93           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.70/0.93          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.70/0.93          | ~ (v1_funct_1 @ X1))),
% 0.70/0.93      inference('demod', [status(thm)], ['14', '15'])).
% 0.70/0.93  thf('17', plain,
% 0.70/0.93      ((~ (v1_funct_1 @ sk_D)
% 0.70/0.93        | (m1_subset_1 @ 
% 0.70/0.93           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.70/0.93           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.70/0.93      inference('sup-', [status(thm)], ['11', '16'])).
% 0.70/0.93  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf('19', plain,
% 0.70/0.93      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.70/0.93         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.70/0.93      inference('demod', [status(thm)], ['7', '8'])).
% 0.70/0.93  thf('20', plain,
% 0.70/0.93      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.70/0.93        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.70/0.93      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.70/0.93  thf(redefinition_r2_relset_1, axiom,
% 0.70/0.93    (![A:$i,B:$i,C:$i,D:$i]:
% 0.70/0.93     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.70/0.93         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.70/0.93       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.70/0.93  thf('21', plain,
% 0.70/0.93      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.70/0.93         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.70/0.93          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.70/0.93          | ((X17) = (X20))
% 0.70/0.93          | ~ (r2_relset_1 @ X18 @ X19 @ X17 @ X20))),
% 0.70/0.93      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.70/0.93  thf('22', plain,
% 0.70/0.93      (![X0 : $i]:
% 0.70/0.93         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 0.70/0.93          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 0.70/0.93          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.70/0.93      inference('sup-', [status(thm)], ['20', '21'])).
% 0.70/0.93  thf('23', plain,
% 0.70/0.93      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.70/0.93           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.70/0.93        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 0.70/0.93      inference('sup-', [status(thm)], ['10', '22'])).
% 0.70/0.93  thf(dt_k6_partfun1, axiom,
% 0.70/0.93    (![A:$i]:
% 0.70/0.93     ( ( m1_subset_1 @
% 0.70/0.93         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.70/0.93       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.70/0.93  thf('24', plain,
% 0.70/0.93      (![X36 : $i]:
% 0.70/0.93         (m1_subset_1 @ (k6_partfun1 @ X36) @ 
% 0.70/0.93          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 0.70/0.93      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.70/0.93  thf('25', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.70/0.93      inference('demod', [status(thm)], ['23', '24'])).
% 0.70/0.93  thf(t64_funct_1, axiom,
% 0.70/0.93    (![A:$i]:
% 0.70/0.93     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.70/0.93       ( ![B:$i]:
% 0.70/0.93         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.70/0.93           ( ( ( v2_funct_1 @ A ) & 
% 0.70/0.93               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.70/0.93               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.70/0.93             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.70/0.93  thf('26', plain,
% 0.70/0.93      (![X9 : $i, X10 : $i]:
% 0.70/0.93         (~ (v1_relat_1 @ X9)
% 0.70/0.93          | ~ (v1_funct_1 @ X9)
% 0.70/0.93          | ((X9) = (k2_funct_1 @ X10))
% 0.70/0.93          | ((k5_relat_1 @ X9 @ X10) != (k6_relat_1 @ (k2_relat_1 @ X10)))
% 0.70/0.93          | ((k2_relat_1 @ X9) != (k1_relat_1 @ X10))
% 0.70/0.93          | ~ (v2_funct_1 @ X10)
% 0.70/0.93          | ~ (v1_funct_1 @ X10)
% 0.70/0.93          | ~ (v1_relat_1 @ X10))),
% 0.70/0.93      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.70/0.93  thf(redefinition_k6_partfun1, axiom,
% 0.70/0.93    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.70/0.93  thf('27', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 0.70/0.93      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.70/0.93  thf('28', plain,
% 0.70/0.93      (![X9 : $i, X10 : $i]:
% 0.70/0.93         (~ (v1_relat_1 @ X9)
% 0.70/0.93          | ~ (v1_funct_1 @ X9)
% 0.70/0.93          | ((X9) = (k2_funct_1 @ X10))
% 0.70/0.93          | ((k5_relat_1 @ X9 @ X10) != (k6_partfun1 @ (k2_relat_1 @ X10)))
% 0.70/0.93          | ((k2_relat_1 @ X9) != (k1_relat_1 @ X10))
% 0.70/0.93          | ~ (v2_funct_1 @ X10)
% 0.70/0.93          | ~ (v1_funct_1 @ X10)
% 0.70/0.93          | ~ (v1_relat_1 @ X10))),
% 0.70/0.93      inference('demod', [status(thm)], ['26', '27'])).
% 0.70/0.93  thf('29', plain,
% 0.70/0.93      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 0.70/0.93        | ~ (v1_relat_1 @ sk_D)
% 0.70/0.93        | ~ (v1_funct_1 @ sk_D)
% 0.70/0.93        | ~ (v2_funct_1 @ sk_D)
% 0.70/0.93        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.70/0.93        | ((sk_C) = (k2_funct_1 @ sk_D))
% 0.70/0.93        | ~ (v1_funct_1 @ sk_C)
% 0.70/0.93        | ~ (v1_relat_1 @ sk_C))),
% 0.70/0.93      inference('sup-', [status(thm)], ['25', '28'])).
% 0.70/0.93  thf('30', plain,
% 0.70/0.93      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.70/0.93        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.70/0.93        (k6_partfun1 @ sk_A))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf('31', plain,
% 0.70/0.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf(t24_funct_2, axiom,
% 0.70/0.93    (![A:$i,B:$i,C:$i]:
% 0.70/0.93     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.70/0.93         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.70/0.93       ( ![D:$i]:
% 0.70/0.93         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.70/0.93             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.70/0.93           ( ( r2_relset_1 @
% 0.70/0.93               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.70/0.93               ( k6_partfun1 @ B ) ) =>
% 0.70/0.93             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.70/0.93  thf('32', plain,
% 0.70/0.93      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.70/0.93         (~ (v1_funct_1 @ X44)
% 0.70/0.93          | ~ (v1_funct_2 @ X44 @ X45 @ X46)
% 0.70/0.93          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 0.70/0.93          | ~ (r2_relset_1 @ X45 @ X45 @ 
% 0.70/0.93               (k1_partfun1 @ X45 @ X46 @ X46 @ X45 @ X44 @ X47) @ 
% 0.70/0.93               (k6_partfun1 @ X45))
% 0.70/0.93          | ((k2_relset_1 @ X46 @ X45 @ X47) = (X45))
% 0.70/0.93          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45)))
% 0.70/0.93          | ~ (v1_funct_2 @ X47 @ X46 @ X45)
% 0.70/0.93          | ~ (v1_funct_1 @ X47))),
% 0.70/0.93      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.70/0.93  thf('33', plain,
% 0.70/0.93      (![X0 : $i]:
% 0.70/0.93         (~ (v1_funct_1 @ X0)
% 0.70/0.93          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.70/0.93          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.70/0.93          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.70/0.93          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.70/0.93               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.70/0.93               (k6_partfun1 @ sk_A))
% 0.70/0.93          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.70/0.93          | ~ (v1_funct_1 @ sk_C))),
% 0.70/0.93      inference('sup-', [status(thm)], ['31', '32'])).
% 0.70/0.93  thf('34', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf('36', plain,
% 0.70/0.93      (![X0 : $i]:
% 0.70/0.93         (~ (v1_funct_1 @ X0)
% 0.70/0.93          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.70/0.93          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.70/0.93          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.70/0.93          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.70/0.93               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.70/0.93               (k6_partfun1 @ sk_A)))),
% 0.70/0.93      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.70/0.93  thf('37', plain,
% 0.70/0.93      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.70/0.93        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.70/0.93        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.70/0.93        | ~ (v1_funct_1 @ sk_D))),
% 0.70/0.93      inference('sup-', [status(thm)], ['30', '36'])).
% 0.70/0.93  thf('38', plain,
% 0.70/0.93      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf(redefinition_k2_relset_1, axiom,
% 0.70/0.93    (![A:$i,B:$i,C:$i]:
% 0.70/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.70/0.93       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.70/0.93  thf('39', plain,
% 0.70/0.93      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.70/0.93         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.70/0.93          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.70/0.93      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.70/0.93  thf('40', plain,
% 0.70/0.93      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.70/0.93      inference('sup-', [status(thm)], ['38', '39'])).
% 0.70/0.93  thf('41', plain,
% 0.70/0.93      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf('42', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf('43', plain, ((v1_funct_1 @ sk_D)),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf('44', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.70/0.93      inference('demod', [status(thm)], ['37', '40', '41', '42', '43'])).
% 0.70/0.93  thf('45', plain,
% 0.70/0.93      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf(cc2_relat_1, axiom,
% 0.70/0.93    (![A:$i]:
% 0.70/0.93     ( ( v1_relat_1 @ A ) =>
% 0.70/0.93       ( ![B:$i]:
% 0.70/0.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.70/0.93  thf('46', plain,
% 0.70/0.93      (![X0 : $i, X1 : $i]:
% 0.70/0.93         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.70/0.93          | (v1_relat_1 @ X0)
% 0.70/0.93          | ~ (v1_relat_1 @ X1))),
% 0.70/0.93      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.70/0.93  thf('47', plain,
% 0.70/0.93      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.70/0.93      inference('sup-', [status(thm)], ['45', '46'])).
% 0.70/0.93  thf(fc6_relat_1, axiom,
% 0.70/0.93    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.70/0.93  thf('48', plain,
% 0.70/0.93      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.70/0.93      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.70/0.93  thf('49', plain, ((v1_relat_1 @ sk_D)),
% 0.70/0.93      inference('demod', [status(thm)], ['47', '48'])).
% 0.70/0.93  thf('50', plain, ((v1_funct_1 @ sk_D)),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf('51', plain,
% 0.70/0.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf('52', plain,
% 0.70/0.93      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.70/0.93         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.70/0.93          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.70/0.93      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.70/0.93  thf('53', plain,
% 0.70/0.93      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.70/0.93      inference('sup-', [status(thm)], ['51', '52'])).
% 0.70/0.93  thf('54', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf('55', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.70/0.93      inference('sup+', [status(thm)], ['53', '54'])).
% 0.70/0.93  thf('56', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf(d1_funct_2, axiom,
% 0.70/0.93    (![A:$i,B:$i,C:$i]:
% 0.70/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.70/0.93       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.70/0.93           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.70/0.93             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.70/0.93         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.70/0.93           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.70/0.93             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.70/0.93  thf(zf_stmt_1, axiom,
% 0.70/0.93    (![C:$i,B:$i,A:$i]:
% 0.70/0.93     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.70/0.93       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.70/0.93  thf('57', plain,
% 0.70/0.93      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.70/0.93         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 0.70/0.93          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 0.70/0.93          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.70/0.93  thf('58', plain,
% 0.70/0.93      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 0.70/0.93        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 0.70/0.93      inference('sup-', [status(thm)], ['56', '57'])).
% 0.70/0.93  thf(zf_stmt_2, axiom,
% 0.70/0.93    (![B:$i,A:$i]:
% 0.70/0.93     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.70/0.93       ( zip_tseitin_0 @ B @ A ) ))).
% 0.70/0.93  thf('59', plain,
% 0.70/0.93      (![X21 : $i, X22 : $i]:
% 0.70/0.93         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.70/0.93  thf('60', plain,
% 0.70/0.93      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.70/0.93  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.70/0.93  thf(zf_stmt_5, axiom,
% 0.70/0.93    (![A:$i,B:$i,C:$i]:
% 0.70/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.70/0.93       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.70/0.93         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.70/0.93           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.70/0.93             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.70/0.93  thf('61', plain,
% 0.70/0.93      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.70/0.93         (~ (zip_tseitin_0 @ X26 @ X27)
% 0.70/0.93          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 0.70/0.93          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.70/0.93  thf('62', plain,
% 0.70/0.93      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 0.70/0.93      inference('sup-', [status(thm)], ['60', '61'])).
% 0.70/0.93  thf('63', plain,
% 0.70/0.93      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 0.70/0.93      inference('sup-', [status(thm)], ['59', '62'])).
% 0.70/0.93  thf('64', plain, (((sk_A) != (k1_xboole_0))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf('65', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 0.70/0.93      inference('simplify_reflect-', [status(thm)], ['63', '64'])).
% 0.70/0.93  thf('66', plain,
% 0.70/0.93      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf(redefinition_k1_relset_1, axiom,
% 0.70/0.93    (![A:$i,B:$i,C:$i]:
% 0.70/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.70/0.93       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.70/0.93  thf('67', plain,
% 0.70/0.93      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.70/0.93         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 0.70/0.93          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.70/0.93      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.70/0.93  thf('68', plain,
% 0.70/0.93      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.70/0.93      inference('sup-', [status(thm)], ['66', '67'])).
% 0.70/0.93  thf('69', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.70/0.93      inference('demod', [status(thm)], ['58', '65', '68'])).
% 0.70/0.93  thf('70', plain, ((v1_funct_1 @ sk_C)),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf('71', plain,
% 0.70/0.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf('72', plain,
% 0.70/0.93      (![X0 : $i, X1 : $i]:
% 0.70/0.93         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.70/0.93          | (v1_relat_1 @ X0)
% 0.70/0.93          | ~ (v1_relat_1 @ X1))),
% 0.70/0.93      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.70/0.93  thf('73', plain,
% 0.70/0.93      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.70/0.93      inference('sup-', [status(thm)], ['71', '72'])).
% 0.70/0.93  thf('74', plain,
% 0.70/0.93      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.70/0.93      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.70/0.93  thf('75', plain, ((v1_relat_1 @ sk_C)),
% 0.70/0.93      inference('demod', [status(thm)], ['73', '74'])).
% 0.70/0.93  thf('76', plain,
% 0.70/0.93      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 0.70/0.93        | ~ (v2_funct_1 @ sk_D)
% 0.70/0.93        | ((sk_B) != (sk_B))
% 0.70/0.93        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 0.70/0.93      inference('demod', [status(thm)],
% 0.70/0.93                ['29', '44', '49', '50', '55', '69', '70', '75'])).
% 0.70/0.93  thf('77', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 0.70/0.93      inference('simplify', [status(thm)], ['76'])).
% 0.70/0.93  thf('78', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.70/0.93      inference('demod', [status(thm)], ['23', '24'])).
% 0.70/0.93  thf(t48_funct_1, axiom,
% 0.70/0.93    (![A:$i]:
% 0.70/0.93     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.70/0.93       ( ![B:$i]:
% 0.70/0.93         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.70/0.93           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.70/0.93               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.70/0.93             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.70/0.93  thf('79', plain,
% 0.70/0.93      (![X6 : $i, X7 : $i]:
% 0.70/0.93         (~ (v1_relat_1 @ X6)
% 0.70/0.93          | ~ (v1_funct_1 @ X6)
% 0.70/0.93          | (v2_funct_1 @ X7)
% 0.70/0.93          | ((k2_relat_1 @ X6) != (k1_relat_1 @ X7))
% 0.70/0.93          | ~ (v2_funct_1 @ (k5_relat_1 @ X6 @ X7))
% 0.70/0.93          | ~ (v1_funct_1 @ X7)
% 0.70/0.93          | ~ (v1_relat_1 @ X7))),
% 0.70/0.93      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.70/0.93  thf('80', plain,
% 0.70/0.93      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.70/0.93        | ~ (v1_relat_1 @ sk_D)
% 0.70/0.93        | ~ (v1_funct_1 @ sk_D)
% 0.70/0.93        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.70/0.93        | (v2_funct_1 @ sk_D)
% 0.70/0.93        | ~ (v1_funct_1 @ sk_C)
% 0.70/0.93        | ~ (v1_relat_1 @ sk_C))),
% 0.70/0.93      inference('sup-', [status(thm)], ['78', '79'])).
% 0.70/0.93  thf(fc4_funct_1, axiom,
% 0.70/0.93    (![A:$i]:
% 0.70/0.93     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.70/0.93       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.70/0.93  thf('81', plain, (![X5 : $i]: (v2_funct_1 @ (k6_relat_1 @ X5))),
% 0.70/0.93      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.70/0.93  thf('82', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 0.70/0.93      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.70/0.93  thf('83', plain, (![X5 : $i]: (v2_funct_1 @ (k6_partfun1 @ X5))),
% 0.70/0.93      inference('demod', [status(thm)], ['81', '82'])).
% 0.70/0.93  thf('84', plain, ((v1_relat_1 @ sk_D)),
% 0.70/0.93      inference('demod', [status(thm)], ['47', '48'])).
% 0.70/0.93  thf('85', plain, ((v1_funct_1 @ sk_D)),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf('86', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.70/0.93      inference('sup+', [status(thm)], ['53', '54'])).
% 0.70/0.93  thf('87', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.70/0.93      inference('demod', [status(thm)], ['58', '65', '68'])).
% 0.70/0.93  thf('88', plain, ((v1_funct_1 @ sk_C)),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf('89', plain, ((v1_relat_1 @ sk_C)),
% 0.70/0.93      inference('demod', [status(thm)], ['73', '74'])).
% 0.70/0.93  thf('90', plain, ((((sk_B) != (sk_B)) | (v2_funct_1 @ sk_D))),
% 0.70/0.93      inference('demod', [status(thm)],
% 0.70/0.93                ['80', '83', '84', '85', '86', '87', '88', '89'])).
% 0.70/0.93  thf('91', plain, ((v2_funct_1 @ sk_D)),
% 0.70/0.93      inference('simplify', [status(thm)], ['90'])).
% 0.70/0.93  thf('92', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.70/0.93      inference('demod', [status(thm)], ['77', '91'])).
% 0.70/0.93  thf(t61_funct_1, axiom,
% 0.70/0.93    (![A:$i]:
% 0.70/0.93     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.70/0.93       ( ( v2_funct_1 @ A ) =>
% 0.70/0.93         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.70/0.93             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.70/0.93           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.70/0.93             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.70/0.93  thf('93', plain,
% 0.70/0.93      (![X8 : $i]:
% 0.70/0.93         (~ (v2_funct_1 @ X8)
% 0.70/0.93          | ((k5_relat_1 @ X8 @ (k2_funct_1 @ X8))
% 0.70/0.93              = (k6_relat_1 @ (k1_relat_1 @ X8)))
% 0.70/0.93          | ~ (v1_funct_1 @ X8)
% 0.70/0.93          | ~ (v1_relat_1 @ X8))),
% 0.70/0.93      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.70/0.93  thf('94', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 0.70/0.93      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.70/0.93  thf('95', plain,
% 0.70/0.93      (![X8 : $i]:
% 0.70/0.93         (~ (v2_funct_1 @ X8)
% 0.70/0.93          | ((k5_relat_1 @ X8 @ (k2_funct_1 @ X8))
% 0.70/0.93              = (k6_partfun1 @ (k1_relat_1 @ X8)))
% 0.70/0.93          | ~ (v1_funct_1 @ X8)
% 0.70/0.93          | ~ (v1_relat_1 @ X8))),
% 0.70/0.93      inference('demod', [status(thm)], ['93', '94'])).
% 0.70/0.93  thf('96', plain,
% 0.70/0.93      (![X9 : $i, X10 : $i]:
% 0.70/0.93         (~ (v1_relat_1 @ X9)
% 0.70/0.93          | ~ (v1_funct_1 @ X9)
% 0.70/0.93          | ((X9) = (k2_funct_1 @ X10))
% 0.70/0.93          | ((k5_relat_1 @ X9 @ X10) != (k6_partfun1 @ (k2_relat_1 @ X10)))
% 0.70/0.93          | ((k2_relat_1 @ X9) != (k1_relat_1 @ X10))
% 0.70/0.93          | ~ (v2_funct_1 @ X10)
% 0.70/0.93          | ~ (v1_funct_1 @ X10)
% 0.70/0.93          | ~ (v1_relat_1 @ X10))),
% 0.70/0.93      inference('demod', [status(thm)], ['26', '27'])).
% 0.70/0.93  thf('97', plain,
% 0.70/0.93      (![X0 : $i]:
% 0.70/0.93         (((k6_partfun1 @ (k1_relat_1 @ X0))
% 0.70/0.93            != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.70/0.93          | ~ (v1_relat_1 @ X0)
% 0.70/0.93          | ~ (v1_funct_1 @ X0)
% 0.70/0.93          | ~ (v2_funct_1 @ X0)
% 0.70/0.93          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.70/0.93          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.70/0.93          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.70/0.93          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.70/0.93          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.70/0.93          | ~ (v1_funct_1 @ X0)
% 0.70/0.93          | ~ (v1_relat_1 @ X0))),
% 0.70/0.93      inference('sup-', [status(thm)], ['95', '96'])).
% 0.70/0.93  thf('98', plain,
% 0.70/0.93      (![X0 : $i]:
% 0.70/0.93         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.70/0.93          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.70/0.93          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.70/0.93          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.70/0.93          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.70/0.93          | ~ (v2_funct_1 @ X0)
% 0.70/0.93          | ~ (v1_funct_1 @ X0)
% 0.70/0.93          | ~ (v1_relat_1 @ X0)
% 0.70/0.93          | ((k6_partfun1 @ (k1_relat_1 @ X0))
% 0.70/0.93              != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.70/0.93      inference('simplify', [status(thm)], ['97'])).
% 0.70/0.93  thf('99', plain,
% 0.70/0.93      ((((k6_partfun1 @ (k1_relat_1 @ sk_D))
% 0.70/0.93          != (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 0.70/0.93        | ~ (v1_relat_1 @ sk_D)
% 0.70/0.93        | ~ (v1_funct_1 @ sk_D)
% 0.70/0.93        | ~ (v2_funct_1 @ sk_D)
% 0.70/0.93        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D))
% 0.70/0.93        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 0.70/0.93        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_D))
% 0.70/0.93        | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ (k2_funct_1 @ sk_D)))
% 0.70/0.93        | ((sk_D) = (k2_funct_1 @ (k2_funct_1 @ sk_D))))),
% 0.70/0.93      inference('sup-', [status(thm)], ['92', '98'])).
% 0.70/0.93  thf('100', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.70/0.93      inference('demod', [status(thm)], ['58', '65', '68'])).
% 0.70/0.93  thf('101', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.70/0.93      inference('sup+', [status(thm)], ['53', '54'])).
% 0.70/0.93  thf('102', plain, ((v1_relat_1 @ sk_D)),
% 0.70/0.93      inference('demod', [status(thm)], ['47', '48'])).
% 0.70/0.93  thf('103', plain, ((v1_funct_1 @ sk_D)),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf('104', plain, ((v2_funct_1 @ sk_D)),
% 0.70/0.93      inference('simplify', [status(thm)], ['90'])).
% 0.70/0.93  thf('105', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.70/0.93      inference('demod', [status(thm)], ['77', '91'])).
% 0.70/0.93  thf('106', plain, ((v1_relat_1 @ sk_C)),
% 0.70/0.93      inference('demod', [status(thm)], ['73', '74'])).
% 0.70/0.93  thf('107', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.70/0.93      inference('demod', [status(thm)], ['77', '91'])).
% 0.70/0.93  thf('108', plain, ((v1_funct_1 @ sk_C)),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf('109', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.70/0.93      inference('demod', [status(thm)], ['77', '91'])).
% 0.70/0.93  thf('110', plain, ((v2_funct_1 @ sk_C)),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf('111', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.70/0.93      inference('demod', [status(thm)], ['37', '40', '41', '42', '43'])).
% 0.70/0.93  thf('112', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.70/0.93      inference('demod', [status(thm)], ['77', '91'])).
% 0.70/0.93  thf('113', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf('114', plain,
% 0.70/0.93      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.70/0.93         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 0.70/0.93          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 0.70/0.93          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.70/0.93  thf('115', plain,
% 0.70/0.93      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.70/0.93        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.70/0.93      inference('sup-', [status(thm)], ['113', '114'])).
% 0.70/0.93  thf('116', plain,
% 0.70/0.93      (![X21 : $i, X22 : $i]:
% 0.70/0.93         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.70/0.93  thf('117', plain,
% 0.70/0.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf('118', plain,
% 0.70/0.93      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.70/0.93         (~ (zip_tseitin_0 @ X26 @ X27)
% 0.70/0.93          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 0.70/0.93          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.70/0.93  thf('119', plain,
% 0.70/0.93      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.70/0.93      inference('sup-', [status(thm)], ['117', '118'])).
% 0.70/0.93  thf('120', plain,
% 0.70/0.93      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.70/0.93      inference('sup-', [status(thm)], ['116', '119'])).
% 0.70/0.93  thf('121', plain, (((sk_B) != (k1_xboole_0))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf('122', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.70/0.93      inference('simplify_reflect-', [status(thm)], ['120', '121'])).
% 0.70/0.93  thf('123', plain,
% 0.70/0.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf('124', plain,
% 0.70/0.93      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.70/0.93         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 0.70/0.93          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.70/0.93      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.70/0.93  thf('125', plain,
% 0.70/0.93      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.70/0.93      inference('sup-', [status(thm)], ['123', '124'])).
% 0.70/0.93  thf('126', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.70/0.93      inference('demod', [status(thm)], ['115', '122', '125'])).
% 0.70/0.93  thf('127', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.70/0.93      inference('demod', [status(thm)], ['77', '91'])).
% 0.70/0.93  thf('128', plain,
% 0.70/0.93      ((((k6_partfun1 @ sk_B) != (k6_partfun1 @ sk_B))
% 0.70/0.93        | ((sk_A) != (sk_A))
% 0.70/0.93        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 0.70/0.93      inference('demod', [status(thm)],
% 0.70/0.93                ['99', '100', '101', '102', '103', '104', '105', '106', '107', 
% 0.70/0.93                 '108', '109', '110', '111', '112', '126', '127'])).
% 0.70/0.93  thf('129', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 0.70/0.93      inference('simplify', [status(thm)], ['128'])).
% 0.70/0.93  thf('130', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.70/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.93  thf('131', plain, ($false),
% 0.70/0.93      inference('simplify_reflect-', [status(thm)], ['129', '130'])).
% 0.70/0.93  
% 0.70/0.93  % SZS output end Refutation
% 0.70/0.93  
% 0.79/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

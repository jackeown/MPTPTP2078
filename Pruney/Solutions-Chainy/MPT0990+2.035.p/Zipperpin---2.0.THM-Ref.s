%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sDnujrcFW1

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:59 EST 2020

% Result     : Theorem 0.99s
% Output     : Refutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :  174 (2032 expanded)
%              Number of leaves         :   45 ( 617 expanded)
%              Depth                    :   18
%              Number of atoms          : 1636 (54294 expanded)
%              Number of equality atoms :  119 (3740 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( ( k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39 )
        = ( k5_relat_1 @ X36 @ X39 ) ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X33 ) ) ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( X16 = X19 )
      | ~ ( r2_relset_1 @ X17 @ X18 @ X16 @ X19 ) ) ),
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
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ( X5
        = ( k2_funct_1 @ X6 ) )
      | ( ( k5_relat_1 @ X5 @ X6 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X6 ) ) )
      | ( ( k2_relat_1 @ X5 )
       != ( k1_relat_1 @ X6 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('27',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ( X5
        = ( k2_funct_1 @ X6 ) )
      | ( ( k5_relat_1 @ X5 @ X6 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X6 ) ) )
      | ( ( k2_relat_1 @ X5 )
       != ( k1_relat_1 @ X6 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
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

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('46',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('47',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('51',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
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

thf('55',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ( X22
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('56',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('57',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('58',plain,(
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

thf('59',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('60',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('65',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('66',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['56','63','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('71',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B != sk_B )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['29','44','47','48','53','67','68','71'])).

thf('73',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
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

thf('75',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v2_funct_1 @ X3 )
      | ( ( k2_relat_1 @ X2 )
       != ( k1_relat_1 @ X3 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X2 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('76',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('77',plain,(
    ! [X1: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('78',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('79',plain,(
    ! [X1: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X1 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['45','46'])).

thf('81',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['51','52'])).

thf('83',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['56','63','66'])).

thf('84',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['69','70'])).

thf('86',plain,
    ( ( sk_B != sk_B )
    | ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['76','79','80','81','82','83','84','85'])).

thf('87',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['73','87'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('89',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ X4 @ ( k2_funct_1 @ X4 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('90',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('91',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ X4 @ ( k2_funct_1 @ X4 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ( X5
        = ( k2_funct_1 @ X6 ) )
      | ( ( k5_relat_1 @ X5 @ X6 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X6 ) ) )
      | ( ( k2_relat_1 @ X5 )
       != ( k1_relat_1 @ X6 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('93',plain,(
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
      | ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,
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
    inference('sup-',[status(thm)],['88','94'])).

thf('96',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['56','63','66'])).

thf('97',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['51','52'])).

thf('98',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['45','46'])).

thf('99',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['86'])).

thf('101',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['73','87'])).

thf('102',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['69','70'])).

thf('103',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['73','87'])).

thf('104',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['73','87'])).

thf('106',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['37','40','41','42','43'])).

thf('108',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['73','87'])).

thf('109',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ( X22
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('111',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('113',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
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
    inference(demod,[status(thm)],['73','87'])).

thf('124',plain,
    ( ( ( k6_partfun1 @ sk_B )
     != ( k6_partfun1 @ sk_B ) )
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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sDnujrcFW1
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:53:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.99/1.16  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.99/1.16  % Solved by: fo/fo7.sh
% 0.99/1.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.99/1.16  % done 419 iterations in 0.696s
% 0.99/1.16  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.99/1.16  % SZS output start Refutation
% 0.99/1.16  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.99/1.16  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.99/1.16  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.99/1.16  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.99/1.16  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.99/1.16  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.99/1.16  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.99/1.16  thf(sk_B_type, type, sk_B: $i).
% 0.99/1.16  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.99/1.16  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.99/1.16  thf(sk_A_type, type, sk_A: $i).
% 0.99/1.16  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.99/1.16  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.99/1.16  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.99/1.16  thf(sk_C_type, type, sk_C: $i).
% 0.99/1.16  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.99/1.16  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.99/1.16  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.99/1.16  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.99/1.16  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.99/1.16  thf(sk_D_type, type, sk_D: $i).
% 0.99/1.16  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.99/1.16  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.99/1.16  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.99/1.16  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.99/1.16  thf(t36_funct_2, conjecture,
% 0.99/1.16    (![A:$i,B:$i,C:$i]:
% 0.99/1.16     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.99/1.16         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.99/1.16       ( ![D:$i]:
% 0.99/1.16         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.99/1.16             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.99/1.16           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.99/1.16               ( r2_relset_1 @
% 0.99/1.16                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.99/1.16                 ( k6_partfun1 @ A ) ) & 
% 0.99/1.16               ( v2_funct_1 @ C ) ) =>
% 0.99/1.16             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.99/1.16               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.99/1.16  thf(zf_stmt_0, negated_conjecture,
% 0.99/1.16    (~( ![A:$i,B:$i,C:$i]:
% 0.99/1.16        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.99/1.16            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.99/1.16          ( ![D:$i]:
% 0.99/1.16            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.99/1.16                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.99/1.16              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.99/1.16                  ( r2_relset_1 @
% 0.99/1.16                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.99/1.16                    ( k6_partfun1 @ A ) ) & 
% 0.99/1.16                  ( v2_funct_1 @ C ) ) =>
% 0.99/1.16                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.99/1.16                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.99/1.16    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.99/1.16  thf('0', plain,
% 0.99/1.16      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.99/1.16        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.99/1.16        (k6_partfun1 @ sk_A))),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf('1', plain,
% 0.99/1.16      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf('2', plain,
% 0.99/1.16      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf(redefinition_k1_partfun1, axiom,
% 0.99/1.16    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.99/1.16     ( ( ( v1_funct_1 @ E ) & 
% 0.99/1.16         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.99/1.16         ( v1_funct_1 @ F ) & 
% 0.99/1.16         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.99/1.16       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.99/1.16  thf('3', plain,
% 0.99/1.16      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.99/1.16         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.99/1.16          | ~ (v1_funct_1 @ X36)
% 0.99/1.16          | ~ (v1_funct_1 @ X39)
% 0.99/1.16          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.99/1.16          | ((k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39)
% 0.99/1.16              = (k5_relat_1 @ X36 @ X39)))),
% 0.99/1.16      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.99/1.16  thf('4', plain,
% 0.99/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.16         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.99/1.16            = (k5_relat_1 @ sk_C @ X0))
% 0.99/1.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.99/1.16          | ~ (v1_funct_1 @ X0)
% 0.99/1.16          | ~ (v1_funct_1 @ sk_C))),
% 0.99/1.16      inference('sup-', [status(thm)], ['2', '3'])).
% 0.99/1.16  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf('6', plain,
% 0.99/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.16         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.99/1.16            = (k5_relat_1 @ sk_C @ X0))
% 0.99/1.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.99/1.16          | ~ (v1_funct_1 @ X0))),
% 0.99/1.16      inference('demod', [status(thm)], ['4', '5'])).
% 0.99/1.16  thf('7', plain,
% 0.99/1.16      ((~ (v1_funct_1 @ sk_D)
% 0.99/1.16        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.99/1.16            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.99/1.16      inference('sup-', [status(thm)], ['1', '6'])).
% 0.99/1.16  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf('9', plain,
% 0.99/1.16      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.99/1.16         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.99/1.16      inference('demod', [status(thm)], ['7', '8'])).
% 0.99/1.16  thf('10', plain,
% 0.99/1.16      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.99/1.16        (k6_partfun1 @ sk_A))),
% 0.99/1.16      inference('demod', [status(thm)], ['0', '9'])).
% 0.99/1.16  thf('11', plain,
% 0.99/1.16      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf('12', plain,
% 0.99/1.16      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf(dt_k1_partfun1, axiom,
% 0.99/1.16    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.99/1.16     ( ( ( v1_funct_1 @ E ) & 
% 0.99/1.16         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.99/1.16         ( v1_funct_1 @ F ) & 
% 0.99/1.16         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.99/1.16       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.99/1.16         ( m1_subset_1 @
% 0.99/1.16           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.99/1.16           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.99/1.16  thf('13', plain,
% 0.99/1.16      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.99/1.16         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.99/1.16          | ~ (v1_funct_1 @ X28)
% 0.99/1.16          | ~ (v1_funct_1 @ X31)
% 0.99/1.16          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.99/1.16          | (m1_subset_1 @ (k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31) @ 
% 0.99/1.16             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X33))))),
% 0.99/1.16      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.99/1.16  thf('14', plain,
% 0.99/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.16         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.99/1.16           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.99/1.16          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.99/1.16          | ~ (v1_funct_1 @ X1)
% 0.99/1.16          | ~ (v1_funct_1 @ sk_C))),
% 0.99/1.16      inference('sup-', [status(thm)], ['12', '13'])).
% 0.99/1.16  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf('16', plain,
% 0.99/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.16         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.99/1.16           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.99/1.16          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.99/1.16          | ~ (v1_funct_1 @ X1))),
% 0.99/1.16      inference('demod', [status(thm)], ['14', '15'])).
% 0.99/1.16  thf('17', plain,
% 0.99/1.16      ((~ (v1_funct_1 @ sk_D)
% 0.99/1.16        | (m1_subset_1 @ 
% 0.99/1.16           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.99/1.16           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.99/1.16      inference('sup-', [status(thm)], ['11', '16'])).
% 0.99/1.16  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf('19', plain,
% 0.99/1.16      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.99/1.16         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.99/1.16      inference('demod', [status(thm)], ['7', '8'])).
% 0.99/1.16  thf('20', plain,
% 0.99/1.16      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.99/1.16        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.99/1.16      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.99/1.16  thf(redefinition_r2_relset_1, axiom,
% 0.99/1.16    (![A:$i,B:$i,C:$i,D:$i]:
% 0.99/1.16     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.99/1.16         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.99/1.16       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.99/1.16  thf('21', plain,
% 0.99/1.16      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.99/1.16         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.99/1.16          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.99/1.16          | ((X16) = (X19))
% 0.99/1.16          | ~ (r2_relset_1 @ X17 @ X18 @ X16 @ X19))),
% 0.99/1.16      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.99/1.16  thf('22', plain,
% 0.99/1.16      (![X0 : $i]:
% 0.99/1.16         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 0.99/1.16          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 0.99/1.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.99/1.16      inference('sup-', [status(thm)], ['20', '21'])).
% 0.99/1.16  thf('23', plain,
% 0.99/1.16      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.99/1.16           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.99/1.16        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 0.99/1.16      inference('sup-', [status(thm)], ['10', '22'])).
% 0.99/1.16  thf(dt_k6_partfun1, axiom,
% 0.99/1.16    (![A:$i]:
% 0.99/1.16     ( ( m1_subset_1 @
% 0.99/1.16         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.99/1.16       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.99/1.16  thf('24', plain,
% 0.99/1.16      (![X35 : $i]:
% 0.99/1.16         (m1_subset_1 @ (k6_partfun1 @ X35) @ 
% 0.99/1.16          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 0.99/1.16      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.99/1.16  thf('25', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.99/1.16      inference('demod', [status(thm)], ['23', '24'])).
% 0.99/1.16  thf(t64_funct_1, axiom,
% 0.99/1.16    (![A:$i]:
% 0.99/1.16     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.99/1.16       ( ![B:$i]:
% 0.99/1.16         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.99/1.16           ( ( ( v2_funct_1 @ A ) & 
% 0.99/1.16               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.99/1.16               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.99/1.16             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.99/1.16  thf('26', plain,
% 0.99/1.16      (![X5 : $i, X6 : $i]:
% 0.99/1.16         (~ (v1_relat_1 @ X5)
% 0.99/1.16          | ~ (v1_funct_1 @ X5)
% 0.99/1.16          | ((X5) = (k2_funct_1 @ X6))
% 0.99/1.16          | ((k5_relat_1 @ X5 @ X6) != (k6_relat_1 @ (k2_relat_1 @ X6)))
% 0.99/1.16          | ((k2_relat_1 @ X5) != (k1_relat_1 @ X6))
% 0.99/1.16          | ~ (v2_funct_1 @ X6)
% 0.99/1.16          | ~ (v1_funct_1 @ X6)
% 0.99/1.16          | ~ (v1_relat_1 @ X6))),
% 0.99/1.16      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.99/1.16  thf(redefinition_k6_partfun1, axiom,
% 0.99/1.16    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.99/1.16  thf('27', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 0.99/1.16      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.99/1.16  thf('28', plain,
% 0.99/1.16      (![X5 : $i, X6 : $i]:
% 0.99/1.16         (~ (v1_relat_1 @ X5)
% 0.99/1.16          | ~ (v1_funct_1 @ X5)
% 0.99/1.16          | ((X5) = (k2_funct_1 @ X6))
% 0.99/1.16          | ((k5_relat_1 @ X5 @ X6) != (k6_partfun1 @ (k2_relat_1 @ X6)))
% 0.99/1.16          | ((k2_relat_1 @ X5) != (k1_relat_1 @ X6))
% 0.99/1.16          | ~ (v2_funct_1 @ X6)
% 0.99/1.16          | ~ (v1_funct_1 @ X6)
% 0.99/1.16          | ~ (v1_relat_1 @ X6))),
% 0.99/1.16      inference('demod', [status(thm)], ['26', '27'])).
% 0.99/1.16  thf('29', plain,
% 0.99/1.16      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 0.99/1.16        | ~ (v1_relat_1 @ sk_D)
% 0.99/1.16        | ~ (v1_funct_1 @ sk_D)
% 0.99/1.16        | ~ (v2_funct_1 @ sk_D)
% 0.99/1.16        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.99/1.16        | ((sk_C) = (k2_funct_1 @ sk_D))
% 0.99/1.16        | ~ (v1_funct_1 @ sk_C)
% 0.99/1.16        | ~ (v1_relat_1 @ sk_C))),
% 0.99/1.16      inference('sup-', [status(thm)], ['25', '28'])).
% 0.99/1.16  thf('30', plain,
% 0.99/1.16      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.99/1.16        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.99/1.16        (k6_partfun1 @ sk_A))),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf('31', plain,
% 0.99/1.16      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf(t24_funct_2, axiom,
% 0.99/1.16    (![A:$i,B:$i,C:$i]:
% 0.99/1.16     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.99/1.16         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.99/1.16       ( ![D:$i]:
% 0.99/1.16         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.99/1.16             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.99/1.16           ( ( r2_relset_1 @
% 0.99/1.16               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.99/1.16               ( k6_partfun1 @ B ) ) =>
% 0.99/1.16             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.99/1.16  thf('32', plain,
% 0.99/1.16      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.99/1.16         (~ (v1_funct_1 @ X43)
% 0.99/1.16          | ~ (v1_funct_2 @ X43 @ X44 @ X45)
% 0.99/1.16          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 0.99/1.16          | ~ (r2_relset_1 @ X44 @ X44 @ 
% 0.99/1.16               (k1_partfun1 @ X44 @ X45 @ X45 @ X44 @ X43 @ X46) @ 
% 0.99/1.16               (k6_partfun1 @ X44))
% 0.99/1.16          | ((k2_relset_1 @ X45 @ X44 @ X46) = (X44))
% 0.99/1.16          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 0.99/1.16          | ~ (v1_funct_2 @ X46 @ X45 @ X44)
% 0.99/1.16          | ~ (v1_funct_1 @ X46))),
% 0.99/1.16      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.99/1.16  thf('33', plain,
% 0.99/1.16      (![X0 : $i]:
% 0.99/1.16         (~ (v1_funct_1 @ X0)
% 0.99/1.16          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.99/1.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.99/1.16          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.99/1.16          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.99/1.16               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.99/1.16               (k6_partfun1 @ sk_A))
% 0.99/1.16          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.99/1.16          | ~ (v1_funct_1 @ sk_C))),
% 0.99/1.16      inference('sup-', [status(thm)], ['31', '32'])).
% 0.99/1.16  thf('34', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf('36', plain,
% 0.99/1.16      (![X0 : $i]:
% 0.99/1.16         (~ (v1_funct_1 @ X0)
% 0.99/1.16          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.99/1.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.99/1.16          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.99/1.16          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.99/1.16               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.99/1.16               (k6_partfun1 @ sk_A)))),
% 0.99/1.16      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.99/1.16  thf('37', plain,
% 0.99/1.16      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.99/1.16        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.99/1.16        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.99/1.16        | ~ (v1_funct_1 @ sk_D))),
% 0.99/1.16      inference('sup-', [status(thm)], ['30', '36'])).
% 0.99/1.16  thf('38', plain,
% 0.99/1.16      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf(redefinition_k2_relset_1, axiom,
% 0.99/1.16    (![A:$i,B:$i,C:$i]:
% 0.99/1.16     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.99/1.16       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.99/1.16  thf('39', plain,
% 0.99/1.16      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.99/1.16         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 0.99/1.16          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.99/1.16      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.99/1.16  thf('40', plain,
% 0.99/1.16      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.99/1.16      inference('sup-', [status(thm)], ['38', '39'])).
% 0.99/1.16  thf('41', plain,
% 0.99/1.16      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf('42', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf('43', plain, ((v1_funct_1 @ sk_D)),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf('44', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.99/1.16      inference('demod', [status(thm)], ['37', '40', '41', '42', '43'])).
% 0.99/1.16  thf('45', plain,
% 0.99/1.16      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf(cc1_relset_1, axiom,
% 0.99/1.16    (![A:$i,B:$i,C:$i]:
% 0.99/1.16     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.99/1.16       ( v1_relat_1 @ C ) ))).
% 0.99/1.16  thf('46', plain,
% 0.99/1.16      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.99/1.16         ((v1_relat_1 @ X7)
% 0.99/1.16          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.99/1.16      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.99/1.16  thf('47', plain, ((v1_relat_1 @ sk_D)),
% 0.99/1.16      inference('sup-', [status(thm)], ['45', '46'])).
% 0.99/1.16  thf('48', plain, ((v1_funct_1 @ sk_D)),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf('49', plain,
% 0.99/1.16      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf('50', plain,
% 0.99/1.16      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.99/1.16         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 0.99/1.16          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.99/1.16      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.99/1.16  thf('51', plain,
% 0.99/1.16      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.99/1.16      inference('sup-', [status(thm)], ['49', '50'])).
% 0.99/1.16  thf('52', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf('53', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.99/1.16      inference('sup+', [status(thm)], ['51', '52'])).
% 0.99/1.16  thf('54', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf(d1_funct_2, axiom,
% 0.99/1.16    (![A:$i,B:$i,C:$i]:
% 0.99/1.16     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.99/1.16       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.99/1.16           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.99/1.16             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.99/1.16         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.99/1.16           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.99/1.16             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.99/1.16  thf(zf_stmt_1, axiom,
% 0.99/1.16    (![C:$i,B:$i,A:$i]:
% 0.99/1.16     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.99/1.16       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.99/1.16  thf('55', plain,
% 0.99/1.16      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.99/1.16         (~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.99/1.16          | ((X22) = (k1_relset_1 @ X22 @ X23 @ X24))
% 0.99/1.16          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.99/1.16  thf('56', plain,
% 0.99/1.16      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 0.99/1.16        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 0.99/1.16      inference('sup-', [status(thm)], ['54', '55'])).
% 0.99/1.16  thf(zf_stmt_2, axiom,
% 0.99/1.16    (![B:$i,A:$i]:
% 0.99/1.16     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.99/1.16       ( zip_tseitin_0 @ B @ A ) ))).
% 0.99/1.16  thf('57', plain,
% 0.99/1.16      (![X20 : $i, X21 : $i]:
% 0.99/1.16         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.99/1.16  thf('58', plain,
% 0.99/1.16      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.99/1.16  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.99/1.16  thf(zf_stmt_5, axiom,
% 0.99/1.16    (![A:$i,B:$i,C:$i]:
% 0.99/1.16     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.99/1.16       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.99/1.16         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.99/1.16           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.99/1.16             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.99/1.16  thf('59', plain,
% 0.99/1.16      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.99/1.16         (~ (zip_tseitin_0 @ X25 @ X26)
% 0.99/1.16          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 0.99/1.16          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.99/1.16  thf('60', plain,
% 0.99/1.16      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 0.99/1.16      inference('sup-', [status(thm)], ['58', '59'])).
% 0.99/1.16  thf('61', plain,
% 0.99/1.16      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 0.99/1.16      inference('sup-', [status(thm)], ['57', '60'])).
% 0.99/1.16  thf('62', plain, (((sk_A) != (k1_xboole_0))),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf('63', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 0.99/1.16      inference('simplify_reflect-', [status(thm)], ['61', '62'])).
% 0.99/1.16  thf('64', plain,
% 0.99/1.16      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf(redefinition_k1_relset_1, axiom,
% 0.99/1.16    (![A:$i,B:$i,C:$i]:
% 0.99/1.16     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.99/1.16       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.99/1.16  thf('65', plain,
% 0.99/1.16      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.99/1.16         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 0.99/1.16          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.99/1.16      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.99/1.16  thf('66', plain,
% 0.99/1.16      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.99/1.16      inference('sup-', [status(thm)], ['64', '65'])).
% 0.99/1.16  thf('67', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.99/1.16      inference('demod', [status(thm)], ['56', '63', '66'])).
% 0.99/1.16  thf('68', plain, ((v1_funct_1 @ sk_C)),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf('69', plain,
% 0.99/1.16      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf('70', plain,
% 0.99/1.16      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.99/1.16         ((v1_relat_1 @ X7)
% 0.99/1.16          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.99/1.16      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.99/1.16  thf('71', plain, ((v1_relat_1 @ sk_C)),
% 0.99/1.16      inference('sup-', [status(thm)], ['69', '70'])).
% 0.99/1.16  thf('72', plain,
% 0.99/1.16      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 0.99/1.16        | ~ (v2_funct_1 @ sk_D)
% 0.99/1.16        | ((sk_B) != (sk_B))
% 0.99/1.16        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 0.99/1.16      inference('demod', [status(thm)],
% 0.99/1.16                ['29', '44', '47', '48', '53', '67', '68', '71'])).
% 0.99/1.16  thf('73', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 0.99/1.16      inference('simplify', [status(thm)], ['72'])).
% 0.99/1.16  thf('74', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.99/1.16      inference('demod', [status(thm)], ['23', '24'])).
% 0.99/1.16  thf(t48_funct_1, axiom,
% 0.99/1.16    (![A:$i]:
% 0.99/1.16     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.99/1.16       ( ![B:$i]:
% 0.99/1.16         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.99/1.16           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.99/1.16               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.99/1.16             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.99/1.16  thf('75', plain,
% 0.99/1.16      (![X2 : $i, X3 : $i]:
% 0.99/1.16         (~ (v1_relat_1 @ X2)
% 0.99/1.16          | ~ (v1_funct_1 @ X2)
% 0.99/1.16          | (v2_funct_1 @ X3)
% 0.99/1.16          | ((k2_relat_1 @ X2) != (k1_relat_1 @ X3))
% 0.99/1.16          | ~ (v2_funct_1 @ (k5_relat_1 @ X2 @ X3))
% 0.99/1.16          | ~ (v1_funct_1 @ X3)
% 0.99/1.16          | ~ (v1_relat_1 @ X3))),
% 0.99/1.16      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.99/1.16  thf('76', plain,
% 0.99/1.16      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.99/1.16        | ~ (v1_relat_1 @ sk_D)
% 0.99/1.16        | ~ (v1_funct_1 @ sk_D)
% 0.99/1.16        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.99/1.16        | (v2_funct_1 @ sk_D)
% 0.99/1.16        | ~ (v1_funct_1 @ sk_C)
% 0.99/1.16        | ~ (v1_relat_1 @ sk_C))),
% 0.99/1.16      inference('sup-', [status(thm)], ['74', '75'])).
% 0.99/1.16  thf(fc4_funct_1, axiom,
% 0.99/1.16    (![A:$i]:
% 0.99/1.16     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.99/1.16       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.99/1.16  thf('77', plain, (![X1 : $i]: (v2_funct_1 @ (k6_relat_1 @ X1))),
% 0.99/1.16      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.99/1.16  thf('78', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 0.99/1.16      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.99/1.16  thf('79', plain, (![X1 : $i]: (v2_funct_1 @ (k6_partfun1 @ X1))),
% 0.99/1.16      inference('demod', [status(thm)], ['77', '78'])).
% 0.99/1.16  thf('80', plain, ((v1_relat_1 @ sk_D)),
% 0.99/1.16      inference('sup-', [status(thm)], ['45', '46'])).
% 0.99/1.16  thf('81', plain, ((v1_funct_1 @ sk_D)),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf('82', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.99/1.16      inference('sup+', [status(thm)], ['51', '52'])).
% 0.99/1.16  thf('83', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.99/1.16      inference('demod', [status(thm)], ['56', '63', '66'])).
% 0.99/1.16  thf('84', plain, ((v1_funct_1 @ sk_C)),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf('85', plain, ((v1_relat_1 @ sk_C)),
% 0.99/1.16      inference('sup-', [status(thm)], ['69', '70'])).
% 0.99/1.16  thf('86', plain, ((((sk_B) != (sk_B)) | (v2_funct_1 @ sk_D))),
% 0.99/1.16      inference('demod', [status(thm)],
% 0.99/1.16                ['76', '79', '80', '81', '82', '83', '84', '85'])).
% 0.99/1.16  thf('87', plain, ((v2_funct_1 @ sk_D)),
% 0.99/1.16      inference('simplify', [status(thm)], ['86'])).
% 0.99/1.16  thf('88', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.99/1.16      inference('demod', [status(thm)], ['73', '87'])).
% 0.99/1.16  thf(t61_funct_1, axiom,
% 0.99/1.16    (![A:$i]:
% 0.99/1.16     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.99/1.16       ( ( v2_funct_1 @ A ) =>
% 0.99/1.16         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.99/1.16             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.99/1.16           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.99/1.16             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.99/1.16  thf('89', plain,
% 0.99/1.16      (![X4 : $i]:
% 0.99/1.16         (~ (v2_funct_1 @ X4)
% 0.99/1.16          | ((k5_relat_1 @ X4 @ (k2_funct_1 @ X4))
% 0.99/1.16              = (k6_relat_1 @ (k1_relat_1 @ X4)))
% 0.99/1.16          | ~ (v1_funct_1 @ X4)
% 0.99/1.16          | ~ (v1_relat_1 @ X4))),
% 0.99/1.16      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.99/1.16  thf('90', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 0.99/1.16      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.99/1.16  thf('91', plain,
% 0.99/1.16      (![X4 : $i]:
% 0.99/1.16         (~ (v2_funct_1 @ X4)
% 0.99/1.16          | ((k5_relat_1 @ X4 @ (k2_funct_1 @ X4))
% 0.99/1.16              = (k6_partfun1 @ (k1_relat_1 @ X4)))
% 0.99/1.16          | ~ (v1_funct_1 @ X4)
% 0.99/1.16          | ~ (v1_relat_1 @ X4))),
% 0.99/1.16      inference('demod', [status(thm)], ['89', '90'])).
% 0.99/1.16  thf('92', plain,
% 0.99/1.16      (![X5 : $i, X6 : $i]:
% 0.99/1.16         (~ (v1_relat_1 @ X5)
% 0.99/1.16          | ~ (v1_funct_1 @ X5)
% 0.99/1.16          | ((X5) = (k2_funct_1 @ X6))
% 0.99/1.16          | ((k5_relat_1 @ X5 @ X6) != (k6_partfun1 @ (k2_relat_1 @ X6)))
% 0.99/1.16          | ((k2_relat_1 @ X5) != (k1_relat_1 @ X6))
% 0.99/1.16          | ~ (v2_funct_1 @ X6)
% 0.99/1.16          | ~ (v1_funct_1 @ X6)
% 0.99/1.16          | ~ (v1_relat_1 @ X6))),
% 0.99/1.16      inference('demod', [status(thm)], ['26', '27'])).
% 0.99/1.16  thf('93', plain,
% 0.99/1.16      (![X0 : $i]:
% 0.99/1.16         (((k6_partfun1 @ (k1_relat_1 @ X0))
% 0.99/1.16            != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.99/1.16          | ~ (v1_relat_1 @ X0)
% 0.99/1.16          | ~ (v1_funct_1 @ X0)
% 0.99/1.16          | ~ (v2_funct_1 @ X0)
% 0.99/1.16          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.99/1.16          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.99/1.16          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.99/1.16          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.99/1.16          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.99/1.16          | ~ (v1_funct_1 @ X0)
% 0.99/1.16          | ~ (v1_relat_1 @ X0))),
% 0.99/1.16      inference('sup-', [status(thm)], ['91', '92'])).
% 0.99/1.16  thf('94', plain,
% 0.99/1.16      (![X0 : $i]:
% 0.99/1.16         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.99/1.16          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.99/1.16          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.99/1.16          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.99/1.16          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.99/1.16          | ~ (v2_funct_1 @ X0)
% 0.99/1.16          | ~ (v1_funct_1 @ X0)
% 0.99/1.16          | ~ (v1_relat_1 @ X0)
% 0.99/1.16          | ((k6_partfun1 @ (k1_relat_1 @ X0))
% 0.99/1.16              != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.99/1.16      inference('simplify', [status(thm)], ['93'])).
% 0.99/1.16  thf('95', plain,
% 0.99/1.16      ((((k6_partfun1 @ (k1_relat_1 @ sk_D))
% 0.99/1.16          != (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 0.99/1.16        | ~ (v1_relat_1 @ sk_D)
% 0.99/1.16        | ~ (v1_funct_1 @ sk_D)
% 0.99/1.16        | ~ (v2_funct_1 @ sk_D)
% 0.99/1.16        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D))
% 0.99/1.16        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 0.99/1.16        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_D))
% 0.99/1.16        | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ (k2_funct_1 @ sk_D)))
% 0.99/1.16        | ((sk_D) = (k2_funct_1 @ (k2_funct_1 @ sk_D))))),
% 0.99/1.16      inference('sup-', [status(thm)], ['88', '94'])).
% 0.99/1.16  thf('96', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.99/1.16      inference('demod', [status(thm)], ['56', '63', '66'])).
% 0.99/1.16  thf('97', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.99/1.16      inference('sup+', [status(thm)], ['51', '52'])).
% 0.99/1.16  thf('98', plain, ((v1_relat_1 @ sk_D)),
% 0.99/1.16      inference('sup-', [status(thm)], ['45', '46'])).
% 0.99/1.16  thf('99', plain, ((v1_funct_1 @ sk_D)),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf('100', plain, ((v2_funct_1 @ sk_D)),
% 0.99/1.16      inference('simplify', [status(thm)], ['86'])).
% 0.99/1.16  thf('101', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.99/1.16      inference('demod', [status(thm)], ['73', '87'])).
% 0.99/1.16  thf('102', plain, ((v1_relat_1 @ sk_C)),
% 0.99/1.16      inference('sup-', [status(thm)], ['69', '70'])).
% 0.99/1.16  thf('103', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.99/1.16      inference('demod', [status(thm)], ['73', '87'])).
% 0.99/1.16  thf('104', plain, ((v1_funct_1 @ sk_C)),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf('105', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.99/1.16      inference('demod', [status(thm)], ['73', '87'])).
% 0.99/1.16  thf('106', plain, ((v2_funct_1 @ sk_C)),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf('107', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.99/1.16      inference('demod', [status(thm)], ['37', '40', '41', '42', '43'])).
% 0.99/1.16  thf('108', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.99/1.16      inference('demod', [status(thm)], ['73', '87'])).
% 0.99/1.16  thf('109', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf('110', plain,
% 0.99/1.16      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.99/1.16         (~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.99/1.16          | ((X22) = (k1_relset_1 @ X22 @ X23 @ X24))
% 0.99/1.16          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.99/1.16  thf('111', plain,
% 0.99/1.16      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.99/1.16        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.99/1.16      inference('sup-', [status(thm)], ['109', '110'])).
% 0.99/1.16  thf('112', plain,
% 0.99/1.16      (![X20 : $i, X21 : $i]:
% 0.99/1.16         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.99/1.16  thf('113', plain,
% 0.99/1.16      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf('114', plain,
% 0.99/1.16      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.99/1.16         (~ (zip_tseitin_0 @ X25 @ X26)
% 0.99/1.16          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 0.99/1.16          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.99/1.16  thf('115', plain,
% 0.99/1.16      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.99/1.16      inference('sup-', [status(thm)], ['113', '114'])).
% 0.99/1.16  thf('116', plain,
% 0.99/1.16      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.99/1.16      inference('sup-', [status(thm)], ['112', '115'])).
% 0.99/1.16  thf('117', plain, (((sk_B) != (k1_xboole_0))),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf('118', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.99/1.16      inference('simplify_reflect-', [status(thm)], ['116', '117'])).
% 0.99/1.16  thf('119', plain,
% 0.99/1.16      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf('120', plain,
% 0.99/1.16      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.99/1.16         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 0.99/1.16          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.99/1.16      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.99/1.16  thf('121', plain,
% 0.99/1.16      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.99/1.16      inference('sup-', [status(thm)], ['119', '120'])).
% 0.99/1.16  thf('122', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.99/1.16      inference('demod', [status(thm)], ['111', '118', '121'])).
% 0.99/1.16  thf('123', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.99/1.16      inference('demod', [status(thm)], ['73', '87'])).
% 0.99/1.16  thf('124', plain,
% 0.99/1.16      ((((k6_partfun1 @ sk_B) != (k6_partfun1 @ sk_B))
% 0.99/1.16        | ((sk_A) != (sk_A))
% 0.99/1.16        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 0.99/1.16      inference('demod', [status(thm)],
% 0.99/1.16                ['95', '96', '97', '98', '99', '100', '101', '102', '103', 
% 0.99/1.16                 '104', '105', '106', '107', '108', '122', '123'])).
% 0.99/1.16  thf('125', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 0.99/1.16      inference('simplify', [status(thm)], ['124'])).
% 0.99/1.16  thf('126', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf('127', plain, ($false),
% 0.99/1.16      inference('simplify_reflect-', [status(thm)], ['125', '126'])).
% 0.99/1.16  
% 0.99/1.16  % SZS output end Refutation
% 0.99/1.16  
% 0.99/1.17  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

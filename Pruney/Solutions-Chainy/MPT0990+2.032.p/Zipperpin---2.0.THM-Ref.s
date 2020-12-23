%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DXbZ3zjVbl

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:59 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 276 expanded)
%              Number of leaves         :   47 ( 102 expanded)
%              Depth                    :   13
%              Number of atoms          : 1511 (5970 expanded)
%              Number of equality atoms :  111 ( 440 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

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

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('26',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
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

thf('27',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X9 ) @ X9 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('28',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('29',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X9 ) @ X9 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['25','34'])).

thf('36',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X9 ) @ X9 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('37',plain,(
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

thf('38',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( X43 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ X45 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X43 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X44 ) @ X44 )
        = ( k6_partfun1 @ X43 ) )
      | ~ ( v2_funct_1 @ X44 )
      | ( ( k2_relset_1 @ X45 @ X43 @ X44 )
       != X43 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('39',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40','41','42','43'])).

thf('45',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['36','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('50',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['48','51','52','53'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('55',plain,(
    ! [X3: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X3 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('56',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('57',plain,(
    ! [X3: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X3 ) )
      = X3 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X3: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X3 ) )
      = X3 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('60',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
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

thf('62',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ( X22
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('63',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('64',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('65',plain,(
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

thf('66',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('67',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('72',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('73',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['63','70','73'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('75',plain,(
    ! [X5: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X5 ) ) @ X5 )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('76',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('77',plain,(
    ! [X5: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X5 ) ) @ X5 )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['74','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('81',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['78','81'])).

thf('83',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ( X22
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('85',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('87',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('89',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['90','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('95',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['85','92','95'])).

thf('97',plain,(
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

thf('98',plain,(
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

thf('99',plain,(
    ! [X6: $i] :
      ( ( ( k5_relat_1 @ X6 @ ( k6_relat_1 @ ( k2_relat_1 @ X6 ) ) )
        = X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('100',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('101',plain,(
    ! [X6: $i] :
      ( ( ( k5_relat_1 @ X6 @ ( k6_partfun1 @ ( k2_relat_1 @ X6 ) ) )
        = X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['98','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['97','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['96','104'])).

thf('106',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['49','50'])).

thf('107',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['105','106','107','108'])).

thf('110',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['49','50'])).

thf('111',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['79','80'])).

thf('114',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['35','60','82','109','110','111','112','113'])).

thf('115',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['114','115'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DXbZ3zjVbl
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:11:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.51/1.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.51/1.71  % Solved by: fo/fo7.sh
% 1.51/1.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.51/1.71  % done 461 iterations in 1.257s
% 1.51/1.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.51/1.71  % SZS output start Refutation
% 1.51/1.71  thf(sk_B_type, type, sk_B: $i).
% 1.51/1.71  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.51/1.71  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.51/1.71  thf(sk_A_type, type, sk_A: $i).
% 1.51/1.71  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.51/1.71  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.51/1.71  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.51/1.71  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.51/1.71  thf(sk_D_type, type, sk_D: $i).
% 1.51/1.71  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.51/1.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.51/1.71  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.51/1.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.51/1.71  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.51/1.71  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.51/1.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.51/1.71  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.51/1.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.51/1.71  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.51/1.71  thf(sk_C_type, type, sk_C: $i).
% 1.51/1.71  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.51/1.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.51/1.71  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.51/1.71  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.51/1.71  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.51/1.71  thf(t36_funct_2, conjecture,
% 1.51/1.71    (![A:$i,B:$i,C:$i]:
% 1.51/1.71     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.51/1.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.51/1.71       ( ![D:$i]:
% 1.51/1.71         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.51/1.71             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.51/1.71           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.51/1.71               ( r2_relset_1 @
% 1.51/1.71                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.51/1.72                 ( k6_partfun1 @ A ) ) & 
% 1.51/1.72               ( v2_funct_1 @ C ) ) =>
% 1.51/1.72             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.51/1.72               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.51/1.72  thf(zf_stmt_0, negated_conjecture,
% 1.51/1.72    (~( ![A:$i,B:$i,C:$i]:
% 1.51/1.72        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.51/1.72            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.51/1.72          ( ![D:$i]:
% 1.51/1.72            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.51/1.72                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.51/1.72              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.51/1.72                  ( r2_relset_1 @
% 1.51/1.72                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.51/1.72                    ( k6_partfun1 @ A ) ) & 
% 1.51/1.72                  ( v2_funct_1 @ C ) ) =>
% 1.51/1.72                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.51/1.72                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.51/1.72    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.51/1.72  thf('0', plain,
% 1.51/1.72      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.51/1.72        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.51/1.72        (k6_partfun1 @ sk_A))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('1', plain,
% 1.51/1.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('2', plain,
% 1.51/1.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf(redefinition_k1_partfun1, axiom,
% 1.51/1.72    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.51/1.72     ( ( ( v1_funct_1 @ E ) & 
% 1.51/1.72         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.51/1.72         ( v1_funct_1 @ F ) & 
% 1.51/1.72         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.51/1.72       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.51/1.72  thf('3', plain,
% 1.51/1.72      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 1.51/1.72         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 1.51/1.72          | ~ (v1_funct_1 @ X36)
% 1.51/1.72          | ~ (v1_funct_1 @ X39)
% 1.51/1.72          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 1.51/1.72          | ((k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39)
% 1.51/1.72              = (k5_relat_1 @ X36 @ X39)))),
% 1.51/1.72      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.51/1.72  thf('4', plain,
% 1.51/1.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.72         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.51/1.72            = (k5_relat_1 @ sk_C @ X0))
% 1.51/1.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.51/1.72          | ~ (v1_funct_1 @ X0)
% 1.51/1.72          | ~ (v1_funct_1 @ sk_C))),
% 1.51/1.72      inference('sup-', [status(thm)], ['2', '3'])).
% 1.51/1.72  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('6', plain,
% 1.51/1.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.72         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.51/1.72            = (k5_relat_1 @ sk_C @ X0))
% 1.51/1.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.51/1.72          | ~ (v1_funct_1 @ X0))),
% 1.51/1.72      inference('demod', [status(thm)], ['4', '5'])).
% 1.51/1.72  thf('7', plain,
% 1.51/1.72      ((~ (v1_funct_1 @ sk_D)
% 1.51/1.72        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.51/1.72            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.51/1.72      inference('sup-', [status(thm)], ['1', '6'])).
% 1.51/1.72  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('9', plain,
% 1.51/1.72      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.51/1.72         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.51/1.72      inference('demod', [status(thm)], ['7', '8'])).
% 1.51/1.72  thf('10', plain,
% 1.51/1.72      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.51/1.72        (k6_partfun1 @ sk_A))),
% 1.51/1.72      inference('demod', [status(thm)], ['0', '9'])).
% 1.51/1.72  thf('11', plain,
% 1.51/1.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('12', plain,
% 1.51/1.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf(dt_k1_partfun1, axiom,
% 1.51/1.72    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.51/1.72     ( ( ( v1_funct_1 @ E ) & 
% 1.51/1.72         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.51/1.72         ( v1_funct_1 @ F ) & 
% 1.51/1.72         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.51/1.72       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.51/1.72         ( m1_subset_1 @
% 1.51/1.72           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.51/1.72           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.51/1.72  thf('13', plain,
% 1.51/1.72      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.51/1.72         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 1.51/1.72          | ~ (v1_funct_1 @ X28)
% 1.51/1.72          | ~ (v1_funct_1 @ X31)
% 1.51/1.72          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.51/1.72          | (m1_subset_1 @ (k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31) @ 
% 1.51/1.72             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X33))))),
% 1.51/1.72      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.51/1.72  thf('14', plain,
% 1.51/1.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.72         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.51/1.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.51/1.72          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.51/1.72          | ~ (v1_funct_1 @ X1)
% 1.51/1.72          | ~ (v1_funct_1 @ sk_C))),
% 1.51/1.72      inference('sup-', [status(thm)], ['12', '13'])).
% 1.51/1.72  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('16', plain,
% 1.51/1.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.72         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.51/1.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.51/1.72          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.51/1.72          | ~ (v1_funct_1 @ X1))),
% 1.51/1.72      inference('demod', [status(thm)], ['14', '15'])).
% 1.51/1.72  thf('17', plain,
% 1.51/1.72      ((~ (v1_funct_1 @ sk_D)
% 1.51/1.72        | (m1_subset_1 @ 
% 1.51/1.72           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.51/1.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.51/1.72      inference('sup-', [status(thm)], ['11', '16'])).
% 1.51/1.72  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('19', plain,
% 1.51/1.72      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.51/1.72         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.51/1.72      inference('demod', [status(thm)], ['7', '8'])).
% 1.51/1.72  thf('20', plain,
% 1.51/1.72      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.51/1.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.51/1.72      inference('demod', [status(thm)], ['17', '18', '19'])).
% 1.51/1.72  thf(redefinition_r2_relset_1, axiom,
% 1.51/1.72    (![A:$i,B:$i,C:$i,D:$i]:
% 1.51/1.72     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.51/1.72         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.51/1.72       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.51/1.72  thf('21', plain,
% 1.51/1.72      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 1.51/1.72         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 1.51/1.72          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 1.51/1.72          | ((X16) = (X19))
% 1.51/1.72          | ~ (r2_relset_1 @ X17 @ X18 @ X16 @ X19))),
% 1.51/1.72      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.51/1.72  thf('22', plain,
% 1.51/1.72      (![X0 : $i]:
% 1.51/1.72         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 1.51/1.72          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 1.51/1.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.51/1.72      inference('sup-', [status(thm)], ['20', '21'])).
% 1.51/1.72  thf('23', plain,
% 1.51/1.72      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.51/1.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.51/1.72        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 1.51/1.72      inference('sup-', [status(thm)], ['10', '22'])).
% 1.51/1.72  thf(dt_k6_partfun1, axiom,
% 1.51/1.72    (![A:$i]:
% 1.51/1.72     ( ( m1_subset_1 @
% 1.51/1.72         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 1.51/1.72       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 1.51/1.72  thf('24', plain,
% 1.51/1.72      (![X35 : $i]:
% 1.51/1.72         (m1_subset_1 @ (k6_partfun1 @ X35) @ 
% 1.51/1.72          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 1.51/1.72      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.51/1.72  thf('25', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.51/1.72      inference('demod', [status(thm)], ['23', '24'])).
% 1.51/1.72  thf(dt_k2_funct_1, axiom,
% 1.51/1.72    (![A:$i]:
% 1.51/1.72     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.51/1.72       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.51/1.72         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.51/1.72  thf('26', plain,
% 1.51/1.72      (![X7 : $i]:
% 1.51/1.72         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 1.51/1.72          | ~ (v1_funct_1 @ X7)
% 1.51/1.72          | ~ (v1_relat_1 @ X7))),
% 1.51/1.72      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.51/1.72  thf(t61_funct_1, axiom,
% 1.51/1.72    (![A:$i]:
% 1.51/1.72     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.51/1.72       ( ( v2_funct_1 @ A ) =>
% 1.51/1.72         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.51/1.72             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.51/1.72           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.51/1.72             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.51/1.72  thf('27', plain,
% 1.51/1.72      (![X9 : $i]:
% 1.51/1.72         (~ (v2_funct_1 @ X9)
% 1.51/1.72          | ((k5_relat_1 @ (k2_funct_1 @ X9) @ X9)
% 1.51/1.72              = (k6_relat_1 @ (k2_relat_1 @ X9)))
% 1.51/1.72          | ~ (v1_funct_1 @ X9)
% 1.51/1.72          | ~ (v1_relat_1 @ X9))),
% 1.51/1.72      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.51/1.72  thf(redefinition_k6_partfun1, axiom,
% 1.51/1.72    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.51/1.72  thf('28', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 1.51/1.72      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.51/1.72  thf('29', plain,
% 1.51/1.72      (![X9 : $i]:
% 1.51/1.72         (~ (v2_funct_1 @ X9)
% 1.51/1.72          | ((k5_relat_1 @ (k2_funct_1 @ X9) @ X9)
% 1.51/1.72              = (k6_partfun1 @ (k2_relat_1 @ X9)))
% 1.51/1.72          | ~ (v1_funct_1 @ X9)
% 1.51/1.72          | ~ (v1_relat_1 @ X9))),
% 1.51/1.72      inference('demod', [status(thm)], ['27', '28'])).
% 1.51/1.72  thf(t55_relat_1, axiom,
% 1.51/1.72    (![A:$i]:
% 1.51/1.72     ( ( v1_relat_1 @ A ) =>
% 1.51/1.72       ( ![B:$i]:
% 1.51/1.72         ( ( v1_relat_1 @ B ) =>
% 1.51/1.72           ( ![C:$i]:
% 1.51/1.72             ( ( v1_relat_1 @ C ) =>
% 1.51/1.72               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 1.51/1.72                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 1.51/1.72  thf('30', plain,
% 1.51/1.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.72         (~ (v1_relat_1 @ X0)
% 1.51/1.72          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 1.51/1.72              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 1.51/1.72          | ~ (v1_relat_1 @ X2)
% 1.51/1.72          | ~ (v1_relat_1 @ X1))),
% 1.51/1.72      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.51/1.72  thf('31', plain,
% 1.51/1.72      (![X0 : $i, X1 : $i]:
% 1.51/1.72         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 1.51/1.72            = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 1.51/1.72          | ~ (v1_relat_1 @ X0)
% 1.51/1.72          | ~ (v1_funct_1 @ X0)
% 1.51/1.72          | ~ (v2_funct_1 @ X0)
% 1.51/1.72          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.51/1.72          | ~ (v1_relat_1 @ X1)
% 1.51/1.72          | ~ (v1_relat_1 @ X0))),
% 1.51/1.72      inference('sup+', [status(thm)], ['29', '30'])).
% 1.51/1.72  thf('32', plain,
% 1.51/1.72      (![X0 : $i, X1 : $i]:
% 1.51/1.72         (~ (v1_relat_1 @ X1)
% 1.51/1.72          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.51/1.72          | ~ (v2_funct_1 @ X0)
% 1.51/1.72          | ~ (v1_funct_1 @ X0)
% 1.51/1.72          | ~ (v1_relat_1 @ X0)
% 1.51/1.72          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 1.51/1.72              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1))))),
% 1.51/1.72      inference('simplify', [status(thm)], ['31'])).
% 1.51/1.72  thf('33', plain,
% 1.51/1.72      (![X0 : $i, X1 : $i]:
% 1.51/1.72         (~ (v1_relat_1 @ X0)
% 1.51/1.72          | ~ (v1_funct_1 @ X0)
% 1.51/1.72          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 1.51/1.72              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 1.51/1.72          | ~ (v1_relat_1 @ X0)
% 1.51/1.72          | ~ (v1_funct_1 @ X0)
% 1.51/1.72          | ~ (v2_funct_1 @ X0)
% 1.51/1.72          | ~ (v1_relat_1 @ X1))),
% 1.51/1.72      inference('sup-', [status(thm)], ['26', '32'])).
% 1.51/1.72  thf('34', plain,
% 1.51/1.72      (![X0 : $i, X1 : $i]:
% 1.51/1.72         (~ (v1_relat_1 @ X1)
% 1.51/1.72          | ~ (v2_funct_1 @ X0)
% 1.51/1.72          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 1.51/1.72              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 1.51/1.72          | ~ (v1_funct_1 @ X0)
% 1.51/1.72          | ~ (v1_relat_1 @ X0))),
% 1.51/1.72      inference('simplify', [status(thm)], ['33'])).
% 1.51/1.72  thf('35', plain,
% 1.51/1.72      ((((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)) @ sk_D)
% 1.51/1.72          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 1.51/1.72        | ~ (v1_relat_1 @ sk_C)
% 1.51/1.72        | ~ (v1_funct_1 @ sk_C)
% 1.51/1.72        | ~ (v2_funct_1 @ sk_C)
% 1.51/1.72        | ~ (v1_relat_1 @ sk_D))),
% 1.51/1.72      inference('sup+', [status(thm)], ['25', '34'])).
% 1.51/1.72  thf('36', plain,
% 1.51/1.72      (![X9 : $i]:
% 1.51/1.72         (~ (v2_funct_1 @ X9)
% 1.51/1.72          | ((k5_relat_1 @ (k2_funct_1 @ X9) @ X9)
% 1.51/1.72              = (k6_partfun1 @ (k2_relat_1 @ X9)))
% 1.51/1.72          | ~ (v1_funct_1 @ X9)
% 1.51/1.72          | ~ (v1_relat_1 @ X9))),
% 1.51/1.72      inference('demod', [status(thm)], ['27', '28'])).
% 1.51/1.72  thf('37', plain,
% 1.51/1.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf(t35_funct_2, axiom,
% 1.51/1.72    (![A:$i,B:$i,C:$i]:
% 1.51/1.72     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.51/1.72         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.51/1.72       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.51/1.72         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.51/1.72           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 1.51/1.72             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 1.51/1.72  thf('38', plain,
% 1.51/1.72      (![X43 : $i, X44 : $i, X45 : $i]:
% 1.51/1.72         (((X43) = (k1_xboole_0))
% 1.51/1.72          | ~ (v1_funct_1 @ X44)
% 1.51/1.72          | ~ (v1_funct_2 @ X44 @ X45 @ X43)
% 1.51/1.72          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X43)))
% 1.51/1.72          | ((k5_relat_1 @ (k2_funct_1 @ X44) @ X44) = (k6_partfun1 @ X43))
% 1.51/1.72          | ~ (v2_funct_1 @ X44)
% 1.51/1.72          | ((k2_relset_1 @ X45 @ X43 @ X44) != (X43)))),
% 1.51/1.72      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.51/1.72  thf('39', plain,
% 1.51/1.72      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.51/1.72        | ~ (v2_funct_1 @ sk_C)
% 1.51/1.72        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 1.51/1.72        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.51/1.72        | ~ (v1_funct_1 @ sk_C)
% 1.51/1.72        | ((sk_B) = (k1_xboole_0)))),
% 1.51/1.72      inference('sup-', [status(thm)], ['37', '38'])).
% 1.51/1.72  thf('40', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('41', plain, ((v2_funct_1 @ sk_C)),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('42', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('43', plain, ((v1_funct_1 @ sk_C)),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('44', plain,
% 1.51/1.72      ((((sk_B) != (sk_B))
% 1.51/1.72        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 1.51/1.72        | ((sk_B) = (k1_xboole_0)))),
% 1.51/1.72      inference('demod', [status(thm)], ['39', '40', '41', '42', '43'])).
% 1.51/1.72  thf('45', plain,
% 1.51/1.72      ((((sk_B) = (k1_xboole_0))
% 1.51/1.72        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 1.51/1.72      inference('simplify', [status(thm)], ['44'])).
% 1.51/1.72  thf('46', plain, (((sk_B) != (k1_xboole_0))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('47', plain,
% 1.51/1.72      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 1.51/1.72      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 1.51/1.72  thf('48', plain,
% 1.51/1.72      ((((k6_partfun1 @ (k2_relat_1 @ sk_C)) = (k6_partfun1 @ sk_B))
% 1.51/1.72        | ~ (v1_relat_1 @ sk_C)
% 1.51/1.72        | ~ (v1_funct_1 @ sk_C)
% 1.51/1.72        | ~ (v2_funct_1 @ sk_C))),
% 1.51/1.72      inference('sup+', [status(thm)], ['36', '47'])).
% 1.51/1.72  thf('49', plain,
% 1.51/1.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf(cc1_relset_1, axiom,
% 1.51/1.72    (![A:$i,B:$i,C:$i]:
% 1.51/1.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.51/1.72       ( v1_relat_1 @ C ) ))).
% 1.51/1.72  thf('50', plain,
% 1.51/1.72      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.51/1.72         ((v1_relat_1 @ X10)
% 1.51/1.72          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 1.51/1.72      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.51/1.72  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 1.51/1.72      inference('sup-', [status(thm)], ['49', '50'])).
% 1.51/1.72  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('53', plain, ((v2_funct_1 @ sk_C)),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('54', plain,
% 1.51/1.72      (((k6_partfun1 @ (k2_relat_1 @ sk_C)) = (k6_partfun1 @ sk_B))),
% 1.51/1.72      inference('demod', [status(thm)], ['48', '51', '52', '53'])).
% 1.51/1.72  thf(t71_relat_1, axiom,
% 1.51/1.72    (![A:$i]:
% 1.51/1.72     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.51/1.72       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.51/1.72  thf('55', plain, (![X3 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X3)) = (X3))),
% 1.51/1.72      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.51/1.72  thf('56', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 1.51/1.72      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.51/1.72  thf('57', plain, (![X3 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X3)) = (X3))),
% 1.51/1.72      inference('demod', [status(thm)], ['55', '56'])).
% 1.51/1.72  thf('58', plain,
% 1.51/1.72      (((k1_relat_1 @ (k6_partfun1 @ sk_B)) = (k2_relat_1 @ sk_C))),
% 1.51/1.72      inference('sup+', [status(thm)], ['54', '57'])).
% 1.51/1.72  thf('59', plain, (![X3 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X3)) = (X3))),
% 1.51/1.72      inference('demod', [status(thm)], ['55', '56'])).
% 1.51/1.72  thf('60', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 1.51/1.72      inference('demod', [status(thm)], ['58', '59'])).
% 1.51/1.72  thf('61', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf(d1_funct_2, axiom,
% 1.51/1.72    (![A:$i,B:$i,C:$i]:
% 1.51/1.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.51/1.72       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.51/1.72           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.51/1.72             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.51/1.72         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.51/1.72           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.51/1.72             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.51/1.72  thf(zf_stmt_1, axiom,
% 1.51/1.72    (![C:$i,B:$i,A:$i]:
% 1.51/1.72     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.51/1.72       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.51/1.72  thf('62', plain,
% 1.51/1.72      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.51/1.72         (~ (v1_funct_2 @ X24 @ X22 @ X23)
% 1.51/1.72          | ((X22) = (k1_relset_1 @ X22 @ X23 @ X24))
% 1.51/1.72          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.51/1.72  thf('63', plain,
% 1.51/1.72      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 1.51/1.72        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 1.51/1.72      inference('sup-', [status(thm)], ['61', '62'])).
% 1.51/1.72  thf(zf_stmt_2, axiom,
% 1.51/1.72    (![B:$i,A:$i]:
% 1.51/1.72     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.51/1.72       ( zip_tseitin_0 @ B @ A ) ))).
% 1.51/1.72  thf('64', plain,
% 1.51/1.72      (![X20 : $i, X21 : $i]:
% 1.51/1.72         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.51/1.72  thf('65', plain,
% 1.51/1.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.51/1.72  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.51/1.72  thf(zf_stmt_5, axiom,
% 1.51/1.72    (![A:$i,B:$i,C:$i]:
% 1.51/1.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.51/1.72       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.51/1.72         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.51/1.72           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.51/1.72             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.51/1.72  thf('66', plain,
% 1.51/1.72      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.51/1.72         (~ (zip_tseitin_0 @ X25 @ X26)
% 1.51/1.72          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 1.51/1.72          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.51/1.72  thf('67', plain,
% 1.51/1.72      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 1.51/1.72      inference('sup-', [status(thm)], ['65', '66'])).
% 1.51/1.72  thf('68', plain,
% 1.51/1.72      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 1.51/1.72      inference('sup-', [status(thm)], ['64', '67'])).
% 1.51/1.72  thf('69', plain, (((sk_A) != (k1_xboole_0))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('70', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 1.51/1.72      inference('simplify_reflect-', [status(thm)], ['68', '69'])).
% 1.51/1.72  thf('71', plain,
% 1.51/1.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf(redefinition_k1_relset_1, axiom,
% 1.51/1.72    (![A:$i,B:$i,C:$i]:
% 1.51/1.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.51/1.72       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.51/1.72  thf('72', plain,
% 1.51/1.72      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.51/1.72         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 1.51/1.72          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.51/1.72      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.51/1.72  thf('73', plain,
% 1.51/1.72      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.51/1.72      inference('sup-', [status(thm)], ['71', '72'])).
% 1.51/1.72  thf('74', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.51/1.72      inference('demod', [status(thm)], ['63', '70', '73'])).
% 1.51/1.72  thf(t78_relat_1, axiom,
% 1.51/1.72    (![A:$i]:
% 1.51/1.72     ( ( v1_relat_1 @ A ) =>
% 1.51/1.72       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 1.51/1.72  thf('75', plain,
% 1.51/1.72      (![X5 : $i]:
% 1.51/1.72         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X5)) @ X5) = (X5))
% 1.51/1.72          | ~ (v1_relat_1 @ X5))),
% 1.51/1.72      inference('cnf', [status(esa)], [t78_relat_1])).
% 1.51/1.72  thf('76', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 1.51/1.72      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.51/1.72  thf('77', plain,
% 1.51/1.72      (![X5 : $i]:
% 1.51/1.72         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X5)) @ X5) = (X5))
% 1.51/1.72          | ~ (v1_relat_1 @ X5))),
% 1.51/1.72      inference('demod', [status(thm)], ['75', '76'])).
% 1.51/1.72  thf('78', plain,
% 1.51/1.72      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))
% 1.51/1.72        | ~ (v1_relat_1 @ sk_D))),
% 1.51/1.72      inference('sup+', [status(thm)], ['74', '77'])).
% 1.51/1.72  thf('79', plain,
% 1.51/1.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('80', plain,
% 1.51/1.72      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.51/1.72         ((v1_relat_1 @ X10)
% 1.51/1.72          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 1.51/1.72      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.51/1.72  thf('81', plain, ((v1_relat_1 @ sk_D)),
% 1.51/1.72      inference('sup-', [status(thm)], ['79', '80'])).
% 1.51/1.72  thf('82', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))),
% 1.51/1.72      inference('demod', [status(thm)], ['78', '81'])).
% 1.51/1.72  thf('83', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('84', plain,
% 1.51/1.72      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.51/1.72         (~ (v1_funct_2 @ X24 @ X22 @ X23)
% 1.51/1.72          | ((X22) = (k1_relset_1 @ X22 @ X23 @ X24))
% 1.51/1.72          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.51/1.72  thf('85', plain,
% 1.51/1.72      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 1.51/1.72        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 1.51/1.72      inference('sup-', [status(thm)], ['83', '84'])).
% 1.51/1.72  thf('86', plain,
% 1.51/1.72      (![X20 : $i, X21 : $i]:
% 1.51/1.72         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.51/1.72  thf('87', plain,
% 1.51/1.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('88', plain,
% 1.51/1.72      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.51/1.72         (~ (zip_tseitin_0 @ X25 @ X26)
% 1.51/1.72          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 1.51/1.72          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.51/1.72  thf('89', plain,
% 1.51/1.72      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.51/1.72      inference('sup-', [status(thm)], ['87', '88'])).
% 1.51/1.72  thf('90', plain,
% 1.51/1.72      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 1.51/1.72      inference('sup-', [status(thm)], ['86', '89'])).
% 1.51/1.72  thf('91', plain, (((sk_B) != (k1_xboole_0))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('92', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 1.51/1.72      inference('simplify_reflect-', [status(thm)], ['90', '91'])).
% 1.51/1.72  thf('93', plain,
% 1.51/1.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('94', plain,
% 1.51/1.72      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.51/1.72         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 1.51/1.72          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.51/1.72      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.51/1.72  thf('95', plain,
% 1.51/1.72      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 1.51/1.72      inference('sup-', [status(thm)], ['93', '94'])).
% 1.51/1.72  thf('96', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 1.51/1.72      inference('demod', [status(thm)], ['85', '92', '95'])).
% 1.51/1.72  thf('97', plain,
% 1.51/1.72      (![X7 : $i]:
% 1.51/1.72         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 1.51/1.72          | ~ (v1_funct_1 @ X7)
% 1.51/1.72          | ~ (v1_relat_1 @ X7))),
% 1.51/1.72      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.51/1.72  thf(t55_funct_1, axiom,
% 1.51/1.72    (![A:$i]:
% 1.51/1.72     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.51/1.72       ( ( v2_funct_1 @ A ) =>
% 1.51/1.72         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.51/1.72           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.51/1.72  thf('98', plain,
% 1.51/1.72      (![X8 : $i]:
% 1.51/1.72         (~ (v2_funct_1 @ X8)
% 1.51/1.72          | ((k1_relat_1 @ X8) = (k2_relat_1 @ (k2_funct_1 @ X8)))
% 1.51/1.72          | ~ (v1_funct_1 @ X8)
% 1.51/1.72          | ~ (v1_relat_1 @ X8))),
% 1.51/1.72      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.51/1.72  thf(t80_relat_1, axiom,
% 1.51/1.72    (![A:$i]:
% 1.51/1.72     ( ( v1_relat_1 @ A ) =>
% 1.51/1.72       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 1.51/1.72  thf('99', plain,
% 1.51/1.72      (![X6 : $i]:
% 1.51/1.72         (((k5_relat_1 @ X6 @ (k6_relat_1 @ (k2_relat_1 @ X6))) = (X6))
% 1.51/1.72          | ~ (v1_relat_1 @ X6))),
% 1.51/1.72      inference('cnf', [status(esa)], [t80_relat_1])).
% 1.51/1.72  thf('100', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 1.51/1.72      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.51/1.72  thf('101', plain,
% 1.51/1.72      (![X6 : $i]:
% 1.51/1.72         (((k5_relat_1 @ X6 @ (k6_partfun1 @ (k2_relat_1 @ X6))) = (X6))
% 1.51/1.72          | ~ (v1_relat_1 @ X6))),
% 1.51/1.72      inference('demod', [status(thm)], ['99', '100'])).
% 1.51/1.72  thf('102', plain,
% 1.51/1.72      (![X0 : $i]:
% 1.51/1.72         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.51/1.72            = (k2_funct_1 @ X0))
% 1.51/1.72          | ~ (v1_relat_1 @ X0)
% 1.51/1.72          | ~ (v1_funct_1 @ X0)
% 1.51/1.72          | ~ (v2_funct_1 @ X0)
% 1.51/1.72          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.51/1.72      inference('sup+', [status(thm)], ['98', '101'])).
% 1.51/1.72  thf('103', plain,
% 1.51/1.72      (![X0 : $i]:
% 1.51/1.72         (~ (v1_relat_1 @ X0)
% 1.51/1.72          | ~ (v1_funct_1 @ X0)
% 1.51/1.72          | ~ (v2_funct_1 @ X0)
% 1.51/1.72          | ~ (v1_funct_1 @ X0)
% 1.51/1.72          | ~ (v1_relat_1 @ X0)
% 1.51/1.72          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 1.51/1.72              (k6_partfun1 @ (k1_relat_1 @ X0))) = (k2_funct_1 @ X0)))),
% 1.51/1.72      inference('sup-', [status(thm)], ['97', '102'])).
% 1.51/1.72  thf('104', plain,
% 1.51/1.72      (![X0 : $i]:
% 1.51/1.72         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.51/1.72            = (k2_funct_1 @ X0))
% 1.51/1.72          | ~ (v2_funct_1 @ X0)
% 1.51/1.72          | ~ (v1_funct_1 @ X0)
% 1.51/1.72          | ~ (v1_relat_1 @ X0))),
% 1.51/1.72      inference('simplify', [status(thm)], ['103'])).
% 1.51/1.72  thf('105', plain,
% 1.51/1.72      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 1.51/1.72          = (k2_funct_1 @ sk_C))
% 1.51/1.72        | ~ (v1_relat_1 @ sk_C)
% 1.51/1.72        | ~ (v1_funct_1 @ sk_C)
% 1.51/1.72        | ~ (v2_funct_1 @ sk_C))),
% 1.51/1.72      inference('sup+', [status(thm)], ['96', '104'])).
% 1.51/1.72  thf('106', plain, ((v1_relat_1 @ sk_C)),
% 1.51/1.72      inference('sup-', [status(thm)], ['49', '50'])).
% 1.51/1.72  thf('107', plain, ((v1_funct_1 @ sk_C)),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('108', plain, ((v2_funct_1 @ sk_C)),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('109', plain,
% 1.51/1.72      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 1.51/1.72         = (k2_funct_1 @ sk_C))),
% 1.51/1.72      inference('demod', [status(thm)], ['105', '106', '107', '108'])).
% 1.51/1.72  thf('110', plain, ((v1_relat_1 @ sk_C)),
% 1.51/1.72      inference('sup-', [status(thm)], ['49', '50'])).
% 1.51/1.72  thf('111', plain, ((v1_funct_1 @ sk_C)),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('112', plain, ((v2_funct_1 @ sk_C)),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('113', plain, ((v1_relat_1 @ sk_D)),
% 1.51/1.72      inference('sup-', [status(thm)], ['79', '80'])).
% 1.51/1.72  thf('114', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 1.51/1.72      inference('demod', [status(thm)],
% 1.51/1.72                ['35', '60', '82', '109', '110', '111', '112', '113'])).
% 1.51/1.72  thf('115', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('116', plain, ($false),
% 1.51/1.72      inference('simplify_reflect-', [status(thm)], ['114', '115'])).
% 1.51/1.72  
% 1.51/1.72  % SZS output end Refutation
% 1.51/1.72  
% 1.51/1.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ao77jhR5Kv

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:14 EST 2020

% Result     : Theorem 1.15s
% Output     : Refutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :  222 (1051 expanded)
%              Number of leaves         :   43 ( 345 expanded)
%              Depth                    :   29
%              Number of atoms          : 1858 (17723 expanded)
%              Number of equality atoms :   87 (1107 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ( ( k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45 )
        = ( k5_relat_1 @ X42 @ X45 ) ) ) ),
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
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X41 ) ) ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( X31 = X34 )
      | ~ ( r2_relset_1 @ X32 @ X33 @ X31 @ X34 ) ) ),
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

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('24',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('25',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('26',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('28',plain,(
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X24 ) @ X24 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('29',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('30',plain,(
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X24 ) @ X24 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('31',plain,(
    ! [X18: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
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

thf('32',plain,(
    ! [X23: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k2_relat_1 @ X23 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('33',plain,(
    ! [X18: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('35',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('36',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X18: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('40',plain,(
    ! [X23: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k2_relat_1 @ X23 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('42',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['41'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('43',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ( v4_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['38','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('52',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('53',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['48','53','54','55'])).

thf('57',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('58',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['33','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('61',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('64',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['32','64'])).

thf('66',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['36','37'])).

thf('67',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('68',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('69',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['65','66','67','68','69','70'])).

thf('72',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['41'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('73',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X14 ) @ X15 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X15 ) @ X14 )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('74',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('75',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X14 ) @ X15 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X15 ) @ X14 )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['71','76'])).

thf('78',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['31','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('80',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('83',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k6_partfun1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('88',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k6_partfun1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['86','91'])).

thf('93',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X14 ) @ X15 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X15 ) @ X14 )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('97',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) @ X13 )
        = ( k5_relat_1 @ X12 @ ( k5_relat_1 @ X11 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('98',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) @ X13 )
        = ( k5_relat_1 @ X12 @ ( k5_relat_1 @ X11 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ ( k5_relat_1 @ X0 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ ( k5_relat_1 @ X0 @ X3 ) ) ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X2 ) ) @ X1 )
        = ( k5_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['96','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('104',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('105',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X2 ) ) @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['101','102','103','104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['81','106'])).

thf('108',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('109',plain,(
    ! [X18: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('110',plain,(
    ! [X18: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('111',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['65','66','67','68','69','70'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('112',plain,(
    ! [X49: $i] :
      ( ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X49 ) @ ( k2_relat_1 @ X49 ) ) ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('113',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['110','113'])).

thf('115',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('116',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['109','117'])).

thf('119',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('120',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['118','119','120'])).

thf('122',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('123',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('125',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['107','108','125'])).

thf('127',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['30','126'])).

thf('128',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['36','37'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('130',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('131',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('134',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['127','128','129','130','131','132','133'])).

thf('135',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) @ X13 )
        = ( k5_relat_1 @ X12 @ ( k5_relat_1 @ X11 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('138',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('140',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['27','139'])).

thf('141',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('143',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('145',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('148',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('150',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['145','150'])).

thf('152',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X14 ) @ X15 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X15 ) @ X14 )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('153',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = sk_D ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['148','149'])).

thf('155',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('158',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('160',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('162',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X23: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k1_relat_1 @ X23 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('164',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X16 ) @ X17 )
      | ( ( k5_relat_1 @ X16 @ ( k6_relat_1 @ X17 ) )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('165',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('166',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X16 ) @ X17 )
      | ( ( k5_relat_1 @ X16 @ ( k6_partfun1 @ X17 ) )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ X1 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['163','166'])).

thf('168',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['162','167'])).

thf('169',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('170',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('173',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['168','169','170','171','172'])).

thf('174',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['148','149'])).

thf('175',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['140','155','173','174'])).

thf('176',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['175','176'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ao77jhR5Kv
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:28:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.15/1.36  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.15/1.36  % Solved by: fo/fo7.sh
% 1.15/1.36  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.15/1.36  % done 1235 iterations in 0.925s
% 1.15/1.36  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.15/1.36  % SZS output start Refutation
% 1.15/1.36  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.15/1.36  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.15/1.36  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.15/1.36  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.15/1.36  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.15/1.36  thf(sk_B_type, type, sk_B: $i).
% 1.15/1.36  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.15/1.36  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.15/1.36  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.15/1.36  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.15/1.36  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.15/1.36  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.15/1.36  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.15/1.36  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.15/1.36  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.15/1.36  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.15/1.36  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.15/1.36  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.15/1.36  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.15/1.36  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.15/1.36  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.15/1.36  thf(sk_A_type, type, sk_A: $i).
% 1.15/1.36  thf(sk_D_type, type, sk_D: $i).
% 1.15/1.36  thf(sk_C_type, type, sk_C: $i).
% 1.15/1.36  thf(t36_funct_2, conjecture,
% 1.15/1.36    (![A:$i,B:$i,C:$i]:
% 1.15/1.36     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.15/1.36         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.15/1.36       ( ![D:$i]:
% 1.15/1.36         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.15/1.36             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.15/1.36           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.15/1.36               ( r2_relset_1 @
% 1.15/1.36                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.15/1.36                 ( k6_partfun1 @ A ) ) & 
% 1.15/1.36               ( v2_funct_1 @ C ) ) =>
% 1.15/1.36             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.15/1.36               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.15/1.36  thf(zf_stmt_0, negated_conjecture,
% 1.15/1.36    (~( ![A:$i,B:$i,C:$i]:
% 1.15/1.36        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.15/1.36            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.15/1.36          ( ![D:$i]:
% 1.15/1.36            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.15/1.36                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.15/1.36              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.15/1.36                  ( r2_relset_1 @
% 1.15/1.36                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.15/1.36                    ( k6_partfun1 @ A ) ) & 
% 1.15/1.36                  ( v2_funct_1 @ C ) ) =>
% 1.15/1.36                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.15/1.36                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.15/1.36    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.15/1.36  thf('0', plain,
% 1.15/1.36      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.15/1.36        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.15/1.36        (k6_partfun1 @ sk_A))),
% 1.15/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.36  thf('1', plain,
% 1.15/1.36      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.15/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.36  thf('2', plain,
% 1.15/1.36      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.15/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.36  thf(redefinition_k1_partfun1, axiom,
% 1.15/1.36    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.15/1.36     ( ( ( v1_funct_1 @ E ) & 
% 1.15/1.36         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.15/1.36         ( v1_funct_1 @ F ) & 
% 1.15/1.36         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.15/1.36       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.15/1.36  thf('3', plain,
% 1.15/1.36      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 1.15/1.36         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 1.15/1.36          | ~ (v1_funct_1 @ X42)
% 1.15/1.36          | ~ (v1_funct_1 @ X45)
% 1.15/1.36          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 1.15/1.36          | ((k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45)
% 1.15/1.36              = (k5_relat_1 @ X42 @ X45)))),
% 1.15/1.36      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.15/1.36  thf('4', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.36         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.15/1.36            = (k5_relat_1 @ sk_C @ X0))
% 1.15/1.36          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.15/1.36          | ~ (v1_funct_1 @ X0)
% 1.15/1.36          | ~ (v1_funct_1 @ sk_C))),
% 1.15/1.36      inference('sup-', [status(thm)], ['2', '3'])).
% 1.15/1.36  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.36  thf('6', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.36         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.15/1.36            = (k5_relat_1 @ sk_C @ X0))
% 1.15/1.36          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.15/1.36          | ~ (v1_funct_1 @ X0))),
% 1.15/1.36      inference('demod', [status(thm)], ['4', '5'])).
% 1.15/1.36  thf('7', plain,
% 1.15/1.36      ((~ (v1_funct_1 @ sk_D)
% 1.15/1.36        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.15/1.36            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.15/1.36      inference('sup-', [status(thm)], ['1', '6'])).
% 1.15/1.36  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 1.15/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.36  thf('9', plain,
% 1.15/1.36      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.15/1.36         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.15/1.36      inference('demod', [status(thm)], ['7', '8'])).
% 1.15/1.36  thf('10', plain,
% 1.15/1.36      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.15/1.36        (k6_partfun1 @ sk_A))),
% 1.15/1.36      inference('demod', [status(thm)], ['0', '9'])).
% 1.15/1.36  thf('11', plain,
% 1.15/1.36      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.15/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.36  thf('12', plain,
% 1.15/1.36      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.15/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.36  thf(dt_k1_partfun1, axiom,
% 1.15/1.36    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.15/1.36     ( ( ( v1_funct_1 @ E ) & 
% 1.15/1.36         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.15/1.36         ( v1_funct_1 @ F ) & 
% 1.15/1.36         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.15/1.36       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.15/1.36         ( m1_subset_1 @
% 1.15/1.36           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.15/1.36           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.15/1.36  thf('13', plain,
% 1.15/1.36      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 1.15/1.36         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 1.15/1.36          | ~ (v1_funct_1 @ X36)
% 1.15/1.36          | ~ (v1_funct_1 @ X39)
% 1.15/1.36          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 1.15/1.36          | (m1_subset_1 @ (k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39) @ 
% 1.15/1.36             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X41))))),
% 1.15/1.36      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.15/1.36  thf('14', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.36         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.15/1.36           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.15/1.36          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.15/1.36          | ~ (v1_funct_1 @ X1)
% 1.15/1.36          | ~ (v1_funct_1 @ sk_C))),
% 1.15/1.36      inference('sup-', [status(thm)], ['12', '13'])).
% 1.15/1.36  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.36  thf('16', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.36         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.15/1.36           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.15/1.36          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.15/1.36          | ~ (v1_funct_1 @ X1))),
% 1.15/1.36      inference('demod', [status(thm)], ['14', '15'])).
% 1.15/1.36  thf('17', plain,
% 1.15/1.36      ((~ (v1_funct_1 @ sk_D)
% 1.15/1.36        | (m1_subset_1 @ 
% 1.15/1.36           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.15/1.36           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.15/1.36      inference('sup-', [status(thm)], ['11', '16'])).
% 1.15/1.36  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 1.15/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.36  thf('19', plain,
% 1.15/1.36      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.15/1.36         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.15/1.36      inference('demod', [status(thm)], ['7', '8'])).
% 1.15/1.36  thf('20', plain,
% 1.15/1.36      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.15/1.36        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.15/1.36      inference('demod', [status(thm)], ['17', '18', '19'])).
% 1.15/1.36  thf(redefinition_r2_relset_1, axiom,
% 1.15/1.36    (![A:$i,B:$i,C:$i,D:$i]:
% 1.15/1.36     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.15/1.36         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.15/1.36       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.15/1.36  thf('21', plain,
% 1.15/1.36      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.15/1.36         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.15/1.36          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.15/1.36          | ((X31) = (X34))
% 1.15/1.36          | ~ (r2_relset_1 @ X32 @ X33 @ X31 @ X34))),
% 1.15/1.36      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.15/1.36  thf('22', plain,
% 1.15/1.36      (![X0 : $i]:
% 1.15/1.36         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 1.15/1.36          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 1.15/1.36          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.15/1.36      inference('sup-', [status(thm)], ['20', '21'])).
% 1.15/1.36  thf('23', plain,
% 1.15/1.36      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.15/1.36           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.15/1.36        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 1.15/1.36      inference('sup-', [status(thm)], ['10', '22'])).
% 1.15/1.36  thf(t29_relset_1, axiom,
% 1.15/1.36    (![A:$i]:
% 1.15/1.36     ( m1_subset_1 @
% 1.15/1.36       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.15/1.36  thf('24', plain,
% 1.15/1.36      (![X35 : $i]:
% 1.15/1.36         (m1_subset_1 @ (k6_relat_1 @ X35) @ 
% 1.15/1.36          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 1.15/1.36      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.15/1.36  thf(redefinition_k6_partfun1, axiom,
% 1.15/1.36    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.15/1.36  thf('25', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 1.15/1.36      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.15/1.36  thf('26', plain,
% 1.15/1.36      (![X35 : $i]:
% 1.15/1.36         (m1_subset_1 @ (k6_partfun1 @ X35) @ 
% 1.15/1.36          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 1.15/1.36      inference('demod', [status(thm)], ['24', '25'])).
% 1.15/1.36  thf('27', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.15/1.36      inference('demod', [status(thm)], ['23', '26'])).
% 1.15/1.36  thf(t61_funct_1, axiom,
% 1.15/1.36    (![A:$i]:
% 1.15/1.36     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.15/1.36       ( ( v2_funct_1 @ A ) =>
% 1.15/1.36         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.15/1.36             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.15/1.36           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.15/1.36             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.15/1.36  thf('28', plain,
% 1.15/1.36      (![X24 : $i]:
% 1.15/1.36         (~ (v2_funct_1 @ X24)
% 1.15/1.36          | ((k5_relat_1 @ (k2_funct_1 @ X24) @ X24)
% 1.15/1.36              = (k6_relat_1 @ (k2_relat_1 @ X24)))
% 1.15/1.36          | ~ (v1_funct_1 @ X24)
% 1.15/1.36          | ~ (v1_relat_1 @ X24))),
% 1.15/1.36      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.15/1.36  thf('29', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 1.15/1.36      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.15/1.36  thf('30', plain,
% 1.15/1.36      (![X24 : $i]:
% 1.15/1.36         (~ (v2_funct_1 @ X24)
% 1.15/1.36          | ((k5_relat_1 @ (k2_funct_1 @ X24) @ X24)
% 1.15/1.36              = (k6_partfun1 @ (k2_relat_1 @ X24)))
% 1.15/1.36          | ~ (v1_funct_1 @ X24)
% 1.15/1.36          | ~ (v1_relat_1 @ X24))),
% 1.15/1.36      inference('demod', [status(thm)], ['28', '29'])).
% 1.15/1.36  thf(dt_k2_funct_1, axiom,
% 1.15/1.36    (![A:$i]:
% 1.15/1.36     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.15/1.36       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.15/1.36         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.15/1.36  thf('31', plain,
% 1.15/1.36      (![X18 : $i]:
% 1.15/1.36         ((v1_relat_1 @ (k2_funct_1 @ X18))
% 1.15/1.36          | ~ (v1_funct_1 @ X18)
% 1.15/1.36          | ~ (v1_relat_1 @ X18))),
% 1.15/1.36      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.15/1.36  thf(t55_funct_1, axiom,
% 1.15/1.36    (![A:$i]:
% 1.15/1.36     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.15/1.36       ( ( v2_funct_1 @ A ) =>
% 1.15/1.36         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.15/1.36           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.15/1.36  thf('32', plain,
% 1.15/1.36      (![X23 : $i]:
% 1.15/1.36         (~ (v2_funct_1 @ X23)
% 1.15/1.36          | ((k2_relat_1 @ X23) = (k1_relat_1 @ (k2_funct_1 @ X23)))
% 1.15/1.36          | ~ (v1_funct_1 @ X23)
% 1.15/1.36          | ~ (v1_relat_1 @ X23))),
% 1.15/1.36      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.15/1.36  thf('33', plain,
% 1.15/1.36      (![X18 : $i]:
% 1.15/1.36         ((v1_relat_1 @ (k2_funct_1 @ X18))
% 1.15/1.36          | ~ (v1_funct_1 @ X18)
% 1.15/1.36          | ~ (v1_relat_1 @ X18))),
% 1.15/1.36      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.15/1.36  thf('34', plain,
% 1.15/1.36      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.15/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.36  thf(redefinition_k2_relset_1, axiom,
% 1.15/1.36    (![A:$i,B:$i,C:$i]:
% 1.15/1.36     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.15/1.36       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.15/1.36  thf('35', plain,
% 1.15/1.36      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.15/1.36         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 1.15/1.36          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 1.15/1.36      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.15/1.36  thf('36', plain,
% 1.15/1.36      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.15/1.36      inference('sup-', [status(thm)], ['34', '35'])).
% 1.15/1.36  thf('37', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.15/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.36  thf('38', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.15/1.36      inference('sup+', [status(thm)], ['36', '37'])).
% 1.15/1.36  thf('39', plain,
% 1.15/1.36      (![X18 : $i]:
% 1.15/1.36         ((v1_relat_1 @ (k2_funct_1 @ X18))
% 1.15/1.36          | ~ (v1_funct_1 @ X18)
% 1.15/1.36          | ~ (v1_relat_1 @ X18))),
% 1.15/1.36      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.15/1.36  thf('40', plain,
% 1.15/1.36      (![X23 : $i]:
% 1.15/1.36         (~ (v2_funct_1 @ X23)
% 1.15/1.36          | ((k2_relat_1 @ X23) = (k1_relat_1 @ (k2_funct_1 @ X23)))
% 1.15/1.36          | ~ (v1_funct_1 @ X23)
% 1.15/1.36          | ~ (v1_relat_1 @ X23))),
% 1.15/1.36      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.15/1.36  thf(d10_xboole_0, axiom,
% 1.15/1.36    (![A:$i,B:$i]:
% 1.15/1.36     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.15/1.36  thf('41', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.15/1.36      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.15/1.36  thf('42', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.15/1.36      inference('simplify', [status(thm)], ['41'])).
% 1.15/1.36  thf(d18_relat_1, axiom,
% 1.15/1.36    (![A:$i,B:$i]:
% 1.15/1.36     ( ( v1_relat_1 @ B ) =>
% 1.15/1.36       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.15/1.36  thf('43', plain,
% 1.15/1.36      (![X5 : $i, X6 : $i]:
% 1.15/1.36         (~ (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 1.15/1.36          | (v4_relat_1 @ X5 @ X6)
% 1.15/1.36          | ~ (v1_relat_1 @ X5))),
% 1.15/1.36      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.15/1.36  thf('44', plain,
% 1.15/1.36      (![X0 : $i]:
% 1.15/1.36         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 1.15/1.36      inference('sup-', [status(thm)], ['42', '43'])).
% 1.15/1.36  thf('45', plain,
% 1.15/1.36      (![X0 : $i]:
% 1.15/1.36         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.15/1.36          | ~ (v1_relat_1 @ X0)
% 1.15/1.36          | ~ (v1_funct_1 @ X0)
% 1.15/1.36          | ~ (v2_funct_1 @ X0)
% 1.15/1.36          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.15/1.36      inference('sup+', [status(thm)], ['40', '44'])).
% 1.15/1.36  thf('46', plain,
% 1.15/1.36      (![X0 : $i]:
% 1.15/1.36         (~ (v1_relat_1 @ X0)
% 1.15/1.36          | ~ (v1_funct_1 @ X0)
% 1.15/1.36          | ~ (v2_funct_1 @ X0)
% 1.15/1.36          | ~ (v1_funct_1 @ X0)
% 1.15/1.36          | ~ (v1_relat_1 @ X0)
% 1.15/1.36          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 1.15/1.36      inference('sup-', [status(thm)], ['39', '45'])).
% 1.15/1.36  thf('47', plain,
% 1.15/1.36      (![X0 : $i]:
% 1.15/1.36         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.15/1.36          | ~ (v2_funct_1 @ X0)
% 1.15/1.36          | ~ (v1_funct_1 @ X0)
% 1.15/1.36          | ~ (v1_relat_1 @ X0))),
% 1.15/1.36      inference('simplify', [status(thm)], ['46'])).
% 1.15/1.36  thf('48', plain,
% 1.15/1.36      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)
% 1.15/1.36        | ~ (v1_relat_1 @ sk_C)
% 1.15/1.36        | ~ (v1_funct_1 @ sk_C)
% 1.15/1.36        | ~ (v2_funct_1 @ sk_C))),
% 1.15/1.36      inference('sup+', [status(thm)], ['38', '47'])).
% 1.15/1.36  thf('49', plain,
% 1.15/1.36      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.15/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.36  thf(cc2_relat_1, axiom,
% 1.15/1.36    (![A:$i]:
% 1.15/1.36     ( ( v1_relat_1 @ A ) =>
% 1.15/1.36       ( ![B:$i]:
% 1.15/1.36         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.15/1.36  thf('50', plain,
% 1.15/1.36      (![X3 : $i, X4 : $i]:
% 1.15/1.36         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 1.15/1.36          | (v1_relat_1 @ X3)
% 1.15/1.36          | ~ (v1_relat_1 @ X4))),
% 1.15/1.36      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.15/1.36  thf('51', plain,
% 1.15/1.36      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 1.15/1.36      inference('sup-', [status(thm)], ['49', '50'])).
% 1.15/1.36  thf(fc6_relat_1, axiom,
% 1.15/1.36    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.15/1.36  thf('52', plain,
% 1.15/1.36      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 1.15/1.36      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.15/1.36  thf('53', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.36      inference('demod', [status(thm)], ['51', '52'])).
% 1.15/1.36  thf('54', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.36  thf('55', plain, ((v2_funct_1 @ sk_C)),
% 1.15/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.36  thf('56', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)),
% 1.15/1.36      inference('demod', [status(thm)], ['48', '53', '54', '55'])).
% 1.15/1.36  thf('57', plain,
% 1.15/1.36      (![X5 : $i, X6 : $i]:
% 1.15/1.36         (~ (v4_relat_1 @ X5 @ X6)
% 1.15/1.36          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 1.15/1.36          | ~ (v1_relat_1 @ X5))),
% 1.15/1.36      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.15/1.36  thf('58', plain,
% 1.15/1.36      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.15/1.36        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 1.15/1.36      inference('sup-', [status(thm)], ['56', '57'])).
% 1.15/1.36  thf('59', plain,
% 1.15/1.36      ((~ (v1_relat_1 @ sk_C)
% 1.15/1.36        | ~ (v1_funct_1 @ sk_C)
% 1.15/1.36        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 1.15/1.36      inference('sup-', [status(thm)], ['33', '58'])).
% 1.15/1.36  thf('60', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.36      inference('demod', [status(thm)], ['51', '52'])).
% 1.15/1.36  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.36  thf('62', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B)),
% 1.15/1.36      inference('demod', [status(thm)], ['59', '60', '61'])).
% 1.15/1.36  thf('63', plain,
% 1.15/1.36      (![X0 : $i, X2 : $i]:
% 1.15/1.36         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.15/1.36      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.15/1.36  thf('64', plain,
% 1.15/1.36      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.15/1.36        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.15/1.36      inference('sup-', [status(thm)], ['62', '63'])).
% 1.15/1.36  thf('65', plain,
% 1.15/1.36      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C))
% 1.15/1.36        | ~ (v1_relat_1 @ sk_C)
% 1.15/1.36        | ~ (v1_funct_1 @ sk_C)
% 1.15/1.36        | ~ (v2_funct_1 @ sk_C)
% 1.15/1.36        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.15/1.36      inference('sup-', [status(thm)], ['32', '64'])).
% 1.15/1.36  thf('66', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.15/1.36      inference('sup+', [status(thm)], ['36', '37'])).
% 1.15/1.36  thf('67', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.15/1.36      inference('simplify', [status(thm)], ['41'])).
% 1.15/1.36  thf('68', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.36      inference('demod', [status(thm)], ['51', '52'])).
% 1.15/1.36  thf('69', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.36  thf('70', plain, ((v2_funct_1 @ sk_C)),
% 1.15/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.36  thf('71', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.15/1.36      inference('demod', [status(thm)], ['65', '66', '67', '68', '69', '70'])).
% 1.15/1.36  thf('72', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.15/1.36      inference('simplify', [status(thm)], ['41'])).
% 1.15/1.36  thf(t77_relat_1, axiom,
% 1.15/1.36    (![A:$i,B:$i]:
% 1.15/1.36     ( ( v1_relat_1 @ B ) =>
% 1.15/1.36       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 1.15/1.36         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 1.15/1.36  thf('73', plain,
% 1.15/1.36      (![X14 : $i, X15 : $i]:
% 1.15/1.36         (~ (r1_tarski @ (k1_relat_1 @ X14) @ X15)
% 1.15/1.36          | ((k5_relat_1 @ (k6_relat_1 @ X15) @ X14) = (X14))
% 1.15/1.36          | ~ (v1_relat_1 @ X14))),
% 1.15/1.36      inference('cnf', [status(esa)], [t77_relat_1])).
% 1.15/1.36  thf('74', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 1.15/1.36      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.15/1.36  thf('75', plain,
% 1.15/1.36      (![X14 : $i, X15 : $i]:
% 1.15/1.36         (~ (r1_tarski @ (k1_relat_1 @ X14) @ X15)
% 1.15/1.36          | ((k5_relat_1 @ (k6_partfun1 @ X15) @ X14) = (X14))
% 1.15/1.36          | ~ (v1_relat_1 @ X14))),
% 1.15/1.36      inference('demod', [status(thm)], ['73', '74'])).
% 1.15/1.36  thf('76', plain,
% 1.15/1.36      (![X0 : $i]:
% 1.15/1.36         (~ (v1_relat_1 @ X0)
% 1.15/1.36          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 1.15/1.36      inference('sup-', [status(thm)], ['72', '75'])).
% 1.15/1.36  thf('77', plain,
% 1.15/1.36      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.15/1.36          = (k2_funct_1 @ sk_C))
% 1.15/1.36        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.15/1.36      inference('sup+', [status(thm)], ['71', '76'])).
% 1.15/1.36  thf('78', plain,
% 1.15/1.36      ((~ (v1_relat_1 @ sk_C)
% 1.15/1.36        | ~ (v1_funct_1 @ sk_C)
% 1.15/1.36        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.15/1.36            = (k2_funct_1 @ sk_C)))),
% 1.15/1.36      inference('sup-', [status(thm)], ['31', '77'])).
% 1.15/1.36  thf('79', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.36      inference('demod', [status(thm)], ['51', '52'])).
% 1.15/1.36  thf('80', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.36  thf('81', plain,
% 1.15/1.36      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.15/1.36         = (k2_funct_1 @ sk_C))),
% 1.15/1.36      inference('demod', [status(thm)], ['78', '79', '80'])).
% 1.15/1.36  thf('82', plain,
% 1.15/1.36      (![X35 : $i]:
% 1.15/1.36         (m1_subset_1 @ (k6_partfun1 @ X35) @ 
% 1.15/1.36          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 1.15/1.36      inference('demod', [status(thm)], ['24', '25'])).
% 1.15/1.36  thf(cc2_relset_1, axiom,
% 1.15/1.36    (![A:$i,B:$i,C:$i]:
% 1.15/1.36     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.15/1.36       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.15/1.36  thf('83', plain,
% 1.15/1.36      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.15/1.36         ((v4_relat_1 @ X25 @ X26)
% 1.15/1.36          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 1.15/1.36      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.15/1.36  thf('84', plain, (![X0 : $i]: (v4_relat_1 @ (k6_partfun1 @ X0) @ X0)),
% 1.15/1.36      inference('sup-', [status(thm)], ['82', '83'])).
% 1.15/1.36  thf('85', plain,
% 1.15/1.36      (![X5 : $i, X6 : $i]:
% 1.15/1.36         (~ (v4_relat_1 @ X5 @ X6)
% 1.15/1.36          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 1.15/1.36          | ~ (v1_relat_1 @ X5))),
% 1.15/1.36      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.15/1.36  thf('86', plain,
% 1.15/1.36      (![X0 : $i]:
% 1.15/1.36         (~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 1.15/1.36          | (r1_tarski @ (k1_relat_1 @ (k6_partfun1 @ X0)) @ X0))),
% 1.15/1.36      inference('sup-', [status(thm)], ['84', '85'])).
% 1.15/1.36  thf('87', plain,
% 1.15/1.36      (![X35 : $i]:
% 1.15/1.36         (m1_subset_1 @ (k6_partfun1 @ X35) @ 
% 1.15/1.36          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 1.15/1.36      inference('demod', [status(thm)], ['24', '25'])).
% 1.15/1.36  thf('88', plain,
% 1.15/1.36      (![X3 : $i, X4 : $i]:
% 1.15/1.36         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 1.15/1.36          | (v1_relat_1 @ X3)
% 1.15/1.36          | ~ (v1_relat_1 @ X4))),
% 1.15/1.36      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.15/1.36  thf('89', plain,
% 1.15/1.36      (![X0 : $i]:
% 1.15/1.36         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X0))
% 1.15/1.36          | (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 1.15/1.36      inference('sup-', [status(thm)], ['87', '88'])).
% 1.15/1.36  thf('90', plain,
% 1.15/1.36      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 1.15/1.36      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.15/1.36  thf('91', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.15/1.36      inference('demod', [status(thm)], ['89', '90'])).
% 1.15/1.36  thf('92', plain,
% 1.15/1.36      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ (k6_partfun1 @ X0)) @ X0)),
% 1.15/1.36      inference('demod', [status(thm)], ['86', '91'])).
% 1.15/1.36  thf('93', plain,
% 1.15/1.36      (![X14 : $i, X15 : $i]:
% 1.15/1.36         (~ (r1_tarski @ (k1_relat_1 @ X14) @ X15)
% 1.15/1.36          | ((k5_relat_1 @ (k6_partfun1 @ X15) @ X14) = (X14))
% 1.15/1.36          | ~ (v1_relat_1 @ X14))),
% 1.15/1.36      inference('demod', [status(thm)], ['73', '74'])).
% 1.15/1.36  thf('94', plain,
% 1.15/1.36      (![X0 : $i]:
% 1.15/1.36         (~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 1.15/1.36          | ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 1.15/1.36              = (k6_partfun1 @ X0)))),
% 1.15/1.36      inference('sup-', [status(thm)], ['92', '93'])).
% 1.15/1.36  thf('95', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.15/1.36      inference('demod', [status(thm)], ['89', '90'])).
% 1.15/1.36  thf('96', plain,
% 1.15/1.36      (![X0 : $i]:
% 1.15/1.36         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 1.15/1.36           = (k6_partfun1 @ X0))),
% 1.15/1.36      inference('demod', [status(thm)], ['94', '95'])).
% 1.15/1.36  thf(t55_relat_1, axiom,
% 1.15/1.36    (![A:$i]:
% 1.15/1.36     ( ( v1_relat_1 @ A ) =>
% 1.15/1.36       ( ![B:$i]:
% 1.15/1.36         ( ( v1_relat_1 @ B ) =>
% 1.15/1.36           ( ![C:$i]:
% 1.15/1.36             ( ( v1_relat_1 @ C ) =>
% 1.15/1.36               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 1.15/1.36                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 1.15/1.36  thf('97', plain,
% 1.15/1.36      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.15/1.36         (~ (v1_relat_1 @ X11)
% 1.15/1.36          | ((k5_relat_1 @ (k5_relat_1 @ X12 @ X11) @ X13)
% 1.15/1.36              = (k5_relat_1 @ X12 @ (k5_relat_1 @ X11 @ X13)))
% 1.15/1.36          | ~ (v1_relat_1 @ X13)
% 1.15/1.36          | ~ (v1_relat_1 @ X12))),
% 1.15/1.36      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.15/1.36  thf('98', plain,
% 1.15/1.36      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.15/1.36         (~ (v1_relat_1 @ X11)
% 1.15/1.36          | ((k5_relat_1 @ (k5_relat_1 @ X12 @ X11) @ X13)
% 1.15/1.36              = (k5_relat_1 @ X12 @ (k5_relat_1 @ X11 @ X13)))
% 1.15/1.36          | ~ (v1_relat_1 @ X13)
% 1.15/1.36          | ~ (v1_relat_1 @ X12))),
% 1.15/1.36      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.15/1.36  thf('99', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.15/1.36         (((k5_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X3)
% 1.15/1.36            = (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ (k5_relat_1 @ X0 @ X3)))
% 1.15/1.36          | ~ (v1_relat_1 @ X2)
% 1.15/1.36          | ~ (v1_relat_1 @ X0)
% 1.15/1.36          | ~ (v1_relat_1 @ X1)
% 1.15/1.36          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 1.15/1.36          | ~ (v1_relat_1 @ X3)
% 1.15/1.36          | ~ (v1_relat_1 @ X0))),
% 1.15/1.36      inference('sup+', [status(thm)], ['97', '98'])).
% 1.15/1.36  thf('100', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.15/1.36         (~ (v1_relat_1 @ X3)
% 1.15/1.36          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 1.15/1.36          | ~ (v1_relat_1 @ X1)
% 1.15/1.36          | ~ (v1_relat_1 @ X0)
% 1.15/1.36          | ~ (v1_relat_1 @ X2)
% 1.15/1.36          | ((k5_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X3)
% 1.15/1.36              = (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ (k5_relat_1 @ X0 @ X3))))),
% 1.15/1.36      inference('simplify', [status(thm)], ['99'])).
% 1.15/1.36  thf('101', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.36         (~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 1.15/1.36          | ((k5_relat_1 @ 
% 1.15/1.36              (k5_relat_1 @ (k6_partfun1 @ X0) @ 
% 1.15/1.36               (k5_relat_1 @ (k6_partfun1 @ X0) @ X2)) @ 
% 1.15/1.36              X1)
% 1.15/1.36              = (k5_relat_1 @ 
% 1.15/1.36                 (k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0)) @ 
% 1.15/1.36                 (k5_relat_1 @ X2 @ X1)))
% 1.15/1.36          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 1.15/1.36          | ~ (v1_relat_1 @ X2)
% 1.15/1.36          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 1.15/1.36          | ~ (v1_relat_1 @ X1))),
% 1.15/1.36      inference('sup-', [status(thm)], ['96', '100'])).
% 1.15/1.36  thf('102', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.15/1.36      inference('demod', [status(thm)], ['89', '90'])).
% 1.15/1.36  thf('103', plain,
% 1.15/1.36      (![X0 : $i]:
% 1.15/1.36         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 1.15/1.36           = (k6_partfun1 @ X0))),
% 1.15/1.36      inference('demod', [status(thm)], ['94', '95'])).
% 1.15/1.36  thf('104', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.15/1.36      inference('demod', [status(thm)], ['89', '90'])).
% 1.15/1.36  thf('105', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.15/1.36      inference('demod', [status(thm)], ['89', '90'])).
% 1.15/1.36  thf('106', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.36         (((k5_relat_1 @ 
% 1.15/1.36            (k5_relat_1 @ (k6_partfun1 @ X0) @ 
% 1.15/1.36             (k5_relat_1 @ (k6_partfun1 @ X0) @ X2)) @ 
% 1.15/1.36            X1) = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k5_relat_1 @ X2 @ X1)))
% 1.15/1.36          | ~ (v1_relat_1 @ X2)
% 1.15/1.36          | ~ (v1_relat_1 @ X1))),
% 1.15/1.36      inference('demod', [status(thm)], ['101', '102', '103', '104', '105'])).
% 1.15/1.36  thf('107', plain,
% 1.15/1.36      (![X0 : $i]:
% 1.15/1.36         (((k5_relat_1 @ 
% 1.15/1.36            (k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C)) @ X0)
% 1.15/1.36            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.15/1.36               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 1.15/1.36          | ~ (v1_relat_1 @ X0)
% 1.15/1.36          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.15/1.36      inference('sup+', [status(thm)], ['81', '106'])).
% 1.15/1.36  thf('108', plain,
% 1.15/1.36      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.15/1.36         = (k2_funct_1 @ sk_C))),
% 1.15/1.36      inference('demod', [status(thm)], ['78', '79', '80'])).
% 1.15/1.36  thf('109', plain,
% 1.15/1.36      (![X18 : $i]:
% 1.15/1.36         ((v1_funct_1 @ (k2_funct_1 @ X18))
% 1.15/1.36          | ~ (v1_funct_1 @ X18)
% 1.15/1.36          | ~ (v1_relat_1 @ X18))),
% 1.15/1.36      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.15/1.36  thf('110', plain,
% 1.15/1.36      (![X18 : $i]:
% 1.15/1.36         ((v1_relat_1 @ (k2_funct_1 @ X18))
% 1.15/1.36          | ~ (v1_funct_1 @ X18)
% 1.15/1.36          | ~ (v1_relat_1 @ X18))),
% 1.15/1.36      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.15/1.36  thf('111', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.15/1.36      inference('demod', [status(thm)], ['65', '66', '67', '68', '69', '70'])).
% 1.15/1.36  thf(t3_funct_2, axiom,
% 1.15/1.36    (![A:$i]:
% 1.15/1.36     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.15/1.36       ( ( v1_funct_1 @ A ) & 
% 1.15/1.36         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.15/1.36         ( m1_subset_1 @
% 1.15/1.36           A @ 
% 1.15/1.36           ( k1_zfmisc_1 @
% 1.15/1.36             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.15/1.36  thf('112', plain,
% 1.15/1.36      (![X49 : $i]:
% 1.15/1.36         ((m1_subset_1 @ X49 @ 
% 1.15/1.36           (k1_zfmisc_1 @ 
% 1.15/1.36            (k2_zfmisc_1 @ (k1_relat_1 @ X49) @ (k2_relat_1 @ X49))))
% 1.15/1.36          | ~ (v1_funct_1 @ X49)
% 1.15/1.36          | ~ (v1_relat_1 @ X49))),
% 1.15/1.36      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.15/1.36  thf('113', plain,
% 1.15/1.36      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.15/1.36         (k1_zfmisc_1 @ 
% 1.15/1.36          (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))
% 1.15/1.36        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.15/1.36        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.15/1.36      inference('sup+', [status(thm)], ['111', '112'])).
% 1.15/1.36  thf('114', plain,
% 1.15/1.36      ((~ (v1_relat_1 @ sk_C)
% 1.15/1.36        | ~ (v1_funct_1 @ sk_C)
% 1.15/1.36        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.15/1.36        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.15/1.36           (k1_zfmisc_1 @ 
% 1.15/1.36            (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))))),
% 1.15/1.36      inference('sup-', [status(thm)], ['110', '113'])).
% 1.15/1.36  thf('115', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.36      inference('demod', [status(thm)], ['51', '52'])).
% 1.15/1.36  thf('116', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.36  thf('117', plain,
% 1.15/1.36      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.15/1.36        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.15/1.36           (k1_zfmisc_1 @ 
% 1.15/1.36            (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))))),
% 1.15/1.36      inference('demod', [status(thm)], ['114', '115', '116'])).
% 1.15/1.36  thf('118', plain,
% 1.15/1.36      ((~ (v1_relat_1 @ sk_C)
% 1.15/1.36        | ~ (v1_funct_1 @ sk_C)
% 1.15/1.36        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.15/1.36           (k1_zfmisc_1 @ 
% 1.15/1.36            (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))))),
% 1.15/1.36      inference('sup-', [status(thm)], ['109', '117'])).
% 1.15/1.36  thf('119', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.36      inference('demod', [status(thm)], ['51', '52'])).
% 1.15/1.36  thf('120', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.36  thf('121', plain,
% 1.15/1.36      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.15/1.36        (k1_zfmisc_1 @ 
% 1.15/1.36         (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 1.15/1.36      inference('demod', [status(thm)], ['118', '119', '120'])).
% 1.15/1.36  thf('122', plain,
% 1.15/1.36      (![X3 : $i, X4 : $i]:
% 1.15/1.36         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 1.15/1.36          | (v1_relat_1 @ X3)
% 1.15/1.36          | ~ (v1_relat_1 @ X4))),
% 1.15/1.36      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.15/1.36  thf('123', plain,
% 1.15/1.36      ((~ (v1_relat_1 @ 
% 1.15/1.36           (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 1.15/1.36        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.15/1.36      inference('sup-', [status(thm)], ['121', '122'])).
% 1.15/1.36  thf('124', plain,
% 1.15/1.36      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 1.15/1.36      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.15/1.36  thf('125', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.15/1.36      inference('demod', [status(thm)], ['123', '124'])).
% 1.15/1.36  thf('126', plain,
% 1.15/1.36      (![X0 : $i]:
% 1.15/1.36         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 1.15/1.36            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.15/1.36               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 1.15/1.36          | ~ (v1_relat_1 @ X0))),
% 1.15/1.36      inference('demod', [status(thm)], ['107', '108', '125'])).
% 1.15/1.36  thf('127', plain,
% 1.15/1.36      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 1.15/1.36          = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.15/1.36             (k6_partfun1 @ (k2_relat_1 @ sk_C))))
% 1.15/1.36        | ~ (v1_relat_1 @ sk_C)
% 1.15/1.36        | ~ (v1_funct_1 @ sk_C)
% 1.15/1.36        | ~ (v2_funct_1 @ sk_C)
% 1.15/1.36        | ~ (v1_relat_1 @ sk_C))),
% 1.15/1.36      inference('sup+', [status(thm)], ['30', '126'])).
% 1.15/1.36  thf('128', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.15/1.36      inference('sup+', [status(thm)], ['36', '37'])).
% 1.15/1.36  thf('129', plain,
% 1.15/1.36      (![X0 : $i]:
% 1.15/1.36         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 1.15/1.36           = (k6_partfun1 @ X0))),
% 1.15/1.36      inference('demod', [status(thm)], ['94', '95'])).
% 1.15/1.36  thf('130', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.36      inference('demod', [status(thm)], ['51', '52'])).
% 1.15/1.36  thf('131', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.36  thf('132', plain, ((v2_funct_1 @ sk_C)),
% 1.15/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.36  thf('133', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.36      inference('demod', [status(thm)], ['51', '52'])).
% 1.15/1.36  thf('134', plain,
% 1.15/1.36      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 1.15/1.36      inference('demod', [status(thm)],
% 1.15/1.36                ['127', '128', '129', '130', '131', '132', '133'])).
% 1.15/1.36  thf('135', plain,
% 1.15/1.36      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.15/1.36         (~ (v1_relat_1 @ X11)
% 1.15/1.36          | ((k5_relat_1 @ (k5_relat_1 @ X12 @ X11) @ X13)
% 1.15/1.36              = (k5_relat_1 @ X12 @ (k5_relat_1 @ X11 @ X13)))
% 1.15/1.36          | ~ (v1_relat_1 @ X13)
% 1.15/1.36          | ~ (v1_relat_1 @ X12))),
% 1.15/1.36      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.15/1.36  thf('136', plain,
% 1.15/1.36      (![X0 : $i]:
% 1.15/1.36         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.15/1.36            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.15/1.36          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.15/1.36          | ~ (v1_relat_1 @ X0)
% 1.15/1.36          | ~ (v1_relat_1 @ sk_C))),
% 1.15/1.36      inference('sup+', [status(thm)], ['134', '135'])).
% 1.15/1.36  thf('137', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.15/1.36      inference('demod', [status(thm)], ['123', '124'])).
% 1.15/1.36  thf('138', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.36      inference('demod', [status(thm)], ['51', '52'])).
% 1.15/1.36  thf('139', plain,
% 1.15/1.36      (![X0 : $i]:
% 1.15/1.36         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.15/1.36            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.15/1.36          | ~ (v1_relat_1 @ X0))),
% 1.15/1.36      inference('demod', [status(thm)], ['136', '137', '138'])).
% 1.15/1.36  thf('140', plain,
% 1.15/1.36      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 1.15/1.36          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 1.15/1.36        | ~ (v1_relat_1 @ sk_D))),
% 1.15/1.36      inference('sup+', [status(thm)], ['27', '139'])).
% 1.15/1.36  thf('141', plain,
% 1.15/1.36      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.15/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.36  thf('142', plain,
% 1.15/1.36      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.15/1.36         ((v4_relat_1 @ X25 @ X26)
% 1.15/1.36          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 1.15/1.36      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.15/1.36  thf('143', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 1.15/1.36      inference('sup-', [status(thm)], ['141', '142'])).
% 1.15/1.36  thf('144', plain,
% 1.15/1.36      (![X5 : $i, X6 : $i]:
% 1.15/1.36         (~ (v4_relat_1 @ X5 @ X6)
% 1.15/1.36          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 1.15/1.36          | ~ (v1_relat_1 @ X5))),
% 1.15/1.36      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.15/1.36  thf('145', plain,
% 1.15/1.36      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B))),
% 1.15/1.36      inference('sup-', [status(thm)], ['143', '144'])).
% 1.15/1.36  thf('146', plain,
% 1.15/1.36      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.15/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.36  thf('147', plain,
% 1.15/1.36      (![X3 : $i, X4 : $i]:
% 1.15/1.36         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 1.15/1.36          | (v1_relat_1 @ X3)
% 1.15/1.36          | ~ (v1_relat_1 @ X4))),
% 1.15/1.36      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.15/1.36  thf('148', plain,
% 1.15/1.36      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 1.15/1.36      inference('sup-', [status(thm)], ['146', '147'])).
% 1.15/1.36  thf('149', plain,
% 1.15/1.36      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 1.15/1.36      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.15/1.36  thf('150', plain, ((v1_relat_1 @ sk_D)),
% 1.15/1.36      inference('demod', [status(thm)], ['148', '149'])).
% 1.15/1.36  thf('151', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 1.15/1.36      inference('demod', [status(thm)], ['145', '150'])).
% 1.15/1.36  thf('152', plain,
% 1.15/1.36      (![X14 : $i, X15 : $i]:
% 1.15/1.36         (~ (r1_tarski @ (k1_relat_1 @ X14) @ X15)
% 1.15/1.36          | ((k5_relat_1 @ (k6_partfun1 @ X15) @ X14) = (X14))
% 1.15/1.36          | ~ (v1_relat_1 @ X14))),
% 1.15/1.36      inference('demod', [status(thm)], ['73', '74'])).
% 1.15/1.36  thf('153', plain,
% 1.15/1.36      ((~ (v1_relat_1 @ sk_D)
% 1.15/1.36        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D)))),
% 1.15/1.36      inference('sup-', [status(thm)], ['151', '152'])).
% 1.15/1.36  thf('154', plain, ((v1_relat_1 @ sk_D)),
% 1.15/1.36      inference('demod', [status(thm)], ['148', '149'])).
% 1.15/1.36  thf('155', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))),
% 1.15/1.36      inference('demod', [status(thm)], ['153', '154'])).
% 1.15/1.36  thf('156', plain,
% 1.15/1.36      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.15/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.36  thf('157', plain,
% 1.15/1.36      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.15/1.36         ((v4_relat_1 @ X25 @ X26)
% 1.15/1.36          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 1.15/1.36      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.15/1.36  thf('158', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 1.15/1.36      inference('sup-', [status(thm)], ['156', '157'])).
% 1.15/1.36  thf('159', plain,
% 1.15/1.36      (![X5 : $i, X6 : $i]:
% 1.15/1.36         (~ (v4_relat_1 @ X5 @ X6)
% 1.15/1.36          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 1.15/1.36          | ~ (v1_relat_1 @ X5))),
% 1.15/1.36      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.15/1.36  thf('160', plain,
% 1.15/1.36      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 1.15/1.36      inference('sup-', [status(thm)], ['158', '159'])).
% 1.15/1.36  thf('161', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.36      inference('demod', [status(thm)], ['51', '52'])).
% 1.15/1.36  thf('162', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 1.15/1.36      inference('demod', [status(thm)], ['160', '161'])).
% 1.15/1.36  thf('163', plain,
% 1.15/1.36      (![X23 : $i]:
% 1.15/1.36         (~ (v2_funct_1 @ X23)
% 1.15/1.36          | ((k1_relat_1 @ X23) = (k2_relat_1 @ (k2_funct_1 @ X23)))
% 1.15/1.36          | ~ (v1_funct_1 @ X23)
% 1.15/1.36          | ~ (v1_relat_1 @ X23))),
% 1.15/1.36      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.15/1.36  thf(t79_relat_1, axiom,
% 1.15/1.36    (![A:$i,B:$i]:
% 1.15/1.36     ( ( v1_relat_1 @ B ) =>
% 1.15/1.36       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 1.15/1.36         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 1.15/1.36  thf('164', plain,
% 1.15/1.36      (![X16 : $i, X17 : $i]:
% 1.15/1.36         (~ (r1_tarski @ (k2_relat_1 @ X16) @ X17)
% 1.15/1.36          | ((k5_relat_1 @ X16 @ (k6_relat_1 @ X17)) = (X16))
% 1.15/1.36          | ~ (v1_relat_1 @ X16))),
% 1.15/1.36      inference('cnf', [status(esa)], [t79_relat_1])).
% 1.15/1.36  thf('165', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 1.15/1.36      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.15/1.36  thf('166', plain,
% 1.15/1.36      (![X16 : $i, X17 : $i]:
% 1.15/1.36         (~ (r1_tarski @ (k2_relat_1 @ X16) @ X17)
% 1.15/1.36          | ((k5_relat_1 @ X16 @ (k6_partfun1 @ X17)) = (X16))
% 1.15/1.36          | ~ (v1_relat_1 @ X16))),
% 1.15/1.36      inference('demod', [status(thm)], ['164', '165'])).
% 1.15/1.36  thf('167', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i]:
% 1.15/1.36         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 1.15/1.36          | ~ (v1_relat_1 @ X0)
% 1.15/1.36          | ~ (v1_funct_1 @ X0)
% 1.15/1.36          | ~ (v2_funct_1 @ X0)
% 1.15/1.36          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.15/1.36          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ X1))
% 1.15/1.36              = (k2_funct_1 @ X0)))),
% 1.15/1.36      inference('sup-', [status(thm)], ['163', '166'])).
% 1.15/1.36  thf('168', plain,
% 1.15/1.36      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 1.15/1.36          = (k2_funct_1 @ sk_C))
% 1.15/1.36        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.15/1.36        | ~ (v2_funct_1 @ sk_C)
% 1.15/1.36        | ~ (v1_funct_1 @ sk_C)
% 1.15/1.36        | ~ (v1_relat_1 @ sk_C))),
% 1.15/1.36      inference('sup-', [status(thm)], ['162', '167'])).
% 1.15/1.36  thf('169', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.15/1.36      inference('demod', [status(thm)], ['123', '124'])).
% 1.15/1.36  thf('170', plain, ((v2_funct_1 @ sk_C)),
% 1.15/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.36  thf('171', plain, ((v1_funct_1 @ sk_C)),
% 1.15/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.36  thf('172', plain, ((v1_relat_1 @ sk_C)),
% 1.15/1.36      inference('demod', [status(thm)], ['51', '52'])).
% 1.15/1.36  thf('173', plain,
% 1.15/1.36      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 1.15/1.36         = (k2_funct_1 @ sk_C))),
% 1.15/1.36      inference('demod', [status(thm)], ['168', '169', '170', '171', '172'])).
% 1.15/1.36  thf('174', plain, ((v1_relat_1 @ sk_D)),
% 1.15/1.36      inference('demod', [status(thm)], ['148', '149'])).
% 1.15/1.36  thf('175', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 1.15/1.36      inference('demod', [status(thm)], ['140', '155', '173', '174'])).
% 1.15/1.36  thf('176', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.15/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.36  thf('177', plain, ($false),
% 1.15/1.36      inference('simplify_reflect-', [status(thm)], ['175', '176'])).
% 1.15/1.36  
% 1.15/1.36  % SZS output end Refutation
% 1.15/1.36  
% 1.15/1.37  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

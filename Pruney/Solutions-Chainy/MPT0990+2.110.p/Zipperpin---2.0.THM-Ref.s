%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FL6RDx4MQs

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:13 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :  212 ( 808 expanded)
%              Number of leaves         :   44 ( 267 expanded)
%              Depth                    :   29
%              Number of atoms          : 1712 (14648 expanded)
%              Number of equality atoms :   79 ( 914 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

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
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( ( k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46 )
        = ( k5_relat_1 @ X43 @ X46 ) ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X40 ) ) ) ) ),
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

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('24',plain,(
    ! [X42: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('25',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('26',plain,(
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X24 ) @ X24 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('27',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X24 ) @ X24 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('29',plain,(
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

thf('30',plain,(
    ! [X23: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k2_relat_1 @ X23 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('31',plain,(
    ! [X18: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('33',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('34',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X18: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('38',plain,(
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

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('40',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['39'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('41',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ( v4_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['36','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('48',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('50',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['46','51','52','53'])).

thf('55',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('56',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['31','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('59',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('62',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['30','62'])).

thf('64',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['34','35'])).

thf('65',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('66',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('67',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['63','64','65','66','67','68'])).

thf('70',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['39'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('71',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X14 ) @ X15 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X15 ) @ X14 )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('72',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('73',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X14 ) @ X15 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X15 ) @ X14 )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['69','74'])).

thf('76',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['29','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('78',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('80',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) @ X13 )
        = ( k5_relat_1 @ X12 @ ( k5_relat_1 @ X11 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X42: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('83',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['81','86'])).

thf('88',plain,(
    ! [X18: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('89',plain,(
    ! [X18: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('90',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['63','64','65','66','67','68'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('91',plain,(
    ! [X50: $i] :
      ( ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) ) ) )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('92',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf('94',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('95',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['88','96'])).

thf('98',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('99',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('102',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('104',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['87','104'])).

thf('106',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['28','105'])).

thf('107',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['34','35'])).

thf('108',plain,(
    ! [X42: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('109',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('110',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k6_partfun1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('114',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k6_partfun1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X14 ) @ X15 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X15 ) @ X14 )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('120',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('123',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['106','107','118','119','120','121','122'])).

thf('124',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) @ X13 )
        = ( k5_relat_1 @ X12 @ ( k5_relat_1 @ X11 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('127',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['125','126','127'])).

thf('129',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['25','128'])).

thf('130',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('132',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('134',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('137',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('139',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['134','139'])).

thf('141',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X14 ) @ X15 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X15 ) @ X14 )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('142',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = sk_D ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['137','138'])).

thf('144',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('147',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('149',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('151',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,(
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

thf('153',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X16 ) @ X17 )
      | ( ( k5_relat_1 @ X16 @ ( k6_relat_1 @ X17 ) )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('154',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('155',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X16 ) @ X17 )
      | ( ( k5_relat_1 @ X16 @ ( k6_partfun1 @ X17 ) )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ X1 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['152','155'])).

thf('157',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['151','156'])).

thf('158',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('159',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('162',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['157','158','159','160','161'])).

thf('163',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['137','138'])).

thf('164',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['129','144','162','163'])).

thf('165',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['164','165'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FL6RDx4MQs
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:01:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 1.05/1.24  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.05/1.24  % Solved by: fo/fo7.sh
% 1.05/1.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.05/1.24  % done 1273 iterations in 0.785s
% 1.05/1.24  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.05/1.24  % SZS output start Refutation
% 1.05/1.24  thf(sk_B_type, type, sk_B: $i).
% 1.05/1.24  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.05/1.24  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.05/1.24  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.05/1.24  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.05/1.24  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.05/1.24  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.05/1.24  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.05/1.24  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.05/1.24  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.05/1.24  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.05/1.24  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.05/1.24  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.05/1.24  thf(sk_A_type, type, sk_A: $i).
% 1.05/1.24  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.05/1.24  thf(sk_D_type, type, sk_D: $i).
% 1.05/1.24  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.05/1.24  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.05/1.24  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.05/1.24  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.05/1.24  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.05/1.24  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.05/1.24  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.05/1.24  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.05/1.24  thf(sk_C_type, type, sk_C: $i).
% 1.05/1.24  thf(t36_funct_2, conjecture,
% 1.05/1.24    (![A:$i,B:$i,C:$i]:
% 1.05/1.24     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.05/1.24         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.05/1.24       ( ![D:$i]:
% 1.05/1.24         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.05/1.24             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.05/1.24           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.05/1.24               ( r2_relset_1 @
% 1.05/1.24                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.05/1.24                 ( k6_partfun1 @ A ) ) & 
% 1.05/1.24               ( v2_funct_1 @ C ) ) =>
% 1.05/1.24             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.05/1.24               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.05/1.24  thf(zf_stmt_0, negated_conjecture,
% 1.05/1.24    (~( ![A:$i,B:$i,C:$i]:
% 1.05/1.24        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.05/1.24            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.05/1.24          ( ![D:$i]:
% 1.05/1.24            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.05/1.24                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.05/1.24              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.05/1.24                  ( r2_relset_1 @
% 1.05/1.24                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.05/1.24                    ( k6_partfun1 @ A ) ) & 
% 1.05/1.24                  ( v2_funct_1 @ C ) ) =>
% 1.05/1.24                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.05/1.24                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.05/1.24    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.05/1.24  thf('0', plain,
% 1.05/1.24      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.05/1.24        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.05/1.24        (k6_partfun1 @ sk_A))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('1', plain,
% 1.05/1.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('2', plain,
% 1.05/1.24      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf(redefinition_k1_partfun1, axiom,
% 1.05/1.24    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.05/1.24     ( ( ( v1_funct_1 @ E ) & 
% 1.05/1.24         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.05/1.24         ( v1_funct_1 @ F ) & 
% 1.05/1.24         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.05/1.24       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.05/1.24  thf('3', plain,
% 1.05/1.24      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 1.05/1.24         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 1.05/1.24          | ~ (v1_funct_1 @ X43)
% 1.05/1.24          | ~ (v1_funct_1 @ X46)
% 1.05/1.24          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 1.05/1.24          | ((k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46)
% 1.05/1.24              = (k5_relat_1 @ X43 @ X46)))),
% 1.05/1.24      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.05/1.24  thf('4', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.24         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.05/1.24            = (k5_relat_1 @ sk_C @ X0))
% 1.05/1.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.05/1.24          | ~ (v1_funct_1 @ X0)
% 1.05/1.24          | ~ (v1_funct_1 @ sk_C))),
% 1.05/1.24      inference('sup-', [status(thm)], ['2', '3'])).
% 1.05/1.24  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('6', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.24         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.05/1.24            = (k5_relat_1 @ sk_C @ X0))
% 1.05/1.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.05/1.24          | ~ (v1_funct_1 @ X0))),
% 1.05/1.24      inference('demod', [status(thm)], ['4', '5'])).
% 1.05/1.24  thf('7', plain,
% 1.05/1.24      ((~ (v1_funct_1 @ sk_D)
% 1.05/1.24        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.05/1.24            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.05/1.24      inference('sup-', [status(thm)], ['1', '6'])).
% 1.05/1.24  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('9', plain,
% 1.05/1.24      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.05/1.24         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.05/1.24      inference('demod', [status(thm)], ['7', '8'])).
% 1.05/1.24  thf('10', plain,
% 1.05/1.24      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.05/1.24        (k6_partfun1 @ sk_A))),
% 1.05/1.24      inference('demod', [status(thm)], ['0', '9'])).
% 1.05/1.24  thf('11', plain,
% 1.05/1.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('12', plain,
% 1.05/1.24      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf(dt_k1_partfun1, axiom,
% 1.05/1.24    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.05/1.24     ( ( ( v1_funct_1 @ E ) & 
% 1.05/1.24         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.05/1.24         ( v1_funct_1 @ F ) & 
% 1.05/1.24         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.05/1.24       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.05/1.24         ( m1_subset_1 @
% 1.05/1.24           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.05/1.24           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.05/1.24  thf('13', plain,
% 1.05/1.24      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.05/1.24         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 1.05/1.24          | ~ (v1_funct_1 @ X35)
% 1.05/1.24          | ~ (v1_funct_1 @ X38)
% 1.05/1.24          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 1.05/1.24          | (m1_subset_1 @ (k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38) @ 
% 1.05/1.24             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X40))))),
% 1.05/1.24      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.05/1.24  thf('14', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.24         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.05/1.24           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.05/1.24          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.05/1.24          | ~ (v1_funct_1 @ X1)
% 1.05/1.24          | ~ (v1_funct_1 @ sk_C))),
% 1.05/1.24      inference('sup-', [status(thm)], ['12', '13'])).
% 1.05/1.24  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('16', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.24         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.05/1.24           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.05/1.24          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.05/1.24          | ~ (v1_funct_1 @ X1))),
% 1.05/1.24      inference('demod', [status(thm)], ['14', '15'])).
% 1.05/1.24  thf('17', plain,
% 1.05/1.24      ((~ (v1_funct_1 @ sk_D)
% 1.05/1.24        | (m1_subset_1 @ 
% 1.05/1.24           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.05/1.24           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.05/1.24      inference('sup-', [status(thm)], ['11', '16'])).
% 1.05/1.24  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('19', plain,
% 1.05/1.24      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.05/1.24         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.05/1.24      inference('demod', [status(thm)], ['7', '8'])).
% 1.05/1.24  thf('20', plain,
% 1.05/1.24      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.05/1.24        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.05/1.24      inference('demod', [status(thm)], ['17', '18', '19'])).
% 1.05/1.24  thf(redefinition_r2_relset_1, axiom,
% 1.05/1.24    (![A:$i,B:$i,C:$i,D:$i]:
% 1.05/1.24     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.05/1.24         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.05/1.24       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.05/1.24  thf('21', plain,
% 1.05/1.24      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.05/1.24         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.05/1.24          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.05/1.24          | ((X31) = (X34))
% 1.05/1.24          | ~ (r2_relset_1 @ X32 @ X33 @ X31 @ X34))),
% 1.05/1.24      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.05/1.24  thf('22', plain,
% 1.05/1.24      (![X0 : $i]:
% 1.05/1.24         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 1.05/1.24          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 1.05/1.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.05/1.24      inference('sup-', [status(thm)], ['20', '21'])).
% 1.05/1.24  thf('23', plain,
% 1.05/1.24      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.05/1.24           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.05/1.24        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 1.05/1.24      inference('sup-', [status(thm)], ['10', '22'])).
% 1.05/1.24  thf(dt_k6_partfun1, axiom,
% 1.05/1.24    (![A:$i]:
% 1.05/1.24     ( ( m1_subset_1 @
% 1.05/1.24         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 1.05/1.24       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 1.05/1.24  thf('24', plain,
% 1.05/1.24      (![X42 : $i]:
% 1.05/1.24         (m1_subset_1 @ (k6_partfun1 @ X42) @ 
% 1.05/1.24          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X42)))),
% 1.05/1.24      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.05/1.24  thf('25', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.05/1.24      inference('demod', [status(thm)], ['23', '24'])).
% 1.05/1.24  thf(t61_funct_1, axiom,
% 1.05/1.24    (![A:$i]:
% 1.05/1.24     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.05/1.24       ( ( v2_funct_1 @ A ) =>
% 1.05/1.24         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.05/1.24             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.05/1.24           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.05/1.24             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.05/1.24  thf('26', plain,
% 1.05/1.24      (![X24 : $i]:
% 1.05/1.24         (~ (v2_funct_1 @ X24)
% 1.05/1.24          | ((k5_relat_1 @ (k2_funct_1 @ X24) @ X24)
% 1.05/1.24              = (k6_relat_1 @ (k2_relat_1 @ X24)))
% 1.05/1.24          | ~ (v1_funct_1 @ X24)
% 1.05/1.24          | ~ (v1_relat_1 @ X24))),
% 1.05/1.24      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.05/1.24  thf(redefinition_k6_partfun1, axiom,
% 1.05/1.24    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.05/1.24  thf('27', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 1.05/1.24      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.05/1.24  thf('28', plain,
% 1.05/1.24      (![X24 : $i]:
% 1.05/1.24         (~ (v2_funct_1 @ X24)
% 1.05/1.24          | ((k5_relat_1 @ (k2_funct_1 @ X24) @ X24)
% 1.05/1.24              = (k6_partfun1 @ (k2_relat_1 @ X24)))
% 1.05/1.24          | ~ (v1_funct_1 @ X24)
% 1.05/1.24          | ~ (v1_relat_1 @ X24))),
% 1.05/1.24      inference('demod', [status(thm)], ['26', '27'])).
% 1.05/1.24  thf(dt_k2_funct_1, axiom,
% 1.05/1.24    (![A:$i]:
% 1.05/1.24     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.05/1.24       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.05/1.24         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.05/1.24  thf('29', plain,
% 1.05/1.24      (![X18 : $i]:
% 1.05/1.24         ((v1_relat_1 @ (k2_funct_1 @ X18))
% 1.05/1.24          | ~ (v1_funct_1 @ X18)
% 1.05/1.24          | ~ (v1_relat_1 @ X18))),
% 1.05/1.24      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.05/1.24  thf(t55_funct_1, axiom,
% 1.05/1.24    (![A:$i]:
% 1.05/1.24     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.05/1.24       ( ( v2_funct_1 @ A ) =>
% 1.05/1.24         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.05/1.24           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.05/1.24  thf('30', plain,
% 1.05/1.24      (![X23 : $i]:
% 1.05/1.24         (~ (v2_funct_1 @ X23)
% 1.05/1.24          | ((k2_relat_1 @ X23) = (k1_relat_1 @ (k2_funct_1 @ X23)))
% 1.05/1.24          | ~ (v1_funct_1 @ X23)
% 1.05/1.24          | ~ (v1_relat_1 @ X23))),
% 1.05/1.24      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.05/1.24  thf('31', plain,
% 1.05/1.24      (![X18 : $i]:
% 1.05/1.24         ((v1_relat_1 @ (k2_funct_1 @ X18))
% 1.05/1.24          | ~ (v1_funct_1 @ X18)
% 1.05/1.24          | ~ (v1_relat_1 @ X18))),
% 1.05/1.24      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.05/1.24  thf('32', plain,
% 1.05/1.24      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf(redefinition_k2_relset_1, axiom,
% 1.05/1.24    (![A:$i,B:$i,C:$i]:
% 1.05/1.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.24       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.05/1.24  thf('33', plain,
% 1.05/1.24      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.05/1.24         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 1.05/1.24          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 1.05/1.24      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.05/1.24  thf('34', plain,
% 1.05/1.24      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.05/1.24      inference('sup-', [status(thm)], ['32', '33'])).
% 1.05/1.24  thf('35', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('36', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.05/1.24      inference('sup+', [status(thm)], ['34', '35'])).
% 1.05/1.24  thf('37', plain,
% 1.05/1.24      (![X18 : $i]:
% 1.05/1.24         ((v1_relat_1 @ (k2_funct_1 @ X18))
% 1.05/1.24          | ~ (v1_funct_1 @ X18)
% 1.05/1.24          | ~ (v1_relat_1 @ X18))),
% 1.05/1.24      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.05/1.24  thf('38', plain,
% 1.05/1.24      (![X23 : $i]:
% 1.05/1.24         (~ (v2_funct_1 @ X23)
% 1.05/1.24          | ((k2_relat_1 @ X23) = (k1_relat_1 @ (k2_funct_1 @ X23)))
% 1.05/1.24          | ~ (v1_funct_1 @ X23)
% 1.05/1.24          | ~ (v1_relat_1 @ X23))),
% 1.05/1.24      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.05/1.24  thf(d10_xboole_0, axiom,
% 1.05/1.24    (![A:$i,B:$i]:
% 1.05/1.24     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.05/1.24  thf('39', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.05/1.24      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.05/1.24  thf('40', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.05/1.24      inference('simplify', [status(thm)], ['39'])).
% 1.05/1.24  thf(d18_relat_1, axiom,
% 1.05/1.24    (![A:$i,B:$i]:
% 1.05/1.24     ( ( v1_relat_1 @ B ) =>
% 1.05/1.24       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.05/1.24  thf('41', plain,
% 1.05/1.24      (![X5 : $i, X6 : $i]:
% 1.05/1.24         (~ (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 1.05/1.24          | (v4_relat_1 @ X5 @ X6)
% 1.05/1.24          | ~ (v1_relat_1 @ X5))),
% 1.05/1.24      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.05/1.24  thf('42', plain,
% 1.05/1.24      (![X0 : $i]:
% 1.05/1.24         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 1.05/1.24      inference('sup-', [status(thm)], ['40', '41'])).
% 1.05/1.24  thf('43', plain,
% 1.05/1.24      (![X0 : $i]:
% 1.05/1.24         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.05/1.24          | ~ (v1_relat_1 @ X0)
% 1.05/1.24          | ~ (v1_funct_1 @ X0)
% 1.05/1.24          | ~ (v2_funct_1 @ X0)
% 1.05/1.24          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.05/1.24      inference('sup+', [status(thm)], ['38', '42'])).
% 1.05/1.24  thf('44', plain,
% 1.05/1.24      (![X0 : $i]:
% 1.05/1.24         (~ (v1_relat_1 @ X0)
% 1.05/1.24          | ~ (v1_funct_1 @ X0)
% 1.05/1.24          | ~ (v2_funct_1 @ X0)
% 1.05/1.24          | ~ (v1_funct_1 @ X0)
% 1.05/1.24          | ~ (v1_relat_1 @ X0)
% 1.05/1.24          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 1.05/1.24      inference('sup-', [status(thm)], ['37', '43'])).
% 1.05/1.24  thf('45', plain,
% 1.05/1.24      (![X0 : $i]:
% 1.05/1.24         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.05/1.24          | ~ (v2_funct_1 @ X0)
% 1.05/1.24          | ~ (v1_funct_1 @ X0)
% 1.05/1.24          | ~ (v1_relat_1 @ X0))),
% 1.05/1.24      inference('simplify', [status(thm)], ['44'])).
% 1.05/1.24  thf('46', plain,
% 1.05/1.24      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)
% 1.05/1.24        | ~ (v1_relat_1 @ sk_C)
% 1.05/1.24        | ~ (v1_funct_1 @ sk_C)
% 1.05/1.24        | ~ (v2_funct_1 @ sk_C))),
% 1.05/1.24      inference('sup+', [status(thm)], ['36', '45'])).
% 1.05/1.24  thf('47', plain,
% 1.05/1.24      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf(cc2_relat_1, axiom,
% 1.05/1.24    (![A:$i]:
% 1.05/1.24     ( ( v1_relat_1 @ A ) =>
% 1.05/1.24       ( ![B:$i]:
% 1.05/1.24         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.05/1.24  thf('48', plain,
% 1.05/1.24      (![X3 : $i, X4 : $i]:
% 1.05/1.24         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 1.05/1.24          | (v1_relat_1 @ X3)
% 1.05/1.24          | ~ (v1_relat_1 @ X4))),
% 1.05/1.24      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.05/1.24  thf('49', plain,
% 1.05/1.24      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 1.05/1.24      inference('sup-', [status(thm)], ['47', '48'])).
% 1.05/1.24  thf(fc6_relat_1, axiom,
% 1.05/1.24    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.05/1.24  thf('50', plain,
% 1.05/1.24      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 1.05/1.24      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.05/1.24  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 1.05/1.24      inference('demod', [status(thm)], ['49', '50'])).
% 1.05/1.24  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('53', plain, ((v2_funct_1 @ sk_C)),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('54', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)),
% 1.05/1.24      inference('demod', [status(thm)], ['46', '51', '52', '53'])).
% 1.05/1.24  thf('55', plain,
% 1.05/1.24      (![X5 : $i, X6 : $i]:
% 1.05/1.24         (~ (v4_relat_1 @ X5 @ X6)
% 1.05/1.24          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 1.05/1.24          | ~ (v1_relat_1 @ X5))),
% 1.05/1.24      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.05/1.24  thf('56', plain,
% 1.05/1.24      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.05/1.24        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 1.05/1.24      inference('sup-', [status(thm)], ['54', '55'])).
% 1.05/1.24  thf('57', plain,
% 1.05/1.24      ((~ (v1_relat_1 @ sk_C)
% 1.05/1.24        | ~ (v1_funct_1 @ sk_C)
% 1.05/1.24        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 1.05/1.24      inference('sup-', [status(thm)], ['31', '56'])).
% 1.05/1.24  thf('58', plain, ((v1_relat_1 @ sk_C)),
% 1.05/1.24      inference('demod', [status(thm)], ['49', '50'])).
% 1.05/1.24  thf('59', plain, ((v1_funct_1 @ sk_C)),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('60', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B)),
% 1.05/1.24      inference('demod', [status(thm)], ['57', '58', '59'])).
% 1.05/1.24  thf('61', plain,
% 1.05/1.24      (![X0 : $i, X2 : $i]:
% 1.05/1.24         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.05/1.24      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.05/1.24  thf('62', plain,
% 1.05/1.24      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.05/1.24        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.05/1.24      inference('sup-', [status(thm)], ['60', '61'])).
% 1.05/1.24  thf('63', plain,
% 1.05/1.24      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C))
% 1.05/1.24        | ~ (v1_relat_1 @ sk_C)
% 1.05/1.24        | ~ (v1_funct_1 @ sk_C)
% 1.05/1.24        | ~ (v2_funct_1 @ sk_C)
% 1.05/1.24        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.05/1.24      inference('sup-', [status(thm)], ['30', '62'])).
% 1.05/1.24  thf('64', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.05/1.24      inference('sup+', [status(thm)], ['34', '35'])).
% 1.05/1.24  thf('65', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.05/1.24      inference('simplify', [status(thm)], ['39'])).
% 1.05/1.24  thf('66', plain, ((v1_relat_1 @ sk_C)),
% 1.05/1.24      inference('demod', [status(thm)], ['49', '50'])).
% 1.05/1.24  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('68', plain, ((v2_funct_1 @ sk_C)),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('69', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.05/1.24      inference('demod', [status(thm)], ['63', '64', '65', '66', '67', '68'])).
% 1.05/1.24  thf('70', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.05/1.24      inference('simplify', [status(thm)], ['39'])).
% 1.05/1.24  thf(t77_relat_1, axiom,
% 1.05/1.24    (![A:$i,B:$i]:
% 1.05/1.24     ( ( v1_relat_1 @ B ) =>
% 1.05/1.24       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 1.05/1.24         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 1.05/1.24  thf('71', plain,
% 1.05/1.24      (![X14 : $i, X15 : $i]:
% 1.05/1.24         (~ (r1_tarski @ (k1_relat_1 @ X14) @ X15)
% 1.05/1.24          | ((k5_relat_1 @ (k6_relat_1 @ X15) @ X14) = (X14))
% 1.05/1.24          | ~ (v1_relat_1 @ X14))),
% 1.05/1.24      inference('cnf', [status(esa)], [t77_relat_1])).
% 1.05/1.24  thf('72', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 1.05/1.24      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.05/1.24  thf('73', plain,
% 1.05/1.24      (![X14 : $i, X15 : $i]:
% 1.05/1.24         (~ (r1_tarski @ (k1_relat_1 @ X14) @ X15)
% 1.05/1.24          | ((k5_relat_1 @ (k6_partfun1 @ X15) @ X14) = (X14))
% 1.05/1.24          | ~ (v1_relat_1 @ X14))),
% 1.05/1.24      inference('demod', [status(thm)], ['71', '72'])).
% 1.05/1.24  thf('74', plain,
% 1.05/1.24      (![X0 : $i]:
% 1.05/1.24         (~ (v1_relat_1 @ X0)
% 1.05/1.24          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 1.05/1.24      inference('sup-', [status(thm)], ['70', '73'])).
% 1.05/1.24  thf('75', plain,
% 1.05/1.24      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.05/1.24          = (k2_funct_1 @ sk_C))
% 1.05/1.24        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.05/1.24      inference('sup+', [status(thm)], ['69', '74'])).
% 1.05/1.24  thf('76', plain,
% 1.05/1.24      ((~ (v1_relat_1 @ sk_C)
% 1.05/1.24        | ~ (v1_funct_1 @ sk_C)
% 1.05/1.24        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.05/1.24            = (k2_funct_1 @ sk_C)))),
% 1.05/1.24      inference('sup-', [status(thm)], ['29', '75'])).
% 1.05/1.24  thf('77', plain, ((v1_relat_1 @ sk_C)),
% 1.05/1.24      inference('demod', [status(thm)], ['49', '50'])).
% 1.05/1.24  thf('78', plain, ((v1_funct_1 @ sk_C)),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('79', plain,
% 1.05/1.24      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.05/1.24         = (k2_funct_1 @ sk_C))),
% 1.05/1.24      inference('demod', [status(thm)], ['76', '77', '78'])).
% 1.05/1.24  thf(t55_relat_1, axiom,
% 1.05/1.24    (![A:$i]:
% 1.05/1.24     ( ( v1_relat_1 @ A ) =>
% 1.05/1.24       ( ![B:$i]:
% 1.05/1.24         ( ( v1_relat_1 @ B ) =>
% 1.05/1.24           ( ![C:$i]:
% 1.05/1.24             ( ( v1_relat_1 @ C ) =>
% 1.05/1.24               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 1.05/1.24                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 1.05/1.24  thf('80', plain,
% 1.05/1.24      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.05/1.24         (~ (v1_relat_1 @ X11)
% 1.05/1.24          | ((k5_relat_1 @ (k5_relat_1 @ X12 @ X11) @ X13)
% 1.05/1.24              = (k5_relat_1 @ X12 @ (k5_relat_1 @ X11 @ X13)))
% 1.05/1.24          | ~ (v1_relat_1 @ X13)
% 1.05/1.24          | ~ (v1_relat_1 @ X12))),
% 1.05/1.24      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.05/1.24  thf('81', plain,
% 1.05/1.24      (![X0 : $i]:
% 1.05/1.24         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 1.05/1.24            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.05/1.24               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 1.05/1.24          | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B))
% 1.05/1.24          | ~ (v1_relat_1 @ X0)
% 1.05/1.24          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.05/1.24      inference('sup+', [status(thm)], ['79', '80'])).
% 1.05/1.24  thf('82', plain,
% 1.05/1.24      (![X42 : $i]:
% 1.05/1.24         (m1_subset_1 @ (k6_partfun1 @ X42) @ 
% 1.05/1.24          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X42)))),
% 1.05/1.24      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.05/1.24  thf('83', plain,
% 1.05/1.24      (![X3 : $i, X4 : $i]:
% 1.05/1.24         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 1.05/1.24          | (v1_relat_1 @ X3)
% 1.05/1.24          | ~ (v1_relat_1 @ X4))),
% 1.05/1.24      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.05/1.24  thf('84', plain,
% 1.05/1.24      (![X0 : $i]:
% 1.05/1.24         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X0))
% 1.05/1.24          | (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 1.05/1.24      inference('sup-', [status(thm)], ['82', '83'])).
% 1.05/1.24  thf('85', plain,
% 1.05/1.24      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 1.05/1.24      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.05/1.24  thf('86', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.05/1.24      inference('demod', [status(thm)], ['84', '85'])).
% 1.05/1.24  thf('87', plain,
% 1.05/1.24      (![X0 : $i]:
% 1.05/1.24         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 1.05/1.24            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.05/1.24               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 1.05/1.24          | ~ (v1_relat_1 @ X0)
% 1.05/1.24          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.05/1.24      inference('demod', [status(thm)], ['81', '86'])).
% 1.05/1.24  thf('88', plain,
% 1.05/1.24      (![X18 : $i]:
% 1.05/1.24         ((v1_funct_1 @ (k2_funct_1 @ X18))
% 1.05/1.24          | ~ (v1_funct_1 @ X18)
% 1.05/1.24          | ~ (v1_relat_1 @ X18))),
% 1.05/1.24      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.05/1.24  thf('89', plain,
% 1.05/1.24      (![X18 : $i]:
% 1.05/1.24         ((v1_relat_1 @ (k2_funct_1 @ X18))
% 1.05/1.24          | ~ (v1_funct_1 @ X18)
% 1.05/1.24          | ~ (v1_relat_1 @ X18))),
% 1.05/1.24      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.05/1.24  thf('90', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.05/1.24      inference('demod', [status(thm)], ['63', '64', '65', '66', '67', '68'])).
% 1.05/1.24  thf(t3_funct_2, axiom,
% 1.05/1.24    (![A:$i]:
% 1.05/1.24     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.05/1.24       ( ( v1_funct_1 @ A ) & 
% 1.05/1.24         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.05/1.24         ( m1_subset_1 @
% 1.05/1.24           A @ 
% 1.05/1.24           ( k1_zfmisc_1 @
% 1.05/1.24             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.05/1.24  thf('91', plain,
% 1.05/1.24      (![X50 : $i]:
% 1.05/1.24         ((m1_subset_1 @ X50 @ 
% 1.05/1.24           (k1_zfmisc_1 @ 
% 1.05/1.24            (k2_zfmisc_1 @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50))))
% 1.05/1.24          | ~ (v1_funct_1 @ X50)
% 1.05/1.24          | ~ (v1_relat_1 @ X50))),
% 1.05/1.24      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.05/1.24  thf('92', plain,
% 1.05/1.24      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.05/1.24         (k1_zfmisc_1 @ 
% 1.05/1.24          (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))
% 1.05/1.24        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.05/1.24        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.05/1.24      inference('sup+', [status(thm)], ['90', '91'])).
% 1.05/1.24  thf('93', plain,
% 1.05/1.24      ((~ (v1_relat_1 @ sk_C)
% 1.05/1.24        | ~ (v1_funct_1 @ sk_C)
% 1.05/1.24        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.05/1.24        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.05/1.24           (k1_zfmisc_1 @ 
% 1.05/1.24            (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))))),
% 1.05/1.24      inference('sup-', [status(thm)], ['89', '92'])).
% 1.05/1.24  thf('94', plain, ((v1_relat_1 @ sk_C)),
% 1.05/1.24      inference('demod', [status(thm)], ['49', '50'])).
% 1.05/1.24  thf('95', plain, ((v1_funct_1 @ sk_C)),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('96', plain,
% 1.05/1.24      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.05/1.24        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.05/1.24           (k1_zfmisc_1 @ 
% 1.05/1.24            (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))))),
% 1.05/1.24      inference('demod', [status(thm)], ['93', '94', '95'])).
% 1.05/1.24  thf('97', plain,
% 1.05/1.24      ((~ (v1_relat_1 @ sk_C)
% 1.05/1.24        | ~ (v1_funct_1 @ sk_C)
% 1.05/1.24        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.05/1.24           (k1_zfmisc_1 @ 
% 1.05/1.24            (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))))),
% 1.05/1.24      inference('sup-', [status(thm)], ['88', '96'])).
% 1.05/1.24  thf('98', plain, ((v1_relat_1 @ sk_C)),
% 1.05/1.24      inference('demod', [status(thm)], ['49', '50'])).
% 1.05/1.24  thf('99', plain, ((v1_funct_1 @ sk_C)),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('100', plain,
% 1.05/1.24      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.05/1.24        (k1_zfmisc_1 @ 
% 1.05/1.24         (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 1.05/1.24      inference('demod', [status(thm)], ['97', '98', '99'])).
% 1.05/1.24  thf('101', plain,
% 1.05/1.24      (![X3 : $i, X4 : $i]:
% 1.05/1.24         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 1.05/1.24          | (v1_relat_1 @ X3)
% 1.05/1.24          | ~ (v1_relat_1 @ X4))),
% 1.05/1.24      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.05/1.24  thf('102', plain,
% 1.05/1.24      ((~ (v1_relat_1 @ 
% 1.05/1.24           (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 1.05/1.24        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.05/1.24      inference('sup-', [status(thm)], ['100', '101'])).
% 1.05/1.24  thf('103', plain,
% 1.05/1.24      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 1.05/1.24      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.05/1.24  thf('104', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.05/1.24      inference('demod', [status(thm)], ['102', '103'])).
% 1.05/1.24  thf('105', plain,
% 1.05/1.24      (![X0 : $i]:
% 1.05/1.24         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 1.05/1.24            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.05/1.24               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 1.05/1.24          | ~ (v1_relat_1 @ X0))),
% 1.05/1.24      inference('demod', [status(thm)], ['87', '104'])).
% 1.05/1.24  thf('106', plain,
% 1.05/1.24      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 1.05/1.24          = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.05/1.24             (k6_partfun1 @ (k2_relat_1 @ sk_C))))
% 1.05/1.24        | ~ (v1_relat_1 @ sk_C)
% 1.05/1.24        | ~ (v1_funct_1 @ sk_C)
% 1.05/1.24        | ~ (v2_funct_1 @ sk_C)
% 1.05/1.24        | ~ (v1_relat_1 @ sk_C))),
% 1.05/1.24      inference('sup+', [status(thm)], ['28', '105'])).
% 1.05/1.24  thf('107', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.05/1.24      inference('sup+', [status(thm)], ['34', '35'])).
% 1.05/1.24  thf('108', plain,
% 1.05/1.24      (![X42 : $i]:
% 1.05/1.24         (m1_subset_1 @ (k6_partfun1 @ X42) @ 
% 1.05/1.24          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X42)))),
% 1.05/1.24      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.05/1.24  thf(cc2_relset_1, axiom,
% 1.05/1.24    (![A:$i,B:$i,C:$i]:
% 1.05/1.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.24       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.05/1.24  thf('109', plain,
% 1.05/1.24      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.05/1.24         ((v4_relat_1 @ X25 @ X26)
% 1.05/1.24          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 1.05/1.24      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.05/1.24  thf('110', plain, (![X0 : $i]: (v4_relat_1 @ (k6_partfun1 @ X0) @ X0)),
% 1.05/1.24      inference('sup-', [status(thm)], ['108', '109'])).
% 1.05/1.24  thf('111', plain,
% 1.05/1.24      (![X5 : $i, X6 : $i]:
% 1.05/1.24         (~ (v4_relat_1 @ X5 @ X6)
% 1.05/1.24          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 1.05/1.24          | ~ (v1_relat_1 @ X5))),
% 1.05/1.24      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.05/1.24  thf('112', plain,
% 1.05/1.24      (![X0 : $i]:
% 1.05/1.24         (~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 1.05/1.24          | (r1_tarski @ (k1_relat_1 @ (k6_partfun1 @ X0)) @ X0))),
% 1.05/1.24      inference('sup-', [status(thm)], ['110', '111'])).
% 1.05/1.24  thf('113', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.05/1.24      inference('demod', [status(thm)], ['84', '85'])).
% 1.05/1.24  thf('114', plain,
% 1.05/1.24      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ (k6_partfun1 @ X0)) @ X0)),
% 1.05/1.24      inference('demod', [status(thm)], ['112', '113'])).
% 1.05/1.24  thf('115', plain,
% 1.05/1.24      (![X14 : $i, X15 : $i]:
% 1.05/1.24         (~ (r1_tarski @ (k1_relat_1 @ X14) @ X15)
% 1.05/1.24          | ((k5_relat_1 @ (k6_partfun1 @ X15) @ X14) = (X14))
% 1.05/1.24          | ~ (v1_relat_1 @ X14))),
% 1.05/1.24      inference('demod', [status(thm)], ['71', '72'])).
% 1.05/1.24  thf('116', plain,
% 1.05/1.24      (![X0 : $i]:
% 1.05/1.24         (~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 1.05/1.24          | ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 1.05/1.24              = (k6_partfun1 @ X0)))),
% 1.05/1.24      inference('sup-', [status(thm)], ['114', '115'])).
% 1.05/1.24  thf('117', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.05/1.24      inference('demod', [status(thm)], ['84', '85'])).
% 1.05/1.24  thf('118', plain,
% 1.05/1.24      (![X0 : $i]:
% 1.05/1.24         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 1.05/1.24           = (k6_partfun1 @ X0))),
% 1.05/1.24      inference('demod', [status(thm)], ['116', '117'])).
% 1.05/1.24  thf('119', plain, ((v1_relat_1 @ sk_C)),
% 1.05/1.24      inference('demod', [status(thm)], ['49', '50'])).
% 1.05/1.24  thf('120', plain, ((v1_funct_1 @ sk_C)),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('121', plain, ((v2_funct_1 @ sk_C)),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('122', plain, ((v1_relat_1 @ sk_C)),
% 1.05/1.24      inference('demod', [status(thm)], ['49', '50'])).
% 1.05/1.24  thf('123', plain,
% 1.05/1.24      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 1.05/1.24      inference('demod', [status(thm)],
% 1.05/1.24                ['106', '107', '118', '119', '120', '121', '122'])).
% 1.05/1.24  thf('124', plain,
% 1.05/1.24      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.05/1.24         (~ (v1_relat_1 @ X11)
% 1.05/1.24          | ((k5_relat_1 @ (k5_relat_1 @ X12 @ X11) @ X13)
% 1.05/1.24              = (k5_relat_1 @ X12 @ (k5_relat_1 @ X11 @ X13)))
% 1.05/1.24          | ~ (v1_relat_1 @ X13)
% 1.05/1.24          | ~ (v1_relat_1 @ X12))),
% 1.05/1.24      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.05/1.24  thf('125', plain,
% 1.05/1.24      (![X0 : $i]:
% 1.05/1.24         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.05/1.24            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.05/1.24          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.05/1.24          | ~ (v1_relat_1 @ X0)
% 1.05/1.24          | ~ (v1_relat_1 @ sk_C))),
% 1.05/1.24      inference('sup+', [status(thm)], ['123', '124'])).
% 1.05/1.24  thf('126', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.05/1.24      inference('demod', [status(thm)], ['102', '103'])).
% 1.05/1.24  thf('127', plain, ((v1_relat_1 @ sk_C)),
% 1.05/1.24      inference('demod', [status(thm)], ['49', '50'])).
% 1.05/1.24  thf('128', plain,
% 1.05/1.24      (![X0 : $i]:
% 1.05/1.24         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.05/1.24            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.05/1.24          | ~ (v1_relat_1 @ X0))),
% 1.05/1.24      inference('demod', [status(thm)], ['125', '126', '127'])).
% 1.05/1.24  thf('129', plain,
% 1.05/1.24      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 1.05/1.24          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 1.05/1.24        | ~ (v1_relat_1 @ sk_D))),
% 1.05/1.24      inference('sup+', [status(thm)], ['25', '128'])).
% 1.05/1.24  thf('130', plain,
% 1.05/1.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('131', plain,
% 1.05/1.24      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.05/1.24         ((v4_relat_1 @ X25 @ X26)
% 1.05/1.24          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 1.05/1.24      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.05/1.24  thf('132', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 1.05/1.24      inference('sup-', [status(thm)], ['130', '131'])).
% 1.05/1.24  thf('133', plain,
% 1.05/1.24      (![X5 : $i, X6 : $i]:
% 1.05/1.24         (~ (v4_relat_1 @ X5 @ X6)
% 1.05/1.24          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 1.05/1.24          | ~ (v1_relat_1 @ X5))),
% 1.05/1.24      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.05/1.24  thf('134', plain,
% 1.05/1.24      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B))),
% 1.05/1.24      inference('sup-', [status(thm)], ['132', '133'])).
% 1.05/1.24  thf('135', plain,
% 1.05/1.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('136', plain,
% 1.05/1.24      (![X3 : $i, X4 : $i]:
% 1.05/1.24         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 1.05/1.24          | (v1_relat_1 @ X3)
% 1.05/1.24          | ~ (v1_relat_1 @ X4))),
% 1.05/1.24      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.05/1.24  thf('137', plain,
% 1.05/1.24      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 1.05/1.24      inference('sup-', [status(thm)], ['135', '136'])).
% 1.05/1.24  thf('138', plain,
% 1.05/1.24      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 1.05/1.24      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.05/1.24  thf('139', plain, ((v1_relat_1 @ sk_D)),
% 1.05/1.24      inference('demod', [status(thm)], ['137', '138'])).
% 1.05/1.24  thf('140', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 1.05/1.24      inference('demod', [status(thm)], ['134', '139'])).
% 1.05/1.24  thf('141', plain,
% 1.05/1.24      (![X14 : $i, X15 : $i]:
% 1.05/1.24         (~ (r1_tarski @ (k1_relat_1 @ X14) @ X15)
% 1.05/1.24          | ((k5_relat_1 @ (k6_partfun1 @ X15) @ X14) = (X14))
% 1.05/1.24          | ~ (v1_relat_1 @ X14))),
% 1.05/1.24      inference('demod', [status(thm)], ['71', '72'])).
% 1.05/1.24  thf('142', plain,
% 1.05/1.24      ((~ (v1_relat_1 @ sk_D)
% 1.05/1.24        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D)))),
% 1.05/1.24      inference('sup-', [status(thm)], ['140', '141'])).
% 1.05/1.24  thf('143', plain, ((v1_relat_1 @ sk_D)),
% 1.05/1.24      inference('demod', [status(thm)], ['137', '138'])).
% 1.05/1.24  thf('144', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))),
% 1.05/1.24      inference('demod', [status(thm)], ['142', '143'])).
% 1.05/1.24  thf('145', plain,
% 1.05/1.24      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('146', plain,
% 1.05/1.24      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.05/1.24         ((v4_relat_1 @ X25 @ X26)
% 1.05/1.24          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 1.05/1.24      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.05/1.24  thf('147', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 1.05/1.24      inference('sup-', [status(thm)], ['145', '146'])).
% 1.05/1.24  thf('148', plain,
% 1.05/1.24      (![X5 : $i, X6 : $i]:
% 1.05/1.24         (~ (v4_relat_1 @ X5 @ X6)
% 1.05/1.24          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 1.05/1.24          | ~ (v1_relat_1 @ X5))),
% 1.05/1.24      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.05/1.24  thf('149', plain,
% 1.05/1.24      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 1.05/1.24      inference('sup-', [status(thm)], ['147', '148'])).
% 1.05/1.24  thf('150', plain, ((v1_relat_1 @ sk_C)),
% 1.05/1.24      inference('demod', [status(thm)], ['49', '50'])).
% 1.05/1.24  thf('151', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 1.05/1.24      inference('demod', [status(thm)], ['149', '150'])).
% 1.05/1.24  thf('152', plain,
% 1.05/1.24      (![X23 : $i]:
% 1.05/1.24         (~ (v2_funct_1 @ X23)
% 1.05/1.24          | ((k1_relat_1 @ X23) = (k2_relat_1 @ (k2_funct_1 @ X23)))
% 1.05/1.24          | ~ (v1_funct_1 @ X23)
% 1.05/1.24          | ~ (v1_relat_1 @ X23))),
% 1.05/1.24      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.05/1.24  thf(t79_relat_1, axiom,
% 1.05/1.24    (![A:$i,B:$i]:
% 1.05/1.24     ( ( v1_relat_1 @ B ) =>
% 1.05/1.24       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 1.05/1.24         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 1.05/1.24  thf('153', plain,
% 1.05/1.24      (![X16 : $i, X17 : $i]:
% 1.05/1.24         (~ (r1_tarski @ (k2_relat_1 @ X16) @ X17)
% 1.05/1.24          | ((k5_relat_1 @ X16 @ (k6_relat_1 @ X17)) = (X16))
% 1.05/1.24          | ~ (v1_relat_1 @ X16))),
% 1.05/1.24      inference('cnf', [status(esa)], [t79_relat_1])).
% 1.05/1.24  thf('154', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 1.05/1.24      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.05/1.24  thf('155', plain,
% 1.05/1.24      (![X16 : $i, X17 : $i]:
% 1.05/1.24         (~ (r1_tarski @ (k2_relat_1 @ X16) @ X17)
% 1.05/1.24          | ((k5_relat_1 @ X16 @ (k6_partfun1 @ X17)) = (X16))
% 1.05/1.24          | ~ (v1_relat_1 @ X16))),
% 1.05/1.24      inference('demod', [status(thm)], ['153', '154'])).
% 1.05/1.24  thf('156', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i]:
% 1.05/1.24         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 1.05/1.24          | ~ (v1_relat_1 @ X0)
% 1.05/1.24          | ~ (v1_funct_1 @ X0)
% 1.05/1.24          | ~ (v2_funct_1 @ X0)
% 1.05/1.24          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.05/1.24          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ X1))
% 1.05/1.24              = (k2_funct_1 @ X0)))),
% 1.05/1.24      inference('sup-', [status(thm)], ['152', '155'])).
% 1.05/1.24  thf('157', plain,
% 1.05/1.24      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 1.05/1.24          = (k2_funct_1 @ sk_C))
% 1.05/1.24        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.05/1.24        | ~ (v2_funct_1 @ sk_C)
% 1.05/1.24        | ~ (v1_funct_1 @ sk_C)
% 1.05/1.24        | ~ (v1_relat_1 @ sk_C))),
% 1.05/1.24      inference('sup-', [status(thm)], ['151', '156'])).
% 1.05/1.24  thf('158', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.05/1.24      inference('demod', [status(thm)], ['102', '103'])).
% 1.05/1.24  thf('159', plain, ((v2_funct_1 @ sk_C)),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('160', plain, ((v1_funct_1 @ sk_C)),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('161', plain, ((v1_relat_1 @ sk_C)),
% 1.05/1.24      inference('demod', [status(thm)], ['49', '50'])).
% 1.05/1.24  thf('162', plain,
% 1.05/1.24      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 1.05/1.24         = (k2_funct_1 @ sk_C))),
% 1.05/1.24      inference('demod', [status(thm)], ['157', '158', '159', '160', '161'])).
% 1.05/1.24  thf('163', plain, ((v1_relat_1 @ sk_D)),
% 1.05/1.24      inference('demod', [status(thm)], ['137', '138'])).
% 1.05/1.24  thf('164', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 1.05/1.24      inference('demod', [status(thm)], ['129', '144', '162', '163'])).
% 1.05/1.24  thf('165', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf('166', plain, ($false),
% 1.05/1.24      inference('simplify_reflect-', [status(thm)], ['164', '165'])).
% 1.05/1.24  
% 1.05/1.24  % SZS output end Refutation
% 1.05/1.24  
% 1.05/1.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

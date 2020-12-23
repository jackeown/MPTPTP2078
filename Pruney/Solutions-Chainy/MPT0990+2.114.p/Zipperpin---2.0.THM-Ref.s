%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uwhjnyCdci

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:14 EST 2020

% Result     : Theorem 2.86s
% Output     : Refutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :  226 ( 932 expanded)
%              Number of leaves         :   43 ( 308 expanded)
%              Depth                    :   29
%              Number of atoms          : 1889 (15526 expanded)
%              Number of equality atoms :   89 ( 972 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X42 ) ) ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( X32 = X35 )
      | ~ ( r2_relset_1 @ X33 @ X34 @ X32 @ X35 ) ) ),
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
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('25',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('26',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
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
    ! [X25: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X25 ) @ X25 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('29',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('30',plain,(
    ! [X25: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X25 ) @ X25 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('31',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
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
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relat_1 @ X24 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('33',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X31 @ X29 )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
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
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('40',plain,(
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relat_1 @ X24 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X14 ) @ X13 )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('74',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('75',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X14 ) @ X13 )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
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
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('83',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v4_relat_1 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
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
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X14 ) @ X13 )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) @ X12 )
        = ( k5_relat_1 @ X11 @ ( k5_relat_1 @ X10 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('98',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) @ X12 )
        = ( k5_relat_1 @ X11 @ ( k5_relat_1 @ X10 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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
    ! [X17: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('110',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
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
    ! [X50: $i] :
      ( ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) ) ) )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) @ X12 )
        = ( k5_relat_1 @ X11 @ ( k5_relat_1 @ X10 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v4_relat_1 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X14 ) @ X13 )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
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
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('157',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v4_relat_1 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('159',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('161',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('163',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k1_relat_1 @ X24 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('165',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ( ( k5_relat_1 @ X15 @ ( k6_relat_1 @ X16 ) )
        = X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('166',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('167',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ( ( k5_relat_1 @ X15 @ ( k6_partfun1 @ X16 ) )
        = X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ X1 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['164','167'])).

thf('169',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['163','168'])).

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
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['169','170','171','172'])).

thf('174',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['156','173'])).

thf('175',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('176',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['174','175','176'])).

thf('178',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['148','149'])).

thf('179',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['140','155','177','178'])).

thf('180',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['179','180'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uwhjnyCdci
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:40:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 2.86/3.04  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.86/3.04  % Solved by: fo/fo7.sh
% 2.86/3.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.86/3.04  % done 1425 iterations in 2.599s
% 2.86/3.04  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.86/3.04  % SZS output start Refutation
% 2.86/3.04  thf(sk_D_type, type, sk_D: $i).
% 2.86/3.04  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.86/3.04  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.86/3.04  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.86/3.04  thf(sk_B_type, type, sk_B: $i).
% 2.86/3.04  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.86/3.04  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.86/3.04  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.86/3.04  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.86/3.04  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.86/3.04  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.86/3.04  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.86/3.04  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.86/3.04  thf(sk_C_type, type, sk_C: $i).
% 2.86/3.04  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.86/3.04  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.86/3.04  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.86/3.04  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.86/3.04  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.86/3.04  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.86/3.04  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.86/3.04  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.86/3.04  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.86/3.04  thf(sk_A_type, type, sk_A: $i).
% 2.86/3.04  thf(t36_funct_2, conjecture,
% 2.86/3.04    (![A:$i,B:$i,C:$i]:
% 2.86/3.04     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.86/3.04         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.86/3.04       ( ![D:$i]:
% 2.86/3.04         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.86/3.04             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.86/3.04           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.86/3.04               ( r2_relset_1 @
% 2.86/3.04                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.86/3.04                 ( k6_partfun1 @ A ) ) & 
% 2.86/3.04               ( v2_funct_1 @ C ) ) =>
% 2.86/3.04             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.86/3.04               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 2.86/3.04  thf(zf_stmt_0, negated_conjecture,
% 2.86/3.04    (~( ![A:$i,B:$i,C:$i]:
% 2.86/3.04        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.86/3.04            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.86/3.04          ( ![D:$i]:
% 2.86/3.04            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.86/3.04                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.86/3.04              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.86/3.04                  ( r2_relset_1 @
% 2.86/3.04                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.86/3.04                    ( k6_partfun1 @ A ) ) & 
% 2.86/3.04                  ( v2_funct_1 @ C ) ) =>
% 2.86/3.04                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.86/3.04                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 2.86/3.04    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 2.86/3.04  thf('0', plain,
% 2.86/3.04      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.86/3.04        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.86/3.04        (k6_partfun1 @ sk_A))),
% 2.86/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.04  thf('1', plain,
% 2.86/3.04      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.86/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.04  thf('2', plain,
% 2.86/3.04      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.86/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.04  thf(redefinition_k1_partfun1, axiom,
% 2.86/3.04    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.86/3.04     ( ( ( v1_funct_1 @ E ) & 
% 2.86/3.04         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.86/3.04         ( v1_funct_1 @ F ) & 
% 2.86/3.04         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.86/3.04       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.86/3.04  thf('3', plain,
% 2.86/3.04      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 2.86/3.04         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 2.86/3.04          | ~ (v1_funct_1 @ X43)
% 2.86/3.04          | ~ (v1_funct_1 @ X46)
% 2.86/3.04          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 2.86/3.04          | ((k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46)
% 2.86/3.04              = (k5_relat_1 @ X43 @ X46)))),
% 2.86/3.04      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 2.86/3.04  thf('4', plain,
% 2.86/3.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.86/3.04         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.86/3.04            = (k5_relat_1 @ sk_C @ X0))
% 2.86/3.04          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.86/3.04          | ~ (v1_funct_1 @ X0)
% 2.86/3.04          | ~ (v1_funct_1 @ sk_C))),
% 2.86/3.04      inference('sup-', [status(thm)], ['2', '3'])).
% 2.86/3.04  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 2.86/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.04  thf('6', plain,
% 2.86/3.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.86/3.04         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.86/3.04            = (k5_relat_1 @ sk_C @ X0))
% 2.86/3.04          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.86/3.04          | ~ (v1_funct_1 @ X0))),
% 2.86/3.04      inference('demod', [status(thm)], ['4', '5'])).
% 2.86/3.04  thf('7', plain,
% 2.86/3.04      ((~ (v1_funct_1 @ sk_D)
% 2.86/3.04        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.86/3.04            = (k5_relat_1 @ sk_C @ sk_D)))),
% 2.86/3.04      inference('sup-', [status(thm)], ['1', '6'])).
% 2.86/3.04  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 2.86/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.04  thf('9', plain,
% 2.86/3.04      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.86/3.04         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.86/3.04      inference('demod', [status(thm)], ['7', '8'])).
% 2.86/3.04  thf('10', plain,
% 2.86/3.04      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 2.86/3.04        (k6_partfun1 @ sk_A))),
% 2.86/3.04      inference('demod', [status(thm)], ['0', '9'])).
% 2.86/3.04  thf('11', plain,
% 2.86/3.04      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.86/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.04  thf('12', plain,
% 2.86/3.04      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.86/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.04  thf(dt_k1_partfun1, axiom,
% 2.86/3.04    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.86/3.04     ( ( ( v1_funct_1 @ E ) & 
% 2.86/3.04         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.86/3.04         ( v1_funct_1 @ F ) & 
% 2.86/3.04         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.86/3.04       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.86/3.04         ( m1_subset_1 @
% 2.86/3.04           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.86/3.04           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.86/3.04  thf('13', plain,
% 2.86/3.04      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 2.86/3.04         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 2.86/3.04          | ~ (v1_funct_1 @ X37)
% 2.86/3.04          | ~ (v1_funct_1 @ X40)
% 2.86/3.04          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 2.86/3.04          | (m1_subset_1 @ (k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40) @ 
% 2.86/3.04             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X42))))),
% 2.86/3.04      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.86/3.04  thf('14', plain,
% 2.86/3.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.86/3.04         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.86/3.04           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.86/3.04          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.86/3.04          | ~ (v1_funct_1 @ X1)
% 2.86/3.04          | ~ (v1_funct_1 @ sk_C))),
% 2.86/3.04      inference('sup-', [status(thm)], ['12', '13'])).
% 2.86/3.04  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 2.86/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.04  thf('16', plain,
% 2.86/3.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.86/3.04         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.86/3.04           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.86/3.04          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.86/3.04          | ~ (v1_funct_1 @ X1))),
% 2.86/3.04      inference('demod', [status(thm)], ['14', '15'])).
% 2.86/3.04  thf('17', plain,
% 2.86/3.04      ((~ (v1_funct_1 @ sk_D)
% 2.86/3.04        | (m1_subset_1 @ 
% 2.86/3.04           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.86/3.04           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.86/3.04      inference('sup-', [status(thm)], ['11', '16'])).
% 2.86/3.04  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 2.86/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.04  thf('19', plain,
% 2.86/3.04      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.86/3.04         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.86/3.04      inference('demod', [status(thm)], ['7', '8'])).
% 2.86/3.05  thf('20', plain,
% 2.86/3.05      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 2.86/3.05        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.86/3.05      inference('demod', [status(thm)], ['17', '18', '19'])).
% 2.86/3.05  thf(redefinition_r2_relset_1, axiom,
% 2.86/3.05    (![A:$i,B:$i,C:$i,D:$i]:
% 2.86/3.05     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.86/3.05         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.86/3.05       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.86/3.05  thf('21', plain,
% 2.86/3.05      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 2.86/3.05         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 2.86/3.05          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 2.86/3.05          | ((X32) = (X35))
% 2.86/3.05          | ~ (r2_relset_1 @ X33 @ X34 @ X32 @ X35))),
% 2.86/3.05      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.86/3.05  thf('22', plain,
% 2.86/3.05      (![X0 : $i]:
% 2.86/3.05         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 2.86/3.05          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 2.86/3.05          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.86/3.05      inference('sup-', [status(thm)], ['20', '21'])).
% 2.86/3.05  thf('23', plain,
% 2.86/3.05      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 2.86/3.05           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.86/3.05        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 2.86/3.05      inference('sup-', [status(thm)], ['10', '22'])).
% 2.86/3.05  thf(t29_relset_1, axiom,
% 2.86/3.05    (![A:$i]:
% 2.86/3.05     ( m1_subset_1 @
% 2.86/3.05       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 2.86/3.05  thf('24', plain,
% 2.86/3.05      (![X36 : $i]:
% 2.86/3.05         (m1_subset_1 @ (k6_relat_1 @ X36) @ 
% 2.86/3.05          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 2.86/3.05      inference('cnf', [status(esa)], [t29_relset_1])).
% 2.86/3.05  thf(redefinition_k6_partfun1, axiom,
% 2.86/3.05    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.86/3.05  thf('25', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 2.86/3.05      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.86/3.05  thf('26', plain,
% 2.86/3.05      (![X36 : $i]:
% 2.86/3.05         (m1_subset_1 @ (k6_partfun1 @ X36) @ 
% 2.86/3.05          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 2.86/3.05      inference('demod', [status(thm)], ['24', '25'])).
% 2.86/3.05  thf('27', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 2.86/3.05      inference('demod', [status(thm)], ['23', '26'])).
% 2.86/3.05  thf(t61_funct_1, axiom,
% 2.86/3.05    (![A:$i]:
% 2.86/3.05     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.86/3.05       ( ( v2_funct_1 @ A ) =>
% 2.86/3.05         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 2.86/3.05             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 2.86/3.05           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 2.86/3.05             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 2.86/3.05  thf('28', plain,
% 2.86/3.05      (![X25 : $i]:
% 2.86/3.05         (~ (v2_funct_1 @ X25)
% 2.86/3.05          | ((k5_relat_1 @ (k2_funct_1 @ X25) @ X25)
% 2.86/3.05              = (k6_relat_1 @ (k2_relat_1 @ X25)))
% 2.86/3.05          | ~ (v1_funct_1 @ X25)
% 2.86/3.05          | ~ (v1_relat_1 @ X25))),
% 2.86/3.05      inference('cnf', [status(esa)], [t61_funct_1])).
% 2.86/3.05  thf('29', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 2.86/3.05      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.86/3.05  thf('30', plain,
% 2.86/3.05      (![X25 : $i]:
% 2.86/3.05         (~ (v2_funct_1 @ X25)
% 2.86/3.05          | ((k5_relat_1 @ (k2_funct_1 @ X25) @ X25)
% 2.86/3.05              = (k6_partfun1 @ (k2_relat_1 @ X25)))
% 2.86/3.05          | ~ (v1_funct_1 @ X25)
% 2.86/3.05          | ~ (v1_relat_1 @ X25))),
% 2.86/3.05      inference('demod', [status(thm)], ['28', '29'])).
% 2.86/3.05  thf(dt_k2_funct_1, axiom,
% 2.86/3.05    (![A:$i]:
% 2.86/3.05     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.86/3.05       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 2.86/3.05         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 2.86/3.05  thf('31', plain,
% 2.86/3.05      (![X17 : $i]:
% 2.86/3.05         ((v1_relat_1 @ (k2_funct_1 @ X17))
% 2.86/3.05          | ~ (v1_funct_1 @ X17)
% 2.86/3.05          | ~ (v1_relat_1 @ X17))),
% 2.86/3.05      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.86/3.05  thf(t55_funct_1, axiom,
% 2.86/3.05    (![A:$i]:
% 2.86/3.05     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.86/3.05       ( ( v2_funct_1 @ A ) =>
% 2.86/3.05         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 2.86/3.05           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.86/3.05  thf('32', plain,
% 2.86/3.05      (![X24 : $i]:
% 2.86/3.05         (~ (v2_funct_1 @ X24)
% 2.86/3.05          | ((k2_relat_1 @ X24) = (k1_relat_1 @ (k2_funct_1 @ X24)))
% 2.86/3.05          | ~ (v1_funct_1 @ X24)
% 2.86/3.05          | ~ (v1_relat_1 @ X24))),
% 2.86/3.05      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.86/3.05  thf('33', plain,
% 2.86/3.05      (![X17 : $i]:
% 2.86/3.05         ((v1_relat_1 @ (k2_funct_1 @ X17))
% 2.86/3.05          | ~ (v1_funct_1 @ X17)
% 2.86/3.05          | ~ (v1_relat_1 @ X17))),
% 2.86/3.05      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.86/3.05  thf('34', plain,
% 2.86/3.05      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.86/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.05  thf(redefinition_k2_relset_1, axiom,
% 2.86/3.05    (![A:$i,B:$i,C:$i]:
% 2.86/3.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.86/3.05       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.86/3.05  thf('35', plain,
% 2.86/3.05      (![X29 : $i, X30 : $i, X31 : $i]:
% 2.86/3.05         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 2.86/3.05          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 2.86/3.05      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.86/3.05  thf('36', plain,
% 2.86/3.05      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 2.86/3.05      inference('sup-', [status(thm)], ['34', '35'])).
% 2.86/3.05  thf('37', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.86/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.05  thf('38', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.86/3.05      inference('sup+', [status(thm)], ['36', '37'])).
% 2.86/3.05  thf('39', plain,
% 2.86/3.05      (![X17 : $i]:
% 2.86/3.05         ((v1_relat_1 @ (k2_funct_1 @ X17))
% 2.86/3.05          | ~ (v1_funct_1 @ X17)
% 2.86/3.05          | ~ (v1_relat_1 @ X17))),
% 2.86/3.05      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.86/3.05  thf('40', plain,
% 2.86/3.05      (![X24 : $i]:
% 2.86/3.05         (~ (v2_funct_1 @ X24)
% 2.86/3.05          | ((k2_relat_1 @ X24) = (k1_relat_1 @ (k2_funct_1 @ X24)))
% 2.86/3.05          | ~ (v1_funct_1 @ X24)
% 2.86/3.05          | ~ (v1_relat_1 @ X24))),
% 2.86/3.05      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.86/3.05  thf(d10_xboole_0, axiom,
% 2.86/3.05    (![A:$i,B:$i]:
% 2.86/3.05     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.86/3.05  thf('41', plain,
% 2.86/3.05      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 2.86/3.05      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.86/3.05  thf('42', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.86/3.05      inference('simplify', [status(thm)], ['41'])).
% 2.86/3.05  thf(d18_relat_1, axiom,
% 2.86/3.05    (![A:$i,B:$i]:
% 2.86/3.05     ( ( v1_relat_1 @ B ) =>
% 2.86/3.05       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 2.86/3.05  thf('43', plain,
% 2.86/3.05      (![X5 : $i, X6 : $i]:
% 2.86/3.05         (~ (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 2.86/3.05          | (v4_relat_1 @ X5 @ X6)
% 2.86/3.05          | ~ (v1_relat_1 @ X5))),
% 2.86/3.05      inference('cnf', [status(esa)], [d18_relat_1])).
% 2.86/3.05  thf('44', plain,
% 2.86/3.05      (![X0 : $i]:
% 2.86/3.05         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 2.86/3.05      inference('sup-', [status(thm)], ['42', '43'])).
% 2.86/3.05  thf('45', plain,
% 2.86/3.05      (![X0 : $i]:
% 2.86/3.05         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 2.86/3.05          | ~ (v1_relat_1 @ X0)
% 2.86/3.05          | ~ (v1_funct_1 @ X0)
% 2.86/3.05          | ~ (v2_funct_1 @ X0)
% 2.86/3.05          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 2.86/3.05      inference('sup+', [status(thm)], ['40', '44'])).
% 2.86/3.05  thf('46', plain,
% 2.86/3.05      (![X0 : $i]:
% 2.86/3.05         (~ (v1_relat_1 @ X0)
% 2.86/3.05          | ~ (v1_funct_1 @ X0)
% 2.86/3.05          | ~ (v2_funct_1 @ X0)
% 2.86/3.05          | ~ (v1_funct_1 @ X0)
% 2.86/3.05          | ~ (v1_relat_1 @ X0)
% 2.86/3.05          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 2.86/3.05      inference('sup-', [status(thm)], ['39', '45'])).
% 2.86/3.05  thf('47', plain,
% 2.86/3.05      (![X0 : $i]:
% 2.86/3.05         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 2.86/3.05          | ~ (v2_funct_1 @ X0)
% 2.86/3.05          | ~ (v1_funct_1 @ X0)
% 2.86/3.05          | ~ (v1_relat_1 @ X0))),
% 2.86/3.05      inference('simplify', [status(thm)], ['46'])).
% 2.86/3.05  thf('48', plain,
% 2.86/3.05      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)
% 2.86/3.05        | ~ (v1_relat_1 @ sk_C)
% 2.86/3.05        | ~ (v1_funct_1 @ sk_C)
% 2.86/3.05        | ~ (v2_funct_1 @ sk_C))),
% 2.86/3.05      inference('sup+', [status(thm)], ['38', '47'])).
% 2.86/3.05  thf('49', plain,
% 2.86/3.05      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.86/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.05  thf(cc2_relat_1, axiom,
% 2.86/3.05    (![A:$i]:
% 2.86/3.05     ( ( v1_relat_1 @ A ) =>
% 2.86/3.05       ( ![B:$i]:
% 2.86/3.05         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.86/3.05  thf('50', plain,
% 2.86/3.05      (![X3 : $i, X4 : $i]:
% 2.86/3.05         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 2.86/3.05          | (v1_relat_1 @ X3)
% 2.86/3.05          | ~ (v1_relat_1 @ X4))),
% 2.86/3.05      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.86/3.05  thf('51', plain,
% 2.86/3.05      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 2.86/3.05      inference('sup-', [status(thm)], ['49', '50'])).
% 2.86/3.05  thf(fc6_relat_1, axiom,
% 2.86/3.05    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.86/3.05  thf('52', plain,
% 2.86/3.05      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 2.86/3.05      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.86/3.05  thf('53', plain, ((v1_relat_1 @ sk_C)),
% 2.86/3.05      inference('demod', [status(thm)], ['51', '52'])).
% 2.86/3.05  thf('54', plain, ((v1_funct_1 @ sk_C)),
% 2.86/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.05  thf('55', plain, ((v2_funct_1 @ sk_C)),
% 2.86/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.05  thf('56', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)),
% 2.86/3.05      inference('demod', [status(thm)], ['48', '53', '54', '55'])).
% 2.86/3.05  thf('57', plain,
% 2.86/3.05      (![X5 : $i, X6 : $i]:
% 2.86/3.05         (~ (v4_relat_1 @ X5 @ X6)
% 2.86/3.05          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 2.86/3.05          | ~ (v1_relat_1 @ X5))),
% 2.86/3.05      inference('cnf', [status(esa)], [d18_relat_1])).
% 2.86/3.05  thf('58', plain,
% 2.86/3.05      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.86/3.05        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 2.86/3.05      inference('sup-', [status(thm)], ['56', '57'])).
% 2.86/3.05  thf('59', plain,
% 2.86/3.05      ((~ (v1_relat_1 @ sk_C)
% 2.86/3.05        | ~ (v1_funct_1 @ sk_C)
% 2.86/3.05        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 2.86/3.05      inference('sup-', [status(thm)], ['33', '58'])).
% 2.86/3.05  thf('60', plain, ((v1_relat_1 @ sk_C)),
% 2.86/3.05      inference('demod', [status(thm)], ['51', '52'])).
% 2.86/3.05  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 2.86/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.05  thf('62', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B)),
% 2.86/3.05      inference('demod', [status(thm)], ['59', '60', '61'])).
% 2.86/3.05  thf('63', plain,
% 2.86/3.05      (![X0 : $i, X2 : $i]:
% 2.86/3.05         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.86/3.05      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.86/3.05  thf('64', plain,
% 2.86/3.05      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 2.86/3.05        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 2.86/3.05      inference('sup-', [status(thm)], ['62', '63'])).
% 2.86/3.05  thf('65', plain,
% 2.86/3.05      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C))
% 2.86/3.05        | ~ (v1_relat_1 @ sk_C)
% 2.86/3.05        | ~ (v1_funct_1 @ sk_C)
% 2.86/3.05        | ~ (v2_funct_1 @ sk_C)
% 2.86/3.05        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 2.86/3.05      inference('sup-', [status(thm)], ['32', '64'])).
% 2.86/3.05  thf('66', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.86/3.05      inference('sup+', [status(thm)], ['36', '37'])).
% 2.86/3.05  thf('67', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.86/3.05      inference('simplify', [status(thm)], ['41'])).
% 2.86/3.05  thf('68', plain, ((v1_relat_1 @ sk_C)),
% 2.86/3.05      inference('demod', [status(thm)], ['51', '52'])).
% 2.86/3.05  thf('69', plain, ((v1_funct_1 @ sk_C)),
% 2.86/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.05  thf('70', plain, ((v2_funct_1 @ sk_C)),
% 2.86/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.05  thf('71', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 2.86/3.05      inference('demod', [status(thm)], ['65', '66', '67', '68', '69', '70'])).
% 2.86/3.05  thf('72', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.86/3.05      inference('simplify', [status(thm)], ['41'])).
% 2.86/3.05  thf(t77_relat_1, axiom,
% 2.86/3.05    (![A:$i,B:$i]:
% 2.86/3.05     ( ( v1_relat_1 @ B ) =>
% 2.86/3.05       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 2.86/3.05         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 2.86/3.05  thf('73', plain,
% 2.86/3.05      (![X13 : $i, X14 : $i]:
% 2.86/3.05         (~ (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 2.86/3.05          | ((k5_relat_1 @ (k6_relat_1 @ X14) @ X13) = (X13))
% 2.86/3.05          | ~ (v1_relat_1 @ X13))),
% 2.86/3.05      inference('cnf', [status(esa)], [t77_relat_1])).
% 2.86/3.05  thf('74', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 2.86/3.05      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.86/3.05  thf('75', plain,
% 2.86/3.05      (![X13 : $i, X14 : $i]:
% 2.86/3.05         (~ (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 2.86/3.05          | ((k5_relat_1 @ (k6_partfun1 @ X14) @ X13) = (X13))
% 2.86/3.05          | ~ (v1_relat_1 @ X13))),
% 2.86/3.05      inference('demod', [status(thm)], ['73', '74'])).
% 2.86/3.05  thf('76', plain,
% 2.86/3.05      (![X0 : $i]:
% 2.86/3.05         (~ (v1_relat_1 @ X0)
% 2.86/3.05          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 2.86/3.05      inference('sup-', [status(thm)], ['72', '75'])).
% 2.86/3.05  thf('77', plain,
% 2.86/3.05      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 2.86/3.05          = (k2_funct_1 @ sk_C))
% 2.86/3.05        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 2.86/3.05      inference('sup+', [status(thm)], ['71', '76'])).
% 2.86/3.05  thf('78', plain,
% 2.86/3.05      ((~ (v1_relat_1 @ sk_C)
% 2.86/3.05        | ~ (v1_funct_1 @ sk_C)
% 2.86/3.05        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 2.86/3.05            = (k2_funct_1 @ sk_C)))),
% 2.86/3.05      inference('sup-', [status(thm)], ['31', '77'])).
% 2.86/3.05  thf('79', plain, ((v1_relat_1 @ sk_C)),
% 2.86/3.05      inference('demod', [status(thm)], ['51', '52'])).
% 2.86/3.05  thf('80', plain, ((v1_funct_1 @ sk_C)),
% 2.86/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.05  thf('81', plain,
% 2.86/3.05      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 2.86/3.05         = (k2_funct_1 @ sk_C))),
% 2.86/3.05      inference('demod', [status(thm)], ['78', '79', '80'])).
% 2.86/3.05  thf('82', plain,
% 2.86/3.05      (![X36 : $i]:
% 2.86/3.05         (m1_subset_1 @ (k6_partfun1 @ X36) @ 
% 2.86/3.05          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 2.86/3.05      inference('demod', [status(thm)], ['24', '25'])).
% 2.86/3.05  thf(cc2_relset_1, axiom,
% 2.86/3.05    (![A:$i,B:$i,C:$i]:
% 2.86/3.05     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.86/3.05       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.86/3.05  thf('83', plain,
% 2.86/3.05      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.86/3.05         ((v4_relat_1 @ X26 @ X27)
% 2.86/3.05          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 2.86/3.05      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.86/3.05  thf('84', plain, (![X0 : $i]: (v4_relat_1 @ (k6_partfun1 @ X0) @ X0)),
% 2.86/3.05      inference('sup-', [status(thm)], ['82', '83'])).
% 2.86/3.05  thf('85', plain,
% 2.86/3.05      (![X5 : $i, X6 : $i]:
% 2.86/3.05         (~ (v4_relat_1 @ X5 @ X6)
% 2.86/3.05          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 2.86/3.05          | ~ (v1_relat_1 @ X5))),
% 2.86/3.05      inference('cnf', [status(esa)], [d18_relat_1])).
% 2.86/3.05  thf('86', plain,
% 2.86/3.05      (![X0 : $i]:
% 2.86/3.05         (~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 2.86/3.05          | (r1_tarski @ (k1_relat_1 @ (k6_partfun1 @ X0)) @ X0))),
% 2.86/3.05      inference('sup-', [status(thm)], ['84', '85'])).
% 2.86/3.05  thf('87', plain,
% 2.86/3.05      (![X36 : $i]:
% 2.86/3.05         (m1_subset_1 @ (k6_partfun1 @ X36) @ 
% 2.86/3.05          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 2.86/3.05      inference('demod', [status(thm)], ['24', '25'])).
% 2.86/3.05  thf('88', plain,
% 2.86/3.05      (![X3 : $i, X4 : $i]:
% 2.86/3.05         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 2.86/3.05          | (v1_relat_1 @ X3)
% 2.86/3.05          | ~ (v1_relat_1 @ X4))),
% 2.86/3.05      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.86/3.05  thf('89', plain,
% 2.86/3.05      (![X0 : $i]:
% 2.86/3.05         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X0))
% 2.86/3.05          | (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 2.86/3.05      inference('sup-', [status(thm)], ['87', '88'])).
% 2.86/3.05  thf('90', plain,
% 2.86/3.05      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 2.86/3.05      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.86/3.05  thf('91', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 2.86/3.05      inference('demod', [status(thm)], ['89', '90'])).
% 2.86/3.05  thf('92', plain,
% 2.86/3.05      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ (k6_partfun1 @ X0)) @ X0)),
% 2.86/3.05      inference('demod', [status(thm)], ['86', '91'])).
% 2.86/3.05  thf('93', plain,
% 2.86/3.05      (![X13 : $i, X14 : $i]:
% 2.86/3.05         (~ (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 2.86/3.05          | ((k5_relat_1 @ (k6_partfun1 @ X14) @ X13) = (X13))
% 2.86/3.05          | ~ (v1_relat_1 @ X13))),
% 2.86/3.05      inference('demod', [status(thm)], ['73', '74'])).
% 2.86/3.05  thf('94', plain,
% 2.86/3.05      (![X0 : $i]:
% 2.86/3.05         (~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 2.86/3.05          | ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 2.86/3.05              = (k6_partfun1 @ X0)))),
% 2.86/3.05      inference('sup-', [status(thm)], ['92', '93'])).
% 2.86/3.05  thf('95', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 2.86/3.05      inference('demod', [status(thm)], ['89', '90'])).
% 2.86/3.05  thf('96', plain,
% 2.86/3.05      (![X0 : $i]:
% 2.86/3.05         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 2.86/3.05           = (k6_partfun1 @ X0))),
% 2.86/3.05      inference('demod', [status(thm)], ['94', '95'])).
% 2.86/3.05  thf(t55_relat_1, axiom,
% 2.86/3.05    (![A:$i]:
% 2.86/3.05     ( ( v1_relat_1 @ A ) =>
% 2.86/3.05       ( ![B:$i]:
% 2.86/3.05         ( ( v1_relat_1 @ B ) =>
% 2.86/3.05           ( ![C:$i]:
% 2.86/3.05             ( ( v1_relat_1 @ C ) =>
% 2.86/3.05               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 2.86/3.05                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 2.86/3.05  thf('97', plain,
% 2.86/3.05      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.86/3.05         (~ (v1_relat_1 @ X10)
% 2.86/3.05          | ((k5_relat_1 @ (k5_relat_1 @ X11 @ X10) @ X12)
% 2.86/3.05              = (k5_relat_1 @ X11 @ (k5_relat_1 @ X10 @ X12)))
% 2.86/3.05          | ~ (v1_relat_1 @ X12)
% 2.86/3.05          | ~ (v1_relat_1 @ X11))),
% 2.86/3.05      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.86/3.05  thf('98', plain,
% 2.86/3.05      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.86/3.05         (~ (v1_relat_1 @ X10)
% 2.86/3.05          | ((k5_relat_1 @ (k5_relat_1 @ X11 @ X10) @ X12)
% 2.86/3.05              = (k5_relat_1 @ X11 @ (k5_relat_1 @ X10 @ X12)))
% 2.86/3.05          | ~ (v1_relat_1 @ X12)
% 2.86/3.05          | ~ (v1_relat_1 @ X11))),
% 2.86/3.05      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.86/3.05  thf('99', plain,
% 2.86/3.05      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.86/3.05         (((k5_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X3)
% 2.86/3.05            = (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ (k5_relat_1 @ X0 @ X3)))
% 2.86/3.05          | ~ (v1_relat_1 @ X2)
% 2.86/3.05          | ~ (v1_relat_1 @ X0)
% 2.86/3.05          | ~ (v1_relat_1 @ X1)
% 2.86/3.05          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 2.86/3.05          | ~ (v1_relat_1 @ X3)
% 2.86/3.05          | ~ (v1_relat_1 @ X0))),
% 2.86/3.05      inference('sup+', [status(thm)], ['97', '98'])).
% 2.86/3.05  thf('100', plain,
% 2.86/3.05      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.86/3.05         (~ (v1_relat_1 @ X3)
% 2.86/3.05          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 2.86/3.05          | ~ (v1_relat_1 @ X1)
% 2.86/3.05          | ~ (v1_relat_1 @ X0)
% 2.86/3.05          | ~ (v1_relat_1 @ X2)
% 2.86/3.05          | ((k5_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X3)
% 2.86/3.05              = (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ (k5_relat_1 @ X0 @ X3))))),
% 2.86/3.05      inference('simplify', [status(thm)], ['99'])).
% 2.86/3.05  thf('101', plain,
% 2.86/3.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.86/3.05         (~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 2.86/3.05          | ((k5_relat_1 @ 
% 2.86/3.05              (k5_relat_1 @ (k6_partfun1 @ X0) @ 
% 2.86/3.05               (k5_relat_1 @ (k6_partfun1 @ X0) @ X2)) @ 
% 2.86/3.05              X1)
% 2.86/3.05              = (k5_relat_1 @ 
% 2.86/3.05                 (k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0)) @ 
% 2.86/3.05                 (k5_relat_1 @ X2 @ X1)))
% 2.86/3.05          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 2.86/3.05          | ~ (v1_relat_1 @ X2)
% 2.86/3.05          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 2.86/3.05          | ~ (v1_relat_1 @ X1))),
% 2.86/3.05      inference('sup-', [status(thm)], ['96', '100'])).
% 2.86/3.05  thf('102', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 2.86/3.05      inference('demod', [status(thm)], ['89', '90'])).
% 2.86/3.05  thf('103', plain,
% 2.86/3.05      (![X0 : $i]:
% 2.86/3.05         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 2.86/3.05           = (k6_partfun1 @ X0))),
% 2.86/3.05      inference('demod', [status(thm)], ['94', '95'])).
% 2.86/3.05  thf('104', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 2.86/3.05      inference('demod', [status(thm)], ['89', '90'])).
% 2.86/3.05  thf('105', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 2.86/3.05      inference('demod', [status(thm)], ['89', '90'])).
% 2.86/3.05  thf('106', plain,
% 2.86/3.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.86/3.05         (((k5_relat_1 @ 
% 2.86/3.05            (k5_relat_1 @ (k6_partfun1 @ X0) @ 
% 2.86/3.05             (k5_relat_1 @ (k6_partfun1 @ X0) @ X2)) @ 
% 2.86/3.05            X1) = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k5_relat_1 @ X2 @ X1)))
% 2.86/3.05          | ~ (v1_relat_1 @ X2)
% 2.86/3.05          | ~ (v1_relat_1 @ X1))),
% 2.86/3.05      inference('demod', [status(thm)], ['101', '102', '103', '104', '105'])).
% 2.86/3.05  thf('107', plain,
% 2.86/3.05      (![X0 : $i]:
% 2.86/3.05         (((k5_relat_1 @ 
% 2.86/3.05            (k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C)) @ X0)
% 2.86/3.05            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 2.86/3.05               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 2.86/3.05          | ~ (v1_relat_1 @ X0)
% 2.86/3.05          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 2.86/3.05      inference('sup+', [status(thm)], ['81', '106'])).
% 2.86/3.05  thf('108', plain,
% 2.86/3.05      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 2.86/3.05         = (k2_funct_1 @ sk_C))),
% 2.86/3.05      inference('demod', [status(thm)], ['78', '79', '80'])).
% 2.86/3.05  thf('109', plain,
% 2.86/3.05      (![X17 : $i]:
% 2.86/3.05         ((v1_funct_1 @ (k2_funct_1 @ X17))
% 2.86/3.05          | ~ (v1_funct_1 @ X17)
% 2.86/3.05          | ~ (v1_relat_1 @ X17))),
% 2.86/3.05      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.86/3.05  thf('110', plain,
% 2.86/3.05      (![X17 : $i]:
% 2.86/3.05         ((v1_relat_1 @ (k2_funct_1 @ X17))
% 2.86/3.05          | ~ (v1_funct_1 @ X17)
% 2.86/3.05          | ~ (v1_relat_1 @ X17))),
% 2.86/3.05      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.86/3.05  thf('111', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 2.86/3.05      inference('demod', [status(thm)], ['65', '66', '67', '68', '69', '70'])).
% 2.86/3.05  thf(t3_funct_2, axiom,
% 2.86/3.05    (![A:$i]:
% 2.86/3.05     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.86/3.05       ( ( v1_funct_1 @ A ) & 
% 2.86/3.05         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 2.86/3.05         ( m1_subset_1 @
% 2.86/3.05           A @ 
% 2.86/3.05           ( k1_zfmisc_1 @
% 2.86/3.05             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 2.86/3.05  thf('112', plain,
% 2.86/3.05      (![X50 : $i]:
% 2.86/3.05         ((m1_subset_1 @ X50 @ 
% 2.86/3.05           (k1_zfmisc_1 @ 
% 2.86/3.05            (k2_zfmisc_1 @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50))))
% 2.86/3.05          | ~ (v1_funct_1 @ X50)
% 2.86/3.05          | ~ (v1_relat_1 @ X50))),
% 2.86/3.05      inference('cnf', [status(esa)], [t3_funct_2])).
% 2.86/3.05  thf('113', plain,
% 2.86/3.05      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.86/3.05         (k1_zfmisc_1 @ 
% 2.86/3.05          (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))
% 2.86/3.05        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.86/3.05        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.86/3.05      inference('sup+', [status(thm)], ['111', '112'])).
% 2.86/3.05  thf('114', plain,
% 2.86/3.05      ((~ (v1_relat_1 @ sk_C)
% 2.86/3.05        | ~ (v1_funct_1 @ sk_C)
% 2.86/3.05        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 2.86/3.05        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.86/3.05           (k1_zfmisc_1 @ 
% 2.86/3.05            (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))))),
% 2.86/3.05      inference('sup-', [status(thm)], ['110', '113'])).
% 2.86/3.05  thf('115', plain, ((v1_relat_1 @ sk_C)),
% 2.86/3.05      inference('demod', [status(thm)], ['51', '52'])).
% 2.86/3.05  thf('116', plain, ((v1_funct_1 @ sk_C)),
% 2.86/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.05  thf('117', plain,
% 2.86/3.05      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 2.86/3.05        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.86/3.05           (k1_zfmisc_1 @ 
% 2.86/3.05            (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))))),
% 2.86/3.05      inference('demod', [status(thm)], ['114', '115', '116'])).
% 2.86/3.05  thf('118', plain,
% 2.86/3.05      ((~ (v1_relat_1 @ sk_C)
% 2.86/3.05        | ~ (v1_funct_1 @ sk_C)
% 2.86/3.05        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.86/3.05           (k1_zfmisc_1 @ 
% 2.86/3.05            (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))))),
% 2.86/3.05      inference('sup-', [status(thm)], ['109', '117'])).
% 2.86/3.05  thf('119', plain, ((v1_relat_1 @ sk_C)),
% 2.86/3.05      inference('demod', [status(thm)], ['51', '52'])).
% 2.86/3.05  thf('120', plain, ((v1_funct_1 @ sk_C)),
% 2.86/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.05  thf('121', plain,
% 2.86/3.05      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.86/3.05        (k1_zfmisc_1 @ 
% 2.86/3.05         (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 2.86/3.05      inference('demod', [status(thm)], ['118', '119', '120'])).
% 2.86/3.05  thf('122', plain,
% 2.86/3.05      (![X3 : $i, X4 : $i]:
% 2.86/3.05         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 2.86/3.05          | (v1_relat_1 @ X3)
% 2.86/3.05          | ~ (v1_relat_1 @ X4))),
% 2.86/3.05      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.86/3.05  thf('123', plain,
% 2.86/3.05      ((~ (v1_relat_1 @ 
% 2.86/3.05           (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 2.86/3.05        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 2.86/3.05      inference('sup-', [status(thm)], ['121', '122'])).
% 2.86/3.05  thf('124', plain,
% 2.86/3.05      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 2.86/3.05      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.86/3.05  thf('125', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 2.86/3.05      inference('demod', [status(thm)], ['123', '124'])).
% 2.86/3.05  thf('126', plain,
% 2.86/3.05      (![X0 : $i]:
% 2.86/3.05         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 2.86/3.05            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 2.86/3.05               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 2.86/3.05          | ~ (v1_relat_1 @ X0))),
% 2.86/3.05      inference('demod', [status(thm)], ['107', '108', '125'])).
% 2.86/3.05  thf('127', plain,
% 2.86/3.05      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 2.86/3.05          = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 2.86/3.05             (k6_partfun1 @ (k2_relat_1 @ sk_C))))
% 2.86/3.05        | ~ (v1_relat_1 @ sk_C)
% 2.86/3.05        | ~ (v1_funct_1 @ sk_C)
% 2.86/3.05        | ~ (v2_funct_1 @ sk_C)
% 2.86/3.05        | ~ (v1_relat_1 @ sk_C))),
% 2.86/3.05      inference('sup+', [status(thm)], ['30', '126'])).
% 2.86/3.05  thf('128', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.86/3.05      inference('sup+', [status(thm)], ['36', '37'])).
% 2.86/3.05  thf('129', plain,
% 2.86/3.05      (![X0 : $i]:
% 2.86/3.05         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 2.86/3.05           = (k6_partfun1 @ X0))),
% 2.86/3.05      inference('demod', [status(thm)], ['94', '95'])).
% 2.86/3.05  thf('130', plain, ((v1_relat_1 @ sk_C)),
% 2.86/3.05      inference('demod', [status(thm)], ['51', '52'])).
% 2.86/3.05  thf('131', plain, ((v1_funct_1 @ sk_C)),
% 2.86/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.05  thf('132', plain, ((v2_funct_1 @ sk_C)),
% 2.86/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.05  thf('133', plain, ((v1_relat_1 @ sk_C)),
% 2.86/3.05      inference('demod', [status(thm)], ['51', '52'])).
% 2.86/3.05  thf('134', plain,
% 2.86/3.05      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 2.86/3.05      inference('demod', [status(thm)],
% 2.86/3.05                ['127', '128', '129', '130', '131', '132', '133'])).
% 2.86/3.05  thf('135', plain,
% 2.86/3.05      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.86/3.05         (~ (v1_relat_1 @ X10)
% 2.86/3.05          | ((k5_relat_1 @ (k5_relat_1 @ X11 @ X10) @ X12)
% 2.86/3.05              = (k5_relat_1 @ X11 @ (k5_relat_1 @ X10 @ X12)))
% 2.86/3.05          | ~ (v1_relat_1 @ X12)
% 2.86/3.05          | ~ (v1_relat_1 @ X11))),
% 2.86/3.05      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.86/3.05  thf('136', plain,
% 2.86/3.05      (![X0 : $i]:
% 2.86/3.05         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 2.86/3.05            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 2.86/3.05          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.86/3.05          | ~ (v1_relat_1 @ X0)
% 2.86/3.05          | ~ (v1_relat_1 @ sk_C))),
% 2.86/3.05      inference('sup+', [status(thm)], ['134', '135'])).
% 2.86/3.05  thf('137', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 2.86/3.05      inference('demod', [status(thm)], ['123', '124'])).
% 2.86/3.05  thf('138', plain, ((v1_relat_1 @ sk_C)),
% 2.86/3.05      inference('demod', [status(thm)], ['51', '52'])).
% 2.86/3.05  thf('139', plain,
% 2.86/3.05      (![X0 : $i]:
% 2.86/3.05         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 2.86/3.05            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 2.86/3.05          | ~ (v1_relat_1 @ X0))),
% 2.86/3.05      inference('demod', [status(thm)], ['136', '137', '138'])).
% 2.86/3.05  thf('140', plain,
% 2.86/3.05      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 2.86/3.05          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 2.86/3.05        | ~ (v1_relat_1 @ sk_D))),
% 2.86/3.05      inference('sup+', [status(thm)], ['27', '139'])).
% 2.86/3.05  thf('141', plain,
% 2.86/3.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.86/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.05  thf('142', plain,
% 2.86/3.05      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.86/3.05         ((v4_relat_1 @ X26 @ X27)
% 2.86/3.05          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 2.86/3.05      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.86/3.05  thf('143', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 2.86/3.05      inference('sup-', [status(thm)], ['141', '142'])).
% 2.86/3.05  thf('144', plain,
% 2.86/3.05      (![X5 : $i, X6 : $i]:
% 2.86/3.05         (~ (v4_relat_1 @ X5 @ X6)
% 2.86/3.05          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 2.86/3.05          | ~ (v1_relat_1 @ X5))),
% 2.86/3.05      inference('cnf', [status(esa)], [d18_relat_1])).
% 2.86/3.05  thf('145', plain,
% 2.86/3.05      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B))),
% 2.86/3.05      inference('sup-', [status(thm)], ['143', '144'])).
% 2.86/3.05  thf('146', plain,
% 2.86/3.05      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.86/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.05  thf('147', plain,
% 2.86/3.05      (![X3 : $i, X4 : $i]:
% 2.86/3.05         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 2.86/3.05          | (v1_relat_1 @ X3)
% 2.86/3.05          | ~ (v1_relat_1 @ X4))),
% 2.86/3.05      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.86/3.05  thf('148', plain,
% 2.86/3.05      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 2.86/3.05      inference('sup-', [status(thm)], ['146', '147'])).
% 2.86/3.05  thf('149', plain,
% 2.86/3.05      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 2.86/3.05      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.86/3.05  thf('150', plain, ((v1_relat_1 @ sk_D)),
% 2.86/3.05      inference('demod', [status(thm)], ['148', '149'])).
% 2.86/3.05  thf('151', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 2.86/3.05      inference('demod', [status(thm)], ['145', '150'])).
% 2.86/3.05  thf('152', plain,
% 2.86/3.05      (![X13 : $i, X14 : $i]:
% 2.86/3.05         (~ (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 2.86/3.05          | ((k5_relat_1 @ (k6_partfun1 @ X14) @ X13) = (X13))
% 2.86/3.05          | ~ (v1_relat_1 @ X13))),
% 2.86/3.05      inference('demod', [status(thm)], ['73', '74'])).
% 2.86/3.05  thf('153', plain,
% 2.86/3.05      ((~ (v1_relat_1 @ sk_D)
% 2.86/3.05        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D)))),
% 2.86/3.05      inference('sup-', [status(thm)], ['151', '152'])).
% 2.86/3.05  thf('154', plain, ((v1_relat_1 @ sk_D)),
% 2.86/3.05      inference('demod', [status(thm)], ['148', '149'])).
% 2.86/3.05  thf('155', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))),
% 2.86/3.05      inference('demod', [status(thm)], ['153', '154'])).
% 2.86/3.05  thf('156', plain,
% 2.86/3.05      (![X17 : $i]:
% 2.86/3.05         ((v1_relat_1 @ (k2_funct_1 @ X17))
% 2.86/3.05          | ~ (v1_funct_1 @ X17)
% 2.86/3.05          | ~ (v1_relat_1 @ X17))),
% 2.86/3.05      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.86/3.05  thf('157', plain,
% 2.86/3.05      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.86/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.05  thf('158', plain,
% 2.86/3.05      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.86/3.05         ((v4_relat_1 @ X26 @ X27)
% 2.86/3.05          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 2.86/3.05      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.86/3.05  thf('159', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 2.86/3.05      inference('sup-', [status(thm)], ['157', '158'])).
% 2.86/3.05  thf('160', plain,
% 2.86/3.05      (![X5 : $i, X6 : $i]:
% 2.86/3.05         (~ (v4_relat_1 @ X5 @ X6)
% 2.86/3.05          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 2.86/3.05          | ~ (v1_relat_1 @ X5))),
% 2.86/3.05      inference('cnf', [status(esa)], [d18_relat_1])).
% 2.86/3.05  thf('161', plain,
% 2.86/3.05      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 2.86/3.05      inference('sup-', [status(thm)], ['159', '160'])).
% 2.86/3.05  thf('162', plain, ((v1_relat_1 @ sk_C)),
% 2.86/3.05      inference('demod', [status(thm)], ['51', '52'])).
% 2.86/3.05  thf('163', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 2.86/3.05      inference('demod', [status(thm)], ['161', '162'])).
% 2.86/3.05  thf('164', plain,
% 2.86/3.05      (![X24 : $i]:
% 2.86/3.05         (~ (v2_funct_1 @ X24)
% 2.86/3.05          | ((k1_relat_1 @ X24) = (k2_relat_1 @ (k2_funct_1 @ X24)))
% 2.86/3.05          | ~ (v1_funct_1 @ X24)
% 2.86/3.05          | ~ (v1_relat_1 @ X24))),
% 2.86/3.05      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.86/3.05  thf(t79_relat_1, axiom,
% 2.86/3.05    (![A:$i,B:$i]:
% 2.86/3.05     ( ( v1_relat_1 @ B ) =>
% 2.86/3.05       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 2.86/3.05         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 2.86/3.05  thf('165', plain,
% 2.86/3.05      (![X15 : $i, X16 : $i]:
% 2.86/3.05         (~ (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 2.86/3.05          | ((k5_relat_1 @ X15 @ (k6_relat_1 @ X16)) = (X15))
% 2.86/3.05          | ~ (v1_relat_1 @ X15))),
% 2.86/3.05      inference('cnf', [status(esa)], [t79_relat_1])).
% 2.86/3.05  thf('166', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 2.86/3.05      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.86/3.05  thf('167', plain,
% 2.86/3.05      (![X15 : $i, X16 : $i]:
% 2.86/3.05         (~ (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 2.86/3.05          | ((k5_relat_1 @ X15 @ (k6_partfun1 @ X16)) = (X15))
% 2.86/3.05          | ~ (v1_relat_1 @ X15))),
% 2.86/3.05      inference('demod', [status(thm)], ['165', '166'])).
% 2.86/3.05  thf('168', plain,
% 2.86/3.05      (![X0 : $i, X1 : $i]:
% 2.86/3.05         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 2.86/3.05          | ~ (v1_relat_1 @ X0)
% 2.86/3.05          | ~ (v1_funct_1 @ X0)
% 2.86/3.05          | ~ (v2_funct_1 @ X0)
% 2.86/3.05          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.86/3.05          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ X1))
% 2.86/3.05              = (k2_funct_1 @ X0)))),
% 2.86/3.05      inference('sup-', [status(thm)], ['164', '167'])).
% 2.86/3.05  thf('169', plain,
% 2.86/3.05      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 2.86/3.05          = (k2_funct_1 @ sk_C))
% 2.86/3.05        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.86/3.05        | ~ (v2_funct_1 @ sk_C)
% 2.86/3.05        | ~ (v1_funct_1 @ sk_C)
% 2.86/3.05        | ~ (v1_relat_1 @ sk_C))),
% 2.86/3.05      inference('sup-', [status(thm)], ['163', '168'])).
% 2.86/3.05  thf('170', plain, ((v2_funct_1 @ sk_C)),
% 2.86/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.05  thf('171', plain, ((v1_funct_1 @ sk_C)),
% 2.86/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.05  thf('172', plain, ((v1_relat_1 @ sk_C)),
% 2.86/3.05      inference('demod', [status(thm)], ['51', '52'])).
% 2.86/3.05  thf('173', plain,
% 2.86/3.05      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 2.86/3.05          = (k2_funct_1 @ sk_C))
% 2.86/3.05        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 2.86/3.05      inference('demod', [status(thm)], ['169', '170', '171', '172'])).
% 2.86/3.05  thf('174', plain,
% 2.86/3.05      ((~ (v1_relat_1 @ sk_C)
% 2.86/3.05        | ~ (v1_funct_1 @ sk_C)
% 2.86/3.05        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 2.86/3.05            = (k2_funct_1 @ sk_C)))),
% 2.86/3.05      inference('sup-', [status(thm)], ['156', '173'])).
% 2.86/3.05  thf('175', plain, ((v1_relat_1 @ sk_C)),
% 2.86/3.05      inference('demod', [status(thm)], ['51', '52'])).
% 2.86/3.05  thf('176', plain, ((v1_funct_1 @ sk_C)),
% 2.86/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.05  thf('177', plain,
% 2.86/3.05      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 2.86/3.05         = (k2_funct_1 @ sk_C))),
% 2.86/3.05      inference('demod', [status(thm)], ['174', '175', '176'])).
% 2.86/3.05  thf('178', plain, ((v1_relat_1 @ sk_D)),
% 2.86/3.05      inference('demod', [status(thm)], ['148', '149'])).
% 2.86/3.05  thf('179', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 2.86/3.05      inference('demod', [status(thm)], ['140', '155', '177', '178'])).
% 2.86/3.05  thf('180', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 2.86/3.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.86/3.05  thf('181', plain, ($false),
% 2.86/3.05      inference('simplify_reflect-', [status(thm)], ['179', '180'])).
% 2.86/3.05  
% 2.86/3.05  % SZS output end Refutation
% 2.86/3.05  
% 2.86/3.06  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

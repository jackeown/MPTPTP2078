%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.APonXYbYu4

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:15 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 418 expanded)
%              Number of leaves         :   45 ( 145 expanded)
%              Depth                    :   18
%              Number of atoms          : 1350 (7873 expanded)
%              Number of equality atoms :   64 ( 501 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

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
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( X24 = X27 )
      | ~ ( r2_relset_1 @ X25 @ X26 @ X24 @ X27 ) ) ),
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
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
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
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X17 ) @ X17 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
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
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X17 ) @ X17 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) @ X10 )
        = ( k5_relat_1 @ X9 @ ( k5_relat_1 @ X8 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('37',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('38',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('42',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v4_relat_1 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('43',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['41','42'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('44',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v4_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('49',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('50',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['45','50'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('52',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X11 ) @ X12 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X12 ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('53',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('54',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X11 ) @ X12 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X12 ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = sk_D ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['48','49'])).

thf('57',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('60',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('62',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['60','61'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('63',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k2_funct_1 @ X15 )
        = ( k4_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('64',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('68',plain,(
    ! [X7: $i] :
      ( ( ( k2_relat_1 @ X7 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('69',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X4 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('70',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v4_relat_1 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('72',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v4_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('74',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['60','61'])).

thf('76',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X4 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('78',plain,(
    ! [X7: $i] :
      ( ( ( k1_relat_1 @ X7 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('79',plain,(
    ! [X7: $i] :
      ( ( ( k2_relat_1 @ X7 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('80',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ( v4_relat_1 @ X2 @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( v4_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( v4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['77','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ( v4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['76','84'])).

thf('86',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('87',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('88',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['60','61'])).

thf('90',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['60','61'])).

thf('93',plain,(
    v4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['85','91','92'])).

thf('94',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v4_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('95',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['69','95'])).

thf('97',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('98',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) @ sk_A ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ sk_A )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['68','98'])).

thf('100',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('101',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['99','100'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('102',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ( ( k5_relat_1 @ X13 @ ( k6_relat_1 @ X14 ) )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('103',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('104',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ( ( k5_relat_1 @ X13 @ ( k6_partfun1 @ X14 ) )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      = ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['101','104'])).

thf('106',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('107',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['60','61'])).

thf('109',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['48','49'])).

thf('112',plain,
    ( sk_D
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['35','40','57','67','107','108','109','110','111'])).

thf('113',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('115',plain,(
    sk_D
 != ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['112','115'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.APonXYbYu4
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:39:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.55/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.55/0.73  % Solved by: fo/fo7.sh
% 0.55/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.73  % done 344 iterations in 0.277s
% 0.55/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.55/0.73  % SZS output start Refutation
% 0.55/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.73  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.55/0.73  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.55/0.73  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.55/0.73  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.55/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.55/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.55/0.73  thf(sk_D_type, type, sk_D: $i).
% 0.55/0.73  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.55/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.55/0.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.55/0.73  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.55/0.73  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.55/0.73  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.55/0.73  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.55/0.73  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.55/0.73  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.55/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.73  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.55/0.73  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.55/0.73  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.55/0.73  thf(sk_C_type, type, sk_C: $i).
% 0.55/0.73  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.55/0.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.55/0.73  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.55/0.73  thf(t36_funct_2, conjecture,
% 0.55/0.73    (![A:$i,B:$i,C:$i]:
% 0.55/0.73     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.55/0.73         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.55/0.73       ( ![D:$i]:
% 0.55/0.73         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.55/0.73             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.55/0.73           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.55/0.73               ( r2_relset_1 @
% 0.55/0.73                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.55/0.73                 ( k6_partfun1 @ A ) ) & 
% 0.55/0.73               ( v2_funct_1 @ C ) ) =>
% 0.55/0.73             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.55/0.73               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.55/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.73    (~( ![A:$i,B:$i,C:$i]:
% 0.55/0.73        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.55/0.73            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.55/0.73          ( ![D:$i]:
% 0.55/0.73            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.55/0.73                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.55/0.73              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.55/0.73                  ( r2_relset_1 @
% 0.55/0.73                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.55/0.73                    ( k6_partfun1 @ A ) ) & 
% 0.55/0.73                  ( v2_funct_1 @ C ) ) =>
% 0.55/0.73                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.55/0.73                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.55/0.73    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.55/0.73  thf('0', plain,
% 0.55/0.73      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.55/0.73        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.55/0.73        (k6_partfun1 @ sk_A))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('1', plain,
% 0.55/0.73      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('2', plain,
% 0.55/0.73      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf(redefinition_k1_partfun1, axiom,
% 0.55/0.73    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.55/0.73     ( ( ( v1_funct_1 @ E ) & 
% 0.55/0.73         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.55/0.73         ( v1_funct_1 @ F ) & 
% 0.55/0.73         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.55/0.73       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.55/0.73  thf('3', plain,
% 0.55/0.73      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.55/0.73         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.55/0.73          | ~ (v1_funct_1 @ X36)
% 0.55/0.73          | ~ (v1_funct_1 @ X39)
% 0.55/0.73          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.55/0.73          | ((k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39)
% 0.55/0.73              = (k5_relat_1 @ X36 @ X39)))),
% 0.55/0.73      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.55/0.73  thf('4', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.73         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.55/0.73            = (k5_relat_1 @ sk_C @ X0))
% 0.55/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.55/0.73          | ~ (v1_funct_1 @ X0)
% 0.55/0.73          | ~ (v1_funct_1 @ sk_C))),
% 0.55/0.73      inference('sup-', [status(thm)], ['2', '3'])).
% 0.55/0.73  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('6', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.73         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.55/0.73            = (k5_relat_1 @ sk_C @ X0))
% 0.55/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.55/0.73          | ~ (v1_funct_1 @ X0))),
% 0.55/0.73      inference('demod', [status(thm)], ['4', '5'])).
% 0.55/0.73  thf('7', plain,
% 0.55/0.73      ((~ (v1_funct_1 @ sk_D)
% 0.55/0.73        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.55/0.73            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['1', '6'])).
% 0.55/0.73  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('9', plain,
% 0.55/0.73      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.55/0.73         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.55/0.73      inference('demod', [status(thm)], ['7', '8'])).
% 0.55/0.73  thf('10', plain,
% 0.55/0.73      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.55/0.73        (k6_partfun1 @ sk_A))),
% 0.55/0.73      inference('demod', [status(thm)], ['0', '9'])).
% 0.55/0.73  thf('11', plain,
% 0.55/0.73      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('12', plain,
% 0.55/0.73      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf(dt_k1_partfun1, axiom,
% 0.55/0.73    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.55/0.73     ( ( ( v1_funct_1 @ E ) & 
% 0.55/0.73         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.55/0.73         ( v1_funct_1 @ F ) & 
% 0.55/0.73         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.55/0.73       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.55/0.73         ( m1_subset_1 @
% 0.55/0.73           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.55/0.73           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.55/0.73  thf('13', plain,
% 0.55/0.73      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.55/0.73         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.55/0.73          | ~ (v1_funct_1 @ X28)
% 0.55/0.73          | ~ (v1_funct_1 @ X31)
% 0.55/0.73          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.55/0.73          | (m1_subset_1 @ (k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31) @ 
% 0.55/0.73             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X33))))),
% 0.55/0.73      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.55/0.73  thf('14', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.73         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.55/0.73           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.55/0.73          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.55/0.73          | ~ (v1_funct_1 @ X1)
% 0.55/0.73          | ~ (v1_funct_1 @ sk_C))),
% 0.55/0.73      inference('sup-', [status(thm)], ['12', '13'])).
% 0.55/0.73  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('16', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.73         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.55/0.73           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.55/0.73          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.55/0.73          | ~ (v1_funct_1 @ X1))),
% 0.55/0.73      inference('demod', [status(thm)], ['14', '15'])).
% 0.55/0.73  thf('17', plain,
% 0.55/0.73      ((~ (v1_funct_1 @ sk_D)
% 0.55/0.73        | (m1_subset_1 @ 
% 0.55/0.73           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.55/0.73           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.55/0.73      inference('sup-', [status(thm)], ['11', '16'])).
% 0.55/0.73  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('19', plain,
% 0.55/0.73      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.55/0.73         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.55/0.73      inference('demod', [status(thm)], ['7', '8'])).
% 0.55/0.73  thf('20', plain,
% 0.55/0.73      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.55/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.55/0.73      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.55/0.73  thf(redefinition_r2_relset_1, axiom,
% 0.55/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.73     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.55/0.73         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.55/0.73       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.55/0.73  thf('21', plain,
% 0.55/0.73      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.55/0.73         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.55/0.73          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.55/0.73          | ((X24) = (X27))
% 0.55/0.73          | ~ (r2_relset_1 @ X25 @ X26 @ X24 @ X27))),
% 0.55/0.73      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.55/0.73  thf('22', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 0.55/0.73          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 0.55/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.55/0.73      inference('sup-', [status(thm)], ['20', '21'])).
% 0.55/0.73  thf('23', plain,
% 0.55/0.73      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.55/0.73           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.55/0.73        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['10', '22'])).
% 0.55/0.73  thf(dt_k6_partfun1, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( m1_subset_1 @
% 0.55/0.73         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.55/0.73       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.55/0.73  thf('24', plain,
% 0.55/0.73      (![X35 : $i]:
% 0.55/0.73         (m1_subset_1 @ (k6_partfun1 @ X35) @ 
% 0.55/0.73          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 0.55/0.73      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.55/0.73  thf('25', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.55/0.73      inference('demod', [status(thm)], ['23', '24'])).
% 0.55/0.73  thf(dt_k2_funct_1, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.55/0.73       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.55/0.73         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.55/0.73  thf('26', plain,
% 0.55/0.73      (![X16 : $i]:
% 0.55/0.73         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 0.55/0.73          | ~ (v1_funct_1 @ X16)
% 0.55/0.73          | ~ (v1_relat_1 @ X16))),
% 0.55/0.73      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.55/0.73  thf(t61_funct_1, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.55/0.73       ( ( v2_funct_1 @ A ) =>
% 0.55/0.73         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.55/0.73             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.55/0.73           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.55/0.73             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.55/0.73  thf('27', plain,
% 0.55/0.73      (![X17 : $i]:
% 0.55/0.73         (~ (v2_funct_1 @ X17)
% 0.55/0.73          | ((k5_relat_1 @ (k2_funct_1 @ X17) @ X17)
% 0.55/0.73              = (k6_relat_1 @ (k2_relat_1 @ X17)))
% 0.55/0.73          | ~ (v1_funct_1 @ X17)
% 0.55/0.73          | ~ (v1_relat_1 @ X17))),
% 0.55/0.73      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.55/0.73  thf(redefinition_k6_partfun1, axiom,
% 0.55/0.73    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.55/0.73  thf('28', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 0.55/0.73      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.55/0.73  thf('29', plain,
% 0.55/0.73      (![X17 : $i]:
% 0.55/0.73         (~ (v2_funct_1 @ X17)
% 0.55/0.73          | ((k5_relat_1 @ (k2_funct_1 @ X17) @ X17)
% 0.55/0.73              = (k6_partfun1 @ (k2_relat_1 @ X17)))
% 0.55/0.73          | ~ (v1_funct_1 @ X17)
% 0.55/0.73          | ~ (v1_relat_1 @ X17))),
% 0.55/0.73      inference('demod', [status(thm)], ['27', '28'])).
% 0.55/0.73  thf(t55_relat_1, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( v1_relat_1 @ A ) =>
% 0.55/0.73       ( ![B:$i]:
% 0.55/0.73         ( ( v1_relat_1 @ B ) =>
% 0.55/0.73           ( ![C:$i]:
% 0.55/0.73             ( ( v1_relat_1 @ C ) =>
% 0.55/0.73               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.55/0.73                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.55/0.73  thf('30', plain,
% 0.55/0.73      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.55/0.73         (~ (v1_relat_1 @ X8)
% 0.55/0.73          | ((k5_relat_1 @ (k5_relat_1 @ X9 @ X8) @ X10)
% 0.55/0.73              = (k5_relat_1 @ X9 @ (k5_relat_1 @ X8 @ X10)))
% 0.55/0.73          | ~ (v1_relat_1 @ X10)
% 0.55/0.73          | ~ (v1_relat_1 @ X9))),
% 0.55/0.73      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.55/0.73  thf('31', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i]:
% 0.55/0.73         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 0.55/0.73            = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 0.55/0.73          | ~ (v1_relat_1 @ X0)
% 0.55/0.73          | ~ (v1_funct_1 @ X0)
% 0.55/0.73          | ~ (v2_funct_1 @ X0)
% 0.55/0.73          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.55/0.73          | ~ (v1_relat_1 @ X1)
% 0.55/0.73          | ~ (v1_relat_1 @ X0))),
% 0.55/0.73      inference('sup+', [status(thm)], ['29', '30'])).
% 0.55/0.73  thf('32', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i]:
% 0.55/0.73         (~ (v1_relat_1 @ X1)
% 0.55/0.73          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.55/0.73          | ~ (v2_funct_1 @ X0)
% 0.55/0.73          | ~ (v1_funct_1 @ X0)
% 0.55/0.73          | ~ (v1_relat_1 @ X0)
% 0.55/0.73          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 0.55/0.73              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1))))),
% 0.55/0.73      inference('simplify', [status(thm)], ['31'])).
% 0.55/0.73  thf('33', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i]:
% 0.55/0.73         (~ (v1_relat_1 @ X0)
% 0.55/0.73          | ~ (v1_funct_1 @ X0)
% 0.55/0.73          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 0.55/0.73              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 0.55/0.73          | ~ (v1_relat_1 @ X0)
% 0.55/0.73          | ~ (v1_funct_1 @ X0)
% 0.55/0.73          | ~ (v2_funct_1 @ X0)
% 0.55/0.73          | ~ (v1_relat_1 @ X1))),
% 0.55/0.73      inference('sup-', [status(thm)], ['26', '32'])).
% 0.55/0.73  thf('34', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i]:
% 0.55/0.73         (~ (v1_relat_1 @ X1)
% 0.55/0.73          | ~ (v2_funct_1 @ X0)
% 0.55/0.73          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 0.55/0.73              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 0.55/0.73          | ~ (v1_funct_1 @ X0)
% 0.55/0.73          | ~ (v1_relat_1 @ X0))),
% 0.55/0.73      inference('simplify', [status(thm)], ['33'])).
% 0.55/0.73  thf('35', plain,
% 0.55/0.73      ((((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)) @ sk_D)
% 0.55/0.73          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 0.55/0.73        | ~ (v1_relat_1 @ sk_C)
% 0.55/0.73        | ~ (v1_funct_1 @ sk_C)
% 0.55/0.73        | ~ (v2_funct_1 @ sk_C)
% 0.55/0.73        | ~ (v1_relat_1 @ sk_D))),
% 0.55/0.73      inference('sup+', [status(thm)], ['25', '34'])).
% 0.55/0.73  thf('36', plain,
% 0.55/0.73      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf(redefinition_k2_relset_1, axiom,
% 0.55/0.73    (![A:$i,B:$i,C:$i]:
% 0.55/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.73       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.55/0.73  thf('37', plain,
% 0.55/0.73      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.55/0.73         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 0.55/0.73          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.55/0.73      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.55/0.73  thf('38', plain,
% 0.55/0.73      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.55/0.73      inference('sup-', [status(thm)], ['36', '37'])).
% 0.55/0.73  thf('39', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('40', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.55/0.73      inference('sup+', [status(thm)], ['38', '39'])).
% 0.55/0.73  thf('41', plain,
% 0.55/0.73      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf(cc2_relset_1, axiom,
% 0.55/0.73    (![A:$i,B:$i,C:$i]:
% 0.55/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.55/0.73       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.55/0.73  thf('42', plain,
% 0.55/0.73      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.55/0.73         ((v4_relat_1 @ X18 @ X19)
% 0.55/0.73          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.55/0.73      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.55/0.73  thf('43', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 0.55/0.73      inference('sup-', [status(thm)], ['41', '42'])).
% 0.55/0.73  thf(d18_relat_1, axiom,
% 0.55/0.73    (![A:$i,B:$i]:
% 0.55/0.73     ( ( v1_relat_1 @ B ) =>
% 0.55/0.73       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.55/0.73  thf('44', plain,
% 0.55/0.73      (![X2 : $i, X3 : $i]:
% 0.55/0.73         (~ (v4_relat_1 @ X2 @ X3)
% 0.55/0.73          | (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 0.55/0.73          | ~ (v1_relat_1 @ X2))),
% 0.55/0.73      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.55/0.73  thf('45', plain,
% 0.55/0.73      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B))),
% 0.55/0.73      inference('sup-', [status(thm)], ['43', '44'])).
% 0.55/0.73  thf('46', plain,
% 0.55/0.73      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf(cc2_relat_1, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( v1_relat_1 @ A ) =>
% 0.55/0.73       ( ![B:$i]:
% 0.55/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.55/0.73  thf('47', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i]:
% 0.55/0.73         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.55/0.73          | (v1_relat_1 @ X0)
% 0.55/0.73          | ~ (v1_relat_1 @ X1))),
% 0.55/0.73      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.55/0.73  thf('48', plain,
% 0.55/0.73      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.55/0.73      inference('sup-', [status(thm)], ['46', '47'])).
% 0.55/0.73  thf(fc6_relat_1, axiom,
% 0.55/0.73    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.55/0.73  thf('49', plain,
% 0.55/0.73      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.55/0.73      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.55/0.73  thf('50', plain, ((v1_relat_1 @ sk_D)),
% 0.55/0.73      inference('demod', [status(thm)], ['48', '49'])).
% 0.55/0.73  thf('51', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 0.55/0.73      inference('demod', [status(thm)], ['45', '50'])).
% 0.55/0.73  thf(t77_relat_1, axiom,
% 0.55/0.73    (![A:$i,B:$i]:
% 0.55/0.73     ( ( v1_relat_1 @ B ) =>
% 0.55/0.73       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.55/0.73         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.55/0.73  thf('52', plain,
% 0.55/0.73      (![X11 : $i, X12 : $i]:
% 0.55/0.73         (~ (r1_tarski @ (k1_relat_1 @ X11) @ X12)
% 0.55/0.73          | ((k5_relat_1 @ (k6_relat_1 @ X12) @ X11) = (X11))
% 0.55/0.73          | ~ (v1_relat_1 @ X11))),
% 0.55/0.73      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.55/0.73  thf('53', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 0.55/0.73      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.55/0.73  thf('54', plain,
% 0.55/0.73      (![X11 : $i, X12 : $i]:
% 0.55/0.73         (~ (r1_tarski @ (k1_relat_1 @ X11) @ X12)
% 0.55/0.73          | ((k5_relat_1 @ (k6_partfun1 @ X12) @ X11) = (X11))
% 0.55/0.73          | ~ (v1_relat_1 @ X11))),
% 0.55/0.73      inference('demod', [status(thm)], ['52', '53'])).
% 0.55/0.73  thf('55', plain,
% 0.55/0.73      ((~ (v1_relat_1 @ sk_D)
% 0.55/0.73        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['51', '54'])).
% 0.55/0.73  thf('56', plain, ((v1_relat_1 @ sk_D)),
% 0.55/0.74      inference('demod', [status(thm)], ['48', '49'])).
% 0.55/0.74  thf('57', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))),
% 0.55/0.74      inference('demod', [status(thm)], ['55', '56'])).
% 0.55/0.74  thf('58', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('59', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.55/0.74          | (v1_relat_1 @ X0)
% 0.55/0.74          | ~ (v1_relat_1 @ X1))),
% 0.55/0.74      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.55/0.74  thf('60', plain,
% 0.55/0.74      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.55/0.74      inference('sup-', [status(thm)], ['58', '59'])).
% 0.55/0.74  thf('61', plain,
% 0.55/0.74      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.55/0.74      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.55/0.74  thf('62', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.74      inference('demod', [status(thm)], ['60', '61'])).
% 0.55/0.74  thf(d9_funct_1, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.55/0.74       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.55/0.74  thf('63', plain,
% 0.55/0.74      (![X15 : $i]:
% 0.55/0.74         (~ (v2_funct_1 @ X15)
% 0.55/0.74          | ((k2_funct_1 @ X15) = (k4_relat_1 @ X15))
% 0.55/0.74          | ~ (v1_funct_1 @ X15)
% 0.55/0.74          | ~ (v1_relat_1 @ X15))),
% 0.55/0.74      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.55/0.74  thf('64', plain,
% 0.55/0.74      ((~ (v1_funct_1 @ sk_C)
% 0.55/0.74        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 0.55/0.74        | ~ (v2_funct_1 @ sk_C))),
% 0.55/0.74      inference('sup-', [status(thm)], ['62', '63'])).
% 0.55/0.74  thf('65', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('66', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('67', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.55/0.74      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.55/0.74  thf(t37_relat_1, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( v1_relat_1 @ A ) =>
% 0.55/0.74       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.55/0.74         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.55/0.74  thf('68', plain,
% 0.55/0.74      (![X7 : $i]:
% 0.55/0.74         (((k2_relat_1 @ X7) = (k1_relat_1 @ (k4_relat_1 @ X7)))
% 0.55/0.74          | ~ (v1_relat_1 @ X7))),
% 0.55/0.74      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.55/0.74  thf(dt_k4_relat_1, axiom,
% 0.55/0.74    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.55/0.74  thf('69', plain,
% 0.55/0.74      (![X4 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X4)) | ~ (v1_relat_1 @ X4))),
% 0.55/0.74      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.55/0.74  thf('70', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('71', plain,
% 0.55/0.74      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.55/0.74         ((v4_relat_1 @ X18 @ X19)
% 0.55/0.74          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.55/0.74      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.55/0.74  thf('72', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.55/0.74      inference('sup-', [status(thm)], ['70', '71'])).
% 0.55/0.74  thf('73', plain,
% 0.55/0.74      (![X2 : $i, X3 : $i]:
% 0.55/0.74         (~ (v4_relat_1 @ X2 @ X3)
% 0.55/0.74          | (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 0.55/0.74          | ~ (v1_relat_1 @ X2))),
% 0.55/0.74      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.55/0.74  thf('74', plain,
% 0.55/0.74      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 0.55/0.74      inference('sup-', [status(thm)], ['72', '73'])).
% 0.55/0.74  thf('75', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.74      inference('demod', [status(thm)], ['60', '61'])).
% 0.55/0.74  thf('76', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.55/0.74      inference('demod', [status(thm)], ['74', '75'])).
% 0.55/0.74  thf('77', plain,
% 0.55/0.74      (![X4 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X4)) | ~ (v1_relat_1 @ X4))),
% 0.55/0.74      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.55/0.74  thf('78', plain,
% 0.55/0.74      (![X7 : $i]:
% 0.55/0.74         (((k1_relat_1 @ X7) = (k2_relat_1 @ (k4_relat_1 @ X7)))
% 0.55/0.74          | ~ (v1_relat_1 @ X7))),
% 0.55/0.74      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.55/0.74  thf('79', plain,
% 0.55/0.74      (![X7 : $i]:
% 0.55/0.74         (((k2_relat_1 @ X7) = (k1_relat_1 @ (k4_relat_1 @ X7)))
% 0.55/0.74          | ~ (v1_relat_1 @ X7))),
% 0.55/0.74      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.55/0.74  thf('80', plain,
% 0.55/0.74      (![X2 : $i, X3 : $i]:
% 0.55/0.74         (~ (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 0.55/0.74          | (v4_relat_1 @ X2 @ X3)
% 0.55/0.74          | ~ (v1_relat_1 @ X2))),
% 0.55/0.74      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.55/0.74  thf('81', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         (~ (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.55/0.74          | ~ (v1_relat_1 @ X0)
% 0.55/0.74          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.55/0.74          | (v4_relat_1 @ (k4_relat_1 @ X0) @ X1))),
% 0.55/0.74      inference('sup-', [status(thm)], ['79', '80'])).
% 0.55/0.74  thf('82', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.55/0.74          | ~ (v1_relat_1 @ X0)
% 0.55/0.74          | (v4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)) @ X1)
% 0.55/0.74          | ~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))
% 0.55/0.74          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['78', '81'])).
% 0.55/0.74  thf('83', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         (~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.55/0.74          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.55/0.74          | (v4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)) @ X1)
% 0.55/0.74          | ~ (v1_relat_1 @ X0)
% 0.55/0.74          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ X1))),
% 0.55/0.74      inference('sup-', [status(thm)], ['77', '82'])).
% 0.55/0.74  thf('84', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.55/0.74          | ~ (v1_relat_1 @ X0)
% 0.55/0.74          | (v4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)) @ X1)
% 0.55/0.74          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.55/0.74      inference('simplify', [status(thm)], ['83'])).
% 0.55/0.74  thf('85', plain,
% 0.55/0.74      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.55/0.74        | (v4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)) @ sk_A)
% 0.55/0.74        | ~ (v1_relat_1 @ sk_C))),
% 0.55/0.74      inference('sup-', [status(thm)], ['76', '84'])).
% 0.55/0.74  thf('86', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.55/0.74      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.55/0.74  thf('87', plain,
% 0.55/0.74      (![X16 : $i]:
% 0.55/0.74         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 0.55/0.74          | ~ (v1_funct_1 @ X16)
% 0.55/0.74          | ~ (v1_relat_1 @ X16))),
% 0.55/0.74      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.55/0.74  thf('88', plain,
% 0.55/0.74      (((v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.55/0.74        | ~ (v1_relat_1 @ sk_C)
% 0.55/0.74        | ~ (v1_funct_1 @ sk_C))),
% 0.55/0.74      inference('sup+', [status(thm)], ['86', '87'])).
% 0.55/0.74  thf('89', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.74      inference('demod', [status(thm)], ['60', '61'])).
% 0.55/0.74  thf('90', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('91', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.55/0.74      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.55/0.74  thf('92', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.74      inference('demod', [status(thm)], ['60', '61'])).
% 0.55/0.74  thf('93', plain, ((v4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)) @ sk_A)),
% 0.55/0.74      inference('demod', [status(thm)], ['85', '91', '92'])).
% 0.55/0.74  thf('94', plain,
% 0.55/0.74      (![X2 : $i, X3 : $i]:
% 0.55/0.74         (~ (v4_relat_1 @ X2 @ X3)
% 0.55/0.74          | (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 0.55/0.74          | ~ (v1_relat_1 @ X2))),
% 0.55/0.74      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.55/0.74  thf('95', plain,
% 0.55/0.74      ((~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.55/0.74        | (r1_tarski @ (k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C))) @ sk_A))),
% 0.55/0.74      inference('sup-', [status(thm)], ['93', '94'])).
% 0.55/0.74  thf('96', plain,
% 0.55/0.74      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.55/0.74        | (r1_tarski @ (k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C))) @ sk_A))),
% 0.55/0.74      inference('sup-', [status(thm)], ['69', '95'])).
% 0.55/0.74  thf('97', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.55/0.74      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.55/0.74  thf('98', plain,
% 0.55/0.74      ((r1_tarski @ (k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C))) @ sk_A)),
% 0.55/0.74      inference('demod', [status(thm)], ['96', '97'])).
% 0.55/0.74  thf('99', plain,
% 0.55/0.74      (((r1_tarski @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ sk_A)
% 0.55/0.74        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.55/0.74      inference('sup+', [status(thm)], ['68', '98'])).
% 0.55/0.74  thf('100', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.55/0.74      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.55/0.74  thf('101', plain, ((r1_tarski @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ sk_A)),
% 0.55/0.74      inference('demod', [status(thm)], ['99', '100'])).
% 0.55/0.74  thf(t79_relat_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( v1_relat_1 @ B ) =>
% 0.55/0.74       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.55/0.74         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.55/0.74  thf('102', plain,
% 0.55/0.74      (![X13 : $i, X14 : $i]:
% 0.55/0.74         (~ (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 0.55/0.74          | ((k5_relat_1 @ X13 @ (k6_relat_1 @ X14)) = (X13))
% 0.55/0.74          | ~ (v1_relat_1 @ X13))),
% 0.55/0.74      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.55/0.74  thf('103', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 0.55/0.74      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.55/0.74  thf('104', plain,
% 0.55/0.74      (![X13 : $i, X14 : $i]:
% 0.55/0.74         (~ (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 0.55/0.74          | ((k5_relat_1 @ X13 @ (k6_partfun1 @ X14)) = (X13))
% 0.55/0.74          | ~ (v1_relat_1 @ X13))),
% 0.55/0.74      inference('demod', [status(thm)], ['102', '103'])).
% 0.55/0.74  thf('105', plain,
% 0.55/0.74      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.55/0.74        | ((k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 0.55/0.74            = (k4_relat_1 @ sk_C)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['101', '104'])).
% 0.55/0.74  thf('106', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.55/0.74      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.55/0.74  thf('107', plain,
% 0.55/0.74      (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 0.55/0.74         = (k4_relat_1 @ sk_C))),
% 0.55/0.74      inference('demod', [status(thm)], ['105', '106'])).
% 0.55/0.74  thf('108', plain, ((v1_relat_1 @ sk_C)),
% 0.55/0.74      inference('demod', [status(thm)], ['60', '61'])).
% 0.55/0.74  thf('109', plain, ((v1_funct_1 @ sk_C)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('110', plain, ((v2_funct_1 @ sk_C)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('111', plain, ((v1_relat_1 @ sk_D)),
% 0.55/0.74      inference('demod', [status(thm)], ['48', '49'])).
% 0.55/0.74  thf('112', plain, (((sk_D) = (k4_relat_1 @ sk_C))),
% 0.55/0.74      inference('demod', [status(thm)],
% 0.55/0.74                ['35', '40', '57', '67', '107', '108', '109', '110', '111'])).
% 0.55/0.74  thf('113', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('114', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.55/0.74      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.55/0.74  thf('115', plain, (((sk_D) != (k4_relat_1 @ sk_C))),
% 0.55/0.74      inference('demod', [status(thm)], ['113', '114'])).
% 0.55/0.74  thf('116', plain, ($false),
% 0.55/0.74      inference('simplify_reflect-', [status(thm)], ['112', '115'])).
% 0.55/0.74  
% 0.55/0.74  % SZS output end Refutation
% 0.55/0.74  
% 0.55/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

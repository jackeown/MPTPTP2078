%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.F9Zg74yoML

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:15 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 280 expanded)
%              Number of leaves         :   45 ( 103 expanded)
%              Depth                    :   15
%              Number of atoms          : 1215 (5170 expanded)
%              Number of equality atoms :   67 ( 339 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(t72_relat_1,axiom,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('0',plain,(
    ! [X11: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X11 ) )
      = ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

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
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,(
    ! [X11: $i] :
      ( ( k4_relat_1 @ ( k6_partfun1 @ X11 ) )
      = ( k6_partfun1 @ X11 ) ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X6 ) @ ( k4_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('7',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('8',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X16 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','8'])).

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

thf('10',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( ( k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40 )
        = ( k5_relat_1 @ X37 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['10','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
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

thf('23',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('30',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('31',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( X25 = X28 )
      | ~ ( r2_relset_1 @ X26 @ X27 @ X25 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','32'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('34',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('35',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('36',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
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

thf('37',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X18 ) @ X18 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('38',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('39',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X18 ) @ X18 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('40',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) @ X10 )
        = ( k5_relat_1 @ X9 @ ( k5_relat_1 @ X8 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['35','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('47',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('48',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('52',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v4_relat_1 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('53',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['51','52'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('54',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v4_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('55',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('58',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('59',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('60',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['55','60'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('62',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X13 ) @ X12 )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('63',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('64',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X13 ) @ X12 )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = sk_D ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['58','59'])).

thf('67',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('70',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('72',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['70','71'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('73',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k2_funct_1 @ X14 )
        = ( k4_relat_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('74',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['70','71'])).

thf('79',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['58','59'])).

thf('82',plain,
    ( sk_D
    = ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','50','67','77','78','79','80','81'])).

thf('83',plain,
    ( ( sk_D
      = ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['9','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v4_relat_1 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('86',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v4_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('88',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['70','71'])).

thf('90',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X13 ) @ X12 )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('92',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_C )
      = sk_C ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['70','71'])).

thf('94',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['70','71'])).

thf('96',plain,
    ( sk_D
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['83','94','95'])).

thf('97',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('99',plain,(
    sk_D
 != ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['96','99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.F9Zg74yoML
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:35:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.59/0.76  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.76  % Solved by: fo/fo7.sh
% 0.59/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.76  % done 307 iterations in 0.304s
% 0.59/0.76  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.76  % SZS output start Refutation
% 0.59/0.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.76  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.59/0.76  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.59/0.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.76  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.76  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.59/0.76  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.59/0.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.76  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.59/0.76  thf(sk_D_type, type, sk_D: $i).
% 0.59/0.76  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.59/0.76  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.59/0.76  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.59/0.76  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.59/0.76  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.59/0.76  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.59/0.76  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.59/0.76  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.59/0.76  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.59/0.76  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.59/0.76  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.59/0.76  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.59/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.76  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.59/0.76  thf(t72_relat_1, axiom,
% 0.59/0.76    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.59/0.76  thf('0', plain,
% 0.59/0.76      (![X11 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X11)) = (k6_relat_1 @ X11))),
% 0.59/0.76      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.59/0.76  thf(redefinition_k6_partfun1, axiom,
% 0.59/0.76    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.59/0.76  thf('1', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 0.59/0.76      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.59/0.76  thf('2', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 0.59/0.76      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.59/0.76  thf('3', plain,
% 0.59/0.76      (![X11 : $i]: ((k4_relat_1 @ (k6_partfun1 @ X11)) = (k6_partfun1 @ X11))),
% 0.59/0.76      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.59/0.76  thf(t54_relat_1, axiom,
% 0.59/0.76    (![A:$i]:
% 0.59/0.76     ( ( v1_relat_1 @ A ) =>
% 0.59/0.76       ( ![B:$i]:
% 0.59/0.76         ( ( v1_relat_1 @ B ) =>
% 0.59/0.76           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.59/0.76             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.59/0.76  thf('4', plain,
% 0.59/0.76      (![X6 : $i, X7 : $i]:
% 0.59/0.76         (~ (v1_relat_1 @ X6)
% 0.59/0.76          | ((k4_relat_1 @ (k5_relat_1 @ X7 @ X6))
% 0.59/0.76              = (k5_relat_1 @ (k4_relat_1 @ X6) @ (k4_relat_1 @ X7)))
% 0.59/0.76          | ~ (v1_relat_1 @ X7))),
% 0.59/0.76      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.59/0.76  thf('5', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]:
% 0.59/0.76         (((k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 0.59/0.76            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_partfun1 @ X0)))
% 0.59/0.76          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 0.59/0.76          | ~ (v1_relat_1 @ X1))),
% 0.59/0.76      inference('sup+', [status(thm)], ['3', '4'])).
% 0.59/0.76  thf(fc4_funct_1, axiom,
% 0.59/0.76    (![A:$i]:
% 0.59/0.76     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.59/0.76       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.59/0.76  thf('6', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 0.59/0.76      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.59/0.76  thf('7', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 0.59/0.76      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.59/0.76  thf('8', plain, (![X16 : $i]: (v1_relat_1 @ (k6_partfun1 @ X16))),
% 0.59/0.76      inference('demod', [status(thm)], ['6', '7'])).
% 0.59/0.76  thf('9', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]:
% 0.59/0.76         (((k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 0.59/0.76            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_partfun1 @ X0)))
% 0.59/0.76          | ~ (v1_relat_1 @ X1))),
% 0.59/0.76      inference('demod', [status(thm)], ['5', '8'])).
% 0.59/0.76  thf(t36_funct_2, conjecture,
% 0.59/0.76    (![A:$i,B:$i,C:$i]:
% 0.59/0.76     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.59/0.76         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.76       ( ![D:$i]:
% 0.59/0.76         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.59/0.76             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.59/0.76           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.59/0.76               ( r2_relset_1 @
% 0.59/0.76                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.59/0.76                 ( k6_partfun1 @ A ) ) & 
% 0.59/0.76               ( v2_funct_1 @ C ) ) =>
% 0.59/0.76             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.59/0.76               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.59/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.76    (~( ![A:$i,B:$i,C:$i]:
% 0.59/0.76        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.59/0.76            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.76          ( ![D:$i]:
% 0.59/0.76            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.59/0.76                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.59/0.76              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.59/0.76                  ( r2_relset_1 @
% 0.59/0.76                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.59/0.76                    ( k6_partfun1 @ A ) ) & 
% 0.59/0.76                  ( v2_funct_1 @ C ) ) =>
% 0.59/0.76                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.59/0.76                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.59/0.76    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.59/0.76  thf('10', plain,
% 0.59/0.76      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.76        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.59/0.76        (k6_partfun1 @ sk_A))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('11', plain,
% 0.59/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('12', plain,
% 0.59/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf(redefinition_k1_partfun1, axiom,
% 0.59/0.76    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.59/0.76     ( ( ( v1_funct_1 @ E ) & 
% 0.59/0.76         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.59/0.76         ( v1_funct_1 @ F ) & 
% 0.59/0.76         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.59/0.76       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.59/0.76  thf('13', plain,
% 0.59/0.76      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.59/0.76         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.59/0.76          | ~ (v1_funct_1 @ X37)
% 0.59/0.76          | ~ (v1_funct_1 @ X40)
% 0.59/0.76          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.59/0.76          | ((k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40)
% 0.59/0.76              = (k5_relat_1 @ X37 @ X40)))),
% 0.59/0.76      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.59/0.76  thf('14', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.76         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.59/0.76            = (k5_relat_1 @ sk_C @ X0))
% 0.59/0.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.59/0.76          | ~ (v1_funct_1 @ X0)
% 0.59/0.76          | ~ (v1_funct_1 @ sk_C))),
% 0.59/0.76      inference('sup-', [status(thm)], ['12', '13'])).
% 0.59/0.76  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('16', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.76         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.59/0.76            = (k5_relat_1 @ sk_C @ X0))
% 0.59/0.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.59/0.76          | ~ (v1_funct_1 @ X0))),
% 0.59/0.76      inference('demod', [status(thm)], ['14', '15'])).
% 0.59/0.76  thf('17', plain,
% 0.59/0.76      ((~ (v1_funct_1 @ sk_D)
% 0.59/0.76        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.59/0.76            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.59/0.76      inference('sup-', [status(thm)], ['11', '16'])).
% 0.59/0.76  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('19', plain,
% 0.59/0.76      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.59/0.76         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.59/0.76      inference('demod', [status(thm)], ['17', '18'])).
% 0.59/0.76  thf('20', plain,
% 0.59/0.76      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.59/0.76        (k6_partfun1 @ sk_A))),
% 0.59/0.76      inference('demod', [status(thm)], ['10', '19'])).
% 0.59/0.76  thf('21', plain,
% 0.59/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('22', plain,
% 0.59/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf(dt_k1_partfun1, axiom,
% 0.59/0.76    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.59/0.76     ( ( ( v1_funct_1 @ E ) & 
% 0.59/0.76         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.59/0.76         ( v1_funct_1 @ F ) & 
% 0.59/0.76         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.59/0.76       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.59/0.76         ( m1_subset_1 @
% 0.59/0.76           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.59/0.76           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.59/0.76  thf('23', plain,
% 0.59/0.76      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.59/0.76         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.59/0.76          | ~ (v1_funct_1 @ X29)
% 0.59/0.76          | ~ (v1_funct_1 @ X32)
% 0.59/0.76          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.59/0.76          | (m1_subset_1 @ (k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32) @ 
% 0.59/0.76             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X34))))),
% 0.59/0.76      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.59/0.76  thf('24', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.76         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.59/0.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.59/0.76          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.59/0.76          | ~ (v1_funct_1 @ X1)
% 0.59/0.76          | ~ (v1_funct_1 @ sk_C))),
% 0.59/0.76      inference('sup-', [status(thm)], ['22', '23'])).
% 0.59/0.76  thf('25', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('26', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.76         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.59/0.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.59/0.76          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.59/0.76          | ~ (v1_funct_1 @ X1))),
% 0.59/0.76      inference('demod', [status(thm)], ['24', '25'])).
% 0.59/0.76  thf('27', plain,
% 0.59/0.76      ((~ (v1_funct_1 @ sk_D)
% 0.59/0.76        | (m1_subset_1 @ 
% 0.59/0.76           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.59/0.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.59/0.76      inference('sup-', [status(thm)], ['21', '26'])).
% 0.59/0.76  thf('28', plain, ((v1_funct_1 @ sk_D)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('29', plain,
% 0.59/0.76      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.59/0.76         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.59/0.76      inference('demod', [status(thm)], ['17', '18'])).
% 0.59/0.76  thf('30', plain,
% 0.59/0.76      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.59/0.76        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.76      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.59/0.76  thf(redefinition_r2_relset_1, axiom,
% 0.59/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.76     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.59/0.76         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.76       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.59/0.76  thf('31', plain,
% 0.59/0.76      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.59/0.76         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.59/0.76          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.59/0.76          | ((X25) = (X28))
% 0.59/0.76          | ~ (r2_relset_1 @ X26 @ X27 @ X25 @ X28))),
% 0.59/0.76      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.59/0.76  thf('32', plain,
% 0.59/0.76      (![X0 : $i]:
% 0.59/0.76         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 0.59/0.76          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 0.59/0.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.59/0.76      inference('sup-', [status(thm)], ['30', '31'])).
% 0.59/0.76  thf('33', plain,
% 0.59/0.76      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.59/0.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.59/0.76        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 0.59/0.76      inference('sup-', [status(thm)], ['20', '32'])).
% 0.59/0.76  thf(dt_k6_partfun1, axiom,
% 0.59/0.76    (![A:$i]:
% 0.59/0.76     ( ( m1_subset_1 @
% 0.59/0.76         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.59/0.76       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.59/0.76  thf('34', plain,
% 0.59/0.76      (![X36 : $i]:
% 0.59/0.76         (m1_subset_1 @ (k6_partfun1 @ X36) @ 
% 0.59/0.76          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 0.59/0.76      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.59/0.76  thf('35', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.59/0.76      inference('demod', [status(thm)], ['33', '34'])).
% 0.59/0.76  thf(dt_k2_funct_1, axiom,
% 0.59/0.76    (![A:$i]:
% 0.59/0.76     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.59/0.76       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.59/0.76         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.59/0.76  thf('36', plain,
% 0.59/0.76      (![X15 : $i]:
% 0.59/0.76         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 0.59/0.76          | ~ (v1_funct_1 @ X15)
% 0.59/0.76          | ~ (v1_relat_1 @ X15))),
% 0.59/0.76      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.59/0.76  thf(t61_funct_1, axiom,
% 0.59/0.76    (![A:$i]:
% 0.59/0.76     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.59/0.76       ( ( v2_funct_1 @ A ) =>
% 0.59/0.76         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.59/0.76             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.59/0.76           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.59/0.76             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.59/0.76  thf('37', plain,
% 0.59/0.76      (![X18 : $i]:
% 0.59/0.76         (~ (v2_funct_1 @ X18)
% 0.59/0.76          | ((k5_relat_1 @ (k2_funct_1 @ X18) @ X18)
% 0.59/0.76              = (k6_relat_1 @ (k2_relat_1 @ X18)))
% 0.59/0.76          | ~ (v1_funct_1 @ X18)
% 0.59/0.76          | ~ (v1_relat_1 @ X18))),
% 0.59/0.76      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.59/0.76  thf('38', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 0.59/0.76      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.59/0.76  thf('39', plain,
% 0.59/0.76      (![X18 : $i]:
% 0.59/0.76         (~ (v2_funct_1 @ X18)
% 0.59/0.76          | ((k5_relat_1 @ (k2_funct_1 @ X18) @ X18)
% 0.59/0.76              = (k6_partfun1 @ (k2_relat_1 @ X18)))
% 0.59/0.76          | ~ (v1_funct_1 @ X18)
% 0.59/0.76          | ~ (v1_relat_1 @ X18))),
% 0.59/0.76      inference('demod', [status(thm)], ['37', '38'])).
% 0.59/0.76  thf(t55_relat_1, axiom,
% 0.59/0.76    (![A:$i]:
% 0.59/0.76     ( ( v1_relat_1 @ A ) =>
% 0.59/0.76       ( ![B:$i]:
% 0.59/0.76         ( ( v1_relat_1 @ B ) =>
% 0.59/0.76           ( ![C:$i]:
% 0.59/0.76             ( ( v1_relat_1 @ C ) =>
% 0.59/0.76               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.59/0.76                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.59/0.76  thf('40', plain,
% 0.59/0.76      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.59/0.76         (~ (v1_relat_1 @ X8)
% 0.59/0.76          | ((k5_relat_1 @ (k5_relat_1 @ X9 @ X8) @ X10)
% 0.59/0.76              = (k5_relat_1 @ X9 @ (k5_relat_1 @ X8 @ X10)))
% 0.59/0.76          | ~ (v1_relat_1 @ X10)
% 0.59/0.76          | ~ (v1_relat_1 @ X9))),
% 0.59/0.76      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.59/0.76  thf('41', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]:
% 0.59/0.76         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 0.59/0.76            = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 0.59/0.76          | ~ (v1_relat_1 @ X0)
% 0.59/0.76          | ~ (v1_funct_1 @ X0)
% 0.59/0.76          | ~ (v2_funct_1 @ X0)
% 0.59/0.76          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.76          | ~ (v1_relat_1 @ X1)
% 0.59/0.76          | ~ (v1_relat_1 @ X0))),
% 0.59/0.76      inference('sup+', [status(thm)], ['39', '40'])).
% 0.59/0.76  thf('42', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]:
% 0.59/0.76         (~ (v1_relat_1 @ X1)
% 0.59/0.76          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.76          | ~ (v2_funct_1 @ X0)
% 0.59/0.76          | ~ (v1_funct_1 @ X0)
% 0.59/0.76          | ~ (v1_relat_1 @ X0)
% 0.59/0.76          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 0.59/0.76              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1))))),
% 0.59/0.76      inference('simplify', [status(thm)], ['41'])).
% 0.59/0.76  thf('43', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]:
% 0.59/0.76         (~ (v1_relat_1 @ X0)
% 0.59/0.76          | ~ (v1_funct_1 @ X0)
% 0.59/0.76          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 0.59/0.76              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 0.59/0.76          | ~ (v1_relat_1 @ X0)
% 0.59/0.76          | ~ (v1_funct_1 @ X0)
% 0.59/0.76          | ~ (v2_funct_1 @ X0)
% 0.59/0.76          | ~ (v1_relat_1 @ X1))),
% 0.59/0.76      inference('sup-', [status(thm)], ['36', '42'])).
% 0.59/0.76  thf('44', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]:
% 0.59/0.76         (~ (v1_relat_1 @ X1)
% 0.59/0.76          | ~ (v2_funct_1 @ X0)
% 0.59/0.76          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 0.59/0.76              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 0.59/0.76          | ~ (v1_funct_1 @ X0)
% 0.59/0.76          | ~ (v1_relat_1 @ X0))),
% 0.59/0.76      inference('simplify', [status(thm)], ['43'])).
% 0.59/0.76  thf('45', plain,
% 0.59/0.76      ((((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)) @ sk_D)
% 0.59/0.76          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 0.59/0.76        | ~ (v1_relat_1 @ sk_C)
% 0.59/0.76        | ~ (v1_funct_1 @ sk_C)
% 0.59/0.76        | ~ (v2_funct_1 @ sk_C)
% 0.59/0.76        | ~ (v1_relat_1 @ sk_D))),
% 0.59/0.76      inference('sup+', [status(thm)], ['35', '44'])).
% 0.59/0.76  thf('46', plain,
% 0.59/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf(redefinition_k2_relset_1, axiom,
% 0.59/0.76    (![A:$i,B:$i,C:$i]:
% 0.59/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.76       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.59/0.76  thf('47', plain,
% 0.59/0.76      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.59/0.76         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 0.59/0.76          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.59/0.76      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.59/0.76  thf('48', plain,
% 0.59/0.76      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.59/0.76      inference('sup-', [status(thm)], ['46', '47'])).
% 0.59/0.76  thf('49', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('50', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.59/0.76      inference('sup+', [status(thm)], ['48', '49'])).
% 0.59/0.76  thf('51', plain,
% 0.59/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf(cc2_relset_1, axiom,
% 0.59/0.76    (![A:$i,B:$i,C:$i]:
% 0.59/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.76       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.59/0.76  thf('52', plain,
% 0.59/0.76      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.59/0.76         ((v4_relat_1 @ X19 @ X20)
% 0.59/0.76          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.59/0.76      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.59/0.76  thf('53', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 0.59/0.76      inference('sup-', [status(thm)], ['51', '52'])).
% 0.59/0.76  thf(d18_relat_1, axiom,
% 0.59/0.76    (![A:$i,B:$i]:
% 0.59/0.76     ( ( v1_relat_1 @ B ) =>
% 0.59/0.76       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.59/0.76  thf('54', plain,
% 0.59/0.76      (![X2 : $i, X3 : $i]:
% 0.59/0.76         (~ (v4_relat_1 @ X2 @ X3)
% 0.59/0.76          | (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 0.59/0.76          | ~ (v1_relat_1 @ X2))),
% 0.59/0.76      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.59/0.76  thf('55', plain,
% 0.59/0.76      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B))),
% 0.59/0.76      inference('sup-', [status(thm)], ['53', '54'])).
% 0.59/0.76  thf('56', plain,
% 0.59/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf(cc2_relat_1, axiom,
% 0.59/0.76    (![A:$i]:
% 0.59/0.76     ( ( v1_relat_1 @ A ) =>
% 0.59/0.76       ( ![B:$i]:
% 0.59/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.59/0.76  thf('57', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]:
% 0.59/0.76         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.59/0.76          | (v1_relat_1 @ X0)
% 0.59/0.76          | ~ (v1_relat_1 @ X1))),
% 0.59/0.76      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.59/0.76  thf('58', plain,
% 0.59/0.76      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.59/0.76      inference('sup-', [status(thm)], ['56', '57'])).
% 0.59/0.76  thf(fc6_relat_1, axiom,
% 0.59/0.76    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.59/0.76  thf('59', plain,
% 0.59/0.76      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.59/0.76      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.59/0.76  thf('60', plain, ((v1_relat_1 @ sk_D)),
% 0.59/0.76      inference('demod', [status(thm)], ['58', '59'])).
% 0.59/0.76  thf('61', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 0.59/0.76      inference('demod', [status(thm)], ['55', '60'])).
% 0.59/0.76  thf(t77_relat_1, axiom,
% 0.59/0.76    (![A:$i,B:$i]:
% 0.59/0.76     ( ( v1_relat_1 @ B ) =>
% 0.59/0.76       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.59/0.76         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.59/0.76  thf('62', plain,
% 0.59/0.76      (![X12 : $i, X13 : $i]:
% 0.59/0.76         (~ (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.59/0.76          | ((k5_relat_1 @ (k6_relat_1 @ X13) @ X12) = (X12))
% 0.59/0.76          | ~ (v1_relat_1 @ X12))),
% 0.59/0.76      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.59/0.76  thf('63', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 0.59/0.76      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.59/0.76  thf('64', plain,
% 0.59/0.76      (![X12 : $i, X13 : $i]:
% 0.59/0.76         (~ (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.59/0.76          | ((k5_relat_1 @ (k6_partfun1 @ X13) @ X12) = (X12))
% 0.59/0.76          | ~ (v1_relat_1 @ X12))),
% 0.59/0.76      inference('demod', [status(thm)], ['62', '63'])).
% 0.59/0.76  thf('65', plain,
% 0.59/0.76      ((~ (v1_relat_1 @ sk_D)
% 0.59/0.76        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D)))),
% 0.59/0.76      inference('sup-', [status(thm)], ['61', '64'])).
% 0.59/0.76  thf('66', plain, ((v1_relat_1 @ sk_D)),
% 0.59/0.76      inference('demod', [status(thm)], ['58', '59'])).
% 0.59/0.76  thf('67', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))),
% 0.59/0.76      inference('demod', [status(thm)], ['65', '66'])).
% 0.59/0.76  thf('68', plain,
% 0.59/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('69', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]:
% 0.59/0.76         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.59/0.76          | (v1_relat_1 @ X0)
% 0.59/0.76          | ~ (v1_relat_1 @ X1))),
% 0.59/0.76      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.59/0.76  thf('70', plain,
% 0.59/0.76      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.59/0.76      inference('sup-', [status(thm)], ['68', '69'])).
% 0.59/0.76  thf('71', plain,
% 0.59/0.76      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.59/0.76      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.59/0.76  thf('72', plain, ((v1_relat_1 @ sk_C)),
% 0.59/0.76      inference('demod', [status(thm)], ['70', '71'])).
% 0.59/0.76  thf(d9_funct_1, axiom,
% 0.59/0.76    (![A:$i]:
% 0.59/0.76     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.59/0.76       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.59/0.76  thf('73', plain,
% 0.59/0.76      (![X14 : $i]:
% 0.59/0.76         (~ (v2_funct_1 @ X14)
% 0.59/0.76          | ((k2_funct_1 @ X14) = (k4_relat_1 @ X14))
% 0.59/0.76          | ~ (v1_funct_1 @ X14)
% 0.59/0.76          | ~ (v1_relat_1 @ X14))),
% 0.59/0.76      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.59/0.76  thf('74', plain,
% 0.59/0.76      ((~ (v1_funct_1 @ sk_C)
% 0.59/0.76        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 0.59/0.76        | ~ (v2_funct_1 @ sk_C))),
% 0.59/0.76      inference('sup-', [status(thm)], ['72', '73'])).
% 0.59/0.76  thf('75', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('76', plain, ((v2_funct_1 @ sk_C)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('77', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.59/0.76      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.59/0.76  thf('78', plain, ((v1_relat_1 @ sk_C)),
% 0.59/0.76      inference('demod', [status(thm)], ['70', '71'])).
% 0.59/0.76  thf('79', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('80', plain, ((v2_funct_1 @ sk_C)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('81', plain, ((v1_relat_1 @ sk_D)),
% 0.59/0.76      inference('demod', [status(thm)], ['58', '59'])).
% 0.59/0.76  thf('82', plain,
% 0.59/0.76      (((sk_D) = (k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_partfun1 @ sk_A)))),
% 0.59/0.76      inference('demod', [status(thm)],
% 0.59/0.76                ['45', '50', '67', '77', '78', '79', '80', '81'])).
% 0.59/0.76  thf('83', plain,
% 0.59/0.76      ((((sk_D) = (k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ sk_A) @ sk_C)))
% 0.59/0.76        | ~ (v1_relat_1 @ sk_C))),
% 0.59/0.76      inference('sup+', [status(thm)], ['9', '82'])).
% 0.59/0.76  thf('84', plain,
% 0.59/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('85', plain,
% 0.59/0.76      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.59/0.76         ((v4_relat_1 @ X19 @ X20)
% 0.59/0.76          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.59/0.76      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.59/0.76  thf('86', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.59/0.76      inference('sup-', [status(thm)], ['84', '85'])).
% 0.59/0.76  thf('87', plain,
% 0.59/0.76      (![X2 : $i, X3 : $i]:
% 0.59/0.76         (~ (v4_relat_1 @ X2 @ X3)
% 0.59/0.76          | (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 0.59/0.76          | ~ (v1_relat_1 @ X2))),
% 0.59/0.76      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.59/0.76  thf('88', plain,
% 0.59/0.76      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 0.59/0.76      inference('sup-', [status(thm)], ['86', '87'])).
% 0.59/0.76  thf('89', plain, ((v1_relat_1 @ sk_C)),
% 0.59/0.76      inference('demod', [status(thm)], ['70', '71'])).
% 0.59/0.76  thf('90', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.59/0.76      inference('demod', [status(thm)], ['88', '89'])).
% 0.59/0.76  thf('91', plain,
% 0.59/0.76      (![X12 : $i, X13 : $i]:
% 0.59/0.76         (~ (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.59/0.76          | ((k5_relat_1 @ (k6_partfun1 @ X13) @ X12) = (X12))
% 0.59/0.76          | ~ (v1_relat_1 @ X12))),
% 0.59/0.76      inference('demod', [status(thm)], ['62', '63'])).
% 0.59/0.76  thf('92', plain,
% 0.59/0.76      ((~ (v1_relat_1 @ sk_C)
% 0.59/0.76        | ((k5_relat_1 @ (k6_partfun1 @ sk_A) @ sk_C) = (sk_C)))),
% 0.59/0.76      inference('sup-', [status(thm)], ['90', '91'])).
% 0.59/0.76  thf('93', plain, ((v1_relat_1 @ sk_C)),
% 0.59/0.76      inference('demod', [status(thm)], ['70', '71'])).
% 0.59/0.76  thf('94', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_A) @ sk_C) = (sk_C))),
% 0.59/0.76      inference('demod', [status(thm)], ['92', '93'])).
% 0.59/0.76  thf('95', plain, ((v1_relat_1 @ sk_C)),
% 0.59/0.76      inference('demod', [status(thm)], ['70', '71'])).
% 0.59/0.76  thf('96', plain, (((sk_D) = (k4_relat_1 @ sk_C))),
% 0.59/0.76      inference('demod', [status(thm)], ['83', '94', '95'])).
% 0.59/0.76  thf('97', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('98', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.59/0.76      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.59/0.76  thf('99', plain, (((sk_D) != (k4_relat_1 @ sk_C))),
% 0.59/0.76      inference('demod', [status(thm)], ['97', '98'])).
% 0.59/0.76  thf('100', plain, ($false),
% 0.59/0.76      inference('simplify_reflect-', [status(thm)], ['96', '99'])).
% 0.59/0.76  
% 0.59/0.76  % SZS output end Refutation
% 0.59/0.76  
% 0.61/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

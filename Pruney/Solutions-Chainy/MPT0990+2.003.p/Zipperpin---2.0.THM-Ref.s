%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BJf8RdSUI0

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:53 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :  465 (2038 expanded)
%              Number of leaves         :   54 ( 636 expanded)
%              Depth                    :   48
%              Number of atoms          : 3974 (41008 expanded)
%              Number of equality atoms :  222 (2723 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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

thf('2',plain,(
    ! [X56: $i,X57: $i,X58: $i,X59: $i] :
      ( ~ ( v1_funct_1 @ X56 )
      | ~ ( v1_funct_2 @ X56 @ X57 @ X58 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X58 ) ) )
      | ~ ( r2_relset_1 @ X57 @ X57 @ ( k1_partfun1 @ X57 @ X58 @ X58 @ X57 @ X56 @ X59 ) @ ( k6_partfun1 @ X57 ) )
      | ( ( k2_relset_1 @ X58 @ X57 @ X59 )
        = X57 )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X57 ) ) )
      | ~ ( v1_funct_2 @ X59 @ X58 @ X57 )
      | ~ ( v1_funct_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('9',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k2_relset_1 @ X35 @ X36 @ X34 )
        = ( k2_relat_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('10',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['7','10','11','12','13'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('17',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ X18 )
      | ( ( k5_relat_1 @ X17 @ ( k6_relat_1 @ X18 ) )
        = X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('18',plain,(
    ! [X55: $i] :
      ( ( k6_partfun1 @ X55 )
      = ( k6_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('19',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ X18 )
      | ( ( k5_relat_1 @ X17 @ ( k6_partfun1 @ X18 ) )
        = X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ sk_A ) )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['14','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('23',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_relat_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('24',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ sk_A ) )
    = sk_D ),
    inference(demod,[status(thm)],['21','24'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('26',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) )
        = ( k10_relat_1 @ X8 @ ( k1_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('27',plain,(
    ! [X16: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X16 ) ) @ X16 )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('28',plain,(
    ! [X55: $i] :
      ( ( k6_partfun1 @ X55 )
      = ( k6_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('29',plain,(
    ! [X16: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X16 ) ) @ X16 )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ sk_D @ ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) ) ) ) @ ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ sk_A ) ) )
      = ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['22','23'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('33',plain,(
    ! [X48: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X48 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('34',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_relat_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('37',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('38',plain,(
    ! [X55: $i] :
      ( ( k6_partfun1 @ X55 )
      = ( k6_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('39',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X14 ) )
      = X14 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['7','10','11','12','13'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('42',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) )
        = ( k10_relat_1 @ X8 @ ( k1_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X14 ) )
      = X14 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('45',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( k10_relat_1 @ sk_D @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['40','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['22','23'])).

thf('50',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( k10_relat_1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ sk_A ) )
    = sk_D ),
    inference(demod,[status(thm)],['21','24'])).

thf('52',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ sk_A ) )
    = sk_D ),
    inference(demod,[status(thm)],['21','24'])).

thf('53',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['31','32','35','36','39','50','51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('55',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v4_relat_1 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('56',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['54','55'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('57',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v4_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('58',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['22','23'])).

thf('60',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k2_relset_1 @ X35 @ X36 @ X34 )
        = ( k2_relat_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('63',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['63','64'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('66',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X20 @ ( k2_relat_1 @ X21 ) )
      | ( ( k9_relat_1 @ X21 @ ( k10_relat_1 @ X21 @ X20 ) )
        = X20 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_relat_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('70',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['67','70','71'])).

thf('73',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['60','72'])).

thf('74',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) )
        = ( k10_relat_1 @ X8 @ ( k1_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('75',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
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

thf('77',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['75','80'])).

thf('82',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
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

thf('85',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X54 ) ) )
      | ( ( k1_partfun1 @ X50 @ X51 @ X53 @ X54 @ X49 @ X52 )
        = ( k5_relat_1 @ X49 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['83','88'])).

thf('90',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['81','82','91'])).

thf('93',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v4_relat_1 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('94',plain,(
    v4_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ sk_A ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v4_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('96',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['81','82','91'])).

thf('98',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_relat_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('99',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) @ sk_A ),
    inference(demod,[status(thm)],['96','99'])).

thf('101',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['74','100'])).

thf('102',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('103',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['22','23'])).

thf('104',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) @ sk_A ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X14 ) )
      = X14 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('106',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ( v4_relat_1 @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( v4_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( v4_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    v4_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ) @ sk_A ),
    inference('sup-',[status(thm)],['104','109'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('111',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X9
        = ( k7_relat_1 @ X9 @ X10 ) )
      | ~ ( v4_relat_1 @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('112',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ) )
    | ( ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) )
      = ( k7_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('114',plain,
    ( ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) )
    = ( k7_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['112','113'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('115',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) )
        = ( k9_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('116',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ) )
      = ( k9_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X15: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('118',plain,(
    ! [X55: $i] :
      ( ( k6_partfun1 @ X55 )
      = ( k6_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('119',plain,(
    ! [X15: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X15 ) )
      = X15 ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) )
        = ( k10_relat_1 @ X8 @ ( k1_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('121',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) @ sk_A ),
    inference(demod,[status(thm)],['96','99'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( v4_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('123',plain,(
    v4_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) @ sk_A ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X9
        = ( k7_relat_1 @ X9 @ X10 ) )
      | ~ ( v4_relat_1 @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('125',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) )
    | ( ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
      = ( k7_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('127',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
    = ( k7_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) )
        = ( k9_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('129',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) )
      = ( k9_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X15: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X15 ) )
      = X15 ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('131',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('132',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    = ( k9_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
      = ( k9_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['120','132'])).

thf('134',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('135',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['22','23'])).

thf('136',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    = ( k9_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['133','134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('138',plain,
    ( ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) )
    = ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['116','119','136','137'])).

thf('139',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('141',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['81','82','91'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('143',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( X37 = X40 )
      | ~ ( r2_relset_1 @ X38 @ X39 @ X37 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['141','144'])).

thf('146',plain,(
    ! [X48: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X48 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('147',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X14 ) )
      = X14 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('149',plain,
    ( ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) )
    = sk_A ),
    inference(demod,[status(thm)],['138','147','148'])).

thf('150',plain,
    ( ( k9_relat_1 @ sk_C @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['73','149'])).

thf('151',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v4_relat_1 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('153',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X9
        = ( k7_relat_1 @ X9 @ X10 ) )
      | ~ ( v4_relat_1 @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('155',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('157',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) )
        = ( k9_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('159',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['157','158'])).

thf('160',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('161',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['63','64'])).

thf('163',plain,
    ( sk_B
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['150','163'])).

thf('165',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['53','164'])).

thf('166',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['145','146'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('167',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('168',plain,(
    ! [X19: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('169',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('170',plain,(
    ! [X27: $i] :
      ( ~ ( v2_funct_1 @ X27 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X27 ) )
        = X27 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('171',plain,(
    ! [X27: $i] :
      ( ~ ( v2_funct_1 @ X27 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X27 ) )
        = X27 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('172',plain,(
    ! [X27: $i] :
      ( ~ ( v2_funct_1 @ X27 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X27 ) )
        = X27 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('173',plain,(
    ! [X19: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('174',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
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

thf('175',plain,(
    ! [X25: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k2_relat_1 @ X25 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('176',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('177',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['63','64'])).

thf('178',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('179',plain,(
    ! [X25: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k2_relat_1 @ X25 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('180',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('181',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ( v4_relat_1 @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('182',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['179','182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['178','183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['177','185'])).

thf('187',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('188',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['186','187','188','189'])).

thf('191',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v4_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('192',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['176','192'])).

thf('194',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('195',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['193','194','195'])).

thf('197',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('198',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['175','198'])).

thf('200',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['63','64'])).

thf('201',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('202',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('203',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['199','200','201','202','203','204'])).

thf('206',plain,(
    ! [X25: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k1_relat_1 @ X25 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('207',plain,(
    ! [X19: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('208',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
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

thf('209',plain,(
    ! [X26: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X26 ) @ X26 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('210',plain,(
    ! [X55: $i] :
      ( ( k6_partfun1 @ X55 )
      = ( k6_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('211',plain,(
    ! [X26: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X26 ) @ X26 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(demod,[status(thm)],['209','210'])).

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

thf('212',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ( v2_funct_1 @ X22 )
      | ( ( k2_relat_1 @ X22 )
       != ( k1_relat_1 @ X23 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X22 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('213',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('214',plain,(
    ! [X24: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('215',plain,(
    ! [X55: $i] :
      ( ( k6_partfun1 @ X55 )
      = ( k6_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('216',plain,(
    ! [X24: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X24 ) ) ),
    inference(demod,[status(thm)],['214','215'])).

thf('217',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['213','216'])).

thf('218',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['217'])).

thf('219',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['208','218'])).

thf('220',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['219'])).

thf('221',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['207','220'])).

thf('222',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['221'])).

thf('223',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['206','222'])).

thf('224',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['223'])).

thf('225',plain,(
    ! [X19: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('226',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('227',plain,(
    ! [X27: $i] :
      ( ~ ( v2_funct_1 @ X27 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X27 ) )
        = X27 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('228',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['184'])).

thf('229',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['227','228'])).

thf('230',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['226','229'])).

thf('231',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['230'])).

thf('232',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['225','231'])).

thf('233',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['232'])).

thf('234',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['224','233'])).

thf('235',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['234'])).

thf('236',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v4_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('237',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['235','236'])).

thf('238',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['237'])).

thf('239',plain,
    ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['205','238'])).

thf('240',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('241',plain,(
    ! [X19: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('242',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('243',plain,(
    ! [X26: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k5_relat_1 @ X26 @ ( k2_funct_1 @ X26 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('244',plain,(
    ! [X55: $i] :
      ( ( k6_partfun1 @ X55 )
      = ( k6_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('245',plain,(
    ! [X26: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k5_relat_1 @ X26 @ ( k2_funct_1 @ X26 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(demod,[status(thm)],['243','244'])).

thf('246',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['63','64'])).

thf('247',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('248',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['246','247'])).

thf('249',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('250',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['248','249'])).

thf('251',plain,(
    ! [X16: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X16 ) ) @ X16 )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
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

thf('252',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) @ X13 )
        = ( k5_relat_1 @ X12 @ ( k5_relat_1 @ X11 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('253',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['251','252'])).

thf('254',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('255',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['253','254'])).

thf('256',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['255'])).

thf('257',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['250','256'])).

thf('258',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['248','249'])).

thf('259',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('260',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('261',plain,
    ( sk_C
    = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['257','258','259','260'])).

thf('262',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) @ X13 )
        = ( k5_relat_1 @ X12 @ ( k5_relat_1 @ X11 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('263',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['261','262'])).

thf('264',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('265',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('266',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['263','264','265'])).

thf('267',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['245','266'])).

thf('268',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X14 ) )
      = X14 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('269',plain,(
    ! [X16: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X16 ) ) @ X16 )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('270',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['268','269'])).

thf('271',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('272',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['270','271'])).

thf('273',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('274',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('275',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['267','272','273','274','275'])).

thf('277',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['242','276'])).

thf('278',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('279',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('280',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['277','278','279'])).

thf('281',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ( v2_funct_1 @ X23 )
      | ( ( k2_relat_1 @ X22 )
       != ( k1_relat_1 @ X23 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X22 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('282',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['280','281'])).

thf('283',plain,(
    ! [X24: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X24 ) ) ),
    inference(demod,[status(thm)],['214','215'])).

thf('284',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['63','64'])).

thf('285',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['199','200','201','202','203','204'])).

thf('286',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('287',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('288',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_B != sk_B )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['282','283','284','285','286','287'])).

thf('289',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['288'])).

thf('290',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['241','289'])).

thf('291',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('292',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('293',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['290','291','292'])).

thf('294',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['240','293'])).

thf('295',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('296',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('297',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['294','295','296'])).

thf('298',plain,
    ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['239','297'])).

thf('299',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['174','298'])).

thf('300',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('301',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('302',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['299','300','301'])).

thf('303',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['173','302'])).

thf('304',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('305',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('306',plain,(
    r1_tarski @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['303','304','305'])).

thf('307',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('308',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) @ sk_B )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['306','307'])).

thf('309',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['172','308'])).

thf('310',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['63','64'])).

thf('311',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('312',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('313',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('314',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('315',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    = sk_B ),
    inference(demod,[status(thm)],['309','310','311','312','313','314'])).

thf('316',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('317',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k6_partfun1 @ sk_B ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['315','316'])).

thf('318',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k6_partfun1 @ sk_B ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['171','317'])).

thf('319',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('320',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('321',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('322',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('323',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k6_partfun1 @ sk_B ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['318','319','320','321','322'])).

thf('324',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['170','323'])).

thf('325',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['248','249'])).

thf('326',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('327',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('328',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('329',plain,
    ( sk_C
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['324','325','326','327','328'])).

thf('330',plain,(
    ! [X26: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k5_relat_1 @ X26 @ ( k2_funct_1 @ X26 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(demod,[status(thm)],['243','244'])).

thf('331',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['329','330'])).

thf('332',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['199','200','201','202','203','204'])).

thf('333',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['294','295','296'])).

thf('334',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['331','332','333'])).

thf('335',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['169','334'])).

thf('336',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('337',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('338',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['335','336','337'])).

thf('339',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['168','338'])).

thf('340',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('341',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('342',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['339','340','341'])).

thf('343',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) @ X13 )
        = ( k5_relat_1 @ X12 @ ( k5_relat_1 @ X11 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('344',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['342','343'])).

thf('345',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('346',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['344','345'])).

thf('347',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['167','346'])).

thf('348',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('349',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('350',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['347','348','349'])).

thf('351',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['166','350'])).

thf('352',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['151','152'])).

thf('353',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v4_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('354',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['352','353'])).

thf('355',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('356',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['354','355'])).

thf('357',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('358',plain,(
    ! [X25: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k1_relat_1 @ X25 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('359',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['237'])).

thf('360',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['248','249'])).

thf('361',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X14 ) )
      = X14 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('362',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) )
        = ( k10_relat_1 @ X8 @ ( k1_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('363',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ( v4_relat_1 @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('364',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( v4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['362','363'])).

thf('365',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ X2 @ X0 ) @ X1 )
      | ( v4_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_partfun1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['361','364'])).

thf('366',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('367',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ X2 @ X0 ) @ X1 )
      | ( v4_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_partfun1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['365','366'])).

thf('368',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C )
      | ( v4_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ X0 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['360','367'])).

thf('369',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('370',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('371',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['248','249'])).

thf('372',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ sk_C @ X0 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['368','369','370','371'])).

thf('373',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['248','249'])).

thf('374',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) )
        = ( k10_relat_1 @ X8 @ ( k1_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('375',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['373','374'])).

thf('376',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X14 ) )
      = X14 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('377',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('378',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('379',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['375','376','377','378'])).

thf('380',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ sk_C @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['372','379'])).

thf('381',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['359','380'])).

thf('382',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('383',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('384',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('385',plain,(
    v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['381','382','383','384'])).

thf('386',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v4_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('387',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['385','386'])).

thf('388',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('389',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['387','388'])).

thf('390',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('391',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['389','390'])).

thf('392',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['358','391'])).

thf('393',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('394',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('395',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('396',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('397',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['392','393','394','395','396'])).

thf('398',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ X18 )
      | ( ( k5_relat_1 @ X17 @ ( k6_partfun1 @ X18 ) )
        = X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('399',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ X0 ) )
        = ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['397','398'])).

thf('400',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ X0 ) )
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['357','399'])).

thf('401',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('402',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('403',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ X0 ) )
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['400','401','402'])).

thf('404',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['356','403'])).

thf('405',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['22','23'])).

thf('406',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['351','404','405'])).

thf('407',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['165','406'])).

thf('408',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('409',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['407','408'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BJf8RdSUI0
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:31:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.30/1.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.30/1.51  % Solved by: fo/fo7.sh
% 1.30/1.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.30/1.51  % done 1261 iterations in 1.047s
% 1.30/1.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.30/1.51  % SZS output start Refutation
% 1.30/1.51  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.30/1.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.30/1.51  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.30/1.51  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.30/1.51  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.30/1.51  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.30/1.51  thf(sk_B_type, type, sk_B: $i).
% 1.30/1.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.30/1.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.30/1.51  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.30/1.51  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.30/1.51  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.30/1.51  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.30/1.51  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.30/1.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.30/1.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.30/1.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.30/1.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.30/1.51  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.30/1.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.30/1.51  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.30/1.51  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.30/1.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.30/1.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.30/1.51  thf(sk_C_type, type, sk_C: $i).
% 1.30/1.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.30/1.51  thf(sk_A_type, type, sk_A: $i).
% 1.30/1.51  thf(sk_D_type, type, sk_D: $i).
% 1.30/1.51  thf(t36_funct_2, conjecture,
% 1.30/1.51    (![A:$i,B:$i,C:$i]:
% 1.30/1.51     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.30/1.51         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.30/1.51       ( ![D:$i]:
% 1.30/1.51         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.30/1.51             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.30/1.51           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.30/1.51               ( r2_relset_1 @
% 1.30/1.51                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.30/1.51                 ( k6_partfun1 @ A ) ) & 
% 1.30/1.51               ( v2_funct_1 @ C ) ) =>
% 1.30/1.51             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.30/1.51               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.30/1.51  thf(zf_stmt_0, negated_conjecture,
% 1.30/1.51    (~( ![A:$i,B:$i,C:$i]:
% 1.30/1.51        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.30/1.51            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.30/1.51          ( ![D:$i]:
% 1.30/1.51            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.30/1.51                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.30/1.51              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.30/1.51                  ( r2_relset_1 @
% 1.30/1.51                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.30/1.51                    ( k6_partfun1 @ A ) ) & 
% 1.30/1.51                  ( v2_funct_1 @ C ) ) =>
% 1.30/1.51                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.30/1.51                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.30/1.51    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.30/1.51  thf('0', plain,
% 1.30/1.51      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.30/1.51        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.30/1.51        (k6_partfun1 @ sk_A))),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('1', plain,
% 1.30/1.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf(t24_funct_2, axiom,
% 1.30/1.51    (![A:$i,B:$i,C:$i]:
% 1.30/1.51     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.30/1.51         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.30/1.51       ( ![D:$i]:
% 1.30/1.51         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.30/1.51             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.30/1.51           ( ( r2_relset_1 @
% 1.30/1.51               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 1.30/1.51               ( k6_partfun1 @ B ) ) =>
% 1.30/1.51             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 1.30/1.51  thf('2', plain,
% 1.30/1.51      (![X56 : $i, X57 : $i, X58 : $i, X59 : $i]:
% 1.30/1.51         (~ (v1_funct_1 @ X56)
% 1.30/1.51          | ~ (v1_funct_2 @ X56 @ X57 @ X58)
% 1.30/1.51          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X58)))
% 1.30/1.51          | ~ (r2_relset_1 @ X57 @ X57 @ 
% 1.30/1.51               (k1_partfun1 @ X57 @ X58 @ X58 @ X57 @ X56 @ X59) @ 
% 1.30/1.51               (k6_partfun1 @ X57))
% 1.30/1.51          | ((k2_relset_1 @ X58 @ X57 @ X59) = (X57))
% 1.30/1.51          | ~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X57)))
% 1.30/1.51          | ~ (v1_funct_2 @ X59 @ X58 @ X57)
% 1.30/1.51          | ~ (v1_funct_1 @ X59))),
% 1.30/1.51      inference('cnf', [status(esa)], [t24_funct_2])).
% 1.30/1.51  thf('3', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.30/1.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.30/1.51          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.30/1.51          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.30/1.51               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.30/1.51               (k6_partfun1 @ sk_A))
% 1.30/1.51          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.30/1.51          | ~ (v1_funct_1 @ sk_C))),
% 1.30/1.51      inference('sup-', [status(thm)], ['1', '2'])).
% 1.30/1.51  thf('4', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('6', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.30/1.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.30/1.51          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.30/1.51          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.30/1.51               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.30/1.51               (k6_partfun1 @ sk_A)))),
% 1.30/1.51      inference('demod', [status(thm)], ['3', '4', '5'])).
% 1.30/1.51  thf('7', plain,
% 1.30/1.51      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 1.30/1.51        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.30/1.51        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.30/1.51        | ~ (v1_funct_1 @ sk_D))),
% 1.30/1.51      inference('sup-', [status(thm)], ['0', '6'])).
% 1.30/1.51  thf('8', plain,
% 1.30/1.51      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf(redefinition_k2_relset_1, axiom,
% 1.30/1.51    (![A:$i,B:$i,C:$i]:
% 1.30/1.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.30/1.51       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.30/1.51  thf('9', plain,
% 1.30/1.51      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.30/1.51         (((k2_relset_1 @ X35 @ X36 @ X34) = (k2_relat_1 @ X34))
% 1.30/1.51          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 1.30/1.51      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.30/1.51  thf('10', plain,
% 1.30/1.51      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.30/1.51      inference('sup-', [status(thm)], ['8', '9'])).
% 1.30/1.51  thf('11', plain,
% 1.30/1.51      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('12', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('13', plain, ((v1_funct_1 @ sk_D)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('14', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.30/1.51      inference('demod', [status(thm)], ['7', '10', '11', '12', '13'])).
% 1.30/1.51  thf(d10_xboole_0, axiom,
% 1.30/1.51    (![A:$i,B:$i]:
% 1.30/1.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.30/1.51  thf('15', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.30/1.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.30/1.51  thf('16', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.30/1.51      inference('simplify', [status(thm)], ['15'])).
% 1.30/1.51  thf(t79_relat_1, axiom,
% 1.30/1.51    (![A:$i,B:$i]:
% 1.30/1.51     ( ( v1_relat_1 @ B ) =>
% 1.30/1.51       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 1.30/1.51         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 1.30/1.51  thf('17', plain,
% 1.30/1.51      (![X17 : $i, X18 : $i]:
% 1.30/1.51         (~ (r1_tarski @ (k2_relat_1 @ X17) @ X18)
% 1.30/1.51          | ((k5_relat_1 @ X17 @ (k6_relat_1 @ X18)) = (X17))
% 1.30/1.51          | ~ (v1_relat_1 @ X17))),
% 1.30/1.51      inference('cnf', [status(esa)], [t79_relat_1])).
% 1.30/1.51  thf(redefinition_k6_partfun1, axiom,
% 1.30/1.51    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.30/1.51  thf('18', plain, (![X55 : $i]: ((k6_partfun1 @ X55) = (k6_relat_1 @ X55))),
% 1.30/1.51      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.30/1.51  thf('19', plain,
% 1.30/1.51      (![X17 : $i, X18 : $i]:
% 1.30/1.51         (~ (r1_tarski @ (k2_relat_1 @ X17) @ X18)
% 1.30/1.51          | ((k5_relat_1 @ X17 @ (k6_partfun1 @ X18)) = (X17))
% 1.30/1.51          | ~ (v1_relat_1 @ X17))),
% 1.30/1.51      inference('demod', [status(thm)], ['17', '18'])).
% 1.30/1.51  thf('20', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (~ (v1_relat_1 @ X0)
% 1.30/1.51          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) = (X0)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['16', '19'])).
% 1.30/1.51  thf('21', plain,
% 1.30/1.51      ((((k5_relat_1 @ sk_D @ (k6_partfun1 @ sk_A)) = (sk_D))
% 1.30/1.51        | ~ (v1_relat_1 @ sk_D))),
% 1.30/1.51      inference('sup+', [status(thm)], ['14', '20'])).
% 1.30/1.51  thf('22', plain,
% 1.30/1.51      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf(cc1_relset_1, axiom,
% 1.30/1.51    (![A:$i,B:$i,C:$i]:
% 1.30/1.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.30/1.51       ( v1_relat_1 @ C ) ))).
% 1.30/1.51  thf('23', plain,
% 1.30/1.51      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.30/1.51         ((v1_relat_1 @ X28)
% 1.30/1.51          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 1.30/1.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.30/1.51  thf('24', plain, ((v1_relat_1 @ sk_D)),
% 1.30/1.51      inference('sup-', [status(thm)], ['22', '23'])).
% 1.30/1.51  thf('25', plain, (((k5_relat_1 @ sk_D @ (k6_partfun1 @ sk_A)) = (sk_D))),
% 1.30/1.51      inference('demod', [status(thm)], ['21', '24'])).
% 1.30/1.51  thf(t182_relat_1, axiom,
% 1.30/1.51    (![A:$i]:
% 1.30/1.51     ( ( v1_relat_1 @ A ) =>
% 1.30/1.51       ( ![B:$i]:
% 1.30/1.51         ( ( v1_relat_1 @ B ) =>
% 1.30/1.51           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.30/1.51             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 1.30/1.51  thf('26', plain,
% 1.30/1.51      (![X7 : $i, X8 : $i]:
% 1.30/1.51         (~ (v1_relat_1 @ X7)
% 1.30/1.51          | ((k1_relat_1 @ (k5_relat_1 @ X8 @ X7))
% 1.30/1.51              = (k10_relat_1 @ X8 @ (k1_relat_1 @ X7)))
% 1.30/1.51          | ~ (v1_relat_1 @ X8))),
% 1.30/1.51      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.30/1.51  thf(t78_relat_1, axiom,
% 1.30/1.51    (![A:$i]:
% 1.30/1.51     ( ( v1_relat_1 @ A ) =>
% 1.30/1.51       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 1.30/1.51  thf('27', plain,
% 1.30/1.51      (![X16 : $i]:
% 1.30/1.51         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X16)) @ X16) = (X16))
% 1.30/1.51          | ~ (v1_relat_1 @ X16))),
% 1.30/1.51      inference('cnf', [status(esa)], [t78_relat_1])).
% 1.30/1.51  thf('28', plain, (![X55 : $i]: ((k6_partfun1 @ X55) = (k6_relat_1 @ X55))),
% 1.30/1.51      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.30/1.51  thf('29', plain,
% 1.30/1.51      (![X16 : $i]:
% 1.30/1.51         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X16)) @ X16) = (X16))
% 1.30/1.51          | ~ (v1_relat_1 @ X16))),
% 1.30/1.51      inference('demod', [status(thm)], ['27', '28'])).
% 1.30/1.51  thf('30', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]:
% 1.30/1.51         (((k5_relat_1 @ 
% 1.30/1.51            (k6_partfun1 @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0))) @ 
% 1.30/1.51            (k5_relat_1 @ X1 @ X0)) = (k5_relat_1 @ X1 @ X0))
% 1.30/1.51          | ~ (v1_relat_1 @ X1)
% 1.30/1.51          | ~ (v1_relat_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 1.30/1.51      inference('sup+', [status(thm)], ['26', '29'])).
% 1.30/1.51  thf('31', plain,
% 1.30/1.51      ((~ (v1_relat_1 @ sk_D)
% 1.30/1.51        | ~ (v1_relat_1 @ (k6_partfun1 @ sk_A))
% 1.30/1.51        | ~ (v1_relat_1 @ sk_D)
% 1.30/1.51        | ((k5_relat_1 @ 
% 1.30/1.51            (k6_partfun1 @ 
% 1.30/1.51             (k10_relat_1 @ sk_D @ (k1_relat_1 @ (k6_partfun1 @ sk_A)))) @ 
% 1.30/1.51            (k5_relat_1 @ sk_D @ (k6_partfun1 @ sk_A)))
% 1.30/1.51            = (k5_relat_1 @ sk_D @ (k6_partfun1 @ sk_A))))),
% 1.30/1.51      inference('sup-', [status(thm)], ['25', '30'])).
% 1.30/1.51  thf('32', plain, ((v1_relat_1 @ sk_D)),
% 1.30/1.51      inference('sup-', [status(thm)], ['22', '23'])).
% 1.30/1.51  thf(dt_k6_partfun1, axiom,
% 1.30/1.51    (![A:$i]:
% 1.30/1.51     ( ( m1_subset_1 @
% 1.30/1.51         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 1.30/1.51       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 1.30/1.51  thf('33', plain,
% 1.30/1.51      (![X48 : $i]:
% 1.30/1.51         (m1_subset_1 @ (k6_partfun1 @ X48) @ 
% 1.30/1.51          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X48)))),
% 1.30/1.51      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.30/1.51  thf('34', plain,
% 1.30/1.51      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.30/1.51         ((v1_relat_1 @ X28)
% 1.30/1.51          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 1.30/1.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.30/1.51  thf('35', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.30/1.51      inference('sup-', [status(thm)], ['33', '34'])).
% 1.30/1.51  thf('36', plain, ((v1_relat_1 @ sk_D)),
% 1.30/1.51      inference('sup-', [status(thm)], ['22', '23'])).
% 1.30/1.51  thf(t71_relat_1, axiom,
% 1.30/1.51    (![A:$i]:
% 1.30/1.51     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.30/1.51       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.30/1.51  thf('37', plain, (![X14 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X14)) = (X14))),
% 1.30/1.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.30/1.51  thf('38', plain, (![X55 : $i]: ((k6_partfun1 @ X55) = (k6_relat_1 @ X55))),
% 1.30/1.51      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.30/1.51  thf('39', plain, (![X14 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X14)) = (X14))),
% 1.30/1.51      inference('demod', [status(thm)], ['37', '38'])).
% 1.30/1.51  thf('40', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.30/1.51      inference('demod', [status(thm)], ['7', '10', '11', '12', '13'])).
% 1.30/1.51  thf('41', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (~ (v1_relat_1 @ X0)
% 1.30/1.51          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) = (X0)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['16', '19'])).
% 1.30/1.51  thf('42', plain,
% 1.30/1.51      (![X7 : $i, X8 : $i]:
% 1.30/1.51         (~ (v1_relat_1 @ X7)
% 1.30/1.51          | ((k1_relat_1 @ (k5_relat_1 @ X8 @ X7))
% 1.30/1.51              = (k10_relat_1 @ X8 @ (k1_relat_1 @ X7)))
% 1.30/1.51          | ~ (v1_relat_1 @ X8))),
% 1.30/1.51      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.30/1.51  thf('43', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (((k1_relat_1 @ X0)
% 1.30/1.51            = (k10_relat_1 @ X0 @ 
% 1.30/1.51               (k1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)))))
% 1.30/1.51          | ~ (v1_relat_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0))))),
% 1.30/1.51      inference('sup+', [status(thm)], ['41', '42'])).
% 1.30/1.51  thf('44', plain, (![X14 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X14)) = (X14))),
% 1.30/1.51      inference('demod', [status(thm)], ['37', '38'])).
% 1.30/1.51  thf('45', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.30/1.51      inference('sup-', [status(thm)], ['33', '34'])).
% 1.30/1.51  thf('46', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 1.30/1.51          | ~ (v1_relat_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ X0))),
% 1.30/1.51      inference('demod', [status(thm)], ['43', '44', '45'])).
% 1.30/1.51  thf('47', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (~ (v1_relat_1 @ X0)
% 1.30/1.51          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 1.30/1.51      inference('simplify', [status(thm)], ['46'])).
% 1.30/1.51  thf('48', plain,
% 1.30/1.51      ((((k1_relat_1 @ sk_D) = (k10_relat_1 @ sk_D @ sk_A))
% 1.30/1.51        | ~ (v1_relat_1 @ sk_D))),
% 1.30/1.51      inference('sup+', [status(thm)], ['40', '47'])).
% 1.30/1.51  thf('49', plain, ((v1_relat_1 @ sk_D)),
% 1.30/1.51      inference('sup-', [status(thm)], ['22', '23'])).
% 1.30/1.51  thf('50', plain, (((k1_relat_1 @ sk_D) = (k10_relat_1 @ sk_D @ sk_A))),
% 1.30/1.51      inference('demod', [status(thm)], ['48', '49'])).
% 1.30/1.51  thf('51', plain, (((k5_relat_1 @ sk_D @ (k6_partfun1 @ sk_A)) = (sk_D))),
% 1.30/1.51      inference('demod', [status(thm)], ['21', '24'])).
% 1.30/1.51  thf('52', plain, (((k5_relat_1 @ sk_D @ (k6_partfun1 @ sk_A)) = (sk_D))),
% 1.30/1.51      inference('demod', [status(thm)], ['21', '24'])).
% 1.30/1.51  thf('53', plain,
% 1.30/1.51      (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ sk_D) = (sk_D))),
% 1.30/1.51      inference('demod', [status(thm)],
% 1.30/1.51                ['31', '32', '35', '36', '39', '50', '51', '52'])).
% 1.30/1.51  thf('54', plain,
% 1.30/1.51      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf(cc2_relset_1, axiom,
% 1.30/1.51    (![A:$i,B:$i,C:$i]:
% 1.30/1.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.30/1.51       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.30/1.51  thf('55', plain,
% 1.30/1.51      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.30/1.51         ((v4_relat_1 @ X31 @ X32)
% 1.30/1.51          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 1.30/1.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.30/1.51  thf('56', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 1.30/1.51      inference('sup-', [status(thm)], ['54', '55'])).
% 1.30/1.51  thf(d18_relat_1, axiom,
% 1.30/1.51    (![A:$i,B:$i]:
% 1.30/1.51     ( ( v1_relat_1 @ B ) =>
% 1.30/1.51       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.30/1.51  thf('57', plain,
% 1.30/1.51      (![X3 : $i, X4 : $i]:
% 1.30/1.51         (~ (v4_relat_1 @ X3 @ X4)
% 1.30/1.51          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.30/1.51          | ~ (v1_relat_1 @ X3))),
% 1.30/1.51      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.30/1.51  thf('58', plain,
% 1.30/1.51      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B))),
% 1.30/1.51      inference('sup-', [status(thm)], ['56', '57'])).
% 1.30/1.51  thf('59', plain, ((v1_relat_1 @ sk_D)),
% 1.30/1.51      inference('sup-', [status(thm)], ['22', '23'])).
% 1.30/1.51  thf('60', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 1.30/1.51      inference('demod', [status(thm)], ['58', '59'])).
% 1.30/1.51  thf('61', plain,
% 1.30/1.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('62', plain,
% 1.30/1.51      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.30/1.51         (((k2_relset_1 @ X35 @ X36 @ X34) = (k2_relat_1 @ X34))
% 1.30/1.51          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 1.30/1.51      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.30/1.51  thf('63', plain,
% 1.30/1.51      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.30/1.51      inference('sup-', [status(thm)], ['61', '62'])).
% 1.30/1.51  thf('64', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('65', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.30/1.51      inference('sup+', [status(thm)], ['63', '64'])).
% 1.30/1.51  thf(t147_funct_1, axiom,
% 1.30/1.51    (![A:$i,B:$i]:
% 1.30/1.51     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.30/1.51       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 1.30/1.51         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 1.30/1.51  thf('66', plain,
% 1.30/1.51      (![X20 : $i, X21 : $i]:
% 1.30/1.51         (~ (r1_tarski @ X20 @ (k2_relat_1 @ X21))
% 1.30/1.51          | ((k9_relat_1 @ X21 @ (k10_relat_1 @ X21 @ X20)) = (X20))
% 1.30/1.51          | ~ (v1_funct_1 @ X21)
% 1.30/1.51          | ~ (v1_relat_1 @ X21))),
% 1.30/1.51      inference('cnf', [status(esa)], [t147_funct_1])).
% 1.30/1.51  thf('67', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (~ (r1_tarski @ X0 @ sk_B)
% 1.30/1.51          | ~ (v1_relat_1 @ sk_C)
% 1.30/1.51          | ~ (v1_funct_1 @ sk_C)
% 1.30/1.51          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['65', '66'])).
% 1.30/1.51  thf('68', plain,
% 1.30/1.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('69', plain,
% 1.30/1.51      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.30/1.51         ((v1_relat_1 @ X28)
% 1.30/1.51          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 1.30/1.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.30/1.51  thf('70', plain, ((v1_relat_1 @ sk_C)),
% 1.30/1.51      inference('sup-', [status(thm)], ['68', '69'])).
% 1.30/1.51  thf('71', plain, ((v1_funct_1 @ sk_C)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('72', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (~ (r1_tarski @ X0 @ sk_B)
% 1.30/1.51          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 1.30/1.51      inference('demod', [status(thm)], ['67', '70', '71'])).
% 1.30/1.51  thf('73', plain,
% 1.30/1.51      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 1.30/1.51         = (k1_relat_1 @ sk_D))),
% 1.30/1.51      inference('sup-', [status(thm)], ['60', '72'])).
% 1.30/1.51  thf('74', plain,
% 1.30/1.51      (![X7 : $i, X8 : $i]:
% 1.30/1.51         (~ (v1_relat_1 @ X7)
% 1.30/1.51          | ((k1_relat_1 @ (k5_relat_1 @ X8 @ X7))
% 1.30/1.51              = (k10_relat_1 @ X8 @ (k1_relat_1 @ X7)))
% 1.30/1.51          | ~ (v1_relat_1 @ X8))),
% 1.30/1.51      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.30/1.51  thf('75', plain,
% 1.30/1.51      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('76', plain,
% 1.30/1.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf(dt_k1_partfun1, axiom,
% 1.30/1.51    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.30/1.51     ( ( ( v1_funct_1 @ E ) & 
% 1.30/1.51         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.30/1.51         ( v1_funct_1 @ F ) & 
% 1.30/1.51         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.30/1.51       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.30/1.51         ( m1_subset_1 @
% 1.30/1.51           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.30/1.51           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.30/1.51  thf('77', plain,
% 1.30/1.51      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 1.30/1.51         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 1.30/1.51          | ~ (v1_funct_1 @ X41)
% 1.30/1.51          | ~ (v1_funct_1 @ X44)
% 1.30/1.51          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 1.30/1.51          | (m1_subset_1 @ (k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44) @ 
% 1.30/1.51             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X46))))),
% 1.30/1.51      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.30/1.51  thf('78', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.30/1.51         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.30/1.51           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.30/1.51          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.30/1.51          | ~ (v1_funct_1 @ X1)
% 1.30/1.51          | ~ (v1_funct_1 @ sk_C))),
% 1.30/1.51      inference('sup-', [status(thm)], ['76', '77'])).
% 1.30/1.51  thf('79', plain, ((v1_funct_1 @ sk_C)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('80', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.30/1.51         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.30/1.51           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.30/1.51          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.30/1.51          | ~ (v1_funct_1 @ X1))),
% 1.30/1.51      inference('demod', [status(thm)], ['78', '79'])).
% 1.30/1.51  thf('81', plain,
% 1.30/1.51      ((~ (v1_funct_1 @ sk_D)
% 1.30/1.51        | (m1_subset_1 @ 
% 1.30/1.51           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.30/1.51           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.30/1.51      inference('sup-', [status(thm)], ['75', '80'])).
% 1.30/1.51  thf('82', plain, ((v1_funct_1 @ sk_D)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('83', plain,
% 1.30/1.51      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('84', plain,
% 1.30/1.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf(redefinition_k1_partfun1, axiom,
% 1.30/1.51    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.30/1.51     ( ( ( v1_funct_1 @ E ) & 
% 1.30/1.51         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.30/1.51         ( v1_funct_1 @ F ) & 
% 1.30/1.51         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.30/1.51       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.30/1.51  thf('85', plain,
% 1.30/1.51      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 1.30/1.51         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 1.30/1.51          | ~ (v1_funct_1 @ X49)
% 1.30/1.51          | ~ (v1_funct_1 @ X52)
% 1.30/1.51          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X54)))
% 1.30/1.51          | ((k1_partfun1 @ X50 @ X51 @ X53 @ X54 @ X49 @ X52)
% 1.30/1.51              = (k5_relat_1 @ X49 @ X52)))),
% 1.30/1.51      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.30/1.51  thf('86', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.30/1.51         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.30/1.51            = (k5_relat_1 @ sk_C @ X0))
% 1.30/1.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ sk_C))),
% 1.30/1.51      inference('sup-', [status(thm)], ['84', '85'])).
% 1.30/1.51  thf('87', plain, ((v1_funct_1 @ sk_C)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('88', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.30/1.51         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.30/1.51            = (k5_relat_1 @ sk_C @ X0))
% 1.30/1.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.30/1.51          | ~ (v1_funct_1 @ X0))),
% 1.30/1.51      inference('demod', [status(thm)], ['86', '87'])).
% 1.30/1.51  thf('89', plain,
% 1.30/1.51      ((~ (v1_funct_1 @ sk_D)
% 1.30/1.51        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.30/1.51            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['83', '88'])).
% 1.30/1.51  thf('90', plain, ((v1_funct_1 @ sk_D)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('91', plain,
% 1.30/1.51      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.30/1.51         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.30/1.51      inference('demod', [status(thm)], ['89', '90'])).
% 1.30/1.51  thf('92', plain,
% 1.30/1.51      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.30/1.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.30/1.51      inference('demod', [status(thm)], ['81', '82', '91'])).
% 1.30/1.51  thf('93', plain,
% 1.30/1.51      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.30/1.51         ((v4_relat_1 @ X31 @ X32)
% 1.30/1.51          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 1.30/1.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.30/1.51  thf('94', plain, ((v4_relat_1 @ (k5_relat_1 @ sk_C @ sk_D) @ sk_A)),
% 1.30/1.51      inference('sup-', [status(thm)], ['92', '93'])).
% 1.30/1.51  thf('95', plain,
% 1.30/1.51      (![X3 : $i, X4 : $i]:
% 1.30/1.51         (~ (v4_relat_1 @ X3 @ X4)
% 1.30/1.51          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.30/1.51          | ~ (v1_relat_1 @ X3))),
% 1.30/1.51      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.30/1.51  thf('96', plain,
% 1.30/1.51      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 1.30/1.51        | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ sk_A))),
% 1.30/1.51      inference('sup-', [status(thm)], ['94', '95'])).
% 1.30/1.51  thf('97', plain,
% 1.30/1.51      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.30/1.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.30/1.51      inference('demod', [status(thm)], ['81', '82', '91'])).
% 1.30/1.51  thf('98', plain,
% 1.30/1.51      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.30/1.51         ((v1_relat_1 @ X28)
% 1.30/1.51          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 1.30/1.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.30/1.51  thf('99', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))),
% 1.30/1.51      inference('sup-', [status(thm)], ['97', '98'])).
% 1.30/1.51  thf('100', plain,
% 1.30/1.51      ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ sk_A)),
% 1.30/1.51      inference('demod', [status(thm)], ['96', '99'])).
% 1.30/1.51  thf('101', plain,
% 1.30/1.51      (((r1_tarski @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)) @ sk_A)
% 1.30/1.51        | ~ (v1_relat_1 @ sk_C)
% 1.30/1.51        | ~ (v1_relat_1 @ sk_D))),
% 1.30/1.51      inference('sup+', [status(thm)], ['74', '100'])).
% 1.30/1.51  thf('102', plain, ((v1_relat_1 @ sk_C)),
% 1.30/1.51      inference('sup-', [status(thm)], ['68', '69'])).
% 1.30/1.51  thf('103', plain, ((v1_relat_1 @ sk_D)),
% 1.30/1.51      inference('sup-', [status(thm)], ['22', '23'])).
% 1.30/1.51  thf('104', plain,
% 1.30/1.51      ((r1_tarski @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)) @ sk_A)),
% 1.30/1.51      inference('demod', [status(thm)], ['101', '102', '103'])).
% 1.30/1.51  thf('105', plain,
% 1.30/1.51      (![X14 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X14)) = (X14))),
% 1.30/1.51      inference('demod', [status(thm)], ['37', '38'])).
% 1.30/1.51  thf('106', plain,
% 1.30/1.51      (![X3 : $i, X4 : $i]:
% 1.30/1.51         (~ (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.30/1.51          | (v4_relat_1 @ X3 @ X4)
% 1.30/1.51          | ~ (v1_relat_1 @ X3))),
% 1.30/1.51      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.30/1.51  thf('107', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]:
% 1.30/1.51         (~ (r1_tarski @ X0 @ X1)
% 1.30/1.51          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 1.30/1.51          | (v4_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 1.30/1.51      inference('sup-', [status(thm)], ['105', '106'])).
% 1.30/1.51  thf('108', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.30/1.51      inference('sup-', [status(thm)], ['33', '34'])).
% 1.30/1.51  thf('109', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]:
% 1.30/1.51         (~ (r1_tarski @ X0 @ X1) | (v4_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 1.30/1.51      inference('demod', [status(thm)], ['107', '108'])).
% 1.30/1.51  thf('110', plain,
% 1.30/1.51      ((v4_relat_1 @ 
% 1.30/1.51        (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))) @ sk_A)),
% 1.30/1.51      inference('sup-', [status(thm)], ['104', '109'])).
% 1.30/1.51  thf(t209_relat_1, axiom,
% 1.30/1.51    (![A:$i,B:$i]:
% 1.30/1.51     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.30/1.51       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 1.30/1.51  thf('111', plain,
% 1.30/1.51      (![X9 : $i, X10 : $i]:
% 1.30/1.51         (((X9) = (k7_relat_1 @ X9 @ X10))
% 1.30/1.51          | ~ (v4_relat_1 @ X9 @ X10)
% 1.30/1.51          | ~ (v1_relat_1 @ X9))),
% 1.30/1.51      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.30/1.51  thf('112', plain,
% 1.30/1.51      ((~ (v1_relat_1 @ 
% 1.30/1.51           (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))))
% 1.30/1.51        | ((k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 1.30/1.51            = (k7_relat_1 @ 
% 1.30/1.51               (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))) @ 
% 1.30/1.51               sk_A)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['110', '111'])).
% 1.30/1.51  thf('113', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.30/1.51      inference('sup-', [status(thm)], ['33', '34'])).
% 1.30/1.51  thf('114', plain,
% 1.30/1.51      (((k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 1.30/1.51         = (k7_relat_1 @ 
% 1.30/1.51            (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))) @ sk_A))),
% 1.30/1.51      inference('demod', [status(thm)], ['112', '113'])).
% 1.30/1.51  thf(t148_relat_1, axiom,
% 1.30/1.51    (![A:$i,B:$i]:
% 1.30/1.51     ( ( v1_relat_1 @ B ) =>
% 1.30/1.51       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 1.30/1.51  thf('115', plain,
% 1.30/1.51      (![X5 : $i, X6 : $i]:
% 1.30/1.51         (((k2_relat_1 @ (k7_relat_1 @ X5 @ X6)) = (k9_relat_1 @ X5 @ X6))
% 1.30/1.51          | ~ (v1_relat_1 @ X5))),
% 1.30/1.51      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.30/1.51  thf('116', plain,
% 1.30/1.51      ((((k2_relat_1 @ 
% 1.30/1.51          (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))))
% 1.30/1.51          = (k9_relat_1 @ 
% 1.30/1.51             (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))) @ sk_A))
% 1.30/1.51        | ~ (v1_relat_1 @ 
% 1.30/1.51             (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))))),
% 1.30/1.51      inference('sup+', [status(thm)], ['114', '115'])).
% 1.30/1.51  thf('117', plain, (![X15 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X15)) = (X15))),
% 1.30/1.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.30/1.51  thf('118', plain, (![X55 : $i]: ((k6_partfun1 @ X55) = (k6_relat_1 @ X55))),
% 1.30/1.51      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.30/1.51  thf('119', plain,
% 1.30/1.51      (![X15 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X15)) = (X15))),
% 1.30/1.51      inference('demod', [status(thm)], ['117', '118'])).
% 1.30/1.51  thf('120', plain,
% 1.30/1.51      (![X7 : $i, X8 : $i]:
% 1.30/1.51         (~ (v1_relat_1 @ X7)
% 1.30/1.51          | ((k1_relat_1 @ (k5_relat_1 @ X8 @ X7))
% 1.30/1.51              = (k10_relat_1 @ X8 @ (k1_relat_1 @ X7)))
% 1.30/1.51          | ~ (v1_relat_1 @ X8))),
% 1.30/1.51      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.30/1.51  thf('121', plain,
% 1.30/1.51      ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ sk_A)),
% 1.30/1.51      inference('demod', [status(thm)], ['96', '99'])).
% 1.30/1.51  thf('122', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]:
% 1.30/1.51         (~ (r1_tarski @ X0 @ X1) | (v4_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 1.30/1.51      inference('demod', [status(thm)], ['107', '108'])).
% 1.30/1.51  thf('123', plain,
% 1.30/1.51      ((v4_relat_1 @ 
% 1.30/1.51        (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))) @ sk_A)),
% 1.30/1.51      inference('sup-', [status(thm)], ['121', '122'])).
% 1.30/1.51  thf('124', plain,
% 1.30/1.51      (![X9 : $i, X10 : $i]:
% 1.30/1.51         (((X9) = (k7_relat_1 @ X9 @ X10))
% 1.30/1.51          | ~ (v4_relat_1 @ X9 @ X10)
% 1.30/1.51          | ~ (v1_relat_1 @ X9))),
% 1.30/1.51      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.30/1.51  thf('125', plain,
% 1.30/1.51      ((~ (v1_relat_1 @ 
% 1.30/1.51           (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))))
% 1.30/1.51        | ((k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 1.30/1.51            = (k7_relat_1 @ 
% 1.30/1.51               (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))) @ sk_A)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['123', '124'])).
% 1.30/1.51  thf('126', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.30/1.51      inference('sup-', [status(thm)], ['33', '34'])).
% 1.30/1.51  thf('127', plain,
% 1.30/1.51      (((k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 1.30/1.51         = (k7_relat_1 @ 
% 1.30/1.51            (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))) @ sk_A))),
% 1.30/1.51      inference('demod', [status(thm)], ['125', '126'])).
% 1.30/1.51  thf('128', plain,
% 1.30/1.51      (![X5 : $i, X6 : $i]:
% 1.30/1.51         (((k2_relat_1 @ (k7_relat_1 @ X5 @ X6)) = (k9_relat_1 @ X5 @ X6))
% 1.30/1.51          | ~ (v1_relat_1 @ X5))),
% 1.30/1.51      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.30/1.51  thf('129', plain,
% 1.30/1.51      ((((k2_relat_1 @ 
% 1.30/1.51          (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))))
% 1.30/1.51          = (k9_relat_1 @ 
% 1.30/1.51             (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))) @ sk_A))
% 1.30/1.51        | ~ (v1_relat_1 @ 
% 1.30/1.51             (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))))),
% 1.30/1.51      inference('sup+', [status(thm)], ['127', '128'])).
% 1.30/1.51  thf('130', plain,
% 1.30/1.51      (![X15 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X15)) = (X15))),
% 1.30/1.51      inference('demod', [status(thm)], ['117', '118'])).
% 1.30/1.51  thf('131', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.30/1.51      inference('sup-', [status(thm)], ['33', '34'])).
% 1.30/1.51  thf('132', plain,
% 1.30/1.51      (((k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 1.30/1.51         = (k9_relat_1 @ 
% 1.30/1.51            (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))) @ sk_A))),
% 1.30/1.51      inference('demod', [status(thm)], ['129', '130', '131'])).
% 1.30/1.51  thf('133', plain,
% 1.30/1.51      ((((k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 1.30/1.51          = (k9_relat_1 @ 
% 1.30/1.51             (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))) @ sk_A))
% 1.30/1.51        | ~ (v1_relat_1 @ sk_C)
% 1.30/1.51        | ~ (v1_relat_1 @ sk_D))),
% 1.30/1.51      inference('sup+', [status(thm)], ['120', '132'])).
% 1.30/1.51  thf('134', plain, ((v1_relat_1 @ sk_C)),
% 1.30/1.51      inference('sup-', [status(thm)], ['68', '69'])).
% 1.30/1.51  thf('135', plain, ((v1_relat_1 @ sk_D)),
% 1.30/1.51      inference('sup-', [status(thm)], ['22', '23'])).
% 1.30/1.51  thf('136', plain,
% 1.30/1.51      (((k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 1.30/1.51         = (k9_relat_1 @ 
% 1.30/1.51            (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))) @ sk_A))),
% 1.30/1.51      inference('demod', [status(thm)], ['133', '134', '135'])).
% 1.30/1.51  thf('137', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.30/1.51      inference('sup-', [status(thm)], ['33', '34'])).
% 1.30/1.51  thf('138', plain,
% 1.30/1.51      (((k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))
% 1.30/1.51         = (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))),
% 1.30/1.51      inference('demod', [status(thm)], ['116', '119', '136', '137'])).
% 1.30/1.51  thf('139', plain,
% 1.30/1.51      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.30/1.51        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.30/1.51        (k6_partfun1 @ sk_A))),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('140', plain,
% 1.30/1.51      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.30/1.51         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.30/1.51      inference('demod', [status(thm)], ['89', '90'])).
% 1.30/1.51  thf('141', plain,
% 1.30/1.51      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.30/1.51        (k6_partfun1 @ sk_A))),
% 1.30/1.51      inference('demod', [status(thm)], ['139', '140'])).
% 1.30/1.51  thf('142', plain,
% 1.30/1.51      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.30/1.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.30/1.51      inference('demod', [status(thm)], ['81', '82', '91'])).
% 1.30/1.51  thf(redefinition_r2_relset_1, axiom,
% 1.30/1.51    (![A:$i,B:$i,C:$i,D:$i]:
% 1.30/1.51     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.30/1.51         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.30/1.51       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.30/1.51  thf('143', plain,
% 1.30/1.51      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.30/1.51         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 1.30/1.51          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 1.30/1.51          | ((X37) = (X40))
% 1.30/1.51          | ~ (r2_relset_1 @ X38 @ X39 @ X37 @ X40))),
% 1.30/1.51      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.30/1.51  thf('144', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 1.30/1.51          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 1.30/1.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.30/1.51      inference('sup-', [status(thm)], ['142', '143'])).
% 1.30/1.51  thf('145', plain,
% 1.30/1.51      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.30/1.51           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.30/1.51        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['141', '144'])).
% 1.30/1.51  thf('146', plain,
% 1.30/1.51      (![X48 : $i]:
% 1.30/1.51         (m1_subset_1 @ (k6_partfun1 @ X48) @ 
% 1.30/1.51          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X48)))),
% 1.30/1.51      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.30/1.51  thf('147', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.30/1.51      inference('demod', [status(thm)], ['145', '146'])).
% 1.30/1.51  thf('148', plain,
% 1.30/1.51      (![X14 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X14)) = (X14))),
% 1.30/1.51      inference('demod', [status(thm)], ['37', '38'])).
% 1.30/1.51  thf('149', plain, (((k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)) = (sk_A))),
% 1.30/1.51      inference('demod', [status(thm)], ['138', '147', '148'])).
% 1.30/1.51  thf('150', plain, (((k9_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ sk_D))),
% 1.30/1.51      inference('demod', [status(thm)], ['73', '149'])).
% 1.30/1.51  thf('151', plain,
% 1.30/1.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('152', plain,
% 1.30/1.51      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.30/1.51         ((v4_relat_1 @ X31 @ X32)
% 1.30/1.51          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 1.30/1.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.30/1.51  thf('153', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 1.30/1.51      inference('sup-', [status(thm)], ['151', '152'])).
% 1.30/1.51  thf('154', plain,
% 1.30/1.51      (![X9 : $i, X10 : $i]:
% 1.30/1.51         (((X9) = (k7_relat_1 @ X9 @ X10))
% 1.30/1.51          | ~ (v4_relat_1 @ X9 @ X10)
% 1.30/1.51          | ~ (v1_relat_1 @ X9))),
% 1.30/1.51      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.30/1.51  thf('155', plain,
% 1.30/1.51      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['153', '154'])).
% 1.30/1.51  thf('156', plain, ((v1_relat_1 @ sk_C)),
% 1.30/1.51      inference('sup-', [status(thm)], ['68', '69'])).
% 1.30/1.51  thf('157', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 1.30/1.51      inference('demod', [status(thm)], ['155', '156'])).
% 1.30/1.51  thf('158', plain,
% 1.30/1.51      (![X5 : $i, X6 : $i]:
% 1.30/1.51         (((k2_relat_1 @ (k7_relat_1 @ X5 @ X6)) = (k9_relat_1 @ X5 @ X6))
% 1.30/1.51          | ~ (v1_relat_1 @ X5))),
% 1.30/1.51      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.30/1.51  thf('159', plain,
% 1.30/1.51      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))
% 1.30/1.51        | ~ (v1_relat_1 @ sk_C))),
% 1.30/1.51      inference('sup+', [status(thm)], ['157', '158'])).
% 1.30/1.51  thf('160', plain, ((v1_relat_1 @ sk_C)),
% 1.30/1.51      inference('sup-', [status(thm)], ['68', '69'])).
% 1.30/1.51  thf('161', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 1.30/1.51      inference('demod', [status(thm)], ['159', '160'])).
% 1.30/1.51  thf('162', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.30/1.51      inference('sup+', [status(thm)], ['63', '64'])).
% 1.30/1.51  thf('163', plain, (((sk_B) = (k9_relat_1 @ sk_C @ sk_A))),
% 1.30/1.51      inference('demod', [status(thm)], ['161', '162'])).
% 1.30/1.51  thf('164', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.30/1.51      inference('sup+', [status(thm)], ['150', '163'])).
% 1.30/1.51  thf('165', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))),
% 1.30/1.51      inference('demod', [status(thm)], ['53', '164'])).
% 1.30/1.51  thf('166', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.30/1.51      inference('demod', [status(thm)], ['145', '146'])).
% 1.30/1.51  thf(dt_k2_funct_1, axiom,
% 1.30/1.51    (![A:$i]:
% 1.30/1.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.30/1.51       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.30/1.51         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.30/1.51  thf('167', plain,
% 1.30/1.51      (![X19 : $i]:
% 1.30/1.51         ((v1_relat_1 @ (k2_funct_1 @ X19))
% 1.30/1.51          | ~ (v1_funct_1 @ X19)
% 1.30/1.51          | ~ (v1_relat_1 @ X19))),
% 1.30/1.51      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.30/1.51  thf('168', plain,
% 1.30/1.51      (![X19 : $i]:
% 1.30/1.51         ((v1_funct_1 @ (k2_funct_1 @ X19))
% 1.30/1.51          | ~ (v1_funct_1 @ X19)
% 1.30/1.51          | ~ (v1_relat_1 @ X19))),
% 1.30/1.51      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.30/1.51  thf('169', plain,
% 1.30/1.51      (![X19 : $i]:
% 1.30/1.51         ((v1_relat_1 @ (k2_funct_1 @ X19))
% 1.30/1.51          | ~ (v1_funct_1 @ X19)
% 1.30/1.51          | ~ (v1_relat_1 @ X19))),
% 1.30/1.51      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.30/1.51  thf(t65_funct_1, axiom,
% 1.30/1.51    (![A:$i]:
% 1.30/1.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.30/1.51       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 1.30/1.51  thf('170', plain,
% 1.30/1.51      (![X27 : $i]:
% 1.30/1.51         (~ (v2_funct_1 @ X27)
% 1.30/1.51          | ((k2_funct_1 @ (k2_funct_1 @ X27)) = (X27))
% 1.30/1.51          | ~ (v1_funct_1 @ X27)
% 1.30/1.51          | ~ (v1_relat_1 @ X27))),
% 1.30/1.51      inference('cnf', [status(esa)], [t65_funct_1])).
% 1.30/1.51  thf('171', plain,
% 1.30/1.51      (![X27 : $i]:
% 1.30/1.51         (~ (v2_funct_1 @ X27)
% 1.30/1.51          | ((k2_funct_1 @ (k2_funct_1 @ X27)) = (X27))
% 1.30/1.51          | ~ (v1_funct_1 @ X27)
% 1.30/1.51          | ~ (v1_relat_1 @ X27))),
% 1.30/1.51      inference('cnf', [status(esa)], [t65_funct_1])).
% 1.30/1.51  thf('172', plain,
% 1.30/1.51      (![X27 : $i]:
% 1.30/1.51         (~ (v2_funct_1 @ X27)
% 1.30/1.51          | ((k2_funct_1 @ (k2_funct_1 @ X27)) = (X27))
% 1.30/1.51          | ~ (v1_funct_1 @ X27)
% 1.30/1.51          | ~ (v1_relat_1 @ X27))),
% 1.30/1.51      inference('cnf', [status(esa)], [t65_funct_1])).
% 1.30/1.51  thf('173', plain,
% 1.30/1.51      (![X19 : $i]:
% 1.30/1.51         ((v1_funct_1 @ (k2_funct_1 @ X19))
% 1.30/1.51          | ~ (v1_funct_1 @ X19)
% 1.30/1.51          | ~ (v1_relat_1 @ X19))),
% 1.30/1.51      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.30/1.51  thf('174', plain,
% 1.30/1.51      (![X19 : $i]:
% 1.30/1.51         ((v1_relat_1 @ (k2_funct_1 @ X19))
% 1.30/1.51          | ~ (v1_funct_1 @ X19)
% 1.30/1.51          | ~ (v1_relat_1 @ X19))),
% 1.30/1.51      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.30/1.51  thf(t55_funct_1, axiom,
% 1.30/1.51    (![A:$i]:
% 1.30/1.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.30/1.51       ( ( v2_funct_1 @ A ) =>
% 1.30/1.51         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.30/1.51           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.30/1.51  thf('175', plain,
% 1.30/1.51      (![X25 : $i]:
% 1.30/1.51         (~ (v2_funct_1 @ X25)
% 1.30/1.51          | ((k2_relat_1 @ X25) = (k1_relat_1 @ (k2_funct_1 @ X25)))
% 1.30/1.51          | ~ (v1_funct_1 @ X25)
% 1.30/1.51          | ~ (v1_relat_1 @ X25))),
% 1.30/1.51      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.30/1.51  thf('176', plain,
% 1.30/1.51      (![X19 : $i]:
% 1.30/1.51         ((v1_relat_1 @ (k2_funct_1 @ X19))
% 1.30/1.51          | ~ (v1_funct_1 @ X19)
% 1.30/1.51          | ~ (v1_relat_1 @ X19))),
% 1.30/1.51      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.30/1.51  thf('177', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.30/1.51      inference('sup+', [status(thm)], ['63', '64'])).
% 1.30/1.51  thf('178', plain,
% 1.30/1.51      (![X19 : $i]:
% 1.30/1.51         ((v1_relat_1 @ (k2_funct_1 @ X19))
% 1.30/1.51          | ~ (v1_funct_1 @ X19)
% 1.30/1.51          | ~ (v1_relat_1 @ X19))),
% 1.30/1.51      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.30/1.51  thf('179', plain,
% 1.30/1.51      (![X25 : $i]:
% 1.30/1.51         (~ (v2_funct_1 @ X25)
% 1.30/1.51          | ((k2_relat_1 @ X25) = (k1_relat_1 @ (k2_funct_1 @ X25)))
% 1.30/1.51          | ~ (v1_funct_1 @ X25)
% 1.30/1.51          | ~ (v1_relat_1 @ X25))),
% 1.30/1.51      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.30/1.51  thf('180', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.30/1.51      inference('simplify', [status(thm)], ['15'])).
% 1.30/1.51  thf('181', plain,
% 1.30/1.51      (![X3 : $i, X4 : $i]:
% 1.30/1.51         (~ (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.30/1.51          | (v4_relat_1 @ X3 @ X4)
% 1.30/1.51          | ~ (v1_relat_1 @ X3))),
% 1.30/1.51      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.30/1.51  thf('182', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['180', '181'])).
% 1.30/1.51  thf('183', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.30/1.51          | ~ (v1_relat_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v2_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.30/1.51      inference('sup+', [status(thm)], ['179', '182'])).
% 1.30/1.51  thf('184', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (~ (v1_relat_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v2_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ X0)
% 1.30/1.51          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['178', '183'])).
% 1.30/1.51  thf('185', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.30/1.51          | ~ (v2_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ X0))),
% 1.30/1.51      inference('simplify', [status(thm)], ['184'])).
% 1.30/1.51  thf('186', plain,
% 1.30/1.51      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)
% 1.30/1.51        | ~ (v1_relat_1 @ sk_C)
% 1.30/1.51        | ~ (v1_funct_1 @ sk_C)
% 1.30/1.51        | ~ (v2_funct_1 @ sk_C))),
% 1.30/1.51      inference('sup+', [status(thm)], ['177', '185'])).
% 1.30/1.51  thf('187', plain, ((v1_relat_1 @ sk_C)),
% 1.30/1.51      inference('sup-', [status(thm)], ['68', '69'])).
% 1.30/1.51  thf('188', plain, ((v1_funct_1 @ sk_C)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('189', plain, ((v2_funct_1 @ sk_C)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('190', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)),
% 1.30/1.51      inference('demod', [status(thm)], ['186', '187', '188', '189'])).
% 1.30/1.51  thf('191', plain,
% 1.30/1.51      (![X3 : $i, X4 : $i]:
% 1.30/1.51         (~ (v4_relat_1 @ X3 @ X4)
% 1.30/1.51          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.30/1.51          | ~ (v1_relat_1 @ X3))),
% 1.30/1.51      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.30/1.51  thf('192', plain,
% 1.30/1.51      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.30/1.51        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 1.30/1.51      inference('sup-', [status(thm)], ['190', '191'])).
% 1.30/1.51  thf('193', plain,
% 1.30/1.51      ((~ (v1_relat_1 @ sk_C)
% 1.30/1.51        | ~ (v1_funct_1 @ sk_C)
% 1.30/1.51        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 1.30/1.51      inference('sup-', [status(thm)], ['176', '192'])).
% 1.30/1.51  thf('194', plain, ((v1_relat_1 @ sk_C)),
% 1.30/1.51      inference('sup-', [status(thm)], ['68', '69'])).
% 1.30/1.51  thf('195', plain, ((v1_funct_1 @ sk_C)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('196', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B)),
% 1.30/1.51      inference('demod', [status(thm)], ['193', '194', '195'])).
% 1.30/1.51  thf('197', plain,
% 1.30/1.51      (![X0 : $i, X2 : $i]:
% 1.30/1.51         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.30/1.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.30/1.51  thf('198', plain,
% 1.30/1.51      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.30/1.51        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.30/1.51      inference('sup-', [status(thm)], ['196', '197'])).
% 1.30/1.51  thf('199', plain,
% 1.30/1.51      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C))
% 1.30/1.51        | ~ (v1_relat_1 @ sk_C)
% 1.30/1.51        | ~ (v1_funct_1 @ sk_C)
% 1.30/1.51        | ~ (v2_funct_1 @ sk_C)
% 1.30/1.51        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.30/1.51      inference('sup-', [status(thm)], ['175', '198'])).
% 1.30/1.51  thf('200', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.30/1.51      inference('sup+', [status(thm)], ['63', '64'])).
% 1.30/1.51  thf('201', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.30/1.51      inference('simplify', [status(thm)], ['15'])).
% 1.30/1.51  thf('202', plain, ((v1_relat_1 @ sk_C)),
% 1.30/1.51      inference('sup-', [status(thm)], ['68', '69'])).
% 1.30/1.51  thf('203', plain, ((v1_funct_1 @ sk_C)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('204', plain, ((v2_funct_1 @ sk_C)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('205', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.30/1.51      inference('demod', [status(thm)],
% 1.30/1.51                ['199', '200', '201', '202', '203', '204'])).
% 1.30/1.51  thf('206', plain,
% 1.30/1.51      (![X25 : $i]:
% 1.30/1.51         (~ (v2_funct_1 @ X25)
% 1.30/1.51          | ((k1_relat_1 @ X25) = (k2_relat_1 @ (k2_funct_1 @ X25)))
% 1.30/1.51          | ~ (v1_funct_1 @ X25)
% 1.30/1.51          | ~ (v1_relat_1 @ X25))),
% 1.30/1.51      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.30/1.51  thf('207', plain,
% 1.30/1.51      (![X19 : $i]:
% 1.30/1.51         ((v1_funct_1 @ (k2_funct_1 @ X19))
% 1.30/1.51          | ~ (v1_funct_1 @ X19)
% 1.30/1.51          | ~ (v1_relat_1 @ X19))),
% 1.30/1.51      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.30/1.51  thf('208', plain,
% 1.30/1.51      (![X19 : $i]:
% 1.30/1.51         ((v1_relat_1 @ (k2_funct_1 @ X19))
% 1.30/1.51          | ~ (v1_funct_1 @ X19)
% 1.30/1.51          | ~ (v1_relat_1 @ X19))),
% 1.30/1.51      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.30/1.51  thf(t61_funct_1, axiom,
% 1.30/1.51    (![A:$i]:
% 1.30/1.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.30/1.51       ( ( v2_funct_1 @ A ) =>
% 1.30/1.51         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.30/1.51             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.30/1.51           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.30/1.51             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.30/1.51  thf('209', plain,
% 1.30/1.51      (![X26 : $i]:
% 1.30/1.51         (~ (v2_funct_1 @ X26)
% 1.30/1.51          | ((k5_relat_1 @ (k2_funct_1 @ X26) @ X26)
% 1.30/1.51              = (k6_relat_1 @ (k2_relat_1 @ X26)))
% 1.30/1.51          | ~ (v1_funct_1 @ X26)
% 1.30/1.51          | ~ (v1_relat_1 @ X26))),
% 1.30/1.51      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.30/1.51  thf('210', plain, (![X55 : $i]: ((k6_partfun1 @ X55) = (k6_relat_1 @ X55))),
% 1.30/1.51      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.30/1.51  thf('211', plain,
% 1.30/1.51      (![X26 : $i]:
% 1.30/1.51         (~ (v2_funct_1 @ X26)
% 1.30/1.51          | ((k5_relat_1 @ (k2_funct_1 @ X26) @ X26)
% 1.30/1.51              = (k6_partfun1 @ (k2_relat_1 @ X26)))
% 1.30/1.51          | ~ (v1_funct_1 @ X26)
% 1.30/1.51          | ~ (v1_relat_1 @ X26))),
% 1.30/1.51      inference('demod', [status(thm)], ['209', '210'])).
% 1.30/1.51  thf(t48_funct_1, axiom,
% 1.30/1.51    (![A:$i]:
% 1.30/1.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.30/1.51       ( ![B:$i]:
% 1.30/1.51         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.30/1.51           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 1.30/1.51               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 1.30/1.51             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 1.30/1.51  thf('212', plain,
% 1.30/1.51      (![X22 : $i, X23 : $i]:
% 1.30/1.51         (~ (v1_relat_1 @ X22)
% 1.30/1.51          | ~ (v1_funct_1 @ X22)
% 1.30/1.51          | (v2_funct_1 @ X22)
% 1.30/1.51          | ((k2_relat_1 @ X22) != (k1_relat_1 @ X23))
% 1.30/1.51          | ~ (v2_funct_1 @ (k5_relat_1 @ X22 @ X23))
% 1.30/1.51          | ~ (v1_funct_1 @ X23)
% 1.30/1.51          | ~ (v1_relat_1 @ X23))),
% 1.30/1.51      inference('cnf', [status(esa)], [t48_funct_1])).
% 1.30/1.51  thf('213', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (~ (v2_funct_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.30/1.51          | ~ (v1_relat_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v2_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 1.30/1.51          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.30/1.51          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.30/1.51          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['211', '212'])).
% 1.30/1.51  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 1.30/1.51  thf('214', plain, (![X24 : $i]: (v2_funct_1 @ (k6_relat_1 @ X24))),
% 1.30/1.51      inference('cnf', [status(esa)], [t52_funct_1])).
% 1.30/1.51  thf('215', plain, (![X55 : $i]: ((k6_partfun1 @ X55) = (k6_relat_1 @ X55))),
% 1.30/1.51      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.30/1.51  thf('216', plain, (![X24 : $i]: (v2_funct_1 @ (k6_partfun1 @ X24))),
% 1.30/1.51      inference('demod', [status(thm)], ['214', '215'])).
% 1.30/1.51  thf('217', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (~ (v1_relat_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v2_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 1.30/1.51          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.30/1.51          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.30/1.51          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.30/1.51      inference('demod', [status(thm)], ['213', '216'])).
% 1.30/1.51  thf('218', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.30/1.51          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.30/1.51          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.30/1.51          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 1.30/1.51          | ~ (v2_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ X0))),
% 1.30/1.51      inference('simplify', [status(thm)], ['217'])).
% 1.30/1.51  thf('219', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (~ (v1_relat_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v2_funct_1 @ X0)
% 1.30/1.51          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 1.30/1.51          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.30/1.51          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['208', '218'])).
% 1.30/1.51  thf('220', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.30/1.51          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.30/1.51          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 1.30/1.51          | ~ (v2_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ X0))),
% 1.30/1.51      inference('simplify', [status(thm)], ['219'])).
% 1.30/1.51  thf('221', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (~ (v1_relat_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v2_funct_1 @ X0)
% 1.30/1.51          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 1.30/1.51          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['207', '220'])).
% 1.30/1.51  thf('222', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 1.30/1.51          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 1.30/1.51          | ~ (v2_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ X0))),
% 1.30/1.51      inference('simplify', [status(thm)], ['221'])).
% 1.30/1.51  thf('223', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 1.30/1.51          | ~ (v1_relat_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v2_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v2_funct_1 @ X0)
% 1.30/1.51          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['206', '222'])).
% 1.30/1.51  thf('224', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 1.30/1.51          | ~ (v2_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ X0))),
% 1.30/1.51      inference('simplify', [status(thm)], ['223'])).
% 1.30/1.51  thf('225', plain,
% 1.30/1.51      (![X19 : $i]:
% 1.30/1.51         ((v1_funct_1 @ (k2_funct_1 @ X19))
% 1.30/1.51          | ~ (v1_funct_1 @ X19)
% 1.30/1.51          | ~ (v1_relat_1 @ X19))),
% 1.30/1.51      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.30/1.51  thf('226', plain,
% 1.30/1.51      (![X19 : $i]:
% 1.30/1.51         ((v1_relat_1 @ (k2_funct_1 @ X19))
% 1.30/1.51          | ~ (v1_funct_1 @ X19)
% 1.30/1.51          | ~ (v1_relat_1 @ X19))),
% 1.30/1.51      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.30/1.51  thf('227', plain,
% 1.30/1.51      (![X27 : $i]:
% 1.30/1.51         (~ (v2_funct_1 @ X27)
% 1.30/1.51          | ((k2_funct_1 @ (k2_funct_1 @ X27)) = (X27))
% 1.30/1.51          | ~ (v1_funct_1 @ X27)
% 1.30/1.51          | ~ (v1_relat_1 @ X27))),
% 1.30/1.51      inference('cnf', [status(esa)], [t65_funct_1])).
% 1.30/1.51  thf('228', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.30/1.51          | ~ (v2_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ X0))),
% 1.30/1.51      inference('simplify', [status(thm)], ['184'])).
% 1.30/1.51  thf('229', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         ((v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.30/1.51          | ~ (v1_relat_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v2_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.30/1.51          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.30/1.51          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 1.30/1.51      inference('sup+', [status(thm)], ['227', '228'])).
% 1.30/1.51  thf('230', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (~ (v1_relat_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.30/1.51          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.30/1.51          | ~ (v2_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ X0)
% 1.30/1.51          | (v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 1.30/1.51      inference('sup-', [status(thm)], ['226', '229'])).
% 1.30/1.51  thf('231', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         ((v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.30/1.51          | ~ (v2_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.30/1.51          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ X0))),
% 1.30/1.51      inference('simplify', [status(thm)], ['230'])).
% 1.30/1.51  thf('232', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (~ (v1_relat_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.30/1.51          | ~ (v2_funct_1 @ X0)
% 1.30/1.51          | (v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 1.30/1.51      inference('sup-', [status(thm)], ['225', '231'])).
% 1.30/1.51  thf('233', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         ((v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.30/1.51          | ~ (v2_funct_1 @ X0)
% 1.30/1.51          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ X0))),
% 1.30/1.51      inference('simplify', [status(thm)], ['232'])).
% 1.30/1.51  thf('234', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (~ (v1_relat_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v2_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v2_funct_1 @ X0)
% 1.30/1.51          | (v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 1.30/1.51      inference('sup-', [status(thm)], ['224', '233'])).
% 1.30/1.51  thf('235', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         ((v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.30/1.51          | ~ (v2_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ X0))),
% 1.30/1.51      inference('simplify', [status(thm)], ['234'])).
% 1.30/1.51  thf('236', plain,
% 1.30/1.51      (![X3 : $i, X4 : $i]:
% 1.30/1.51         (~ (v4_relat_1 @ X3 @ X4)
% 1.30/1.51          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.30/1.51          | ~ (v1_relat_1 @ X3))),
% 1.30/1.51      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.30/1.51  thf('237', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (~ (v1_relat_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v2_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ X0)
% 1.30/1.51          | (r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 1.30/1.51      inference('sup-', [status(thm)], ['235', '236'])).
% 1.30/1.51  thf('238', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         ((r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.30/1.51          | ~ (v2_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ X0))),
% 1.30/1.51      inference('simplify', [status(thm)], ['237'])).
% 1.30/1.51  thf('239', plain,
% 1.30/1.51      (((r1_tarski @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 1.30/1.51        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.30/1.51        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.30/1.51        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.30/1.51      inference('sup+', [status(thm)], ['205', '238'])).
% 1.30/1.51  thf('240', plain,
% 1.30/1.51      (![X19 : $i]:
% 1.30/1.51         ((v1_relat_1 @ (k2_funct_1 @ X19))
% 1.30/1.51          | ~ (v1_funct_1 @ X19)
% 1.30/1.51          | ~ (v1_relat_1 @ X19))),
% 1.30/1.51      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.30/1.51  thf('241', plain,
% 1.30/1.51      (![X19 : $i]:
% 1.30/1.51         ((v1_funct_1 @ (k2_funct_1 @ X19))
% 1.30/1.51          | ~ (v1_funct_1 @ X19)
% 1.30/1.51          | ~ (v1_relat_1 @ X19))),
% 1.30/1.51      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.30/1.51  thf('242', plain,
% 1.30/1.51      (![X19 : $i]:
% 1.30/1.51         ((v1_relat_1 @ (k2_funct_1 @ X19))
% 1.30/1.51          | ~ (v1_funct_1 @ X19)
% 1.30/1.51          | ~ (v1_relat_1 @ X19))),
% 1.30/1.51      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.30/1.51  thf('243', plain,
% 1.30/1.51      (![X26 : $i]:
% 1.30/1.51         (~ (v2_funct_1 @ X26)
% 1.30/1.51          | ((k5_relat_1 @ X26 @ (k2_funct_1 @ X26))
% 1.30/1.51              = (k6_relat_1 @ (k1_relat_1 @ X26)))
% 1.30/1.51          | ~ (v1_funct_1 @ X26)
% 1.30/1.51          | ~ (v1_relat_1 @ X26))),
% 1.30/1.51      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.30/1.51  thf('244', plain, (![X55 : $i]: ((k6_partfun1 @ X55) = (k6_relat_1 @ X55))),
% 1.30/1.51      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.30/1.51  thf('245', plain,
% 1.30/1.51      (![X26 : $i]:
% 1.30/1.51         (~ (v2_funct_1 @ X26)
% 1.30/1.51          | ((k5_relat_1 @ X26 @ (k2_funct_1 @ X26))
% 1.30/1.51              = (k6_partfun1 @ (k1_relat_1 @ X26)))
% 1.30/1.51          | ~ (v1_funct_1 @ X26)
% 1.30/1.51          | ~ (v1_relat_1 @ X26))),
% 1.30/1.51      inference('demod', [status(thm)], ['243', '244'])).
% 1.30/1.51  thf('246', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.30/1.51      inference('sup+', [status(thm)], ['63', '64'])).
% 1.30/1.51  thf('247', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (~ (v1_relat_1 @ X0)
% 1.30/1.51          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) = (X0)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['16', '19'])).
% 1.30/1.51  thf('248', plain,
% 1.30/1.51      ((((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))
% 1.30/1.51        | ~ (v1_relat_1 @ sk_C))),
% 1.30/1.51      inference('sup+', [status(thm)], ['246', '247'])).
% 1.30/1.51  thf('249', plain, ((v1_relat_1 @ sk_C)),
% 1.30/1.51      inference('sup-', [status(thm)], ['68', '69'])).
% 1.30/1.51  thf('250', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 1.30/1.51      inference('demod', [status(thm)], ['248', '249'])).
% 1.30/1.51  thf('251', plain,
% 1.30/1.51      (![X16 : $i]:
% 1.30/1.51         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X16)) @ X16) = (X16))
% 1.30/1.51          | ~ (v1_relat_1 @ X16))),
% 1.30/1.51      inference('demod', [status(thm)], ['27', '28'])).
% 1.30/1.51  thf(t55_relat_1, axiom,
% 1.30/1.51    (![A:$i]:
% 1.30/1.51     ( ( v1_relat_1 @ A ) =>
% 1.30/1.51       ( ![B:$i]:
% 1.30/1.51         ( ( v1_relat_1 @ B ) =>
% 1.30/1.51           ( ![C:$i]:
% 1.30/1.51             ( ( v1_relat_1 @ C ) =>
% 1.30/1.51               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 1.30/1.51                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 1.30/1.51  thf('252', plain,
% 1.30/1.51      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.30/1.51         (~ (v1_relat_1 @ X11)
% 1.30/1.51          | ((k5_relat_1 @ (k5_relat_1 @ X12 @ X11) @ X13)
% 1.30/1.51              = (k5_relat_1 @ X12 @ (k5_relat_1 @ X11 @ X13)))
% 1.30/1.51          | ~ (v1_relat_1 @ X13)
% 1.30/1.51          | ~ (v1_relat_1 @ X12))),
% 1.30/1.51      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.30/1.51  thf('253', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]:
% 1.30/1.51         (((k5_relat_1 @ X0 @ X1)
% 1.30/1.51            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 1.30/1.51               (k5_relat_1 @ X0 @ X1)))
% 1.30/1.51          | ~ (v1_relat_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.30/1.51          | ~ (v1_relat_1 @ X1)
% 1.30/1.51          | ~ (v1_relat_1 @ X0))),
% 1.30/1.51      inference('sup+', [status(thm)], ['251', '252'])).
% 1.30/1.51  thf('254', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.30/1.51      inference('sup-', [status(thm)], ['33', '34'])).
% 1.30/1.51  thf('255', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]:
% 1.30/1.51         (((k5_relat_1 @ X0 @ X1)
% 1.30/1.51            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 1.30/1.51               (k5_relat_1 @ X0 @ X1)))
% 1.30/1.51          | ~ (v1_relat_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ X1)
% 1.30/1.51          | ~ (v1_relat_1 @ X0))),
% 1.30/1.51      inference('demod', [status(thm)], ['253', '254'])).
% 1.30/1.51  thf('256', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i]:
% 1.30/1.51         (~ (v1_relat_1 @ X1)
% 1.30/1.51          | ~ (v1_relat_1 @ X0)
% 1.30/1.51          | ((k5_relat_1 @ X0 @ X1)
% 1.30/1.51              = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 1.30/1.51                 (k5_relat_1 @ X0 @ X1))))),
% 1.30/1.51      inference('simplify', [status(thm)], ['255'])).
% 1.30/1.51  thf('257', plain,
% 1.30/1.51      ((((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B))
% 1.30/1.51          = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ sk_C))
% 1.30/1.51        | ~ (v1_relat_1 @ sk_C)
% 1.30/1.51        | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B)))),
% 1.30/1.51      inference('sup+', [status(thm)], ['250', '256'])).
% 1.30/1.51  thf('258', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 1.30/1.51      inference('demod', [status(thm)], ['248', '249'])).
% 1.30/1.51  thf('259', plain, ((v1_relat_1 @ sk_C)),
% 1.30/1.51      inference('sup-', [status(thm)], ['68', '69'])).
% 1.30/1.51  thf('260', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.30/1.51      inference('sup-', [status(thm)], ['33', '34'])).
% 1.30/1.51  thf('261', plain,
% 1.30/1.51      (((sk_C) = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ sk_C))),
% 1.30/1.51      inference('demod', [status(thm)], ['257', '258', '259', '260'])).
% 1.30/1.51  thf('262', plain,
% 1.30/1.51      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.30/1.51         (~ (v1_relat_1 @ X11)
% 1.30/1.51          | ((k5_relat_1 @ (k5_relat_1 @ X12 @ X11) @ X13)
% 1.30/1.51              = (k5_relat_1 @ X12 @ (k5_relat_1 @ X11 @ X13)))
% 1.30/1.51          | ~ (v1_relat_1 @ X13)
% 1.30/1.51          | ~ (v1_relat_1 @ X12))),
% 1.30/1.51      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.30/1.51  thf('263', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (((k5_relat_1 @ sk_C @ X0)
% 1.30/1.51            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ 
% 1.30/1.51               (k5_relat_1 @ sk_C @ X0)))
% 1.30/1.51          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 1.30/1.51          | ~ (v1_relat_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ sk_C))),
% 1.30/1.51      inference('sup+', [status(thm)], ['261', '262'])).
% 1.30/1.51  thf('264', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.30/1.51      inference('sup-', [status(thm)], ['33', '34'])).
% 1.30/1.51  thf('265', plain, ((v1_relat_1 @ sk_C)),
% 1.30/1.51      inference('sup-', [status(thm)], ['68', '69'])).
% 1.30/1.51  thf('266', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (((k5_relat_1 @ sk_C @ X0)
% 1.30/1.51            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ 
% 1.30/1.51               (k5_relat_1 @ sk_C @ X0)))
% 1.30/1.51          | ~ (v1_relat_1 @ X0))),
% 1.30/1.51      inference('demod', [status(thm)], ['263', '264', '265'])).
% 1.30/1.51  thf('267', plain,
% 1.30/1.51      ((((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 1.30/1.51          = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ 
% 1.30/1.51             (k6_partfun1 @ (k1_relat_1 @ sk_C))))
% 1.30/1.51        | ~ (v1_relat_1 @ sk_C)
% 1.30/1.51        | ~ (v1_funct_1 @ sk_C)
% 1.30/1.51        | ~ (v2_funct_1 @ sk_C)
% 1.30/1.51        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.30/1.51      inference('sup+', [status(thm)], ['245', '266'])).
% 1.30/1.51  thf('268', plain,
% 1.30/1.51      (![X14 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X14)) = (X14))),
% 1.30/1.51      inference('demod', [status(thm)], ['37', '38'])).
% 1.30/1.51  thf('269', plain,
% 1.30/1.51      (![X16 : $i]:
% 1.30/1.51         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X16)) @ X16) = (X16))
% 1.30/1.51          | ~ (v1_relat_1 @ X16))),
% 1.30/1.51      inference('demod', [status(thm)], ['27', '28'])).
% 1.30/1.51  thf('270', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 1.30/1.51            = (k6_partfun1 @ X0))
% 1.30/1.51          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 1.30/1.51      inference('sup+', [status(thm)], ['268', '269'])).
% 1.30/1.51  thf('271', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.30/1.51      inference('sup-', [status(thm)], ['33', '34'])).
% 1.30/1.51  thf('272', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 1.30/1.51           = (k6_partfun1 @ X0))),
% 1.30/1.51      inference('demod', [status(thm)], ['270', '271'])).
% 1.30/1.51  thf('273', plain, ((v1_relat_1 @ sk_C)),
% 1.30/1.51      inference('sup-', [status(thm)], ['68', '69'])).
% 1.30/1.51  thf('274', plain, ((v1_funct_1 @ sk_C)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('275', plain, ((v2_funct_1 @ sk_C)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('276', plain,
% 1.30/1.51      ((((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 1.30/1.51          = (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 1.30/1.51        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.30/1.51      inference('demod', [status(thm)], ['267', '272', '273', '274', '275'])).
% 1.30/1.51  thf('277', plain,
% 1.30/1.51      ((~ (v1_relat_1 @ sk_C)
% 1.30/1.51        | ~ (v1_funct_1 @ sk_C)
% 1.30/1.51        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 1.30/1.51            = (k6_partfun1 @ (k1_relat_1 @ sk_C))))),
% 1.30/1.51      inference('sup-', [status(thm)], ['242', '276'])).
% 1.30/1.51  thf('278', plain, ((v1_relat_1 @ sk_C)),
% 1.30/1.51      inference('sup-', [status(thm)], ['68', '69'])).
% 1.30/1.51  thf('279', plain, ((v1_funct_1 @ sk_C)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('280', plain,
% 1.30/1.51      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 1.30/1.51         = (k6_partfun1 @ (k1_relat_1 @ sk_C)))),
% 1.30/1.51      inference('demod', [status(thm)], ['277', '278', '279'])).
% 1.30/1.51  thf('281', plain,
% 1.30/1.51      (![X22 : $i, X23 : $i]:
% 1.30/1.51         (~ (v1_relat_1 @ X22)
% 1.30/1.51          | ~ (v1_funct_1 @ X22)
% 1.30/1.51          | (v2_funct_1 @ X23)
% 1.30/1.51          | ((k2_relat_1 @ X22) != (k1_relat_1 @ X23))
% 1.30/1.51          | ~ (v2_funct_1 @ (k5_relat_1 @ X22 @ X23))
% 1.30/1.51          | ~ (v1_funct_1 @ X23)
% 1.30/1.51          | ~ (v1_relat_1 @ X23))),
% 1.30/1.51      inference('cnf', [status(esa)], [t48_funct_1])).
% 1.30/1.51  thf('282', plain,
% 1.30/1.51      ((~ (v2_funct_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 1.30/1.51        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.30/1.51        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.30/1.51        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.30/1.51        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 1.30/1.51        | ~ (v1_funct_1 @ sk_C)
% 1.30/1.51        | ~ (v1_relat_1 @ sk_C))),
% 1.30/1.51      inference('sup-', [status(thm)], ['280', '281'])).
% 1.30/1.51  thf('283', plain, (![X24 : $i]: (v2_funct_1 @ (k6_partfun1 @ X24))),
% 1.30/1.51      inference('demod', [status(thm)], ['214', '215'])).
% 1.30/1.51  thf('284', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.30/1.51      inference('sup+', [status(thm)], ['63', '64'])).
% 1.30/1.51  thf('285', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.30/1.51      inference('demod', [status(thm)],
% 1.30/1.51                ['199', '200', '201', '202', '203', '204'])).
% 1.30/1.51  thf('286', plain, ((v1_funct_1 @ sk_C)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('287', plain, ((v1_relat_1 @ sk_C)),
% 1.30/1.51      inference('sup-', [status(thm)], ['68', '69'])).
% 1.30/1.51  thf('288', plain,
% 1.30/1.51      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.30/1.51        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.30/1.51        | ((sk_B) != (sk_B))
% 1.30/1.51        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.30/1.51      inference('demod', [status(thm)],
% 1.30/1.51                ['282', '283', '284', '285', '286', '287'])).
% 1.30/1.51  thf('289', plain,
% 1.30/1.51      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 1.30/1.51        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.30/1.51        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.30/1.51      inference('simplify', [status(thm)], ['288'])).
% 1.30/1.51  thf('290', plain,
% 1.30/1.51      ((~ (v1_relat_1 @ sk_C)
% 1.30/1.51        | ~ (v1_funct_1 @ sk_C)
% 1.30/1.51        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.30/1.51        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['241', '289'])).
% 1.30/1.51  thf('291', plain, ((v1_relat_1 @ sk_C)),
% 1.30/1.51      inference('sup-', [status(thm)], ['68', '69'])).
% 1.30/1.51  thf('292', plain, ((v1_funct_1 @ sk_C)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('293', plain,
% 1.30/1.51      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.30/1.51        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.30/1.51      inference('demod', [status(thm)], ['290', '291', '292'])).
% 1.30/1.51  thf('294', plain,
% 1.30/1.51      ((~ (v1_relat_1 @ sk_C)
% 1.30/1.51        | ~ (v1_funct_1 @ sk_C)
% 1.30/1.51        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['240', '293'])).
% 1.30/1.51  thf('295', plain, ((v1_relat_1 @ sk_C)),
% 1.30/1.51      inference('sup-', [status(thm)], ['68', '69'])).
% 1.30/1.51  thf('296', plain, ((v1_funct_1 @ sk_C)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('297', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 1.30/1.51      inference('demod', [status(thm)], ['294', '295', '296'])).
% 1.30/1.51  thf('298', plain,
% 1.30/1.51      (((r1_tarski @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 1.30/1.51        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.30/1.51        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.30/1.51      inference('demod', [status(thm)], ['239', '297'])).
% 1.30/1.51  thf('299', plain,
% 1.30/1.51      ((~ (v1_relat_1 @ sk_C)
% 1.30/1.51        | ~ (v1_funct_1 @ sk_C)
% 1.30/1.51        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.30/1.51        | (r1_tarski @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 1.30/1.51      inference('sup-', [status(thm)], ['174', '298'])).
% 1.30/1.51  thf('300', plain, ((v1_relat_1 @ sk_C)),
% 1.30/1.51      inference('sup-', [status(thm)], ['68', '69'])).
% 1.30/1.51  thf('301', plain, ((v1_funct_1 @ sk_C)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('302', plain,
% 1.30/1.51      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.30/1.51        | (r1_tarski @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 1.30/1.51      inference('demod', [status(thm)], ['299', '300', '301'])).
% 1.30/1.51  thf('303', plain,
% 1.30/1.51      ((~ (v1_relat_1 @ sk_C)
% 1.30/1.51        | ~ (v1_funct_1 @ sk_C)
% 1.30/1.51        | (r1_tarski @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 1.30/1.51      inference('sup-', [status(thm)], ['173', '302'])).
% 1.30/1.51  thf('304', plain, ((v1_relat_1 @ sk_C)),
% 1.30/1.51      inference('sup-', [status(thm)], ['68', '69'])).
% 1.30/1.51  thf('305', plain, ((v1_funct_1 @ sk_C)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('306', plain,
% 1.30/1.51      ((r1_tarski @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.30/1.51      inference('demod', [status(thm)], ['303', '304', '305'])).
% 1.30/1.51  thf('307', plain,
% 1.30/1.51      (![X0 : $i, X2 : $i]:
% 1.30/1.51         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.30/1.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.30/1.51  thf('308', plain,
% 1.30/1.51      ((~ (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) @ sk_B)
% 1.30/1.51        | ((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) = (sk_B)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['306', '307'])).
% 1.30/1.51  thf('309', plain,
% 1.30/1.51      ((~ (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)
% 1.30/1.51        | ~ (v1_relat_1 @ sk_C)
% 1.30/1.51        | ~ (v1_funct_1 @ sk_C)
% 1.30/1.51        | ~ (v2_funct_1 @ sk_C)
% 1.30/1.51        | ((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) = (sk_B)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['172', '308'])).
% 1.30/1.51  thf('310', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.30/1.51      inference('sup+', [status(thm)], ['63', '64'])).
% 1.30/1.51  thf('311', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.30/1.51      inference('simplify', [status(thm)], ['15'])).
% 1.30/1.51  thf('312', plain, ((v1_relat_1 @ sk_C)),
% 1.30/1.51      inference('sup-', [status(thm)], ['68', '69'])).
% 1.30/1.51  thf('313', plain, ((v1_funct_1 @ sk_C)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('314', plain, ((v2_funct_1 @ sk_C)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('315', plain,
% 1.30/1.51      (((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) = (sk_B))),
% 1.30/1.51      inference('demod', [status(thm)],
% 1.30/1.51                ['309', '310', '311', '312', '313', '314'])).
% 1.30/1.51  thf('316', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (~ (v1_relat_1 @ X0)
% 1.30/1.51          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) = (X0)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['16', '19'])).
% 1.30/1.51  thf('317', plain,
% 1.30/1.51      ((((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.30/1.51          (k6_partfun1 @ sk_B)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.30/1.51        | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.30/1.51      inference('sup+', [status(thm)], ['315', '316'])).
% 1.30/1.51  thf('318', plain,
% 1.30/1.51      ((~ (v1_relat_1 @ sk_C)
% 1.30/1.51        | ~ (v1_relat_1 @ sk_C)
% 1.30/1.51        | ~ (v1_funct_1 @ sk_C)
% 1.30/1.51        | ~ (v2_funct_1 @ sk_C)
% 1.30/1.51        | ((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.30/1.51            (k6_partfun1 @ sk_B)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.30/1.51      inference('sup-', [status(thm)], ['171', '317'])).
% 1.30/1.51  thf('319', plain, ((v1_relat_1 @ sk_C)),
% 1.30/1.51      inference('sup-', [status(thm)], ['68', '69'])).
% 1.30/1.51  thf('320', plain, ((v1_relat_1 @ sk_C)),
% 1.30/1.51      inference('sup-', [status(thm)], ['68', '69'])).
% 1.30/1.51  thf('321', plain, ((v1_funct_1 @ sk_C)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('322', plain, ((v2_funct_1 @ sk_C)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('323', plain,
% 1.30/1.51      (((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ (k6_partfun1 @ sk_B))
% 1.30/1.51         = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.30/1.51      inference('demod', [status(thm)], ['318', '319', '320', '321', '322'])).
% 1.30/1.51  thf('324', plain,
% 1.30/1.51      ((((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B))
% 1.30/1.51          = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.30/1.51        | ~ (v1_relat_1 @ sk_C)
% 1.30/1.51        | ~ (v1_funct_1 @ sk_C)
% 1.30/1.51        | ~ (v2_funct_1 @ sk_C))),
% 1.30/1.51      inference('sup+', [status(thm)], ['170', '323'])).
% 1.30/1.51  thf('325', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 1.30/1.51      inference('demod', [status(thm)], ['248', '249'])).
% 1.30/1.51  thf('326', plain, ((v1_relat_1 @ sk_C)),
% 1.30/1.51      inference('sup-', [status(thm)], ['68', '69'])).
% 1.30/1.51  thf('327', plain, ((v1_funct_1 @ sk_C)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('328', plain, ((v2_funct_1 @ sk_C)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('329', plain, (((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.30/1.51      inference('demod', [status(thm)], ['324', '325', '326', '327', '328'])).
% 1.30/1.51  thf('330', plain,
% 1.30/1.51      (![X26 : $i]:
% 1.30/1.51         (~ (v2_funct_1 @ X26)
% 1.30/1.51          | ((k5_relat_1 @ X26 @ (k2_funct_1 @ X26))
% 1.30/1.51              = (k6_partfun1 @ (k1_relat_1 @ X26)))
% 1.30/1.51          | ~ (v1_funct_1 @ X26)
% 1.30/1.51          | ~ (v1_relat_1 @ X26))),
% 1.30/1.51      inference('demod', [status(thm)], ['243', '244'])).
% 1.30/1.51  thf('331', plain,
% 1.30/1.51      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 1.30/1.51          = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 1.30/1.51        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.30/1.51        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.30/1.51        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.30/1.51      inference('sup+', [status(thm)], ['329', '330'])).
% 1.30/1.51  thf('332', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.30/1.51      inference('demod', [status(thm)],
% 1.30/1.51                ['199', '200', '201', '202', '203', '204'])).
% 1.30/1.51  thf('333', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 1.30/1.51      inference('demod', [status(thm)], ['294', '295', '296'])).
% 1.30/1.51  thf('334', plain,
% 1.30/1.51      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 1.30/1.51        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.30/1.51        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.30/1.51      inference('demod', [status(thm)], ['331', '332', '333'])).
% 1.30/1.51  thf('335', plain,
% 1.30/1.51      ((~ (v1_relat_1 @ sk_C)
% 1.30/1.51        | ~ (v1_funct_1 @ sk_C)
% 1.30/1.51        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.30/1.51        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['169', '334'])).
% 1.30/1.51  thf('336', plain, ((v1_relat_1 @ sk_C)),
% 1.30/1.51      inference('sup-', [status(thm)], ['68', '69'])).
% 1.30/1.51  thf('337', plain, ((v1_funct_1 @ sk_C)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('338', plain,
% 1.30/1.51      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.30/1.51        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 1.30/1.51      inference('demod', [status(thm)], ['335', '336', '337'])).
% 1.30/1.51  thf('339', plain,
% 1.30/1.51      ((~ (v1_relat_1 @ sk_C)
% 1.30/1.51        | ~ (v1_funct_1 @ sk_C)
% 1.30/1.51        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['168', '338'])).
% 1.30/1.51  thf('340', plain, ((v1_relat_1 @ sk_C)),
% 1.30/1.51      inference('sup-', [status(thm)], ['68', '69'])).
% 1.30/1.51  thf('341', plain, ((v1_funct_1 @ sk_C)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('342', plain,
% 1.30/1.51      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 1.30/1.51      inference('demod', [status(thm)], ['339', '340', '341'])).
% 1.30/1.51  thf('343', plain,
% 1.30/1.51      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.30/1.51         (~ (v1_relat_1 @ X11)
% 1.30/1.51          | ((k5_relat_1 @ (k5_relat_1 @ X12 @ X11) @ X13)
% 1.30/1.51              = (k5_relat_1 @ X12 @ (k5_relat_1 @ X11 @ X13)))
% 1.30/1.51          | ~ (v1_relat_1 @ X13)
% 1.30/1.51          | ~ (v1_relat_1 @ X12))),
% 1.30/1.51      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.30/1.51  thf('344', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.30/1.51            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.30/1.51          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.30/1.51          | ~ (v1_relat_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ sk_C))),
% 1.30/1.51      inference('sup+', [status(thm)], ['342', '343'])).
% 1.30/1.51  thf('345', plain, ((v1_relat_1 @ sk_C)),
% 1.30/1.51      inference('sup-', [status(thm)], ['68', '69'])).
% 1.30/1.51  thf('346', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.30/1.51            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.30/1.51          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.30/1.51          | ~ (v1_relat_1 @ X0))),
% 1.30/1.51      inference('demod', [status(thm)], ['344', '345'])).
% 1.30/1.51  thf('347', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (~ (v1_relat_1 @ sk_C)
% 1.30/1.51          | ~ (v1_funct_1 @ sk_C)
% 1.30/1.51          | ~ (v1_relat_1 @ X0)
% 1.30/1.51          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.30/1.51              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 1.30/1.51      inference('sup-', [status(thm)], ['167', '346'])).
% 1.30/1.51  thf('348', plain, ((v1_relat_1 @ sk_C)),
% 1.30/1.51      inference('sup-', [status(thm)], ['68', '69'])).
% 1.30/1.51  thf('349', plain, ((v1_funct_1 @ sk_C)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('350', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (~ (v1_relat_1 @ X0)
% 1.30/1.51          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.30/1.51              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 1.30/1.51      inference('demod', [status(thm)], ['347', '348', '349'])).
% 1.30/1.51  thf('351', plain,
% 1.30/1.51      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 1.30/1.51          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 1.30/1.51        | ~ (v1_relat_1 @ sk_D))),
% 1.30/1.51      inference('sup+', [status(thm)], ['166', '350'])).
% 1.30/1.51  thf('352', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 1.30/1.51      inference('sup-', [status(thm)], ['151', '152'])).
% 1.30/1.51  thf('353', plain,
% 1.30/1.51      (![X3 : $i, X4 : $i]:
% 1.30/1.51         (~ (v4_relat_1 @ X3 @ X4)
% 1.30/1.51          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.30/1.51          | ~ (v1_relat_1 @ X3))),
% 1.30/1.51      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.30/1.51  thf('354', plain,
% 1.30/1.51      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 1.30/1.51      inference('sup-', [status(thm)], ['352', '353'])).
% 1.30/1.51  thf('355', plain, ((v1_relat_1 @ sk_C)),
% 1.30/1.51      inference('sup-', [status(thm)], ['68', '69'])).
% 1.30/1.51  thf('356', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 1.30/1.51      inference('demod', [status(thm)], ['354', '355'])).
% 1.30/1.51  thf('357', plain,
% 1.30/1.51      (![X19 : $i]:
% 1.30/1.51         ((v1_relat_1 @ (k2_funct_1 @ X19))
% 1.30/1.51          | ~ (v1_funct_1 @ X19)
% 1.30/1.51          | ~ (v1_relat_1 @ X19))),
% 1.30/1.51      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.30/1.51  thf('358', plain,
% 1.30/1.51      (![X25 : $i]:
% 1.30/1.51         (~ (v2_funct_1 @ X25)
% 1.30/1.51          | ((k1_relat_1 @ X25) = (k2_relat_1 @ (k2_funct_1 @ X25)))
% 1.30/1.51          | ~ (v1_funct_1 @ X25)
% 1.30/1.51          | ~ (v1_relat_1 @ X25))),
% 1.30/1.51      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.30/1.51  thf('359', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         ((r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.30/1.51          | ~ (v2_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_funct_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ X0))),
% 1.30/1.51      inference('simplify', [status(thm)], ['237'])).
% 1.30/1.51  thf('360', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 1.30/1.51      inference('demod', [status(thm)], ['248', '249'])).
% 1.30/1.51  thf('361', plain,
% 1.30/1.51      (![X14 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X14)) = (X14))),
% 1.30/1.51      inference('demod', [status(thm)], ['37', '38'])).
% 1.30/1.51  thf('362', plain,
% 1.30/1.51      (![X7 : $i, X8 : $i]:
% 1.30/1.51         (~ (v1_relat_1 @ X7)
% 1.30/1.51          | ((k1_relat_1 @ (k5_relat_1 @ X8 @ X7))
% 1.30/1.51              = (k10_relat_1 @ X8 @ (k1_relat_1 @ X7)))
% 1.30/1.51          | ~ (v1_relat_1 @ X8))),
% 1.30/1.51      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.30/1.51  thf('363', plain,
% 1.30/1.51      (![X3 : $i, X4 : $i]:
% 1.30/1.51         (~ (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.30/1.51          | (v4_relat_1 @ X3 @ X4)
% 1.30/1.51          | ~ (v1_relat_1 @ X3))),
% 1.30/1.51      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.30/1.51  thf('364', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.30/1.51         (~ (r1_tarski @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)) @ X2)
% 1.30/1.51          | ~ (v1_relat_1 @ X1)
% 1.30/1.51          | ~ (v1_relat_1 @ X0)
% 1.30/1.51          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 1.30/1.51          | (v4_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2))),
% 1.30/1.51      inference('sup-', [status(thm)], ['362', '363'])).
% 1.30/1.51  thf('365', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.30/1.51         (~ (r1_tarski @ (k10_relat_1 @ X2 @ X0) @ X1)
% 1.30/1.51          | (v4_relat_1 @ (k5_relat_1 @ X2 @ (k6_partfun1 @ X0)) @ X1)
% 1.30/1.51          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ (k6_partfun1 @ X0)))
% 1.30/1.51          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 1.30/1.51          | ~ (v1_relat_1 @ X2))),
% 1.30/1.51      inference('sup-', [status(thm)], ['361', '364'])).
% 1.30/1.51  thf('366', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.30/1.51      inference('sup-', [status(thm)], ['33', '34'])).
% 1.30/1.51  thf('367', plain,
% 1.30/1.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.30/1.51         (~ (r1_tarski @ (k10_relat_1 @ X2 @ X0) @ X1)
% 1.30/1.51          | (v4_relat_1 @ (k5_relat_1 @ X2 @ (k6_partfun1 @ X0)) @ X1)
% 1.30/1.51          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ (k6_partfun1 @ X0)))
% 1.30/1.51          | ~ (v1_relat_1 @ X2))),
% 1.30/1.51      inference('demod', [status(thm)], ['365', '366'])).
% 1.30/1.51  thf('368', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         (~ (v1_relat_1 @ sk_C)
% 1.30/1.51          | ~ (v1_relat_1 @ sk_C)
% 1.30/1.51          | (v4_relat_1 @ (k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) @ X0)
% 1.30/1.51          | ~ (r1_tarski @ (k10_relat_1 @ sk_C @ sk_B) @ X0))),
% 1.30/1.51      inference('sup-', [status(thm)], ['360', '367'])).
% 1.30/1.51  thf('369', plain, ((v1_relat_1 @ sk_C)),
% 1.30/1.51      inference('sup-', [status(thm)], ['68', '69'])).
% 1.30/1.51  thf('370', plain, ((v1_relat_1 @ sk_C)),
% 1.30/1.51      inference('sup-', [status(thm)], ['68', '69'])).
% 1.30/1.51  thf('371', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 1.30/1.51      inference('demod', [status(thm)], ['248', '249'])).
% 1.30/1.51  thf('372', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         ((v4_relat_1 @ sk_C @ X0)
% 1.30/1.51          | ~ (r1_tarski @ (k10_relat_1 @ sk_C @ sk_B) @ X0))),
% 1.30/1.51      inference('demod', [status(thm)], ['368', '369', '370', '371'])).
% 1.30/1.51  thf('373', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 1.30/1.51      inference('demod', [status(thm)], ['248', '249'])).
% 1.30/1.51  thf('374', plain,
% 1.30/1.51      (![X7 : $i, X8 : $i]:
% 1.30/1.51         (~ (v1_relat_1 @ X7)
% 1.30/1.51          | ((k1_relat_1 @ (k5_relat_1 @ X8 @ X7))
% 1.30/1.51              = (k10_relat_1 @ X8 @ (k1_relat_1 @ X7)))
% 1.30/1.51          | ~ (v1_relat_1 @ X8))),
% 1.30/1.51      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.30/1.51  thf('375', plain,
% 1.30/1.51      ((((k1_relat_1 @ sk_C)
% 1.30/1.51          = (k10_relat_1 @ sk_C @ (k1_relat_1 @ (k6_partfun1 @ sk_B))))
% 1.30/1.51        | ~ (v1_relat_1 @ sk_C)
% 1.30/1.51        | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B)))),
% 1.30/1.51      inference('sup+', [status(thm)], ['373', '374'])).
% 1.30/1.51  thf('376', plain,
% 1.30/1.51      (![X14 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X14)) = (X14))),
% 1.30/1.51      inference('demod', [status(thm)], ['37', '38'])).
% 1.30/1.51  thf('377', plain, ((v1_relat_1 @ sk_C)),
% 1.30/1.51      inference('sup-', [status(thm)], ['68', '69'])).
% 1.30/1.51  thf('378', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.30/1.51      inference('sup-', [status(thm)], ['33', '34'])).
% 1.30/1.51  thf('379', plain, (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_B))),
% 1.30/1.51      inference('demod', [status(thm)], ['375', '376', '377', '378'])).
% 1.30/1.51  thf('380', plain,
% 1.30/1.51      (![X0 : $i]:
% 1.30/1.51         ((v4_relat_1 @ sk_C @ X0) | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 1.30/1.51      inference('demod', [status(thm)], ['372', '379'])).
% 1.30/1.51  thf('381', plain,
% 1.30/1.51      ((~ (v1_relat_1 @ sk_C)
% 1.30/1.51        | ~ (v1_funct_1 @ sk_C)
% 1.30/1.51        | ~ (v2_funct_1 @ sk_C)
% 1.30/1.51        | (v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.30/1.51      inference('sup-', [status(thm)], ['359', '380'])).
% 1.30/1.51  thf('382', plain, ((v1_relat_1 @ sk_C)),
% 1.30/1.51      inference('sup-', [status(thm)], ['68', '69'])).
% 1.30/1.51  thf('383', plain, ((v1_funct_1 @ sk_C)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('384', plain, ((v2_funct_1 @ sk_C)),
% 1.30/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.51  thf('385', plain, ((v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.30/1.51      inference('demod', [status(thm)], ['381', '382', '383', '384'])).
% 1.30/1.51  thf('386', plain,
% 1.30/1.51      (![X3 : $i, X4 : $i]:
% 1.30/1.51         (~ (v4_relat_1 @ X3 @ X4)
% 1.30/1.51          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.30/1.51          | ~ (v1_relat_1 @ X3))),
% 1.30/1.51      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.30/1.51  thf('387', plain,
% 1.30/1.51      ((~ (v1_relat_1 @ sk_C)
% 1.30/1.51        | (r1_tarski @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.30/1.51      inference('sup-', [status(thm)], ['385', '386'])).
% 1.30/1.51  thf('388', plain, ((v1_relat_1 @ sk_C)),
% 1.30/1.51      inference('sup-', [status(thm)], ['68', '69'])).
% 1.30/1.51  thf('389', plain,
% 1.30/1.51      ((r1_tarski @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.30/1.51      inference('demod', [status(thm)], ['387', '388'])).
% 1.30/1.51  thf('390', plain,
% 1.30/1.51      (![X0 : $i, X2 : $i]:
% 1.30/1.51         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.30/1.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.30/1.51  thf('391', plain,
% 1.30/1.51      ((~ (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k1_relat_1 @ sk_C))
% 1.30/1.51        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['389', '390'])).
% 1.30/1.51  thf('392', plain,
% 1.30/1.51      ((~ (r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))
% 1.30/1.51        | ~ (v1_relat_1 @ sk_C)
% 1.30/1.51        | ~ (v1_funct_1 @ sk_C)
% 1.30/1.51        | ~ (v2_funct_1 @ sk_C)
% 1.30/1.51        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C)))),
% 1.30/1.51      inference('sup-', [status(thm)], ['358', '391'])).
% 1.30/1.51  thf('393', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.30/1.51      inference('simplify', [status(thm)], ['15'])).
% 1.30/1.51  thf('394', plain, ((v1_relat_1 @ sk_C)),
% 1.30/1.52      inference('sup-', [status(thm)], ['68', '69'])).
% 1.30/1.52  thf('395', plain, ((v1_funct_1 @ sk_C)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('396', plain, ((v2_funct_1 @ sk_C)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('397', plain,
% 1.30/1.52      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 1.30/1.52      inference('demod', [status(thm)], ['392', '393', '394', '395', '396'])).
% 1.30/1.52  thf('398', plain,
% 1.30/1.52      (![X17 : $i, X18 : $i]:
% 1.30/1.52         (~ (r1_tarski @ (k2_relat_1 @ X17) @ X18)
% 1.30/1.52          | ((k5_relat_1 @ X17 @ (k6_partfun1 @ X18)) = (X17))
% 1.30/1.52          | ~ (v1_relat_1 @ X17))),
% 1.30/1.52      inference('demod', [status(thm)], ['17', '18'])).
% 1.30/1.52  thf('399', plain,
% 1.30/1.52      (![X0 : $i]:
% 1.30/1.52         (~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0)
% 1.30/1.52          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.30/1.52          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ X0))
% 1.30/1.52              = (k2_funct_1 @ sk_C)))),
% 1.30/1.52      inference('sup-', [status(thm)], ['397', '398'])).
% 1.30/1.52  thf('400', plain,
% 1.30/1.52      (![X0 : $i]:
% 1.30/1.52         (~ (v1_relat_1 @ sk_C)
% 1.30/1.52          | ~ (v1_funct_1 @ sk_C)
% 1.30/1.52          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ X0))
% 1.30/1.52              = (k2_funct_1 @ sk_C))
% 1.30/1.52          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 1.30/1.52      inference('sup-', [status(thm)], ['357', '399'])).
% 1.30/1.52  thf('401', plain, ((v1_relat_1 @ sk_C)),
% 1.30/1.52      inference('sup-', [status(thm)], ['68', '69'])).
% 1.30/1.52  thf('402', plain, ((v1_funct_1 @ sk_C)),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('403', plain,
% 1.30/1.52      (![X0 : $i]:
% 1.30/1.52         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ X0))
% 1.30/1.52            = (k2_funct_1 @ sk_C))
% 1.30/1.52          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 1.30/1.52      inference('demod', [status(thm)], ['400', '401', '402'])).
% 1.30/1.52  thf('404', plain,
% 1.30/1.52      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 1.30/1.52         = (k2_funct_1 @ sk_C))),
% 1.30/1.52      inference('sup-', [status(thm)], ['356', '403'])).
% 1.30/1.52  thf('405', plain, ((v1_relat_1 @ sk_D)),
% 1.30/1.52      inference('sup-', [status(thm)], ['22', '23'])).
% 1.30/1.52  thf('406', plain,
% 1.30/1.52      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (k2_funct_1 @ sk_C))),
% 1.30/1.52      inference('demod', [status(thm)], ['351', '404', '405'])).
% 1.30/1.52  thf('407', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 1.30/1.52      inference('sup+', [status(thm)], ['165', '406'])).
% 1.30/1.52  thf('408', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.30/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.52  thf('409', plain, ($false),
% 1.30/1.52      inference('simplify_reflect-', [status(thm)], ['407', '408'])).
% 1.30/1.52  
% 1.30/1.52  % SZS output end Refutation
% 1.30/1.52  
% 1.30/1.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

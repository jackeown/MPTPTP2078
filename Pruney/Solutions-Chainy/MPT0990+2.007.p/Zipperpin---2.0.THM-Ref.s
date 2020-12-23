%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Jbl07fGAEt

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:54 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :  466 (2043 expanded)
%              Number of leaves         :   53 ( 637 expanded)
%              Depth                    :   48
%              Number of atoms          : 3978 (40776 expanded)
%              Number of equality atoms :  224 (2763 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k2_relset_1 @ X36 @ X37 @ X35 )
        = ( k2_relat_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v1_relat_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
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

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('33',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('34',plain,(
    ! [X55: $i] :
      ( ( k6_partfun1 @ X55 )
      = ( k6_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('35',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X20 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

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
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X20 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

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
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v4_relat_1 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k2_relset_1 @ X36 @ X37 @ X35 )
        = ( k2_relat_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X22 @ ( k2_relat_1 @ X23 ) )
      | ( ( k9_relat_1 @ X23 @ ( k10_relat_1 @ X23 @ X22 ) )
        = X22 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v1_relat_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
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
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X48 ) ) ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v4_relat_1 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v1_relat_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
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
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X20 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

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
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X20 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

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
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X20 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

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
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X20 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

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
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X20 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

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
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( X38 = X41 )
      | ~ ( r2_relset_1 @ X39 @ X40 @ X38 @ X41 ) ) ),
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

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('146',plain,(
    ! [X42: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('147',plain,(
    ! [X55: $i] :
      ( ( k6_partfun1 @ X55 )
      = ( k6_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('148',plain,(
    ! [X42: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X42 ) ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['145','148'])).

thf('150',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X14 ) )
      = X14 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('151',plain,
    ( ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) )
    = sk_A ),
    inference(demod,[status(thm)],['138','149','150'])).

thf('152',plain,
    ( ( k9_relat_1 @ sk_C @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['73','151'])).

thf('153',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v4_relat_1 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('155',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X9
        = ( k7_relat_1 @ X9 @ X10 ) )
      | ~ ( v4_relat_1 @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('157',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('159',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) )
        = ( k9_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('161',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['159','160'])).

thf('162',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('163',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['63','64'])).

thf('165',plain,
    ( sk_B
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['152','165'])).

thf('167',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['53','166'])).

thf('168',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['145','148'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('169',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('170',plain,(
    ! [X19: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('171',plain,(
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

thf('172',plain,(
    ! [X28: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X28 ) )
        = X28 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('173',plain,(
    ! [X28: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X28 ) )
        = X28 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('174',plain,(
    ! [X28: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X28 ) )
        = X28 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('175',plain,(
    ! [X19: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('176',plain,(
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

thf('177',plain,(
    ! [X26: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k2_relat_1 @ X26 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('178',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('179',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['63','64'])).

thf('180',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('181',plain,(
    ! [X26: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k2_relat_1 @ X26 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('182',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('183',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ( v4_relat_1 @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('184',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['181','184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['180','185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['186'])).

thf('188',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['179','187'])).

thf('189',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('190',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['188','189','190','191'])).

thf('193',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v4_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('194',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['178','194'])).

thf('196',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('197',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['195','196','197'])).

thf('199',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('200',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['177','200'])).

thf('202',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['63','64'])).

thf('203',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('204',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('205',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['201','202','203','204','205','206'])).

thf('208',plain,(
    ! [X26: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k1_relat_1 @ X26 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('209',plain,(
    ! [X19: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('210',plain,(
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

thf('211',plain,(
    ! [X27: $i] :
      ( ~ ( v2_funct_1 @ X27 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X27 ) @ X27 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('212',plain,(
    ! [X55: $i] :
      ( ( k6_partfun1 @ X55 )
      = ( k6_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('213',plain,(
    ! [X27: $i] :
      ( ~ ( v2_funct_1 @ X27 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X27 ) @ X27 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(demod,[status(thm)],['211','212'])).

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

thf('214',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( v2_funct_1 @ X24 )
      | ( ( k2_relat_1 @ X24 )
       != ( k1_relat_1 @ X25 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X24 @ X25 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('215',plain,(
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
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    ! [X21: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('217',plain,(
    ! [X55: $i] :
      ( ( k6_partfun1 @ X55 )
      = ( k6_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('218',plain,(
    ! [X21: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X21 ) ) ),
    inference(demod,[status(thm)],['216','217'])).

thf('219',plain,(
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
    inference(demod,[status(thm)],['215','218'])).

thf('220',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
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
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['210','220'])).

thf('222',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['221'])).

thf('223',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['209','222'])).

thf('224',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['223'])).

thf('225',plain,(
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
    inference('sup-',[status(thm)],['208','224'])).

thf('226',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['225'])).

thf('227',plain,(
    ! [X19: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('228',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('229',plain,(
    ! [X28: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X28 ) )
        = X28 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('230',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['186'])).

thf('231',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['229','230'])).

thf('232',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['228','231'])).

thf('233',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['232'])).

thf('234',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['227','233'])).

thf('235',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['234'])).

thf('236',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['226','235'])).

thf('237',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['236'])).

thf('238',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v4_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('239',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['237','238'])).

thf('240',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['239'])).

thf('241',plain,
    ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['207','240'])).

thf('242',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('243',plain,(
    ! [X19: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('244',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('245',plain,(
    ! [X27: $i] :
      ( ~ ( v2_funct_1 @ X27 )
      | ( ( k5_relat_1 @ X27 @ ( k2_funct_1 @ X27 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('246',plain,(
    ! [X55: $i] :
      ( ( k6_partfun1 @ X55 )
      = ( k6_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('247',plain,(
    ! [X27: $i] :
      ( ~ ( v2_funct_1 @ X27 )
      | ( ( k5_relat_1 @ X27 @ ( k2_funct_1 @ X27 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(demod,[status(thm)],['245','246'])).

thf('248',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['63','64'])).

thf('249',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('250',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['248','249'])).

thf('251',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('252',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['250','251'])).

thf('253',plain,(
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

thf('254',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) @ X13 )
        = ( k5_relat_1 @ X12 @ ( k5_relat_1 @ X11 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('255',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['253','254'])).

thf('256',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X20 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('257',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['255','256'])).

thf('258',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['257'])).

thf('259',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['252','258'])).

thf('260',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['250','251'])).

thf('261',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('262',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X20 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('263',plain,
    ( sk_C
    = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['259','260','261','262'])).

thf('264',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) @ X13 )
        = ( k5_relat_1 @ X12 @ ( k5_relat_1 @ X11 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('265',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['263','264'])).

thf('266',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X20 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('267',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('268',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['265','266','267'])).

thf('269',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['247','268'])).

thf('270',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X14 ) )
      = X14 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('271',plain,(
    ! [X16: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X16 ) ) @ X16 )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('272',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['270','271'])).

thf('273',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X20 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('274',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['272','273'])).

thf('275',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('276',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('277',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('278',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['269','274','275','276','277'])).

thf('279',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['244','278'])).

thf('280',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('281',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('282',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['279','280','281'])).

thf('283',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( v2_funct_1 @ X25 )
      | ( ( k2_relat_1 @ X24 )
       != ( k1_relat_1 @ X25 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X24 @ X25 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('284',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['282','283'])).

thf('285',plain,(
    ! [X21: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X21 ) ) ),
    inference(demod,[status(thm)],['216','217'])).

thf('286',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['63','64'])).

thf('287',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['201','202','203','204','205','206'])).

thf('288',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('289',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('290',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_B != sk_B )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['284','285','286','287','288','289'])).

thf('291',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['290'])).

thf('292',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['243','291'])).

thf('293',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('294',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('295',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['292','293','294'])).

thf('296',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['242','295'])).

thf('297',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('298',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('299',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['296','297','298'])).

thf('300',plain,
    ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['241','299'])).

thf('301',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['176','300'])).

thf('302',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('303',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('304',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['301','302','303'])).

thf('305',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['175','304'])).

thf('306',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('307',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('308',plain,(
    r1_tarski @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['305','306','307'])).

thf('309',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('310',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) @ sk_B )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['308','309'])).

thf('311',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['174','310'])).

thf('312',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['63','64'])).

thf('313',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('314',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('315',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('316',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('317',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    = sk_B ),
    inference(demod,[status(thm)],['311','312','313','314','315','316'])).

thf('318',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('319',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k6_partfun1 @ sk_B ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['317','318'])).

thf('320',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k6_partfun1 @ sk_B ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['173','319'])).

thf('321',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('322',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('323',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('324',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('325',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k6_partfun1 @ sk_B ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['320','321','322','323','324'])).

thf('326',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['172','325'])).

thf('327',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['250','251'])).

thf('328',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('329',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('330',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('331',plain,
    ( sk_C
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['326','327','328','329','330'])).

thf('332',plain,(
    ! [X27: $i] :
      ( ~ ( v2_funct_1 @ X27 )
      | ( ( k5_relat_1 @ X27 @ ( k2_funct_1 @ X27 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(demod,[status(thm)],['245','246'])).

thf('333',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['331','332'])).

thf('334',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['201','202','203','204','205','206'])).

thf('335',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['296','297','298'])).

thf('336',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['333','334','335'])).

thf('337',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['171','336'])).

thf('338',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('339',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('340',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['337','338','339'])).

thf('341',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['170','340'])).

thf('342',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('343',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('344',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['341','342','343'])).

thf('345',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) @ X13 )
        = ( k5_relat_1 @ X12 @ ( k5_relat_1 @ X11 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('346',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['344','345'])).

thf('347',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('348',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['346','347'])).

thf('349',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['169','348'])).

thf('350',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('351',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('352',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['349','350','351'])).

thf('353',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['168','352'])).

thf('354',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['153','154'])).

thf('355',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v4_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('356',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['354','355'])).

thf('357',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('358',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['356','357'])).

thf('359',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('360',plain,(
    ! [X26: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k1_relat_1 @ X26 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('361',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['239'])).

thf('362',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['250','251'])).

thf('363',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X14 ) )
      = X14 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('364',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) )
        = ( k10_relat_1 @ X8 @ ( k1_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('365',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ( v4_relat_1 @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('366',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( v4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['364','365'])).

thf('367',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ X2 @ X0 ) @ X1 )
      | ( v4_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_partfun1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['363','366'])).

thf('368',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X20 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('369',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ X2 @ X0 ) @ X1 )
      | ( v4_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_partfun1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['367','368'])).

thf('370',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C )
      | ( v4_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ X0 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['362','369'])).

thf('371',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('372',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('373',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['250','251'])).

thf('374',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ sk_C @ X0 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['370','371','372','373'])).

thf('375',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['250','251'])).

thf('376',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) )
        = ( k10_relat_1 @ X8 @ ( k1_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('377',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['375','376'])).

thf('378',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X14 ) )
      = X14 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('379',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('380',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X20 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('381',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['377','378','379','380'])).

thf('382',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ sk_C @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['374','381'])).

thf('383',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['361','382'])).

thf('384',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('385',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('386',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('387',plain,(
    v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['383','384','385','386'])).

thf('388',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v4_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('389',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['387','388'])).

thf('390',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('391',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['389','390'])).

thf('392',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('393',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['391','392'])).

thf('394',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['360','393'])).

thf('395',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('396',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('397',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('398',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('399',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['394','395','396','397','398'])).

thf('400',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ X18 )
      | ( ( k5_relat_1 @ X17 @ ( k6_partfun1 @ X18 ) )
        = X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('401',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ X0 ) )
        = ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['399','400'])).

thf('402',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ X0 ) )
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['359','401'])).

thf('403',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('404',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('405',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ X0 ) )
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['402','403','404'])).

thf('406',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['358','405'])).

thf('407',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['22','23'])).

thf('408',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['353','406','407'])).

thf('409',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['167','408'])).

thf('410',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('411',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['409','410'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Jbl07fGAEt
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:15:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.20/1.40  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.20/1.40  % Solved by: fo/fo7.sh
% 1.20/1.40  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.20/1.40  % done 1262 iterations in 0.947s
% 1.20/1.40  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.20/1.40  % SZS output start Refutation
% 1.20/1.40  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.20/1.40  thf(sk_A_type, type, sk_A: $i).
% 1.20/1.40  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.20/1.40  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.20/1.40  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.20/1.40  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.20/1.40  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.20/1.40  thf(sk_C_type, type, sk_C: $i).
% 1.20/1.40  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.20/1.40  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.20/1.40  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.20/1.40  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.20/1.40  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.20/1.40  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.20/1.40  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.20/1.40  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.20/1.40  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.20/1.40  thf(sk_B_type, type, sk_B: $i).
% 1.20/1.40  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.20/1.40  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.20/1.40  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.20/1.40  thf(sk_D_type, type, sk_D: $i).
% 1.20/1.40  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.20/1.40  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.20/1.40  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.20/1.40  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.20/1.40  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.20/1.40  thf(t36_funct_2, conjecture,
% 1.20/1.40    (![A:$i,B:$i,C:$i]:
% 1.20/1.40     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.20/1.40         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.20/1.40       ( ![D:$i]:
% 1.20/1.40         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.20/1.40             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.20/1.40           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.20/1.40               ( r2_relset_1 @
% 1.20/1.40                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.20/1.40                 ( k6_partfun1 @ A ) ) & 
% 1.20/1.40               ( v2_funct_1 @ C ) ) =>
% 1.20/1.40             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.20/1.40               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.20/1.40  thf(zf_stmt_0, negated_conjecture,
% 1.20/1.40    (~( ![A:$i,B:$i,C:$i]:
% 1.20/1.40        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.20/1.40            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.20/1.40          ( ![D:$i]:
% 1.20/1.40            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.20/1.40                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.20/1.40              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.20/1.40                  ( r2_relset_1 @
% 1.20/1.40                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.20/1.40                    ( k6_partfun1 @ A ) ) & 
% 1.20/1.40                  ( v2_funct_1 @ C ) ) =>
% 1.20/1.40                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.20/1.40                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.20/1.40    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.20/1.40  thf('0', plain,
% 1.20/1.40      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.20/1.40        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.20/1.40        (k6_partfun1 @ sk_A))),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('1', plain,
% 1.20/1.40      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf(t24_funct_2, axiom,
% 1.20/1.40    (![A:$i,B:$i,C:$i]:
% 1.20/1.40     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.20/1.40         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.20/1.40       ( ![D:$i]:
% 1.20/1.40         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.20/1.40             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.20/1.40           ( ( r2_relset_1 @
% 1.20/1.40               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 1.20/1.40               ( k6_partfun1 @ B ) ) =>
% 1.20/1.40             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 1.20/1.40  thf('2', plain,
% 1.20/1.40      (![X56 : $i, X57 : $i, X58 : $i, X59 : $i]:
% 1.20/1.40         (~ (v1_funct_1 @ X56)
% 1.20/1.40          | ~ (v1_funct_2 @ X56 @ X57 @ X58)
% 1.20/1.40          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X58)))
% 1.20/1.40          | ~ (r2_relset_1 @ X57 @ X57 @ 
% 1.20/1.40               (k1_partfun1 @ X57 @ X58 @ X58 @ X57 @ X56 @ X59) @ 
% 1.20/1.40               (k6_partfun1 @ X57))
% 1.20/1.40          | ((k2_relset_1 @ X58 @ X57 @ X59) = (X57))
% 1.20/1.40          | ~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X57)))
% 1.20/1.40          | ~ (v1_funct_2 @ X59 @ X58 @ X57)
% 1.20/1.40          | ~ (v1_funct_1 @ X59))),
% 1.20/1.40      inference('cnf', [status(esa)], [t24_funct_2])).
% 1.20/1.40  thf('3', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (~ (v1_funct_1 @ X0)
% 1.20/1.40          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.20/1.40          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.20/1.40          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.20/1.40          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.20/1.40               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.20/1.40               (k6_partfun1 @ sk_A))
% 1.20/1.40          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.20/1.40          | ~ (v1_funct_1 @ sk_C))),
% 1.20/1.40      inference('sup-', [status(thm)], ['1', '2'])).
% 1.20/1.40  thf('4', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('6', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (~ (v1_funct_1 @ X0)
% 1.20/1.40          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.20/1.40          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.20/1.40          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.20/1.40          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.20/1.40               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.20/1.40               (k6_partfun1 @ sk_A)))),
% 1.20/1.40      inference('demod', [status(thm)], ['3', '4', '5'])).
% 1.20/1.40  thf('7', plain,
% 1.20/1.40      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 1.20/1.40        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.20/1.40        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.20/1.40        | ~ (v1_funct_1 @ sk_D))),
% 1.20/1.40      inference('sup-', [status(thm)], ['0', '6'])).
% 1.20/1.40  thf('8', plain,
% 1.20/1.40      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf(redefinition_k2_relset_1, axiom,
% 1.20/1.40    (![A:$i,B:$i,C:$i]:
% 1.20/1.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.20/1.40       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.20/1.40  thf('9', plain,
% 1.20/1.40      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.20/1.40         (((k2_relset_1 @ X36 @ X37 @ X35) = (k2_relat_1 @ X35))
% 1.20/1.40          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 1.20/1.40      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.20/1.40  thf('10', plain,
% 1.20/1.40      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.20/1.40      inference('sup-', [status(thm)], ['8', '9'])).
% 1.20/1.40  thf('11', plain,
% 1.20/1.40      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('12', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('13', plain, ((v1_funct_1 @ sk_D)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('14', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.20/1.40      inference('demod', [status(thm)], ['7', '10', '11', '12', '13'])).
% 1.20/1.40  thf(d10_xboole_0, axiom,
% 1.20/1.40    (![A:$i,B:$i]:
% 1.20/1.40     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.20/1.40  thf('15', plain,
% 1.20/1.40      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.20/1.40      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.20/1.40  thf('16', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.20/1.40      inference('simplify', [status(thm)], ['15'])).
% 1.20/1.40  thf(t79_relat_1, axiom,
% 1.20/1.40    (![A:$i,B:$i]:
% 1.20/1.40     ( ( v1_relat_1 @ B ) =>
% 1.20/1.40       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 1.20/1.40         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 1.20/1.40  thf('17', plain,
% 1.20/1.40      (![X17 : $i, X18 : $i]:
% 1.20/1.40         (~ (r1_tarski @ (k2_relat_1 @ X17) @ X18)
% 1.20/1.40          | ((k5_relat_1 @ X17 @ (k6_relat_1 @ X18)) = (X17))
% 1.20/1.40          | ~ (v1_relat_1 @ X17))),
% 1.20/1.40      inference('cnf', [status(esa)], [t79_relat_1])).
% 1.20/1.40  thf(redefinition_k6_partfun1, axiom,
% 1.20/1.40    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.20/1.40  thf('18', plain, (![X55 : $i]: ((k6_partfun1 @ X55) = (k6_relat_1 @ X55))),
% 1.20/1.40      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.20/1.40  thf('19', plain,
% 1.20/1.40      (![X17 : $i, X18 : $i]:
% 1.20/1.40         (~ (r1_tarski @ (k2_relat_1 @ X17) @ X18)
% 1.20/1.40          | ((k5_relat_1 @ X17 @ (k6_partfun1 @ X18)) = (X17))
% 1.20/1.40          | ~ (v1_relat_1 @ X17))),
% 1.20/1.40      inference('demod', [status(thm)], ['17', '18'])).
% 1.20/1.40  thf('20', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (~ (v1_relat_1 @ X0)
% 1.20/1.40          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) = (X0)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['16', '19'])).
% 1.20/1.40  thf('21', plain,
% 1.20/1.40      ((((k5_relat_1 @ sk_D @ (k6_partfun1 @ sk_A)) = (sk_D))
% 1.20/1.40        | ~ (v1_relat_1 @ sk_D))),
% 1.20/1.40      inference('sup+', [status(thm)], ['14', '20'])).
% 1.20/1.40  thf('22', plain,
% 1.20/1.40      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf(cc1_relset_1, axiom,
% 1.20/1.40    (![A:$i,B:$i,C:$i]:
% 1.20/1.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.20/1.40       ( v1_relat_1 @ C ) ))).
% 1.20/1.40  thf('23', plain,
% 1.20/1.40      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.20/1.40         ((v1_relat_1 @ X29)
% 1.20/1.40          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 1.20/1.40      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.20/1.40  thf('24', plain, ((v1_relat_1 @ sk_D)),
% 1.20/1.40      inference('sup-', [status(thm)], ['22', '23'])).
% 1.20/1.40  thf('25', plain, (((k5_relat_1 @ sk_D @ (k6_partfun1 @ sk_A)) = (sk_D))),
% 1.20/1.40      inference('demod', [status(thm)], ['21', '24'])).
% 1.20/1.40  thf(t182_relat_1, axiom,
% 1.20/1.40    (![A:$i]:
% 1.20/1.40     ( ( v1_relat_1 @ A ) =>
% 1.20/1.40       ( ![B:$i]:
% 1.20/1.40         ( ( v1_relat_1 @ B ) =>
% 1.20/1.40           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.20/1.40             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 1.20/1.40  thf('26', plain,
% 1.20/1.40      (![X7 : $i, X8 : $i]:
% 1.20/1.40         (~ (v1_relat_1 @ X7)
% 1.20/1.40          | ((k1_relat_1 @ (k5_relat_1 @ X8 @ X7))
% 1.20/1.40              = (k10_relat_1 @ X8 @ (k1_relat_1 @ X7)))
% 1.20/1.40          | ~ (v1_relat_1 @ X8))),
% 1.20/1.40      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.20/1.40  thf(t78_relat_1, axiom,
% 1.20/1.40    (![A:$i]:
% 1.20/1.40     ( ( v1_relat_1 @ A ) =>
% 1.20/1.40       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 1.20/1.40  thf('27', plain,
% 1.20/1.40      (![X16 : $i]:
% 1.20/1.40         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X16)) @ X16) = (X16))
% 1.20/1.40          | ~ (v1_relat_1 @ X16))),
% 1.20/1.40      inference('cnf', [status(esa)], [t78_relat_1])).
% 1.20/1.40  thf('28', plain, (![X55 : $i]: ((k6_partfun1 @ X55) = (k6_relat_1 @ X55))),
% 1.20/1.40      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.20/1.40  thf('29', plain,
% 1.20/1.40      (![X16 : $i]:
% 1.20/1.40         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X16)) @ X16) = (X16))
% 1.20/1.40          | ~ (v1_relat_1 @ X16))),
% 1.20/1.40      inference('demod', [status(thm)], ['27', '28'])).
% 1.20/1.40  thf('30', plain,
% 1.20/1.40      (![X0 : $i, X1 : $i]:
% 1.20/1.40         (((k5_relat_1 @ 
% 1.20/1.40            (k6_partfun1 @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0))) @ 
% 1.20/1.40            (k5_relat_1 @ X1 @ X0)) = (k5_relat_1 @ X1 @ X0))
% 1.20/1.40          | ~ (v1_relat_1 @ X1)
% 1.20/1.40          | ~ (v1_relat_1 @ X0)
% 1.20/1.40          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 1.20/1.40      inference('sup+', [status(thm)], ['26', '29'])).
% 1.20/1.40  thf('31', plain,
% 1.20/1.40      ((~ (v1_relat_1 @ sk_D)
% 1.20/1.40        | ~ (v1_relat_1 @ (k6_partfun1 @ sk_A))
% 1.20/1.40        | ~ (v1_relat_1 @ sk_D)
% 1.20/1.40        | ((k5_relat_1 @ 
% 1.20/1.40            (k6_partfun1 @ 
% 1.20/1.40             (k10_relat_1 @ sk_D @ (k1_relat_1 @ (k6_partfun1 @ sk_A)))) @ 
% 1.20/1.40            (k5_relat_1 @ sk_D @ (k6_partfun1 @ sk_A)))
% 1.20/1.40            = (k5_relat_1 @ sk_D @ (k6_partfun1 @ sk_A))))),
% 1.20/1.40      inference('sup-', [status(thm)], ['25', '30'])).
% 1.20/1.40  thf('32', plain, ((v1_relat_1 @ sk_D)),
% 1.20/1.40      inference('sup-', [status(thm)], ['22', '23'])).
% 1.20/1.40  thf(fc4_funct_1, axiom,
% 1.20/1.40    (![A:$i]:
% 1.20/1.40     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.20/1.40       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.20/1.40  thf('33', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 1.20/1.40      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.20/1.40  thf('34', plain, (![X55 : $i]: ((k6_partfun1 @ X55) = (k6_relat_1 @ X55))),
% 1.20/1.40      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.20/1.40  thf('35', plain, (![X20 : $i]: (v1_relat_1 @ (k6_partfun1 @ X20))),
% 1.20/1.40      inference('demod', [status(thm)], ['33', '34'])).
% 1.20/1.40  thf('36', plain, ((v1_relat_1 @ sk_D)),
% 1.20/1.40      inference('sup-', [status(thm)], ['22', '23'])).
% 1.20/1.40  thf(t71_relat_1, axiom,
% 1.20/1.40    (![A:$i]:
% 1.20/1.40     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.20/1.40       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.20/1.40  thf('37', plain, (![X14 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X14)) = (X14))),
% 1.20/1.40      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.20/1.40  thf('38', plain, (![X55 : $i]: ((k6_partfun1 @ X55) = (k6_relat_1 @ X55))),
% 1.20/1.40      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.20/1.40  thf('39', plain, (![X14 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X14)) = (X14))),
% 1.20/1.40      inference('demod', [status(thm)], ['37', '38'])).
% 1.20/1.40  thf('40', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.20/1.40      inference('demod', [status(thm)], ['7', '10', '11', '12', '13'])).
% 1.20/1.40  thf('41', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (~ (v1_relat_1 @ X0)
% 1.20/1.40          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) = (X0)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['16', '19'])).
% 1.20/1.40  thf('42', plain,
% 1.20/1.40      (![X7 : $i, X8 : $i]:
% 1.20/1.40         (~ (v1_relat_1 @ X7)
% 1.20/1.40          | ((k1_relat_1 @ (k5_relat_1 @ X8 @ X7))
% 1.20/1.40              = (k10_relat_1 @ X8 @ (k1_relat_1 @ X7)))
% 1.20/1.40          | ~ (v1_relat_1 @ X8))),
% 1.20/1.40      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.20/1.40  thf('43', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (((k1_relat_1 @ X0)
% 1.20/1.40            = (k10_relat_1 @ X0 @ 
% 1.20/1.40               (k1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)))))
% 1.20/1.40          | ~ (v1_relat_1 @ X0)
% 1.20/1.40          | ~ (v1_relat_1 @ X0)
% 1.20/1.40          | ~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0))))),
% 1.20/1.40      inference('sup+', [status(thm)], ['41', '42'])).
% 1.20/1.40  thf('44', plain, (![X14 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X14)) = (X14))),
% 1.20/1.40      inference('demod', [status(thm)], ['37', '38'])).
% 1.20/1.40  thf('45', plain, (![X20 : $i]: (v1_relat_1 @ (k6_partfun1 @ X20))),
% 1.20/1.40      inference('demod', [status(thm)], ['33', '34'])).
% 1.20/1.40  thf('46', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 1.20/1.40          | ~ (v1_relat_1 @ X0)
% 1.20/1.40          | ~ (v1_relat_1 @ X0))),
% 1.20/1.40      inference('demod', [status(thm)], ['43', '44', '45'])).
% 1.20/1.40  thf('47', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (~ (v1_relat_1 @ X0)
% 1.20/1.40          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 1.20/1.40      inference('simplify', [status(thm)], ['46'])).
% 1.20/1.40  thf('48', plain,
% 1.20/1.40      ((((k1_relat_1 @ sk_D) = (k10_relat_1 @ sk_D @ sk_A))
% 1.20/1.40        | ~ (v1_relat_1 @ sk_D))),
% 1.20/1.40      inference('sup+', [status(thm)], ['40', '47'])).
% 1.20/1.40  thf('49', plain, ((v1_relat_1 @ sk_D)),
% 1.20/1.40      inference('sup-', [status(thm)], ['22', '23'])).
% 1.20/1.40  thf('50', plain, (((k1_relat_1 @ sk_D) = (k10_relat_1 @ sk_D @ sk_A))),
% 1.20/1.40      inference('demod', [status(thm)], ['48', '49'])).
% 1.20/1.40  thf('51', plain, (((k5_relat_1 @ sk_D @ (k6_partfun1 @ sk_A)) = (sk_D))),
% 1.20/1.40      inference('demod', [status(thm)], ['21', '24'])).
% 1.20/1.40  thf('52', plain, (((k5_relat_1 @ sk_D @ (k6_partfun1 @ sk_A)) = (sk_D))),
% 1.20/1.40      inference('demod', [status(thm)], ['21', '24'])).
% 1.20/1.40  thf('53', plain,
% 1.20/1.40      (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ sk_D) = (sk_D))),
% 1.20/1.40      inference('demod', [status(thm)],
% 1.20/1.40                ['31', '32', '35', '36', '39', '50', '51', '52'])).
% 1.20/1.40  thf('54', plain,
% 1.20/1.40      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf(cc2_relset_1, axiom,
% 1.20/1.40    (![A:$i,B:$i,C:$i]:
% 1.20/1.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.20/1.40       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.20/1.40  thf('55', plain,
% 1.20/1.40      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.20/1.40         ((v4_relat_1 @ X32 @ X33)
% 1.20/1.40          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 1.20/1.40      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.20/1.40  thf('56', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 1.20/1.40      inference('sup-', [status(thm)], ['54', '55'])).
% 1.20/1.40  thf(d18_relat_1, axiom,
% 1.20/1.40    (![A:$i,B:$i]:
% 1.20/1.40     ( ( v1_relat_1 @ B ) =>
% 1.20/1.40       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.20/1.40  thf('57', plain,
% 1.20/1.40      (![X3 : $i, X4 : $i]:
% 1.20/1.40         (~ (v4_relat_1 @ X3 @ X4)
% 1.20/1.40          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.20/1.40          | ~ (v1_relat_1 @ X3))),
% 1.20/1.40      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.20/1.40  thf('58', plain,
% 1.20/1.40      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B))),
% 1.20/1.40      inference('sup-', [status(thm)], ['56', '57'])).
% 1.20/1.40  thf('59', plain, ((v1_relat_1 @ sk_D)),
% 1.20/1.40      inference('sup-', [status(thm)], ['22', '23'])).
% 1.20/1.40  thf('60', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 1.20/1.40      inference('demod', [status(thm)], ['58', '59'])).
% 1.20/1.40  thf('61', plain,
% 1.20/1.40      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('62', plain,
% 1.20/1.40      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.20/1.40         (((k2_relset_1 @ X36 @ X37 @ X35) = (k2_relat_1 @ X35))
% 1.20/1.40          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 1.20/1.40      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.20/1.40  thf('63', plain,
% 1.20/1.40      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.20/1.40      inference('sup-', [status(thm)], ['61', '62'])).
% 1.20/1.40  thf('64', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('65', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.20/1.40      inference('sup+', [status(thm)], ['63', '64'])).
% 1.20/1.40  thf(t147_funct_1, axiom,
% 1.20/1.40    (![A:$i,B:$i]:
% 1.20/1.40     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.20/1.40       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 1.20/1.40         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 1.20/1.40  thf('66', plain,
% 1.20/1.40      (![X22 : $i, X23 : $i]:
% 1.20/1.40         (~ (r1_tarski @ X22 @ (k2_relat_1 @ X23))
% 1.20/1.40          | ((k9_relat_1 @ X23 @ (k10_relat_1 @ X23 @ X22)) = (X22))
% 1.20/1.40          | ~ (v1_funct_1 @ X23)
% 1.20/1.40          | ~ (v1_relat_1 @ X23))),
% 1.20/1.40      inference('cnf', [status(esa)], [t147_funct_1])).
% 1.20/1.40  thf('67', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (~ (r1_tarski @ X0 @ sk_B)
% 1.20/1.40          | ~ (v1_relat_1 @ sk_C)
% 1.20/1.40          | ~ (v1_funct_1 @ sk_C)
% 1.20/1.40          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['65', '66'])).
% 1.20/1.40  thf('68', plain,
% 1.20/1.40      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('69', plain,
% 1.20/1.40      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.20/1.40         ((v1_relat_1 @ X29)
% 1.20/1.40          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 1.20/1.40      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.20/1.40  thf('70', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.40      inference('sup-', [status(thm)], ['68', '69'])).
% 1.20/1.40  thf('71', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('72', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (~ (r1_tarski @ X0 @ sk_B)
% 1.20/1.40          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 1.20/1.40      inference('demod', [status(thm)], ['67', '70', '71'])).
% 1.20/1.40  thf('73', plain,
% 1.20/1.40      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 1.20/1.40         = (k1_relat_1 @ sk_D))),
% 1.20/1.40      inference('sup-', [status(thm)], ['60', '72'])).
% 1.20/1.40  thf('74', plain,
% 1.20/1.40      (![X7 : $i, X8 : $i]:
% 1.20/1.40         (~ (v1_relat_1 @ X7)
% 1.20/1.40          | ((k1_relat_1 @ (k5_relat_1 @ X8 @ X7))
% 1.20/1.40              = (k10_relat_1 @ X8 @ (k1_relat_1 @ X7)))
% 1.20/1.40          | ~ (v1_relat_1 @ X8))),
% 1.20/1.40      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.20/1.40  thf('75', plain,
% 1.20/1.40      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('76', plain,
% 1.20/1.40      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf(dt_k1_partfun1, axiom,
% 1.20/1.40    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.20/1.40     ( ( ( v1_funct_1 @ E ) & 
% 1.20/1.40         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.20/1.40         ( v1_funct_1 @ F ) & 
% 1.20/1.40         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.20/1.40       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.20/1.40         ( m1_subset_1 @
% 1.20/1.40           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.20/1.40           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.20/1.40  thf('77', plain,
% 1.20/1.40      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 1.20/1.40         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 1.20/1.40          | ~ (v1_funct_1 @ X43)
% 1.20/1.40          | ~ (v1_funct_1 @ X46)
% 1.20/1.40          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 1.20/1.40          | (m1_subset_1 @ (k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46) @ 
% 1.20/1.40             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X48))))),
% 1.20/1.40      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.20/1.40  thf('78', plain,
% 1.20/1.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.40         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.20/1.40           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.20/1.40          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.20/1.40          | ~ (v1_funct_1 @ X1)
% 1.20/1.40          | ~ (v1_funct_1 @ sk_C))),
% 1.20/1.40      inference('sup-', [status(thm)], ['76', '77'])).
% 1.20/1.40  thf('79', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('80', plain,
% 1.20/1.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.40         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.20/1.40           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.20/1.40          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.20/1.40          | ~ (v1_funct_1 @ X1))),
% 1.20/1.40      inference('demod', [status(thm)], ['78', '79'])).
% 1.20/1.40  thf('81', plain,
% 1.20/1.40      ((~ (v1_funct_1 @ sk_D)
% 1.20/1.40        | (m1_subset_1 @ 
% 1.20/1.40           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.20/1.40           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.20/1.40      inference('sup-', [status(thm)], ['75', '80'])).
% 1.20/1.40  thf('82', plain, ((v1_funct_1 @ sk_D)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('83', plain,
% 1.20/1.40      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('84', plain,
% 1.20/1.40      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf(redefinition_k1_partfun1, axiom,
% 1.20/1.40    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.20/1.40     ( ( ( v1_funct_1 @ E ) & 
% 1.20/1.40         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.20/1.40         ( v1_funct_1 @ F ) & 
% 1.20/1.40         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.20/1.40       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.20/1.40  thf('85', plain,
% 1.20/1.40      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 1.20/1.40         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 1.20/1.40          | ~ (v1_funct_1 @ X49)
% 1.20/1.40          | ~ (v1_funct_1 @ X52)
% 1.20/1.40          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X54)))
% 1.20/1.40          | ((k1_partfun1 @ X50 @ X51 @ X53 @ X54 @ X49 @ X52)
% 1.20/1.40              = (k5_relat_1 @ X49 @ X52)))),
% 1.20/1.40      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.20/1.40  thf('86', plain,
% 1.20/1.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.40         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.20/1.40            = (k5_relat_1 @ sk_C @ X0))
% 1.20/1.40          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.20/1.40          | ~ (v1_funct_1 @ X0)
% 1.20/1.40          | ~ (v1_funct_1 @ sk_C))),
% 1.20/1.40      inference('sup-', [status(thm)], ['84', '85'])).
% 1.20/1.40  thf('87', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('88', plain,
% 1.20/1.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.40         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.20/1.40            = (k5_relat_1 @ sk_C @ X0))
% 1.20/1.40          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.20/1.40          | ~ (v1_funct_1 @ X0))),
% 1.20/1.40      inference('demod', [status(thm)], ['86', '87'])).
% 1.20/1.40  thf('89', plain,
% 1.20/1.40      ((~ (v1_funct_1 @ sk_D)
% 1.20/1.40        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.20/1.40            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['83', '88'])).
% 1.20/1.40  thf('90', plain, ((v1_funct_1 @ sk_D)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('91', plain,
% 1.20/1.40      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.20/1.40         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.20/1.40      inference('demod', [status(thm)], ['89', '90'])).
% 1.20/1.40  thf('92', plain,
% 1.20/1.40      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.20/1.40        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.20/1.40      inference('demod', [status(thm)], ['81', '82', '91'])).
% 1.20/1.40  thf('93', plain,
% 1.20/1.40      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.20/1.40         ((v4_relat_1 @ X32 @ X33)
% 1.20/1.40          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 1.20/1.40      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.20/1.40  thf('94', plain, ((v4_relat_1 @ (k5_relat_1 @ sk_C @ sk_D) @ sk_A)),
% 1.20/1.40      inference('sup-', [status(thm)], ['92', '93'])).
% 1.20/1.40  thf('95', plain,
% 1.20/1.40      (![X3 : $i, X4 : $i]:
% 1.20/1.40         (~ (v4_relat_1 @ X3 @ X4)
% 1.20/1.40          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.20/1.40          | ~ (v1_relat_1 @ X3))),
% 1.20/1.40      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.20/1.40  thf('96', plain,
% 1.20/1.40      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 1.20/1.40        | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ sk_A))),
% 1.20/1.40      inference('sup-', [status(thm)], ['94', '95'])).
% 1.20/1.40  thf('97', plain,
% 1.20/1.40      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.20/1.40        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.20/1.40      inference('demod', [status(thm)], ['81', '82', '91'])).
% 1.20/1.40  thf('98', plain,
% 1.20/1.40      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.20/1.40         ((v1_relat_1 @ X29)
% 1.20/1.40          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 1.20/1.40      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.20/1.40  thf('99', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))),
% 1.20/1.40      inference('sup-', [status(thm)], ['97', '98'])).
% 1.20/1.40  thf('100', plain,
% 1.20/1.40      ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ sk_A)),
% 1.20/1.40      inference('demod', [status(thm)], ['96', '99'])).
% 1.20/1.40  thf('101', plain,
% 1.20/1.40      (((r1_tarski @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)) @ sk_A)
% 1.20/1.40        | ~ (v1_relat_1 @ sk_C)
% 1.20/1.40        | ~ (v1_relat_1 @ sk_D))),
% 1.20/1.40      inference('sup+', [status(thm)], ['74', '100'])).
% 1.20/1.40  thf('102', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.40      inference('sup-', [status(thm)], ['68', '69'])).
% 1.20/1.40  thf('103', plain, ((v1_relat_1 @ sk_D)),
% 1.20/1.40      inference('sup-', [status(thm)], ['22', '23'])).
% 1.20/1.40  thf('104', plain,
% 1.20/1.40      ((r1_tarski @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)) @ sk_A)),
% 1.20/1.40      inference('demod', [status(thm)], ['101', '102', '103'])).
% 1.20/1.40  thf('105', plain,
% 1.20/1.40      (![X14 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X14)) = (X14))),
% 1.20/1.40      inference('demod', [status(thm)], ['37', '38'])).
% 1.20/1.40  thf('106', plain,
% 1.20/1.40      (![X3 : $i, X4 : $i]:
% 1.20/1.40         (~ (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.20/1.40          | (v4_relat_1 @ X3 @ X4)
% 1.20/1.40          | ~ (v1_relat_1 @ X3))),
% 1.20/1.40      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.20/1.40  thf('107', plain,
% 1.20/1.40      (![X0 : $i, X1 : $i]:
% 1.20/1.40         (~ (r1_tarski @ X0 @ X1)
% 1.20/1.40          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 1.20/1.40          | (v4_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 1.20/1.40      inference('sup-', [status(thm)], ['105', '106'])).
% 1.20/1.40  thf('108', plain, (![X20 : $i]: (v1_relat_1 @ (k6_partfun1 @ X20))),
% 1.20/1.40      inference('demod', [status(thm)], ['33', '34'])).
% 1.20/1.40  thf('109', plain,
% 1.20/1.40      (![X0 : $i, X1 : $i]:
% 1.20/1.40         (~ (r1_tarski @ X0 @ X1) | (v4_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 1.20/1.40      inference('demod', [status(thm)], ['107', '108'])).
% 1.20/1.40  thf('110', plain,
% 1.20/1.40      ((v4_relat_1 @ 
% 1.20/1.40        (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))) @ sk_A)),
% 1.20/1.40      inference('sup-', [status(thm)], ['104', '109'])).
% 1.20/1.40  thf(t209_relat_1, axiom,
% 1.20/1.40    (![A:$i,B:$i]:
% 1.20/1.40     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.20/1.40       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 1.20/1.40  thf('111', plain,
% 1.20/1.40      (![X9 : $i, X10 : $i]:
% 1.20/1.40         (((X9) = (k7_relat_1 @ X9 @ X10))
% 1.20/1.40          | ~ (v4_relat_1 @ X9 @ X10)
% 1.20/1.40          | ~ (v1_relat_1 @ X9))),
% 1.20/1.40      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.20/1.40  thf('112', plain,
% 1.20/1.40      ((~ (v1_relat_1 @ 
% 1.20/1.40           (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))))
% 1.20/1.40        | ((k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 1.20/1.40            = (k7_relat_1 @ 
% 1.20/1.40               (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))) @ 
% 1.20/1.40               sk_A)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['110', '111'])).
% 1.20/1.40  thf('113', plain, (![X20 : $i]: (v1_relat_1 @ (k6_partfun1 @ X20))),
% 1.20/1.40      inference('demod', [status(thm)], ['33', '34'])).
% 1.20/1.40  thf('114', plain,
% 1.20/1.40      (((k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 1.20/1.40         = (k7_relat_1 @ 
% 1.20/1.40            (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))) @ sk_A))),
% 1.20/1.40      inference('demod', [status(thm)], ['112', '113'])).
% 1.20/1.40  thf(t148_relat_1, axiom,
% 1.20/1.40    (![A:$i,B:$i]:
% 1.20/1.40     ( ( v1_relat_1 @ B ) =>
% 1.20/1.40       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 1.20/1.40  thf('115', plain,
% 1.20/1.40      (![X5 : $i, X6 : $i]:
% 1.20/1.40         (((k2_relat_1 @ (k7_relat_1 @ X5 @ X6)) = (k9_relat_1 @ X5 @ X6))
% 1.20/1.40          | ~ (v1_relat_1 @ X5))),
% 1.20/1.40      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.20/1.40  thf('116', plain,
% 1.20/1.40      ((((k2_relat_1 @ 
% 1.20/1.40          (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))))
% 1.20/1.40          = (k9_relat_1 @ 
% 1.20/1.40             (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))) @ sk_A))
% 1.20/1.40        | ~ (v1_relat_1 @ 
% 1.20/1.40             (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))))),
% 1.20/1.40      inference('sup+', [status(thm)], ['114', '115'])).
% 1.20/1.40  thf('117', plain, (![X15 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X15)) = (X15))),
% 1.20/1.40      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.20/1.40  thf('118', plain, (![X55 : $i]: ((k6_partfun1 @ X55) = (k6_relat_1 @ X55))),
% 1.20/1.40      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.20/1.40  thf('119', plain,
% 1.20/1.40      (![X15 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X15)) = (X15))),
% 1.20/1.40      inference('demod', [status(thm)], ['117', '118'])).
% 1.20/1.40  thf('120', plain,
% 1.20/1.40      (![X7 : $i, X8 : $i]:
% 1.20/1.40         (~ (v1_relat_1 @ X7)
% 1.20/1.40          | ((k1_relat_1 @ (k5_relat_1 @ X8 @ X7))
% 1.20/1.40              = (k10_relat_1 @ X8 @ (k1_relat_1 @ X7)))
% 1.20/1.40          | ~ (v1_relat_1 @ X8))),
% 1.20/1.40      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.20/1.40  thf('121', plain,
% 1.20/1.40      ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ sk_A)),
% 1.20/1.40      inference('demod', [status(thm)], ['96', '99'])).
% 1.20/1.40  thf('122', plain,
% 1.20/1.40      (![X0 : $i, X1 : $i]:
% 1.20/1.40         (~ (r1_tarski @ X0 @ X1) | (v4_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 1.20/1.40      inference('demod', [status(thm)], ['107', '108'])).
% 1.20/1.40  thf('123', plain,
% 1.20/1.40      ((v4_relat_1 @ 
% 1.20/1.40        (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))) @ sk_A)),
% 1.20/1.40      inference('sup-', [status(thm)], ['121', '122'])).
% 1.20/1.40  thf('124', plain,
% 1.20/1.40      (![X9 : $i, X10 : $i]:
% 1.20/1.40         (((X9) = (k7_relat_1 @ X9 @ X10))
% 1.20/1.40          | ~ (v4_relat_1 @ X9 @ X10)
% 1.20/1.40          | ~ (v1_relat_1 @ X9))),
% 1.20/1.40      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.20/1.40  thf('125', plain,
% 1.20/1.40      ((~ (v1_relat_1 @ 
% 1.20/1.40           (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))))
% 1.20/1.40        | ((k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 1.20/1.40            = (k7_relat_1 @ 
% 1.20/1.40               (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))) @ sk_A)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['123', '124'])).
% 1.20/1.40  thf('126', plain, (![X20 : $i]: (v1_relat_1 @ (k6_partfun1 @ X20))),
% 1.20/1.40      inference('demod', [status(thm)], ['33', '34'])).
% 1.20/1.40  thf('127', plain,
% 1.20/1.40      (((k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 1.20/1.40         = (k7_relat_1 @ 
% 1.20/1.40            (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))) @ sk_A))),
% 1.20/1.40      inference('demod', [status(thm)], ['125', '126'])).
% 1.20/1.40  thf('128', plain,
% 1.20/1.40      (![X5 : $i, X6 : $i]:
% 1.20/1.40         (((k2_relat_1 @ (k7_relat_1 @ X5 @ X6)) = (k9_relat_1 @ X5 @ X6))
% 1.20/1.40          | ~ (v1_relat_1 @ X5))),
% 1.20/1.40      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.20/1.40  thf('129', plain,
% 1.20/1.40      ((((k2_relat_1 @ 
% 1.20/1.40          (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))))
% 1.20/1.40          = (k9_relat_1 @ 
% 1.20/1.40             (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))) @ sk_A))
% 1.20/1.40        | ~ (v1_relat_1 @ 
% 1.20/1.40             (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))))),
% 1.20/1.40      inference('sup+', [status(thm)], ['127', '128'])).
% 1.20/1.40  thf('130', plain,
% 1.20/1.40      (![X15 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X15)) = (X15))),
% 1.20/1.40      inference('demod', [status(thm)], ['117', '118'])).
% 1.20/1.40  thf('131', plain, (![X20 : $i]: (v1_relat_1 @ (k6_partfun1 @ X20))),
% 1.20/1.40      inference('demod', [status(thm)], ['33', '34'])).
% 1.20/1.40  thf('132', plain,
% 1.20/1.40      (((k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 1.20/1.40         = (k9_relat_1 @ 
% 1.20/1.40            (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))) @ sk_A))),
% 1.20/1.40      inference('demod', [status(thm)], ['129', '130', '131'])).
% 1.20/1.40  thf('133', plain,
% 1.20/1.40      ((((k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 1.20/1.40          = (k9_relat_1 @ 
% 1.20/1.40             (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))) @ sk_A))
% 1.20/1.40        | ~ (v1_relat_1 @ sk_C)
% 1.20/1.40        | ~ (v1_relat_1 @ sk_D))),
% 1.20/1.40      inference('sup+', [status(thm)], ['120', '132'])).
% 1.20/1.40  thf('134', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.40      inference('sup-', [status(thm)], ['68', '69'])).
% 1.20/1.40  thf('135', plain, ((v1_relat_1 @ sk_D)),
% 1.20/1.40      inference('sup-', [status(thm)], ['22', '23'])).
% 1.20/1.40  thf('136', plain,
% 1.20/1.40      (((k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 1.20/1.40         = (k9_relat_1 @ 
% 1.20/1.40            (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))) @ sk_A))),
% 1.20/1.40      inference('demod', [status(thm)], ['133', '134', '135'])).
% 1.20/1.40  thf('137', plain, (![X20 : $i]: (v1_relat_1 @ (k6_partfun1 @ X20))),
% 1.20/1.40      inference('demod', [status(thm)], ['33', '34'])).
% 1.20/1.40  thf('138', plain,
% 1.20/1.40      (((k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))
% 1.20/1.40         = (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))),
% 1.20/1.40      inference('demod', [status(thm)], ['116', '119', '136', '137'])).
% 1.20/1.40  thf('139', plain,
% 1.20/1.40      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.20/1.40        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.20/1.40        (k6_partfun1 @ sk_A))),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('140', plain,
% 1.20/1.40      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.20/1.40         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.20/1.40      inference('demod', [status(thm)], ['89', '90'])).
% 1.20/1.40  thf('141', plain,
% 1.20/1.40      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.20/1.40        (k6_partfun1 @ sk_A))),
% 1.20/1.40      inference('demod', [status(thm)], ['139', '140'])).
% 1.20/1.40  thf('142', plain,
% 1.20/1.40      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.20/1.40        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.20/1.40      inference('demod', [status(thm)], ['81', '82', '91'])).
% 1.20/1.40  thf(redefinition_r2_relset_1, axiom,
% 1.20/1.40    (![A:$i,B:$i,C:$i,D:$i]:
% 1.20/1.40     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.20/1.40         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.20/1.40       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.20/1.40  thf('143', plain,
% 1.20/1.40      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 1.20/1.40         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 1.20/1.40          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 1.20/1.40          | ((X38) = (X41))
% 1.20/1.40          | ~ (r2_relset_1 @ X39 @ X40 @ X38 @ X41))),
% 1.20/1.40      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.20/1.40  thf('144', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 1.20/1.40          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 1.20/1.40          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.20/1.40      inference('sup-', [status(thm)], ['142', '143'])).
% 1.20/1.40  thf('145', plain,
% 1.20/1.40      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.20/1.40           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.20/1.40        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['141', '144'])).
% 1.20/1.40  thf(t29_relset_1, axiom,
% 1.20/1.40    (![A:$i]:
% 1.20/1.40     ( m1_subset_1 @
% 1.20/1.40       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.20/1.40  thf('146', plain,
% 1.20/1.40      (![X42 : $i]:
% 1.20/1.40         (m1_subset_1 @ (k6_relat_1 @ X42) @ 
% 1.20/1.40          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X42)))),
% 1.20/1.40      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.20/1.40  thf('147', plain, (![X55 : $i]: ((k6_partfun1 @ X55) = (k6_relat_1 @ X55))),
% 1.20/1.40      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.20/1.40  thf('148', plain,
% 1.20/1.40      (![X42 : $i]:
% 1.20/1.40         (m1_subset_1 @ (k6_partfun1 @ X42) @ 
% 1.20/1.40          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X42)))),
% 1.20/1.40      inference('demod', [status(thm)], ['146', '147'])).
% 1.20/1.40  thf('149', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.20/1.40      inference('demod', [status(thm)], ['145', '148'])).
% 1.20/1.40  thf('150', plain,
% 1.20/1.40      (![X14 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X14)) = (X14))),
% 1.20/1.40      inference('demod', [status(thm)], ['37', '38'])).
% 1.20/1.40  thf('151', plain, (((k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)) = (sk_A))),
% 1.20/1.40      inference('demod', [status(thm)], ['138', '149', '150'])).
% 1.20/1.40  thf('152', plain, (((k9_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ sk_D))),
% 1.20/1.40      inference('demod', [status(thm)], ['73', '151'])).
% 1.20/1.40  thf('153', plain,
% 1.20/1.40      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('154', plain,
% 1.20/1.40      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.20/1.40         ((v4_relat_1 @ X32 @ X33)
% 1.20/1.40          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 1.20/1.40      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.20/1.40  thf('155', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 1.20/1.40      inference('sup-', [status(thm)], ['153', '154'])).
% 1.20/1.40  thf('156', plain,
% 1.20/1.40      (![X9 : $i, X10 : $i]:
% 1.20/1.40         (((X9) = (k7_relat_1 @ X9 @ X10))
% 1.20/1.40          | ~ (v4_relat_1 @ X9 @ X10)
% 1.20/1.40          | ~ (v1_relat_1 @ X9))),
% 1.20/1.40      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.20/1.40  thf('157', plain,
% 1.20/1.40      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['155', '156'])).
% 1.20/1.40  thf('158', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.40      inference('sup-', [status(thm)], ['68', '69'])).
% 1.20/1.40  thf('159', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 1.20/1.40      inference('demod', [status(thm)], ['157', '158'])).
% 1.20/1.40  thf('160', plain,
% 1.20/1.40      (![X5 : $i, X6 : $i]:
% 1.20/1.40         (((k2_relat_1 @ (k7_relat_1 @ X5 @ X6)) = (k9_relat_1 @ X5 @ X6))
% 1.20/1.40          | ~ (v1_relat_1 @ X5))),
% 1.20/1.40      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.20/1.40  thf('161', plain,
% 1.20/1.40      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))
% 1.20/1.40        | ~ (v1_relat_1 @ sk_C))),
% 1.20/1.40      inference('sup+', [status(thm)], ['159', '160'])).
% 1.20/1.40  thf('162', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.40      inference('sup-', [status(thm)], ['68', '69'])).
% 1.20/1.40  thf('163', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 1.20/1.40      inference('demod', [status(thm)], ['161', '162'])).
% 1.20/1.40  thf('164', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.20/1.40      inference('sup+', [status(thm)], ['63', '64'])).
% 1.20/1.40  thf('165', plain, (((sk_B) = (k9_relat_1 @ sk_C @ sk_A))),
% 1.20/1.40      inference('demod', [status(thm)], ['163', '164'])).
% 1.20/1.40  thf('166', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.20/1.40      inference('sup+', [status(thm)], ['152', '165'])).
% 1.20/1.40  thf('167', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))),
% 1.20/1.40      inference('demod', [status(thm)], ['53', '166'])).
% 1.20/1.40  thf('168', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.20/1.40      inference('demod', [status(thm)], ['145', '148'])).
% 1.20/1.40  thf(dt_k2_funct_1, axiom,
% 1.20/1.40    (![A:$i]:
% 1.20/1.40     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.20/1.40       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.20/1.40         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.20/1.40  thf('169', plain,
% 1.20/1.40      (![X19 : $i]:
% 1.20/1.40         ((v1_relat_1 @ (k2_funct_1 @ X19))
% 1.20/1.40          | ~ (v1_funct_1 @ X19)
% 1.20/1.40          | ~ (v1_relat_1 @ X19))),
% 1.20/1.40      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.20/1.40  thf('170', plain,
% 1.20/1.40      (![X19 : $i]:
% 1.20/1.40         ((v1_funct_1 @ (k2_funct_1 @ X19))
% 1.20/1.40          | ~ (v1_funct_1 @ X19)
% 1.20/1.40          | ~ (v1_relat_1 @ X19))),
% 1.20/1.40      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.20/1.40  thf('171', plain,
% 1.20/1.40      (![X19 : $i]:
% 1.20/1.40         ((v1_relat_1 @ (k2_funct_1 @ X19))
% 1.20/1.40          | ~ (v1_funct_1 @ X19)
% 1.20/1.40          | ~ (v1_relat_1 @ X19))),
% 1.20/1.40      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.20/1.40  thf(t65_funct_1, axiom,
% 1.20/1.40    (![A:$i]:
% 1.20/1.40     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.20/1.40       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 1.20/1.40  thf('172', plain,
% 1.20/1.40      (![X28 : $i]:
% 1.20/1.40         (~ (v2_funct_1 @ X28)
% 1.20/1.40          | ((k2_funct_1 @ (k2_funct_1 @ X28)) = (X28))
% 1.20/1.40          | ~ (v1_funct_1 @ X28)
% 1.20/1.40          | ~ (v1_relat_1 @ X28))),
% 1.20/1.40      inference('cnf', [status(esa)], [t65_funct_1])).
% 1.20/1.40  thf('173', plain,
% 1.20/1.40      (![X28 : $i]:
% 1.20/1.40         (~ (v2_funct_1 @ X28)
% 1.20/1.40          | ((k2_funct_1 @ (k2_funct_1 @ X28)) = (X28))
% 1.20/1.40          | ~ (v1_funct_1 @ X28)
% 1.20/1.40          | ~ (v1_relat_1 @ X28))),
% 1.20/1.40      inference('cnf', [status(esa)], [t65_funct_1])).
% 1.20/1.40  thf('174', plain,
% 1.20/1.40      (![X28 : $i]:
% 1.20/1.40         (~ (v2_funct_1 @ X28)
% 1.20/1.40          | ((k2_funct_1 @ (k2_funct_1 @ X28)) = (X28))
% 1.20/1.40          | ~ (v1_funct_1 @ X28)
% 1.20/1.40          | ~ (v1_relat_1 @ X28))),
% 1.20/1.40      inference('cnf', [status(esa)], [t65_funct_1])).
% 1.20/1.40  thf('175', plain,
% 1.20/1.40      (![X19 : $i]:
% 1.20/1.40         ((v1_funct_1 @ (k2_funct_1 @ X19))
% 1.20/1.40          | ~ (v1_funct_1 @ X19)
% 1.20/1.40          | ~ (v1_relat_1 @ X19))),
% 1.20/1.40      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.20/1.40  thf('176', plain,
% 1.20/1.40      (![X19 : $i]:
% 1.20/1.40         ((v1_relat_1 @ (k2_funct_1 @ X19))
% 1.20/1.40          | ~ (v1_funct_1 @ X19)
% 1.20/1.40          | ~ (v1_relat_1 @ X19))),
% 1.20/1.40      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.20/1.40  thf(t55_funct_1, axiom,
% 1.20/1.40    (![A:$i]:
% 1.20/1.40     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.20/1.40       ( ( v2_funct_1 @ A ) =>
% 1.20/1.40         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.20/1.40           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.20/1.40  thf('177', plain,
% 1.20/1.40      (![X26 : $i]:
% 1.20/1.40         (~ (v2_funct_1 @ X26)
% 1.20/1.40          | ((k2_relat_1 @ X26) = (k1_relat_1 @ (k2_funct_1 @ X26)))
% 1.20/1.40          | ~ (v1_funct_1 @ X26)
% 1.20/1.40          | ~ (v1_relat_1 @ X26))),
% 1.20/1.40      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.20/1.40  thf('178', plain,
% 1.20/1.40      (![X19 : $i]:
% 1.20/1.40         ((v1_relat_1 @ (k2_funct_1 @ X19))
% 1.20/1.40          | ~ (v1_funct_1 @ X19)
% 1.20/1.40          | ~ (v1_relat_1 @ X19))),
% 1.20/1.40      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.20/1.40  thf('179', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.20/1.40      inference('sup+', [status(thm)], ['63', '64'])).
% 1.20/1.40  thf('180', plain,
% 1.20/1.40      (![X19 : $i]:
% 1.20/1.40         ((v1_relat_1 @ (k2_funct_1 @ X19))
% 1.20/1.40          | ~ (v1_funct_1 @ X19)
% 1.20/1.40          | ~ (v1_relat_1 @ X19))),
% 1.20/1.40      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.20/1.40  thf('181', plain,
% 1.20/1.40      (![X26 : $i]:
% 1.20/1.40         (~ (v2_funct_1 @ X26)
% 1.20/1.40          | ((k2_relat_1 @ X26) = (k1_relat_1 @ (k2_funct_1 @ X26)))
% 1.20/1.40          | ~ (v1_funct_1 @ X26)
% 1.20/1.40          | ~ (v1_relat_1 @ X26))),
% 1.20/1.40      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.20/1.40  thf('182', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.20/1.40      inference('simplify', [status(thm)], ['15'])).
% 1.20/1.40  thf('183', plain,
% 1.20/1.40      (![X3 : $i, X4 : $i]:
% 1.20/1.40         (~ (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.20/1.40          | (v4_relat_1 @ X3 @ X4)
% 1.20/1.40          | ~ (v1_relat_1 @ X3))),
% 1.20/1.40      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.20/1.40  thf('184', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['182', '183'])).
% 1.20/1.40  thf('185', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.20/1.40          | ~ (v1_relat_1 @ X0)
% 1.20/1.40          | ~ (v1_funct_1 @ X0)
% 1.20/1.40          | ~ (v2_funct_1 @ X0)
% 1.20/1.40          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.20/1.40      inference('sup+', [status(thm)], ['181', '184'])).
% 1.20/1.40  thf('186', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (~ (v1_relat_1 @ X0)
% 1.20/1.40          | ~ (v1_funct_1 @ X0)
% 1.20/1.40          | ~ (v2_funct_1 @ X0)
% 1.20/1.40          | ~ (v1_funct_1 @ X0)
% 1.20/1.40          | ~ (v1_relat_1 @ X0)
% 1.20/1.40          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['180', '185'])).
% 1.20/1.40  thf('187', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.20/1.40          | ~ (v2_funct_1 @ X0)
% 1.20/1.40          | ~ (v1_funct_1 @ X0)
% 1.20/1.40          | ~ (v1_relat_1 @ X0))),
% 1.20/1.40      inference('simplify', [status(thm)], ['186'])).
% 1.20/1.40  thf('188', plain,
% 1.20/1.40      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)
% 1.20/1.40        | ~ (v1_relat_1 @ sk_C)
% 1.20/1.40        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.40        | ~ (v2_funct_1 @ sk_C))),
% 1.20/1.40      inference('sup+', [status(thm)], ['179', '187'])).
% 1.20/1.40  thf('189', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.40      inference('sup-', [status(thm)], ['68', '69'])).
% 1.20/1.40  thf('190', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('191', plain, ((v2_funct_1 @ sk_C)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('192', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)),
% 1.20/1.40      inference('demod', [status(thm)], ['188', '189', '190', '191'])).
% 1.20/1.40  thf('193', plain,
% 1.20/1.40      (![X3 : $i, X4 : $i]:
% 1.20/1.40         (~ (v4_relat_1 @ X3 @ X4)
% 1.20/1.40          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.20/1.40          | ~ (v1_relat_1 @ X3))),
% 1.20/1.40      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.20/1.40  thf('194', plain,
% 1.20/1.40      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.20/1.40        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 1.20/1.40      inference('sup-', [status(thm)], ['192', '193'])).
% 1.20/1.40  thf('195', plain,
% 1.20/1.40      ((~ (v1_relat_1 @ sk_C)
% 1.20/1.40        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.40        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 1.20/1.40      inference('sup-', [status(thm)], ['178', '194'])).
% 1.20/1.40  thf('196', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.40      inference('sup-', [status(thm)], ['68', '69'])).
% 1.20/1.40  thf('197', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('198', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B)),
% 1.20/1.40      inference('demod', [status(thm)], ['195', '196', '197'])).
% 1.20/1.40  thf('199', plain,
% 1.20/1.40      (![X0 : $i, X2 : $i]:
% 1.20/1.40         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.20/1.40      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.20/1.40  thf('200', plain,
% 1.20/1.40      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.20/1.40        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.20/1.40      inference('sup-', [status(thm)], ['198', '199'])).
% 1.20/1.40  thf('201', plain,
% 1.20/1.40      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C))
% 1.20/1.40        | ~ (v1_relat_1 @ sk_C)
% 1.20/1.40        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.40        | ~ (v2_funct_1 @ sk_C)
% 1.20/1.40        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.20/1.40      inference('sup-', [status(thm)], ['177', '200'])).
% 1.20/1.40  thf('202', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.20/1.40      inference('sup+', [status(thm)], ['63', '64'])).
% 1.20/1.40  thf('203', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.20/1.40      inference('simplify', [status(thm)], ['15'])).
% 1.20/1.40  thf('204', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.40      inference('sup-', [status(thm)], ['68', '69'])).
% 1.20/1.40  thf('205', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('206', plain, ((v2_funct_1 @ sk_C)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('207', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.20/1.40      inference('demod', [status(thm)],
% 1.20/1.40                ['201', '202', '203', '204', '205', '206'])).
% 1.20/1.40  thf('208', plain,
% 1.20/1.40      (![X26 : $i]:
% 1.20/1.40         (~ (v2_funct_1 @ X26)
% 1.20/1.40          | ((k1_relat_1 @ X26) = (k2_relat_1 @ (k2_funct_1 @ X26)))
% 1.20/1.40          | ~ (v1_funct_1 @ X26)
% 1.20/1.40          | ~ (v1_relat_1 @ X26))),
% 1.20/1.40      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.20/1.40  thf('209', plain,
% 1.20/1.40      (![X19 : $i]:
% 1.20/1.40         ((v1_funct_1 @ (k2_funct_1 @ X19))
% 1.20/1.40          | ~ (v1_funct_1 @ X19)
% 1.20/1.40          | ~ (v1_relat_1 @ X19))),
% 1.20/1.40      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.20/1.40  thf('210', plain,
% 1.20/1.40      (![X19 : $i]:
% 1.20/1.40         ((v1_relat_1 @ (k2_funct_1 @ X19))
% 1.20/1.40          | ~ (v1_funct_1 @ X19)
% 1.20/1.40          | ~ (v1_relat_1 @ X19))),
% 1.20/1.40      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.20/1.40  thf(t61_funct_1, axiom,
% 1.20/1.40    (![A:$i]:
% 1.20/1.40     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.20/1.40       ( ( v2_funct_1 @ A ) =>
% 1.20/1.40         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.20/1.40             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.20/1.40           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.20/1.40             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.20/1.40  thf('211', plain,
% 1.20/1.40      (![X27 : $i]:
% 1.20/1.40         (~ (v2_funct_1 @ X27)
% 1.20/1.40          | ((k5_relat_1 @ (k2_funct_1 @ X27) @ X27)
% 1.20/1.40              = (k6_relat_1 @ (k2_relat_1 @ X27)))
% 1.20/1.40          | ~ (v1_funct_1 @ X27)
% 1.20/1.40          | ~ (v1_relat_1 @ X27))),
% 1.20/1.40      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.20/1.40  thf('212', plain, (![X55 : $i]: ((k6_partfun1 @ X55) = (k6_relat_1 @ X55))),
% 1.20/1.40      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.20/1.40  thf('213', plain,
% 1.20/1.40      (![X27 : $i]:
% 1.20/1.40         (~ (v2_funct_1 @ X27)
% 1.20/1.40          | ((k5_relat_1 @ (k2_funct_1 @ X27) @ X27)
% 1.20/1.40              = (k6_partfun1 @ (k2_relat_1 @ X27)))
% 1.20/1.40          | ~ (v1_funct_1 @ X27)
% 1.20/1.40          | ~ (v1_relat_1 @ X27))),
% 1.20/1.40      inference('demod', [status(thm)], ['211', '212'])).
% 1.20/1.40  thf(t48_funct_1, axiom,
% 1.20/1.40    (![A:$i]:
% 1.20/1.40     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.20/1.40       ( ![B:$i]:
% 1.20/1.40         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.20/1.40           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 1.20/1.40               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 1.20/1.40             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 1.20/1.40  thf('214', plain,
% 1.20/1.40      (![X24 : $i, X25 : $i]:
% 1.20/1.40         (~ (v1_relat_1 @ X24)
% 1.20/1.40          | ~ (v1_funct_1 @ X24)
% 1.20/1.40          | (v2_funct_1 @ X24)
% 1.20/1.40          | ((k2_relat_1 @ X24) != (k1_relat_1 @ X25))
% 1.20/1.40          | ~ (v2_funct_1 @ (k5_relat_1 @ X24 @ X25))
% 1.20/1.40          | ~ (v1_funct_1 @ X25)
% 1.20/1.40          | ~ (v1_relat_1 @ X25))),
% 1.20/1.40      inference('cnf', [status(esa)], [t48_funct_1])).
% 1.20/1.40  thf('215', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (~ (v2_funct_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.20/1.40          | ~ (v1_relat_1 @ X0)
% 1.20/1.40          | ~ (v1_funct_1 @ X0)
% 1.20/1.40          | ~ (v2_funct_1 @ X0)
% 1.20/1.40          | ~ (v1_relat_1 @ X0)
% 1.20/1.40          | ~ (v1_funct_1 @ X0)
% 1.20/1.40          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 1.20/1.40          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.20/1.40          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.20/1.40          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['213', '214'])).
% 1.20/1.40  thf('216', plain, (![X21 : $i]: (v2_funct_1 @ (k6_relat_1 @ X21))),
% 1.20/1.40      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.20/1.40  thf('217', plain, (![X55 : $i]: ((k6_partfun1 @ X55) = (k6_relat_1 @ X55))),
% 1.20/1.40      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.20/1.40  thf('218', plain, (![X21 : $i]: (v2_funct_1 @ (k6_partfun1 @ X21))),
% 1.20/1.40      inference('demod', [status(thm)], ['216', '217'])).
% 1.20/1.40  thf('219', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (~ (v1_relat_1 @ X0)
% 1.20/1.40          | ~ (v1_funct_1 @ X0)
% 1.20/1.40          | ~ (v2_funct_1 @ X0)
% 1.20/1.40          | ~ (v1_relat_1 @ X0)
% 1.20/1.40          | ~ (v1_funct_1 @ X0)
% 1.20/1.40          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 1.20/1.40          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.20/1.40          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.20/1.40          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.20/1.40      inference('demod', [status(thm)], ['215', '218'])).
% 1.20/1.40  thf('220', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.20/1.40          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.20/1.40          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.20/1.40          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 1.20/1.40          | ~ (v2_funct_1 @ X0)
% 1.20/1.40          | ~ (v1_funct_1 @ X0)
% 1.20/1.40          | ~ (v1_relat_1 @ X0))),
% 1.20/1.40      inference('simplify', [status(thm)], ['219'])).
% 1.20/1.40  thf('221', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (~ (v1_relat_1 @ X0)
% 1.20/1.40          | ~ (v1_funct_1 @ X0)
% 1.20/1.40          | ~ (v1_relat_1 @ X0)
% 1.20/1.40          | ~ (v1_funct_1 @ X0)
% 1.20/1.40          | ~ (v2_funct_1 @ X0)
% 1.20/1.40          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 1.20/1.40          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.20/1.40          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['210', '220'])).
% 1.20/1.40  thf('222', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.20/1.40          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.20/1.40          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 1.20/1.40          | ~ (v2_funct_1 @ X0)
% 1.20/1.40          | ~ (v1_funct_1 @ X0)
% 1.20/1.40          | ~ (v1_relat_1 @ X0))),
% 1.20/1.40      inference('simplify', [status(thm)], ['221'])).
% 1.20/1.40  thf('223', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (~ (v1_relat_1 @ X0)
% 1.20/1.40          | ~ (v1_funct_1 @ X0)
% 1.20/1.40          | ~ (v1_relat_1 @ X0)
% 1.20/1.40          | ~ (v1_funct_1 @ X0)
% 1.20/1.40          | ~ (v2_funct_1 @ X0)
% 1.20/1.40          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 1.20/1.40          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['209', '222'])).
% 1.20/1.40  thf('224', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 1.20/1.40          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 1.20/1.40          | ~ (v2_funct_1 @ X0)
% 1.20/1.40          | ~ (v1_funct_1 @ X0)
% 1.20/1.40          | ~ (v1_relat_1 @ X0))),
% 1.20/1.40      inference('simplify', [status(thm)], ['223'])).
% 1.20/1.40  thf('225', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 1.20/1.40          | ~ (v1_relat_1 @ X0)
% 1.20/1.40          | ~ (v1_funct_1 @ X0)
% 1.20/1.40          | ~ (v2_funct_1 @ X0)
% 1.20/1.40          | ~ (v1_relat_1 @ X0)
% 1.20/1.40          | ~ (v1_funct_1 @ X0)
% 1.20/1.40          | ~ (v2_funct_1 @ X0)
% 1.20/1.40          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['208', '224'])).
% 1.20/1.40  thf('226', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 1.20/1.40          | ~ (v2_funct_1 @ X0)
% 1.20/1.40          | ~ (v1_funct_1 @ X0)
% 1.20/1.40          | ~ (v1_relat_1 @ X0))),
% 1.20/1.40      inference('simplify', [status(thm)], ['225'])).
% 1.20/1.40  thf('227', plain,
% 1.20/1.40      (![X19 : $i]:
% 1.20/1.40         ((v1_funct_1 @ (k2_funct_1 @ X19))
% 1.20/1.40          | ~ (v1_funct_1 @ X19)
% 1.20/1.40          | ~ (v1_relat_1 @ X19))),
% 1.20/1.40      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.20/1.40  thf('228', plain,
% 1.20/1.40      (![X19 : $i]:
% 1.20/1.40         ((v1_relat_1 @ (k2_funct_1 @ X19))
% 1.20/1.40          | ~ (v1_funct_1 @ X19)
% 1.20/1.40          | ~ (v1_relat_1 @ X19))),
% 1.20/1.40      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.20/1.40  thf('229', plain,
% 1.20/1.40      (![X28 : $i]:
% 1.20/1.40         (~ (v2_funct_1 @ X28)
% 1.20/1.40          | ((k2_funct_1 @ (k2_funct_1 @ X28)) = (X28))
% 1.20/1.40          | ~ (v1_funct_1 @ X28)
% 1.20/1.40          | ~ (v1_relat_1 @ X28))),
% 1.20/1.40      inference('cnf', [status(esa)], [t65_funct_1])).
% 1.20/1.40  thf('230', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.20/1.40          | ~ (v2_funct_1 @ X0)
% 1.20/1.40          | ~ (v1_funct_1 @ X0)
% 1.20/1.40          | ~ (v1_relat_1 @ X0))),
% 1.20/1.40      inference('simplify', [status(thm)], ['186'])).
% 1.20/1.40  thf('231', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         ((v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.20/1.40          | ~ (v1_relat_1 @ X0)
% 1.20/1.40          | ~ (v1_funct_1 @ X0)
% 1.20/1.40          | ~ (v2_funct_1 @ X0)
% 1.20/1.40          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.20/1.40          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.20/1.40          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 1.20/1.40      inference('sup+', [status(thm)], ['229', '230'])).
% 1.20/1.40  thf('232', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (~ (v1_relat_1 @ X0)
% 1.20/1.40          | ~ (v1_funct_1 @ X0)
% 1.20/1.40          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.20/1.40          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.20/1.40          | ~ (v2_funct_1 @ X0)
% 1.20/1.40          | ~ (v1_funct_1 @ X0)
% 1.20/1.40          | ~ (v1_relat_1 @ X0)
% 1.20/1.40          | (v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 1.20/1.40      inference('sup-', [status(thm)], ['228', '231'])).
% 1.20/1.40  thf('233', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         ((v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.20/1.40          | ~ (v2_funct_1 @ X0)
% 1.20/1.40          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.20/1.40          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.20/1.40          | ~ (v1_funct_1 @ X0)
% 1.20/1.40          | ~ (v1_relat_1 @ X0))),
% 1.20/1.40      inference('simplify', [status(thm)], ['232'])).
% 1.20/1.40  thf('234', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (~ (v1_relat_1 @ X0)
% 1.20/1.40          | ~ (v1_funct_1 @ X0)
% 1.20/1.40          | ~ (v1_relat_1 @ X0)
% 1.20/1.40          | ~ (v1_funct_1 @ X0)
% 1.20/1.40          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.20/1.40          | ~ (v2_funct_1 @ X0)
% 1.20/1.40          | (v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 1.20/1.40      inference('sup-', [status(thm)], ['227', '233'])).
% 1.20/1.40  thf('235', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         ((v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.20/1.40          | ~ (v2_funct_1 @ X0)
% 1.20/1.40          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.20/1.40          | ~ (v1_funct_1 @ X0)
% 1.20/1.40          | ~ (v1_relat_1 @ X0))),
% 1.20/1.40      inference('simplify', [status(thm)], ['234'])).
% 1.20/1.40  thf('236', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (~ (v1_relat_1 @ X0)
% 1.20/1.40          | ~ (v1_funct_1 @ X0)
% 1.20/1.40          | ~ (v2_funct_1 @ X0)
% 1.20/1.40          | ~ (v1_relat_1 @ X0)
% 1.20/1.40          | ~ (v1_funct_1 @ X0)
% 1.20/1.40          | ~ (v2_funct_1 @ X0)
% 1.20/1.40          | (v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 1.20/1.40      inference('sup-', [status(thm)], ['226', '235'])).
% 1.20/1.40  thf('237', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         ((v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.20/1.40          | ~ (v2_funct_1 @ X0)
% 1.20/1.40          | ~ (v1_funct_1 @ X0)
% 1.20/1.40          | ~ (v1_relat_1 @ X0))),
% 1.20/1.40      inference('simplify', [status(thm)], ['236'])).
% 1.20/1.40  thf('238', plain,
% 1.20/1.40      (![X3 : $i, X4 : $i]:
% 1.20/1.40         (~ (v4_relat_1 @ X3 @ X4)
% 1.20/1.40          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.20/1.40          | ~ (v1_relat_1 @ X3))),
% 1.20/1.40      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.20/1.40  thf('239', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (~ (v1_relat_1 @ X0)
% 1.20/1.40          | ~ (v1_funct_1 @ X0)
% 1.20/1.40          | ~ (v2_funct_1 @ X0)
% 1.20/1.40          | ~ (v1_relat_1 @ X0)
% 1.20/1.40          | (r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 1.20/1.40      inference('sup-', [status(thm)], ['237', '238'])).
% 1.20/1.40  thf('240', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         ((r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.20/1.40          | ~ (v2_funct_1 @ X0)
% 1.20/1.40          | ~ (v1_funct_1 @ X0)
% 1.20/1.40          | ~ (v1_relat_1 @ X0))),
% 1.20/1.40      inference('simplify', [status(thm)], ['239'])).
% 1.20/1.40  thf('241', plain,
% 1.20/1.40      (((r1_tarski @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 1.20/1.40        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.20/1.40        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.20/1.40        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.20/1.40      inference('sup+', [status(thm)], ['207', '240'])).
% 1.20/1.40  thf('242', plain,
% 1.20/1.40      (![X19 : $i]:
% 1.20/1.40         ((v1_relat_1 @ (k2_funct_1 @ X19))
% 1.20/1.40          | ~ (v1_funct_1 @ X19)
% 1.20/1.40          | ~ (v1_relat_1 @ X19))),
% 1.20/1.40      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.20/1.40  thf('243', plain,
% 1.20/1.40      (![X19 : $i]:
% 1.20/1.40         ((v1_funct_1 @ (k2_funct_1 @ X19))
% 1.20/1.40          | ~ (v1_funct_1 @ X19)
% 1.20/1.40          | ~ (v1_relat_1 @ X19))),
% 1.20/1.40      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.20/1.40  thf('244', plain,
% 1.20/1.40      (![X19 : $i]:
% 1.20/1.40         ((v1_relat_1 @ (k2_funct_1 @ X19))
% 1.20/1.40          | ~ (v1_funct_1 @ X19)
% 1.20/1.40          | ~ (v1_relat_1 @ X19))),
% 1.20/1.40      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.20/1.40  thf('245', plain,
% 1.20/1.40      (![X27 : $i]:
% 1.20/1.40         (~ (v2_funct_1 @ X27)
% 1.20/1.40          | ((k5_relat_1 @ X27 @ (k2_funct_1 @ X27))
% 1.20/1.40              = (k6_relat_1 @ (k1_relat_1 @ X27)))
% 1.20/1.40          | ~ (v1_funct_1 @ X27)
% 1.20/1.40          | ~ (v1_relat_1 @ X27))),
% 1.20/1.40      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.20/1.40  thf('246', plain, (![X55 : $i]: ((k6_partfun1 @ X55) = (k6_relat_1 @ X55))),
% 1.20/1.40      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.20/1.40  thf('247', plain,
% 1.20/1.40      (![X27 : $i]:
% 1.20/1.40         (~ (v2_funct_1 @ X27)
% 1.20/1.40          | ((k5_relat_1 @ X27 @ (k2_funct_1 @ X27))
% 1.20/1.40              = (k6_partfun1 @ (k1_relat_1 @ X27)))
% 1.20/1.40          | ~ (v1_funct_1 @ X27)
% 1.20/1.40          | ~ (v1_relat_1 @ X27))),
% 1.20/1.40      inference('demod', [status(thm)], ['245', '246'])).
% 1.20/1.40  thf('248', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.20/1.40      inference('sup+', [status(thm)], ['63', '64'])).
% 1.20/1.40  thf('249', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (~ (v1_relat_1 @ X0)
% 1.20/1.40          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) = (X0)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['16', '19'])).
% 1.20/1.40  thf('250', plain,
% 1.20/1.40      ((((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))
% 1.20/1.40        | ~ (v1_relat_1 @ sk_C))),
% 1.20/1.40      inference('sup+', [status(thm)], ['248', '249'])).
% 1.20/1.40  thf('251', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.40      inference('sup-', [status(thm)], ['68', '69'])).
% 1.20/1.40  thf('252', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 1.20/1.40      inference('demod', [status(thm)], ['250', '251'])).
% 1.20/1.40  thf('253', plain,
% 1.20/1.40      (![X16 : $i]:
% 1.20/1.40         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X16)) @ X16) = (X16))
% 1.20/1.40          | ~ (v1_relat_1 @ X16))),
% 1.20/1.40      inference('demod', [status(thm)], ['27', '28'])).
% 1.20/1.40  thf(t55_relat_1, axiom,
% 1.20/1.40    (![A:$i]:
% 1.20/1.40     ( ( v1_relat_1 @ A ) =>
% 1.20/1.40       ( ![B:$i]:
% 1.20/1.40         ( ( v1_relat_1 @ B ) =>
% 1.20/1.40           ( ![C:$i]:
% 1.20/1.40             ( ( v1_relat_1 @ C ) =>
% 1.20/1.40               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 1.20/1.40                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 1.20/1.40  thf('254', plain,
% 1.20/1.40      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.20/1.40         (~ (v1_relat_1 @ X11)
% 1.20/1.40          | ((k5_relat_1 @ (k5_relat_1 @ X12 @ X11) @ X13)
% 1.20/1.40              = (k5_relat_1 @ X12 @ (k5_relat_1 @ X11 @ X13)))
% 1.20/1.40          | ~ (v1_relat_1 @ X13)
% 1.20/1.40          | ~ (v1_relat_1 @ X12))),
% 1.20/1.40      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.20/1.40  thf('255', plain,
% 1.20/1.40      (![X0 : $i, X1 : $i]:
% 1.20/1.40         (((k5_relat_1 @ X0 @ X1)
% 1.20/1.40            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 1.20/1.40               (k5_relat_1 @ X0 @ X1)))
% 1.20/1.40          | ~ (v1_relat_1 @ X0)
% 1.20/1.40          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.20/1.40          | ~ (v1_relat_1 @ X1)
% 1.20/1.40          | ~ (v1_relat_1 @ X0))),
% 1.20/1.40      inference('sup+', [status(thm)], ['253', '254'])).
% 1.20/1.40  thf('256', plain, (![X20 : $i]: (v1_relat_1 @ (k6_partfun1 @ X20))),
% 1.20/1.40      inference('demod', [status(thm)], ['33', '34'])).
% 1.20/1.40  thf('257', plain,
% 1.20/1.40      (![X0 : $i, X1 : $i]:
% 1.20/1.40         (((k5_relat_1 @ X0 @ X1)
% 1.20/1.40            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 1.20/1.40               (k5_relat_1 @ X0 @ X1)))
% 1.20/1.40          | ~ (v1_relat_1 @ X0)
% 1.20/1.40          | ~ (v1_relat_1 @ X1)
% 1.20/1.40          | ~ (v1_relat_1 @ X0))),
% 1.20/1.40      inference('demod', [status(thm)], ['255', '256'])).
% 1.20/1.40  thf('258', plain,
% 1.20/1.40      (![X0 : $i, X1 : $i]:
% 1.20/1.40         (~ (v1_relat_1 @ X1)
% 1.20/1.40          | ~ (v1_relat_1 @ X0)
% 1.20/1.40          | ((k5_relat_1 @ X0 @ X1)
% 1.20/1.40              = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 1.20/1.40                 (k5_relat_1 @ X0 @ X1))))),
% 1.20/1.40      inference('simplify', [status(thm)], ['257'])).
% 1.20/1.40  thf('259', plain,
% 1.20/1.40      ((((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B))
% 1.20/1.40          = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ sk_C))
% 1.20/1.40        | ~ (v1_relat_1 @ sk_C)
% 1.20/1.40        | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B)))),
% 1.20/1.40      inference('sup+', [status(thm)], ['252', '258'])).
% 1.20/1.40  thf('260', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 1.20/1.40      inference('demod', [status(thm)], ['250', '251'])).
% 1.20/1.40  thf('261', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.40      inference('sup-', [status(thm)], ['68', '69'])).
% 1.20/1.40  thf('262', plain, (![X20 : $i]: (v1_relat_1 @ (k6_partfun1 @ X20))),
% 1.20/1.40      inference('demod', [status(thm)], ['33', '34'])).
% 1.20/1.40  thf('263', plain,
% 1.20/1.40      (((sk_C) = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ sk_C))),
% 1.20/1.40      inference('demod', [status(thm)], ['259', '260', '261', '262'])).
% 1.20/1.40  thf('264', plain,
% 1.20/1.40      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.20/1.40         (~ (v1_relat_1 @ X11)
% 1.20/1.40          | ((k5_relat_1 @ (k5_relat_1 @ X12 @ X11) @ X13)
% 1.20/1.40              = (k5_relat_1 @ X12 @ (k5_relat_1 @ X11 @ X13)))
% 1.20/1.40          | ~ (v1_relat_1 @ X13)
% 1.20/1.40          | ~ (v1_relat_1 @ X12))),
% 1.20/1.40      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.20/1.40  thf('265', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (((k5_relat_1 @ sk_C @ X0)
% 1.20/1.40            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ 
% 1.20/1.40               (k5_relat_1 @ sk_C @ X0)))
% 1.20/1.40          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 1.20/1.40          | ~ (v1_relat_1 @ X0)
% 1.20/1.40          | ~ (v1_relat_1 @ sk_C))),
% 1.20/1.40      inference('sup+', [status(thm)], ['263', '264'])).
% 1.20/1.40  thf('266', plain, (![X20 : $i]: (v1_relat_1 @ (k6_partfun1 @ X20))),
% 1.20/1.40      inference('demod', [status(thm)], ['33', '34'])).
% 1.20/1.40  thf('267', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.40      inference('sup-', [status(thm)], ['68', '69'])).
% 1.20/1.40  thf('268', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (((k5_relat_1 @ sk_C @ X0)
% 1.20/1.40            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ 
% 1.20/1.40               (k5_relat_1 @ sk_C @ X0)))
% 1.20/1.40          | ~ (v1_relat_1 @ X0))),
% 1.20/1.40      inference('demod', [status(thm)], ['265', '266', '267'])).
% 1.20/1.40  thf('269', plain,
% 1.20/1.40      ((((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 1.20/1.40          = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ 
% 1.20/1.40             (k6_partfun1 @ (k1_relat_1 @ sk_C))))
% 1.20/1.40        | ~ (v1_relat_1 @ sk_C)
% 1.20/1.40        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.40        | ~ (v2_funct_1 @ sk_C)
% 1.20/1.40        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.20/1.40      inference('sup+', [status(thm)], ['247', '268'])).
% 1.20/1.40  thf('270', plain,
% 1.20/1.40      (![X14 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X14)) = (X14))),
% 1.20/1.40      inference('demod', [status(thm)], ['37', '38'])).
% 1.20/1.40  thf('271', plain,
% 1.20/1.40      (![X16 : $i]:
% 1.20/1.40         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X16)) @ X16) = (X16))
% 1.20/1.40          | ~ (v1_relat_1 @ X16))),
% 1.20/1.40      inference('demod', [status(thm)], ['27', '28'])).
% 1.20/1.40  thf('272', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 1.20/1.40            = (k6_partfun1 @ X0))
% 1.20/1.40          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 1.20/1.40      inference('sup+', [status(thm)], ['270', '271'])).
% 1.20/1.40  thf('273', plain, (![X20 : $i]: (v1_relat_1 @ (k6_partfun1 @ X20))),
% 1.20/1.40      inference('demod', [status(thm)], ['33', '34'])).
% 1.20/1.40  thf('274', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 1.20/1.40           = (k6_partfun1 @ X0))),
% 1.20/1.40      inference('demod', [status(thm)], ['272', '273'])).
% 1.20/1.40  thf('275', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.40      inference('sup-', [status(thm)], ['68', '69'])).
% 1.20/1.40  thf('276', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('277', plain, ((v2_funct_1 @ sk_C)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('278', plain,
% 1.20/1.40      ((((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 1.20/1.40          = (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 1.20/1.40        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.20/1.40      inference('demod', [status(thm)], ['269', '274', '275', '276', '277'])).
% 1.20/1.40  thf('279', plain,
% 1.20/1.40      ((~ (v1_relat_1 @ sk_C)
% 1.20/1.40        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.40        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 1.20/1.40            = (k6_partfun1 @ (k1_relat_1 @ sk_C))))),
% 1.20/1.40      inference('sup-', [status(thm)], ['244', '278'])).
% 1.20/1.40  thf('280', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.40      inference('sup-', [status(thm)], ['68', '69'])).
% 1.20/1.40  thf('281', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('282', plain,
% 1.20/1.40      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 1.20/1.40         = (k6_partfun1 @ (k1_relat_1 @ sk_C)))),
% 1.20/1.40      inference('demod', [status(thm)], ['279', '280', '281'])).
% 1.20/1.40  thf('283', plain,
% 1.20/1.40      (![X24 : $i, X25 : $i]:
% 1.20/1.40         (~ (v1_relat_1 @ X24)
% 1.20/1.40          | ~ (v1_funct_1 @ X24)
% 1.20/1.40          | (v2_funct_1 @ X25)
% 1.20/1.40          | ((k2_relat_1 @ X24) != (k1_relat_1 @ X25))
% 1.20/1.40          | ~ (v2_funct_1 @ (k5_relat_1 @ X24 @ X25))
% 1.20/1.40          | ~ (v1_funct_1 @ X25)
% 1.20/1.40          | ~ (v1_relat_1 @ X25))),
% 1.20/1.40      inference('cnf', [status(esa)], [t48_funct_1])).
% 1.20/1.40  thf('284', plain,
% 1.20/1.40      ((~ (v2_funct_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 1.20/1.40        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.20/1.40        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.20/1.40        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.20/1.40        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 1.20/1.40        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.40        | ~ (v1_relat_1 @ sk_C))),
% 1.20/1.40      inference('sup-', [status(thm)], ['282', '283'])).
% 1.20/1.40  thf('285', plain, (![X21 : $i]: (v2_funct_1 @ (k6_partfun1 @ X21))),
% 1.20/1.40      inference('demod', [status(thm)], ['216', '217'])).
% 1.20/1.40  thf('286', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.20/1.40      inference('sup+', [status(thm)], ['63', '64'])).
% 1.20/1.40  thf('287', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.20/1.40      inference('demod', [status(thm)],
% 1.20/1.40                ['201', '202', '203', '204', '205', '206'])).
% 1.20/1.40  thf('288', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('289', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.40      inference('sup-', [status(thm)], ['68', '69'])).
% 1.20/1.40  thf('290', plain,
% 1.20/1.40      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.20/1.40        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.20/1.40        | ((sk_B) != (sk_B))
% 1.20/1.40        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.20/1.40      inference('demod', [status(thm)],
% 1.20/1.40                ['284', '285', '286', '287', '288', '289'])).
% 1.20/1.40  thf('291', plain,
% 1.20/1.40      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 1.20/1.40        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.20/1.40        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.20/1.40      inference('simplify', [status(thm)], ['290'])).
% 1.20/1.40  thf('292', plain,
% 1.20/1.40      ((~ (v1_relat_1 @ sk_C)
% 1.20/1.40        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.40        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.20/1.40        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['243', '291'])).
% 1.20/1.40  thf('293', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.40      inference('sup-', [status(thm)], ['68', '69'])).
% 1.20/1.40  thf('294', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('295', plain,
% 1.20/1.40      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.20/1.40        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.20/1.40      inference('demod', [status(thm)], ['292', '293', '294'])).
% 1.20/1.40  thf('296', plain,
% 1.20/1.40      ((~ (v1_relat_1 @ sk_C)
% 1.20/1.40        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.40        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['242', '295'])).
% 1.20/1.40  thf('297', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.40      inference('sup-', [status(thm)], ['68', '69'])).
% 1.20/1.40  thf('298', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('299', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 1.20/1.40      inference('demod', [status(thm)], ['296', '297', '298'])).
% 1.20/1.40  thf('300', plain,
% 1.20/1.40      (((r1_tarski @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 1.20/1.40        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.20/1.40        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.20/1.40      inference('demod', [status(thm)], ['241', '299'])).
% 1.20/1.40  thf('301', plain,
% 1.20/1.40      ((~ (v1_relat_1 @ sk_C)
% 1.20/1.40        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.40        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.20/1.40        | (r1_tarski @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 1.20/1.40      inference('sup-', [status(thm)], ['176', '300'])).
% 1.20/1.40  thf('302', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.40      inference('sup-', [status(thm)], ['68', '69'])).
% 1.20/1.40  thf('303', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('304', plain,
% 1.20/1.40      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.20/1.40        | (r1_tarski @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 1.20/1.40      inference('demod', [status(thm)], ['301', '302', '303'])).
% 1.20/1.40  thf('305', plain,
% 1.20/1.40      ((~ (v1_relat_1 @ sk_C)
% 1.20/1.40        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.40        | (r1_tarski @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 1.20/1.40      inference('sup-', [status(thm)], ['175', '304'])).
% 1.20/1.40  thf('306', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.40      inference('sup-', [status(thm)], ['68', '69'])).
% 1.20/1.40  thf('307', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('308', plain,
% 1.20/1.40      ((r1_tarski @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.20/1.40      inference('demod', [status(thm)], ['305', '306', '307'])).
% 1.20/1.40  thf('309', plain,
% 1.20/1.40      (![X0 : $i, X2 : $i]:
% 1.20/1.40         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.20/1.40      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.20/1.40  thf('310', plain,
% 1.20/1.40      ((~ (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) @ sk_B)
% 1.20/1.40        | ((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) = (sk_B)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['308', '309'])).
% 1.20/1.40  thf('311', plain,
% 1.20/1.40      ((~ (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)
% 1.20/1.40        | ~ (v1_relat_1 @ sk_C)
% 1.20/1.40        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.40        | ~ (v2_funct_1 @ sk_C)
% 1.20/1.40        | ((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) = (sk_B)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['174', '310'])).
% 1.20/1.40  thf('312', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.20/1.40      inference('sup+', [status(thm)], ['63', '64'])).
% 1.20/1.40  thf('313', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.20/1.40      inference('simplify', [status(thm)], ['15'])).
% 1.20/1.40  thf('314', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.40      inference('sup-', [status(thm)], ['68', '69'])).
% 1.20/1.40  thf('315', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('316', plain, ((v2_funct_1 @ sk_C)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('317', plain,
% 1.20/1.40      (((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) = (sk_B))),
% 1.20/1.40      inference('demod', [status(thm)],
% 1.20/1.40                ['311', '312', '313', '314', '315', '316'])).
% 1.20/1.40  thf('318', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (~ (v1_relat_1 @ X0)
% 1.20/1.40          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) = (X0)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['16', '19'])).
% 1.20/1.40  thf('319', plain,
% 1.20/1.40      ((((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.20/1.40          (k6_partfun1 @ sk_B)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.20/1.40        | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.20/1.40      inference('sup+', [status(thm)], ['317', '318'])).
% 1.20/1.40  thf('320', plain,
% 1.20/1.40      ((~ (v1_relat_1 @ sk_C)
% 1.20/1.40        | ~ (v1_relat_1 @ sk_C)
% 1.20/1.40        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.40        | ~ (v2_funct_1 @ sk_C)
% 1.20/1.40        | ((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 1.20/1.40            (k6_partfun1 @ sk_B)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.20/1.40      inference('sup-', [status(thm)], ['173', '319'])).
% 1.20/1.40  thf('321', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.40      inference('sup-', [status(thm)], ['68', '69'])).
% 1.20/1.40  thf('322', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.40      inference('sup-', [status(thm)], ['68', '69'])).
% 1.20/1.40  thf('323', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('324', plain, ((v2_funct_1 @ sk_C)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('325', plain,
% 1.20/1.40      (((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ (k6_partfun1 @ sk_B))
% 1.20/1.40         = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.20/1.40      inference('demod', [status(thm)], ['320', '321', '322', '323', '324'])).
% 1.20/1.40  thf('326', plain,
% 1.20/1.40      ((((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B))
% 1.20/1.40          = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.20/1.40        | ~ (v1_relat_1 @ sk_C)
% 1.20/1.40        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.40        | ~ (v2_funct_1 @ sk_C))),
% 1.20/1.40      inference('sup+', [status(thm)], ['172', '325'])).
% 1.20/1.40  thf('327', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 1.20/1.40      inference('demod', [status(thm)], ['250', '251'])).
% 1.20/1.40  thf('328', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.40      inference('sup-', [status(thm)], ['68', '69'])).
% 1.20/1.40  thf('329', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('330', plain, ((v2_funct_1 @ sk_C)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('331', plain, (((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.20/1.40      inference('demod', [status(thm)], ['326', '327', '328', '329', '330'])).
% 1.20/1.40  thf('332', plain,
% 1.20/1.40      (![X27 : $i]:
% 1.20/1.40         (~ (v2_funct_1 @ X27)
% 1.20/1.40          | ((k5_relat_1 @ X27 @ (k2_funct_1 @ X27))
% 1.20/1.40              = (k6_partfun1 @ (k1_relat_1 @ X27)))
% 1.20/1.40          | ~ (v1_funct_1 @ X27)
% 1.20/1.40          | ~ (v1_relat_1 @ X27))),
% 1.20/1.40      inference('demod', [status(thm)], ['245', '246'])).
% 1.20/1.40  thf('333', plain,
% 1.20/1.40      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 1.20/1.40          = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 1.20/1.40        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.20/1.40        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.20/1.40        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.20/1.40      inference('sup+', [status(thm)], ['331', '332'])).
% 1.20/1.40  thf('334', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.20/1.40      inference('demod', [status(thm)],
% 1.20/1.40                ['201', '202', '203', '204', '205', '206'])).
% 1.20/1.40  thf('335', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 1.20/1.40      inference('demod', [status(thm)], ['296', '297', '298'])).
% 1.20/1.40  thf('336', plain,
% 1.20/1.40      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 1.20/1.40        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.20/1.40        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.20/1.40      inference('demod', [status(thm)], ['333', '334', '335'])).
% 1.20/1.40  thf('337', plain,
% 1.20/1.40      ((~ (v1_relat_1 @ sk_C)
% 1.20/1.40        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.40        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.20/1.40        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['171', '336'])).
% 1.20/1.40  thf('338', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.40      inference('sup-', [status(thm)], ['68', '69'])).
% 1.20/1.40  thf('339', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('340', plain,
% 1.20/1.40      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.20/1.40        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 1.20/1.40      inference('demod', [status(thm)], ['337', '338', '339'])).
% 1.20/1.40  thf('341', plain,
% 1.20/1.40      ((~ (v1_relat_1 @ sk_C)
% 1.20/1.40        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.40        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['170', '340'])).
% 1.20/1.40  thf('342', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.40      inference('sup-', [status(thm)], ['68', '69'])).
% 1.20/1.40  thf('343', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('344', plain,
% 1.20/1.40      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 1.20/1.40      inference('demod', [status(thm)], ['341', '342', '343'])).
% 1.20/1.40  thf('345', plain,
% 1.20/1.40      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.20/1.40         (~ (v1_relat_1 @ X11)
% 1.20/1.40          | ((k5_relat_1 @ (k5_relat_1 @ X12 @ X11) @ X13)
% 1.20/1.40              = (k5_relat_1 @ X12 @ (k5_relat_1 @ X11 @ X13)))
% 1.20/1.40          | ~ (v1_relat_1 @ X13)
% 1.20/1.40          | ~ (v1_relat_1 @ X12))),
% 1.20/1.40      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.20/1.40  thf('346', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.20/1.40            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.20/1.40          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.20/1.40          | ~ (v1_relat_1 @ X0)
% 1.20/1.40          | ~ (v1_relat_1 @ sk_C))),
% 1.20/1.40      inference('sup+', [status(thm)], ['344', '345'])).
% 1.20/1.40  thf('347', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.40      inference('sup-', [status(thm)], ['68', '69'])).
% 1.20/1.40  thf('348', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.20/1.40            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.20/1.40          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.20/1.40          | ~ (v1_relat_1 @ X0))),
% 1.20/1.40      inference('demod', [status(thm)], ['346', '347'])).
% 1.20/1.40  thf('349', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (~ (v1_relat_1 @ sk_C)
% 1.20/1.40          | ~ (v1_funct_1 @ sk_C)
% 1.20/1.40          | ~ (v1_relat_1 @ X0)
% 1.20/1.40          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.20/1.40              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 1.20/1.40      inference('sup-', [status(thm)], ['169', '348'])).
% 1.20/1.40  thf('350', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.40      inference('sup-', [status(thm)], ['68', '69'])).
% 1.20/1.40  thf('351', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('352', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (~ (v1_relat_1 @ X0)
% 1.20/1.40          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.20/1.40              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 1.20/1.40      inference('demod', [status(thm)], ['349', '350', '351'])).
% 1.20/1.40  thf('353', plain,
% 1.20/1.40      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 1.20/1.40          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 1.20/1.40        | ~ (v1_relat_1 @ sk_D))),
% 1.20/1.40      inference('sup+', [status(thm)], ['168', '352'])).
% 1.20/1.40  thf('354', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 1.20/1.40      inference('sup-', [status(thm)], ['153', '154'])).
% 1.20/1.40  thf('355', plain,
% 1.20/1.40      (![X3 : $i, X4 : $i]:
% 1.20/1.40         (~ (v4_relat_1 @ X3 @ X4)
% 1.20/1.40          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.20/1.40          | ~ (v1_relat_1 @ X3))),
% 1.20/1.40      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.20/1.40  thf('356', plain,
% 1.20/1.40      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 1.20/1.40      inference('sup-', [status(thm)], ['354', '355'])).
% 1.20/1.40  thf('357', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.40      inference('sup-', [status(thm)], ['68', '69'])).
% 1.20/1.40  thf('358', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 1.20/1.40      inference('demod', [status(thm)], ['356', '357'])).
% 1.20/1.40  thf('359', plain,
% 1.20/1.40      (![X19 : $i]:
% 1.20/1.40         ((v1_relat_1 @ (k2_funct_1 @ X19))
% 1.20/1.40          | ~ (v1_funct_1 @ X19)
% 1.20/1.40          | ~ (v1_relat_1 @ X19))),
% 1.20/1.40      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.20/1.40  thf('360', plain,
% 1.20/1.40      (![X26 : $i]:
% 1.20/1.40         (~ (v2_funct_1 @ X26)
% 1.20/1.40          | ((k1_relat_1 @ X26) = (k2_relat_1 @ (k2_funct_1 @ X26)))
% 1.20/1.40          | ~ (v1_funct_1 @ X26)
% 1.20/1.40          | ~ (v1_relat_1 @ X26))),
% 1.20/1.40      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.20/1.40  thf('361', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         ((r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.20/1.40          | ~ (v2_funct_1 @ X0)
% 1.20/1.40          | ~ (v1_funct_1 @ X0)
% 1.20/1.40          | ~ (v1_relat_1 @ X0))),
% 1.20/1.40      inference('simplify', [status(thm)], ['239'])).
% 1.20/1.40  thf('362', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 1.20/1.40      inference('demod', [status(thm)], ['250', '251'])).
% 1.20/1.40  thf('363', plain,
% 1.20/1.40      (![X14 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X14)) = (X14))),
% 1.20/1.40      inference('demod', [status(thm)], ['37', '38'])).
% 1.20/1.40  thf('364', plain,
% 1.20/1.40      (![X7 : $i, X8 : $i]:
% 1.20/1.40         (~ (v1_relat_1 @ X7)
% 1.20/1.40          | ((k1_relat_1 @ (k5_relat_1 @ X8 @ X7))
% 1.20/1.40              = (k10_relat_1 @ X8 @ (k1_relat_1 @ X7)))
% 1.20/1.40          | ~ (v1_relat_1 @ X8))),
% 1.20/1.40      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.20/1.40  thf('365', plain,
% 1.20/1.40      (![X3 : $i, X4 : $i]:
% 1.20/1.40         (~ (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.20/1.40          | (v4_relat_1 @ X3 @ X4)
% 1.20/1.40          | ~ (v1_relat_1 @ X3))),
% 1.20/1.40      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.20/1.40  thf('366', plain,
% 1.20/1.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.40         (~ (r1_tarski @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)) @ X2)
% 1.20/1.40          | ~ (v1_relat_1 @ X1)
% 1.20/1.40          | ~ (v1_relat_1 @ X0)
% 1.20/1.40          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 1.20/1.40          | (v4_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2))),
% 1.20/1.40      inference('sup-', [status(thm)], ['364', '365'])).
% 1.20/1.40  thf('367', plain,
% 1.20/1.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.40         (~ (r1_tarski @ (k10_relat_1 @ X2 @ X0) @ X1)
% 1.20/1.40          | (v4_relat_1 @ (k5_relat_1 @ X2 @ (k6_partfun1 @ X0)) @ X1)
% 1.20/1.40          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ (k6_partfun1 @ X0)))
% 1.20/1.40          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 1.20/1.40          | ~ (v1_relat_1 @ X2))),
% 1.20/1.40      inference('sup-', [status(thm)], ['363', '366'])).
% 1.20/1.40  thf('368', plain, (![X20 : $i]: (v1_relat_1 @ (k6_partfun1 @ X20))),
% 1.20/1.40      inference('demod', [status(thm)], ['33', '34'])).
% 1.20/1.40  thf('369', plain,
% 1.20/1.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.40         (~ (r1_tarski @ (k10_relat_1 @ X2 @ X0) @ X1)
% 1.20/1.40          | (v4_relat_1 @ (k5_relat_1 @ X2 @ (k6_partfun1 @ X0)) @ X1)
% 1.20/1.40          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ (k6_partfun1 @ X0)))
% 1.20/1.40          | ~ (v1_relat_1 @ X2))),
% 1.20/1.40      inference('demod', [status(thm)], ['367', '368'])).
% 1.20/1.40  thf('370', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (~ (v1_relat_1 @ sk_C)
% 1.20/1.40          | ~ (v1_relat_1 @ sk_C)
% 1.20/1.40          | (v4_relat_1 @ (k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) @ X0)
% 1.20/1.40          | ~ (r1_tarski @ (k10_relat_1 @ sk_C @ sk_B) @ X0))),
% 1.20/1.40      inference('sup-', [status(thm)], ['362', '369'])).
% 1.20/1.40  thf('371', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.40      inference('sup-', [status(thm)], ['68', '69'])).
% 1.20/1.40  thf('372', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.40      inference('sup-', [status(thm)], ['68', '69'])).
% 1.20/1.40  thf('373', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 1.20/1.40      inference('demod', [status(thm)], ['250', '251'])).
% 1.20/1.40  thf('374', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         ((v4_relat_1 @ sk_C @ X0)
% 1.20/1.40          | ~ (r1_tarski @ (k10_relat_1 @ sk_C @ sk_B) @ X0))),
% 1.20/1.40      inference('demod', [status(thm)], ['370', '371', '372', '373'])).
% 1.20/1.40  thf('375', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 1.20/1.40      inference('demod', [status(thm)], ['250', '251'])).
% 1.20/1.40  thf('376', plain,
% 1.20/1.40      (![X7 : $i, X8 : $i]:
% 1.20/1.40         (~ (v1_relat_1 @ X7)
% 1.20/1.40          | ((k1_relat_1 @ (k5_relat_1 @ X8 @ X7))
% 1.20/1.40              = (k10_relat_1 @ X8 @ (k1_relat_1 @ X7)))
% 1.20/1.40          | ~ (v1_relat_1 @ X8))),
% 1.20/1.40      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.20/1.40  thf('377', plain,
% 1.20/1.40      ((((k1_relat_1 @ sk_C)
% 1.20/1.40          = (k10_relat_1 @ sk_C @ (k1_relat_1 @ (k6_partfun1 @ sk_B))))
% 1.20/1.40        | ~ (v1_relat_1 @ sk_C)
% 1.20/1.40        | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B)))),
% 1.20/1.40      inference('sup+', [status(thm)], ['375', '376'])).
% 1.20/1.40  thf('378', plain,
% 1.20/1.40      (![X14 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X14)) = (X14))),
% 1.20/1.40      inference('demod', [status(thm)], ['37', '38'])).
% 1.20/1.40  thf('379', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.40      inference('sup-', [status(thm)], ['68', '69'])).
% 1.20/1.40  thf('380', plain, (![X20 : $i]: (v1_relat_1 @ (k6_partfun1 @ X20))),
% 1.20/1.40      inference('demod', [status(thm)], ['33', '34'])).
% 1.20/1.40  thf('381', plain, (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_B))),
% 1.20/1.40      inference('demod', [status(thm)], ['377', '378', '379', '380'])).
% 1.20/1.40  thf('382', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         ((v4_relat_1 @ sk_C @ X0) | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 1.20/1.40      inference('demod', [status(thm)], ['374', '381'])).
% 1.20/1.40  thf('383', plain,
% 1.20/1.40      ((~ (v1_relat_1 @ sk_C)
% 1.20/1.40        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.40        | ~ (v2_funct_1 @ sk_C)
% 1.20/1.40        | (v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.20/1.40      inference('sup-', [status(thm)], ['361', '382'])).
% 1.20/1.40  thf('384', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.40      inference('sup-', [status(thm)], ['68', '69'])).
% 1.20/1.40  thf('385', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('386', plain, ((v2_funct_1 @ sk_C)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('387', plain, ((v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.20/1.40      inference('demod', [status(thm)], ['383', '384', '385', '386'])).
% 1.20/1.40  thf('388', plain,
% 1.20/1.40      (![X3 : $i, X4 : $i]:
% 1.20/1.40         (~ (v4_relat_1 @ X3 @ X4)
% 1.20/1.40          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.20/1.40          | ~ (v1_relat_1 @ X3))),
% 1.20/1.40      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.20/1.40  thf('389', plain,
% 1.20/1.40      ((~ (v1_relat_1 @ sk_C)
% 1.20/1.40        | (r1_tarski @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.20/1.40      inference('sup-', [status(thm)], ['387', '388'])).
% 1.20/1.40  thf('390', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.40      inference('sup-', [status(thm)], ['68', '69'])).
% 1.20/1.40  thf('391', plain,
% 1.20/1.40      ((r1_tarski @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.20/1.40      inference('demod', [status(thm)], ['389', '390'])).
% 1.20/1.40  thf('392', plain,
% 1.20/1.40      (![X0 : $i, X2 : $i]:
% 1.20/1.40         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.20/1.40      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.20/1.40  thf('393', plain,
% 1.20/1.40      ((~ (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k1_relat_1 @ sk_C))
% 1.20/1.40        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['391', '392'])).
% 1.20/1.40  thf('394', plain,
% 1.20/1.40      ((~ (r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))
% 1.20/1.40        | ~ (v1_relat_1 @ sk_C)
% 1.20/1.40        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.40        | ~ (v2_funct_1 @ sk_C)
% 1.20/1.40        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['360', '393'])).
% 1.20/1.40  thf('395', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.20/1.40      inference('simplify', [status(thm)], ['15'])).
% 1.20/1.40  thf('396', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.40      inference('sup-', [status(thm)], ['68', '69'])).
% 1.20/1.40  thf('397', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('398', plain, ((v2_funct_1 @ sk_C)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('399', plain,
% 1.20/1.40      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 1.20/1.40      inference('demod', [status(thm)], ['394', '395', '396', '397', '398'])).
% 1.20/1.40  thf('400', plain,
% 1.20/1.40      (![X17 : $i, X18 : $i]:
% 1.20/1.40         (~ (r1_tarski @ (k2_relat_1 @ X17) @ X18)
% 1.20/1.40          | ((k5_relat_1 @ X17 @ (k6_partfun1 @ X18)) = (X17))
% 1.20/1.40          | ~ (v1_relat_1 @ X17))),
% 1.20/1.40      inference('demod', [status(thm)], ['17', '18'])).
% 1.20/1.40  thf('401', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0)
% 1.20/1.40          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.20/1.40          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ X0))
% 1.20/1.40              = (k2_funct_1 @ sk_C)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['399', '400'])).
% 1.20/1.40  thf('402', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (~ (v1_relat_1 @ sk_C)
% 1.20/1.40          | ~ (v1_funct_1 @ sk_C)
% 1.20/1.40          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ X0))
% 1.20/1.40              = (k2_funct_1 @ sk_C))
% 1.20/1.40          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 1.20/1.40      inference('sup-', [status(thm)], ['359', '401'])).
% 1.20/1.40  thf('403', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.40      inference('sup-', [status(thm)], ['68', '69'])).
% 1.20/1.40  thf('404', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('405', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ X0))
% 1.20/1.40            = (k2_funct_1 @ sk_C))
% 1.20/1.40          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 1.20/1.40      inference('demod', [status(thm)], ['402', '403', '404'])).
% 1.20/1.40  thf('406', plain,
% 1.20/1.40      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 1.20/1.40         = (k2_funct_1 @ sk_C))),
% 1.20/1.40      inference('sup-', [status(thm)], ['358', '405'])).
% 1.20/1.40  thf('407', plain, ((v1_relat_1 @ sk_D)),
% 1.20/1.40      inference('sup-', [status(thm)], ['22', '23'])).
% 1.20/1.40  thf('408', plain,
% 1.20/1.40      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (k2_funct_1 @ sk_C))),
% 1.20/1.40      inference('demod', [status(thm)], ['353', '406', '407'])).
% 1.20/1.40  thf('409', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 1.20/1.40      inference('sup+', [status(thm)], ['167', '408'])).
% 1.20/1.40  thf('410', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('411', plain, ($false),
% 1.20/1.40      inference('simplify_reflect-', [status(thm)], ['409', '410'])).
% 1.20/1.40  
% 1.20/1.40  % SZS output end Refutation
% 1.20/1.40  
% 1.20/1.41  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

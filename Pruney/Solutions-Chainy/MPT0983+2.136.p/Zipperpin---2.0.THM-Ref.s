%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hGrXR6Dn9I

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:23 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 306 expanded)
%              Number of leaves         :   44 ( 105 expanded)
%              Depth                    :   15
%              Number of atoms          : 1296 (5653 expanded)
%              Number of equality atoms :   62 (  92 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t29_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
           => ( ( v2_funct_1 @ C )
              & ( v2_funct_2 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
             => ( ( v2_funct_1 @ C )
                & ( v2_funct_2 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_funct_2])).

thf('0',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
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

thf('4',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i] :
      ( ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_funct_2 @ X55 @ X56 @ X57 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X57 ) ) )
      | ~ ( r2_relset_1 @ X56 @ X56 @ ( k1_partfun1 @ X56 @ X57 @ X57 @ X56 @ X55 @ X58 ) @ ( k6_partfun1 @ X56 ) )
      | ( ( k2_relset_1 @ X57 @ X56 @ X58 )
        = X56 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X56 ) ) )
      | ~ ( v1_funct_2 @ X58 @ X57 @ X56 )
      | ~ ( v1_funct_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k2_relset_1 @ X33 @ X34 @ X32 )
        = ( k2_relat_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('12',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['9','12','13','14','15'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('17',plain,(
    ! [X46: $i,X47: $i] :
      ( ( ( k2_relat_1 @ X47 )
       != X46 )
      | ( v2_funct_2 @ X47 @ X46 )
      | ~ ( v5_relat_1 @ X47 @ X46 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('18',plain,(
    ! [X47: $i] :
      ( ~ ( v1_relat_1 @ X47 )
      | ~ ( v5_relat_1 @ X47 @ ( k2_relat_1 @ X47 ) )
      | ( v2_funct_2 @ X47 @ ( k2_relat_1 @ X47 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['19'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('21',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ( v5_relat_1 @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X47: $i] :
      ( ( v2_funct_2 @ X47 @ ( k2_relat_1 @ X47 ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(clc,[status(thm)],['18','22'])).

thf('24',plain,
    ( ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['16','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('26',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('28',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('29',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['24','29'])).

thf('31',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t162_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B )
        = B ) ) )).

thf('37',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X24 ) @ X23 )
        = X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t162_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('38',plain,(
    ! [X54: $i] :
      ( ( k6_partfun1 @ X54 )
      = ( k6_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('39',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k9_relat_1 @ ( k6_partfun1 @ X24 ) @ X23 )
        = X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k9_relat_1 @ ( k6_partfun1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
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

thf('43',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) )
      | ( ( k1_partfun1 @ X49 @ X50 @ X52 @ X53 @ X48 @ X51 )
        = ( k5_relat_1 @ X48 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
           => ( ( ( C = k1_xboole_0 )
                & ( B != k1_xboole_0 ) )
              | ( v2_funct_1 @ D ) ) ) ) ) )).

thf('51',plain,(
    ! [X59: $i,X60: $i,X61: $i,X62: $i,X63: $i] :
      ( ~ ( v1_funct_1 @ X59 )
      | ~ ( v1_funct_2 @ X59 @ X60 @ X61 )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X61 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X62 @ X60 @ X60 @ X61 @ X63 @ X59 ) )
      | ( v2_funct_1 @ X63 )
      | ( X61 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X62 @ X60 ) ) )
      | ~ ( v1_funct_2 @ X63 @ X62 @ X60 )
      | ~ ( v1_funct_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['49','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf('61',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','34'])).

thf('62',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('65',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( m1_subset_1 @ ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) )).

thf('68',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relset_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('71',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( X41 = X44 )
      | ~ ( r2_relset_1 @ X42 @ X43 @ X41 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('75',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( ( k4_relset_1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38 )
        = ( k5_relat_1 @ X35 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,
    ( ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['72','77','78'])).

thf('80',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','79'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('81',plain,(
    ! [X45: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X45 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('82',plain,(
    ! [X54: $i] :
      ( ( k6_partfun1 @ X54 )
      = ( k6_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('83',plain,(
    ! [X45: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X45 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X45 ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['80','83'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('85',plain,(
    ! [X25: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('86',plain,(
    ! [X54: $i] :
      ( ( k6_partfun1 @ X54 )
      = ( k6_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('87',plain,(
    ! [X25: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X25 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['62','84','87'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('89',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('90',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['89'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('91',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('92',plain,(
    ! [X54: $i] :
      ( ( k6_partfun1 @ X54 )
      = ( k6_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('93',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['91','92'])).

thf(t150_relat_1,axiom,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('94',plain,(
    ! [X19: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t150_relat_1])).

thf('95',plain,(
    k1_xboole_0 = sk_C ),
    inference(demod,[status(thm)],['40','88','90','93','94'])).

thf('96',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['91','92'])).

thf('97',plain,(
    ! [X25: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X25 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('98',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    $false ),
    inference(demod,[status(thm)],['35','95','98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.10  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hGrXR6Dn9I
% 0.10/0.30  % Computer   : n021.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % DateTime   : Tue Dec  1 10:52:34 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.10/0.30  % Running portfolio for 600 s
% 0.10/0.30  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.10/0.30  % Number of cores: 8
% 0.10/0.30  % Python version: Python 3.6.8
% 0.10/0.31  % Running in FO mode
% 0.53/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.53/0.73  % Solved by: fo/fo7.sh
% 0.53/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.73  % done 709 iterations in 0.323s
% 0.53/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.53/0.73  % SZS output start Refutation
% 0.53/0.73  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.53/0.73  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.53/0.73  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.53/0.73  thf(sk_D_type, type, sk_D: $i).
% 0.53/0.73  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.53/0.73  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 0.53/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.53/0.73  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.53/0.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.53/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.73  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.53/0.73  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.53/0.73  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.53/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.73  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.53/0.73  thf(sk_C_type, type, sk_C: $i).
% 0.53/0.73  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.53/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.53/0.73  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.53/0.73  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.53/0.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.53/0.73  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.53/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.73  thf(t29_funct_2, conjecture,
% 0.53/0.73    (![A:$i,B:$i,C:$i]:
% 0.53/0.73     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.53/0.73         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.73       ( ![D:$i]:
% 0.53/0.73         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.53/0.73             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.53/0.73           ( ( r2_relset_1 @
% 0.53/0.73               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.53/0.73               ( k6_partfun1 @ A ) ) =>
% 0.53/0.73             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 0.53/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.73    (~( ![A:$i,B:$i,C:$i]:
% 0.53/0.73        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.53/0.73            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.73          ( ![D:$i]:
% 0.53/0.73            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.53/0.73                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.53/0.73              ( ( r2_relset_1 @
% 0.53/0.73                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.53/0.73                  ( k6_partfun1 @ A ) ) =>
% 0.53/0.73                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 0.53/0.73    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 0.53/0.73  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('1', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.53/0.73      inference('split', [status(esa)], ['0'])).
% 0.53/0.73  thf('2', plain,
% 0.53/0.73      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.53/0.73        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.53/0.73        (k6_partfun1 @ sk_A))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('3', plain,
% 0.53/0.73      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf(t24_funct_2, axiom,
% 0.53/0.73    (![A:$i,B:$i,C:$i]:
% 0.53/0.73     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.53/0.73         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.73       ( ![D:$i]:
% 0.53/0.73         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.53/0.73             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.53/0.73           ( ( r2_relset_1 @
% 0.53/0.73               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.53/0.73               ( k6_partfun1 @ B ) ) =>
% 0.53/0.73             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.53/0.73  thf('4', plain,
% 0.53/0.73      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i]:
% 0.53/0.73         (~ (v1_funct_1 @ X55)
% 0.53/0.73          | ~ (v1_funct_2 @ X55 @ X56 @ X57)
% 0.53/0.73          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X57)))
% 0.53/0.73          | ~ (r2_relset_1 @ X56 @ X56 @ 
% 0.53/0.73               (k1_partfun1 @ X56 @ X57 @ X57 @ X56 @ X55 @ X58) @ 
% 0.53/0.73               (k6_partfun1 @ X56))
% 0.53/0.73          | ((k2_relset_1 @ X57 @ X56 @ X58) = (X56))
% 0.53/0.73          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X56)))
% 0.53/0.73          | ~ (v1_funct_2 @ X58 @ X57 @ X56)
% 0.53/0.73          | ~ (v1_funct_1 @ X58))),
% 0.53/0.73      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.53/0.73  thf('5', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         (~ (v1_funct_1 @ X0)
% 0.53/0.73          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.53/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.53/0.73          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.53/0.73          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.53/0.73               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.53/0.73               (k6_partfun1 @ sk_A))
% 0.53/0.73          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.53/0.73          | ~ (v1_funct_1 @ sk_C))),
% 0.53/0.73      inference('sup-', [status(thm)], ['3', '4'])).
% 0.53/0.73  thf('6', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('8', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         (~ (v1_funct_1 @ X0)
% 0.53/0.73          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.53/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.53/0.73          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.53/0.73          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.53/0.73               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.53/0.73               (k6_partfun1 @ sk_A)))),
% 0.53/0.73      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.53/0.73  thf('9', plain,
% 0.53/0.73      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.53/0.73        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.53/0.73        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.53/0.73        | ~ (v1_funct_1 @ sk_D))),
% 0.53/0.73      inference('sup-', [status(thm)], ['2', '8'])).
% 0.53/0.73  thf('10', plain,
% 0.53/0.73      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf(redefinition_k2_relset_1, axiom,
% 0.53/0.73    (![A:$i,B:$i,C:$i]:
% 0.53/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.73       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.53/0.73  thf('11', plain,
% 0.53/0.73      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.53/0.73         (((k2_relset_1 @ X33 @ X34 @ X32) = (k2_relat_1 @ X32))
% 0.53/0.73          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.53/0.73      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.53/0.73  thf('12', plain,
% 0.53/0.73      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.53/0.73      inference('sup-', [status(thm)], ['10', '11'])).
% 0.53/0.73  thf('13', plain,
% 0.53/0.73      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('14', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('15', plain, ((v1_funct_1 @ sk_D)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('16', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.53/0.73      inference('demod', [status(thm)], ['9', '12', '13', '14', '15'])).
% 0.53/0.73  thf(d3_funct_2, axiom,
% 0.53/0.73    (![A:$i,B:$i]:
% 0.53/0.73     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.53/0.73       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.53/0.73  thf('17', plain,
% 0.53/0.73      (![X46 : $i, X47 : $i]:
% 0.53/0.73         (((k2_relat_1 @ X47) != (X46))
% 0.53/0.73          | (v2_funct_2 @ X47 @ X46)
% 0.53/0.73          | ~ (v5_relat_1 @ X47 @ X46)
% 0.53/0.73          | ~ (v1_relat_1 @ X47))),
% 0.53/0.73      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.53/0.73  thf('18', plain,
% 0.53/0.73      (![X47 : $i]:
% 0.53/0.73         (~ (v1_relat_1 @ X47)
% 0.53/0.73          | ~ (v5_relat_1 @ X47 @ (k2_relat_1 @ X47))
% 0.53/0.73          | (v2_funct_2 @ X47 @ (k2_relat_1 @ X47)))),
% 0.53/0.73      inference('simplify', [status(thm)], ['17'])).
% 0.53/0.73  thf(d10_xboole_0, axiom,
% 0.53/0.73    (![A:$i,B:$i]:
% 0.53/0.73     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.53/0.73  thf('19', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.53/0.73      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.53/0.73  thf('20', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.53/0.73      inference('simplify', [status(thm)], ['19'])).
% 0.53/0.73  thf(d19_relat_1, axiom,
% 0.53/0.73    (![A:$i,B:$i]:
% 0.53/0.73     ( ( v1_relat_1 @ B ) =>
% 0.53/0.73       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.53/0.73  thf('21', plain,
% 0.53/0.73      (![X12 : $i, X13 : $i]:
% 0.53/0.73         (~ (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 0.53/0.73          | (v5_relat_1 @ X12 @ X13)
% 0.53/0.73          | ~ (v1_relat_1 @ X12))),
% 0.53/0.73      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.53/0.73  thf('22', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['20', '21'])).
% 0.53/0.73  thf('23', plain,
% 0.53/0.73      (![X47 : $i]:
% 0.53/0.73         ((v2_funct_2 @ X47 @ (k2_relat_1 @ X47)) | ~ (v1_relat_1 @ X47))),
% 0.53/0.73      inference('clc', [status(thm)], ['18', '22'])).
% 0.53/0.73  thf('24', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 0.53/0.73      inference('sup+', [status(thm)], ['16', '23'])).
% 0.53/0.73  thf('25', plain,
% 0.53/0.73      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf(cc2_relat_1, axiom,
% 0.53/0.73    (![A:$i]:
% 0.53/0.73     ( ( v1_relat_1 @ A ) =>
% 0.53/0.73       ( ![B:$i]:
% 0.53/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.53/0.73  thf('26', plain,
% 0.53/0.73      (![X10 : $i, X11 : $i]:
% 0.53/0.73         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.53/0.73          | (v1_relat_1 @ X10)
% 0.53/0.73          | ~ (v1_relat_1 @ X11))),
% 0.53/0.73      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.53/0.73  thf('27', plain,
% 0.53/0.73      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.53/0.73      inference('sup-', [status(thm)], ['25', '26'])).
% 0.53/0.73  thf(fc6_relat_1, axiom,
% 0.53/0.73    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.53/0.73  thf('28', plain,
% 0.53/0.73      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 0.53/0.73      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.53/0.73  thf('29', plain, ((v1_relat_1 @ sk_D)),
% 0.53/0.73      inference('demod', [status(thm)], ['27', '28'])).
% 0.53/0.73  thf('30', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 0.53/0.73      inference('demod', [status(thm)], ['24', '29'])).
% 0.53/0.73  thf('31', plain,
% 0.53/0.73      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 0.53/0.73      inference('split', [status(esa)], ['0'])).
% 0.53/0.73  thf('32', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 0.53/0.73      inference('sup-', [status(thm)], ['30', '31'])).
% 0.53/0.73  thf('33', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 0.53/0.73      inference('split', [status(esa)], ['0'])).
% 0.53/0.73  thf('34', plain, (~ ((v2_funct_1 @ sk_C))),
% 0.53/0.73      inference('sat_resolution*', [status(thm)], ['32', '33'])).
% 0.53/0.73  thf('35', plain, (~ (v2_funct_1 @ sk_C)),
% 0.53/0.73      inference('simpl_trail', [status(thm)], ['1', '34'])).
% 0.53/0.73  thf('36', plain,
% 0.53/0.73      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf(t162_funct_1, axiom,
% 0.53/0.73    (![A:$i,B:$i]:
% 0.53/0.73     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.53/0.73       ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ))).
% 0.53/0.73  thf('37', plain,
% 0.53/0.73      (![X23 : $i, X24 : $i]:
% 0.53/0.73         (((k9_relat_1 @ (k6_relat_1 @ X24) @ X23) = (X23))
% 0.53/0.73          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 0.53/0.73      inference('cnf', [status(esa)], [t162_funct_1])).
% 0.53/0.73  thf(redefinition_k6_partfun1, axiom,
% 0.53/0.73    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.53/0.73  thf('38', plain, (![X54 : $i]: ((k6_partfun1 @ X54) = (k6_relat_1 @ X54))),
% 0.53/0.73      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.53/0.73  thf('39', plain,
% 0.53/0.73      (![X23 : $i, X24 : $i]:
% 0.53/0.73         (((k9_relat_1 @ (k6_partfun1 @ X24) @ X23) = (X23))
% 0.53/0.73          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 0.53/0.73      inference('demod', [status(thm)], ['37', '38'])).
% 0.53/0.73  thf('40', plain,
% 0.53/0.73      (((k9_relat_1 @ (k6_partfun1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) @ sk_C)
% 0.53/0.73         = (sk_C))),
% 0.53/0.73      inference('sup-', [status(thm)], ['36', '39'])).
% 0.53/0.73  thf('41', plain,
% 0.53/0.73      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('42', plain,
% 0.53/0.73      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf(redefinition_k1_partfun1, axiom,
% 0.53/0.73    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.53/0.73     ( ( ( v1_funct_1 @ E ) & 
% 0.53/0.73         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.53/0.73         ( v1_funct_1 @ F ) & 
% 0.53/0.73         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.53/0.73       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.53/0.73  thf('43', plain,
% 0.53/0.73      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.53/0.73         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 0.53/0.73          | ~ (v1_funct_1 @ X48)
% 0.53/0.73          | ~ (v1_funct_1 @ X51)
% 0.53/0.73          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53)))
% 0.53/0.73          | ((k1_partfun1 @ X49 @ X50 @ X52 @ X53 @ X48 @ X51)
% 0.53/0.73              = (k5_relat_1 @ X48 @ X51)))),
% 0.53/0.73      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.53/0.73  thf('44', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.73         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.53/0.73            = (k5_relat_1 @ sk_C @ X0))
% 0.53/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.53/0.73          | ~ (v1_funct_1 @ X0)
% 0.53/0.73          | ~ (v1_funct_1 @ sk_C))),
% 0.53/0.73      inference('sup-', [status(thm)], ['42', '43'])).
% 0.53/0.73  thf('45', plain, ((v1_funct_1 @ sk_C)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('46', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.73         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.53/0.73            = (k5_relat_1 @ sk_C @ X0))
% 0.53/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.53/0.73          | ~ (v1_funct_1 @ X0))),
% 0.53/0.73      inference('demod', [status(thm)], ['44', '45'])).
% 0.53/0.73  thf('47', plain,
% 0.53/0.73      ((~ (v1_funct_1 @ sk_D)
% 0.53/0.73        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.53/0.73            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['41', '46'])).
% 0.53/0.73  thf('48', plain, ((v1_funct_1 @ sk_D)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('49', plain,
% 0.53/0.73      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.53/0.73         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.53/0.73      inference('demod', [status(thm)], ['47', '48'])).
% 0.53/0.73  thf('50', plain,
% 0.53/0.73      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf(t26_funct_2, axiom,
% 0.53/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.73     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.53/0.73         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.73       ( ![E:$i]:
% 0.53/0.73         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.53/0.73             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.53/0.73           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 0.53/0.73             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 0.53/0.73               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 0.53/0.73  thf('51', plain,
% 0.53/0.73      (![X59 : $i, X60 : $i, X61 : $i, X62 : $i, X63 : $i]:
% 0.53/0.73         (~ (v1_funct_1 @ X59)
% 0.53/0.73          | ~ (v1_funct_2 @ X59 @ X60 @ X61)
% 0.53/0.73          | ~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X61)))
% 0.53/0.73          | ~ (v2_funct_1 @ (k1_partfun1 @ X62 @ X60 @ X60 @ X61 @ X63 @ X59))
% 0.53/0.73          | (v2_funct_1 @ X63)
% 0.53/0.73          | ((X61) = (k1_xboole_0))
% 0.53/0.73          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X62 @ X60)))
% 0.53/0.73          | ~ (v1_funct_2 @ X63 @ X62 @ X60)
% 0.53/0.73          | ~ (v1_funct_1 @ X63))),
% 0.53/0.73      inference('cnf', [status(esa)], [t26_funct_2])).
% 0.53/0.73  thf('52', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         (~ (v1_funct_1 @ X0)
% 0.53/0.73          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.53/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.53/0.73          | ((sk_A) = (k1_xboole_0))
% 0.53/0.73          | (v2_funct_1 @ X0)
% 0.53/0.73          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.53/0.73          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.53/0.73          | ~ (v1_funct_1 @ sk_D))),
% 0.53/0.73      inference('sup-', [status(thm)], ['50', '51'])).
% 0.53/0.73  thf('53', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('54', plain, ((v1_funct_1 @ sk_D)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('55', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         (~ (v1_funct_1 @ X0)
% 0.53/0.73          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.53/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.53/0.73          | ((sk_A) = (k1_xboole_0))
% 0.53/0.73          | (v2_funct_1 @ X0)
% 0.53/0.73          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 0.53/0.73      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.53/0.73  thf('56', plain,
% 0.53/0.73      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 0.53/0.73        | (v2_funct_1 @ sk_C)
% 0.53/0.73        | ((sk_A) = (k1_xboole_0))
% 0.53/0.73        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.53/0.73        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.53/0.73        | ~ (v1_funct_1 @ sk_C))),
% 0.53/0.73      inference('sup-', [status(thm)], ['49', '55'])).
% 0.53/0.73  thf('57', plain,
% 0.53/0.73      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('58', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('59', plain, ((v1_funct_1 @ sk_C)),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('60', plain,
% 0.53/0.73      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 0.53/0.73        | (v2_funct_1 @ sk_C)
% 0.53/0.73        | ((sk_A) = (k1_xboole_0)))),
% 0.53/0.73      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 0.53/0.73  thf('61', plain, (~ (v2_funct_1 @ sk_C)),
% 0.53/0.73      inference('simpl_trail', [status(thm)], ['1', '34'])).
% 0.53/0.73  thf('62', plain,
% 0.53/0.73      ((((sk_A) = (k1_xboole_0)) | ~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D)))),
% 0.53/0.73      inference('clc', [status(thm)], ['60', '61'])).
% 0.53/0.73  thf('63', plain,
% 0.53/0.73      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.53/0.73        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.53/0.73        (k6_partfun1 @ sk_A))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('64', plain,
% 0.53/0.73      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.53/0.73         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.53/0.73      inference('demod', [status(thm)], ['47', '48'])).
% 0.53/0.73  thf('65', plain,
% 0.53/0.73      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.53/0.73        (k6_partfun1 @ sk_A))),
% 0.53/0.73      inference('demod', [status(thm)], ['63', '64'])).
% 0.53/0.73  thf('66', plain,
% 0.53/0.73      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('67', plain,
% 0.53/0.73      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf(dt_k4_relset_1, axiom,
% 0.53/0.73    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.53/0.73     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.53/0.73         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.53/0.73       ( m1_subset_1 @
% 0.53/0.73         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.53/0.73         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 0.53/0.73  thf('68', plain,
% 0.53/0.73      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.53/0.73         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.53/0.73          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.53/0.73          | (m1_subset_1 @ (k4_relset_1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29) @ 
% 0.53/0.73             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X31))))),
% 0.53/0.73      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 0.53/0.73  thf('69', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.73         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.53/0.73           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.53/0.73          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 0.53/0.73      inference('sup-', [status(thm)], ['67', '68'])).
% 0.53/0.73  thf('70', plain,
% 0.53/0.73      ((m1_subset_1 @ 
% 0.53/0.73        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.53/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['66', '69'])).
% 0.53/0.73  thf(redefinition_r2_relset_1, axiom,
% 0.53/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.73     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.53/0.73         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.73       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.53/0.73  thf('71', plain,
% 0.53/0.73      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.53/0.73         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 0.53/0.73          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 0.53/0.73          | ((X41) = (X44))
% 0.53/0.73          | ~ (r2_relset_1 @ X42 @ X43 @ X41 @ X44))),
% 0.53/0.73      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.53/0.73  thf('72', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.53/0.73             (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.53/0.73          | ((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.53/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.53/0.73      inference('sup-', [status(thm)], ['70', '71'])).
% 0.53/0.73  thf('73', plain,
% 0.53/0.73      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('74', plain,
% 0.53/0.73      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf(redefinition_k4_relset_1, axiom,
% 0.53/0.73    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.53/0.73     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.53/0.73         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.53/0.73       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.53/0.73  thf('75', plain,
% 0.53/0.73      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.53/0.73         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.53/0.73          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.53/0.73          | ((k4_relset_1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38)
% 0.53/0.73              = (k5_relat_1 @ X35 @ X38)))),
% 0.53/0.73      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 0.53/0.73  thf('76', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.73         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.53/0.73            = (k5_relat_1 @ sk_C @ X0))
% 0.53/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.53/0.73      inference('sup-', [status(thm)], ['74', '75'])).
% 0.53/0.73  thf('77', plain,
% 0.53/0.73      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.53/0.73         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.53/0.73      inference('sup-', [status(thm)], ['73', '76'])).
% 0.53/0.73  thf('78', plain,
% 0.53/0.73      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.53/0.73         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.53/0.73      inference('sup-', [status(thm)], ['73', '76'])).
% 0.53/0.73  thf('79', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 0.53/0.73          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 0.53/0.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.53/0.73      inference('demod', [status(thm)], ['72', '77', '78'])).
% 0.53/0.73  thf('80', plain,
% 0.53/0.73      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.53/0.73           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.53/0.73        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['65', '79'])).
% 0.53/0.73  thf(t29_relset_1, axiom,
% 0.53/0.73    (![A:$i]:
% 0.53/0.73     ( m1_subset_1 @
% 0.53/0.73       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.53/0.73  thf('81', plain,
% 0.53/0.73      (![X45 : $i]:
% 0.53/0.73         (m1_subset_1 @ (k6_relat_1 @ X45) @ 
% 0.53/0.73          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X45)))),
% 0.53/0.73      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.53/0.73  thf('82', plain, (![X54 : $i]: ((k6_partfun1 @ X54) = (k6_relat_1 @ X54))),
% 0.53/0.73      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.53/0.73  thf('83', plain,
% 0.53/0.73      (![X45 : $i]:
% 0.53/0.73         (m1_subset_1 @ (k6_partfun1 @ X45) @ 
% 0.53/0.73          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X45)))),
% 0.53/0.73      inference('demod', [status(thm)], ['81', '82'])).
% 0.53/0.73  thf('84', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.53/0.73      inference('demod', [status(thm)], ['80', '83'])).
% 0.53/0.73  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 0.53/0.73  thf('85', plain, (![X25 : $i]: (v2_funct_1 @ (k6_relat_1 @ X25))),
% 0.53/0.73      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.53/0.73  thf('86', plain, (![X54 : $i]: ((k6_partfun1 @ X54) = (k6_relat_1 @ X54))),
% 0.53/0.73      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.53/0.73  thf('87', plain, (![X25 : $i]: (v2_funct_1 @ (k6_partfun1 @ X25))),
% 0.53/0.73      inference('demod', [status(thm)], ['85', '86'])).
% 0.53/0.73  thf('88', plain, (((sk_A) = (k1_xboole_0))),
% 0.53/0.73      inference('demod', [status(thm)], ['62', '84', '87'])).
% 0.53/0.73  thf(t113_zfmisc_1, axiom,
% 0.53/0.73    (![A:$i,B:$i]:
% 0.53/0.73     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.53/0.73       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.53/0.73  thf('89', plain,
% 0.53/0.73      (![X4 : $i, X5 : $i]:
% 0.53/0.73         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 0.53/0.73      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.53/0.73  thf('90', plain,
% 0.53/0.73      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.53/0.73      inference('simplify', [status(thm)], ['89'])).
% 0.53/0.73  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.53/0.73  thf('91', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.73      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.53/0.73  thf('92', plain, (![X54 : $i]: ((k6_partfun1 @ X54) = (k6_relat_1 @ X54))),
% 0.53/0.73      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.53/0.73  thf('93', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.73      inference('demod', [status(thm)], ['91', '92'])).
% 0.53/0.73  thf(t150_relat_1, axiom,
% 0.53/0.73    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.53/0.73  thf('94', plain,
% 0.53/0.73      (![X19 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X19) = (k1_xboole_0))),
% 0.53/0.73      inference('cnf', [status(esa)], [t150_relat_1])).
% 0.53/0.73  thf('95', plain, (((k1_xboole_0) = (sk_C))),
% 0.53/0.73      inference('demod', [status(thm)], ['40', '88', '90', '93', '94'])).
% 0.53/0.73  thf('96', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.73      inference('demod', [status(thm)], ['91', '92'])).
% 0.53/0.73  thf('97', plain, (![X25 : $i]: (v2_funct_1 @ (k6_partfun1 @ X25))),
% 0.53/0.73      inference('demod', [status(thm)], ['85', '86'])).
% 0.53/0.73  thf('98', plain, ((v2_funct_1 @ k1_xboole_0)),
% 0.53/0.73      inference('sup+', [status(thm)], ['96', '97'])).
% 0.53/0.73  thf('99', plain, ($false),
% 0.53/0.73      inference('demod', [status(thm)], ['35', '95', '98'])).
% 0.53/0.73  
% 0.53/0.73  % SZS output end Refutation
% 0.53/0.73  
% 0.53/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jhaTdaeBrp

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:32 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 114 expanded)
%              Number of leaves         :   34 (  48 expanded)
%              Depth                    :   15
%              Number of atoms          :  720 (1791 expanded)
%              Number of equality atoms :   24 (  51 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('0',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ X10 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf(cc2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X11: $i] :
      ( ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_funct_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['3','4'])).

thf(t37_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ~ ( ( B != k1_xboole_0 )
          & ? [D: $i] :
              ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
              & ( v1_funct_2 @ D @ B @ A )
              & ( v1_funct_1 @ D ) )
          & ~ ( v2_funct_1 @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ~ ( ( B != k1_xboole_0 )
            & ? [D: $i] :
                ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
                & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
                & ( v1_funct_2 @ D @ B @ A )
                & ( v1_funct_1 @ D ) )
            & ~ ( v2_funct_1 @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t37_funct_2])).

thf('6',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('12',plain,(
    ! [X25: $i] :
      ( ( k6_partfun1 @ X25 )
      = ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('13',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X18 @ X19 @ X21 @ X22 @ X17 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('23',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( X13 = X16 )
      | ~ ( r2_relset_1 @ X14 @ X15 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','24'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('26',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('27',plain,(
    ! [X25: $i] :
      ( ( k6_partfun1 @ X25 )
      = ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,(
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

thf('31',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X29 @ X27 @ X27 @ X28 @ X30 @ X26 ) )
      | ( v2_funct_1 @ X30 )
      | ( X28 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X29 @ X27 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('37',plain,(
    ! [X12: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37','38','39','40'])).

thf('42',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['41','42'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('44',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('45',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    r1_tarski @ sk_C @ k1_xboole_0 ),
    inference(demod,[status(thm)],['10','43','45'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('48',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_xboole_0 @ sk_C ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['7','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jhaTdaeBrp
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:54:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.66  % Solved by: fo/fo7.sh
% 0.45/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.66  % done 330 iterations in 0.206s
% 0.45/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.66  % SZS output start Refutation
% 0.45/0.66  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.45/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.66  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.66  thf(sk_D_type, type, sk_D: $i).
% 0.45/0.66  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.45/0.66  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.45/0.66  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.45/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.66  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.66  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.45/0.66  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.66  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.45/0.66  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.66  thf(cc1_funct_1, axiom,
% 0.45/0.66    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 0.45/0.66  thf('0', plain, (![X10 : $i]: ((v1_funct_1 @ X10) | ~ (v1_xboole_0 @ X10))),
% 0.45/0.66      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.45/0.66  thf(cc2_funct_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( v1_xboole_0 @ A ) & ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.66       ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) ))).
% 0.45/0.66  thf('1', plain,
% 0.45/0.66      (![X11 : $i]:
% 0.45/0.66         ((v2_funct_1 @ X11)
% 0.45/0.66          | ~ (v1_funct_1 @ X11)
% 0.45/0.66          | ~ (v1_relat_1 @ X11)
% 0.45/0.66          | ~ (v1_xboole_0 @ X11))),
% 0.45/0.66      inference('cnf', [status(esa)], [cc2_funct_1])).
% 0.45/0.66  thf('2', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (v1_xboole_0 @ X0)
% 0.45/0.66          | ~ (v1_xboole_0 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | (v2_funct_1 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['0', '1'])).
% 0.45/0.66  thf('3', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((v2_funct_1 @ X0) | ~ (v1_relat_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['2'])).
% 0.45/0.66  thf(cc1_relat_1, axiom,
% 0.45/0.66    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.45/0.66  thf('4', plain, (![X9 : $i]: ((v1_relat_1 @ X9) | ~ (v1_xboole_0 @ X9))),
% 0.45/0.66      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.45/0.66  thf('5', plain, (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v2_funct_1 @ X0))),
% 0.45/0.66      inference('clc', [status(thm)], ['3', '4'])).
% 0.45/0.66  thf(t37_funct_2, conjecture,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.66         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.66       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.45/0.66            ( ?[D:$i]:
% 0.45/0.66              ( ( r2_relset_1 @
% 0.45/0.66                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.45/0.66                  ( k6_partfun1 @ A ) ) & 
% 0.45/0.66                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) & 
% 0.45/0.66                ( v1_funct_2 @ D @ B @ A ) & ( v1_funct_1 @ D ) ) ) & 
% 0.45/0.66            ( ~( v2_funct_1 @ C ) ) ) ) ))).
% 0.45/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.66    (~( ![A:$i,B:$i,C:$i]:
% 0.45/0.66        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.66            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.66          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.45/0.66               ( ?[D:$i]:
% 0.45/0.66                 ( ( r2_relset_1 @
% 0.45/0.66                     A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.45/0.66                     ( k6_partfun1 @ A ) ) & 
% 0.45/0.66                   ( m1_subset_1 @
% 0.45/0.66                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) & 
% 0.45/0.66                   ( v1_funct_2 @ D @ B @ A ) & ( v1_funct_1 @ D ) ) ) & 
% 0.45/0.66               ( ~( v2_funct_1 @ C ) ) ) ) ) )),
% 0.45/0.66    inference('cnf.neg', [status(esa)], [t37_funct_2])).
% 0.45/0.66  thf('6', plain, (~ (v2_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('7', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.45/0.66      inference('sup-', [status(thm)], ['5', '6'])).
% 0.45/0.66  thf('8', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(t3_subset, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.66  thf('9', plain,
% 0.45/0.66      (![X6 : $i, X7 : $i]:
% 0.45/0.66         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.66  thf('10', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.45/0.66      inference('sup-', [status(thm)], ['8', '9'])).
% 0.45/0.66  thf('11', plain,
% 0.45/0.66      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.45/0.66        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.45/0.66        (k6_partfun1 @ sk_A))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(redefinition_k6_partfun1, axiom,
% 0.45/0.66    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.45/0.66  thf('12', plain, (![X25 : $i]: ((k6_partfun1 @ X25) = (k6_relat_1 @ X25))),
% 0.45/0.66      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.45/0.66  thf('13', plain,
% 0.45/0.66      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.45/0.66        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.45/0.66        (k6_relat_1 @ sk_A))),
% 0.45/0.66      inference('demod', [status(thm)], ['11', '12'])).
% 0.45/0.66  thf('14', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('15', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(dt_k1_partfun1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.45/0.66     ( ( ( v1_funct_1 @ E ) & 
% 0.45/0.66         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.45/0.66         ( v1_funct_1 @ F ) & 
% 0.45/0.66         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.45/0.66       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.45/0.66         ( m1_subset_1 @
% 0.45/0.66           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.45/0.66           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.45/0.66  thf('16', plain,
% 0.45/0.66      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.45/0.66          | ~ (v1_funct_1 @ X17)
% 0.45/0.66          | ~ (v1_funct_1 @ X20)
% 0.45/0.66          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.45/0.66          | (m1_subset_1 @ (k1_partfun1 @ X18 @ X19 @ X21 @ X22 @ X17 @ X20) @ 
% 0.45/0.66             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X22))))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.45/0.66  thf('17', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.66         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.45/0.66           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.45/0.66          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.45/0.66          | ~ (v1_funct_1 @ X1)
% 0.45/0.66          | ~ (v1_funct_1 @ sk_C))),
% 0.45/0.66      inference('sup-', [status(thm)], ['15', '16'])).
% 0.45/0.66  thf('18', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('19', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.66         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.45/0.66           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.45/0.66          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.45/0.66          | ~ (v1_funct_1 @ X1))),
% 0.45/0.66      inference('demod', [status(thm)], ['17', '18'])).
% 0.45/0.66  thf('20', plain,
% 0.45/0.66      ((~ (v1_funct_1 @ sk_D)
% 0.45/0.66        | (m1_subset_1 @ 
% 0.45/0.66           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.45/0.66           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['14', '19'])).
% 0.45/0.66  thf('21', plain, ((v1_funct_1 @ sk_D)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('22', plain,
% 0.45/0.66      ((m1_subset_1 @ 
% 0.45/0.66        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.45/0.66        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.45/0.66      inference('demod', [status(thm)], ['20', '21'])).
% 0.45/0.66  thf(redefinition_r2_relset_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.66     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.45/0.66         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.66       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.45/0.66  thf('23', plain,
% 0.45/0.66      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.45/0.66          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.45/0.66          | ((X13) = (X16))
% 0.45/0.66          | ~ (r2_relset_1 @ X14 @ X15 @ X13 @ X16))),
% 0.45/0.66      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.45/0.66  thf('24', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.45/0.66             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.45/0.66          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.45/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['22', '23'])).
% 0.45/0.66  thf('25', plain,
% 0.45/0.66      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 0.45/0.66           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.45/0.66        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.45/0.66            = (k6_relat_1 @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['13', '24'])).
% 0.45/0.66  thf(dt_k6_partfun1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( m1_subset_1 @
% 0.45/0.66         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.45/0.66       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.45/0.66  thf('26', plain,
% 0.45/0.66      (![X24 : $i]:
% 0.45/0.66         (m1_subset_1 @ (k6_partfun1 @ X24) @ 
% 0.45/0.66          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.45/0.66  thf('27', plain, (![X25 : $i]: ((k6_partfun1 @ X25) = (k6_relat_1 @ X25))),
% 0.45/0.66      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.45/0.66  thf('28', plain,
% 0.45/0.66      (![X24 : $i]:
% 0.45/0.66         (m1_subset_1 @ (k6_relat_1 @ X24) @ 
% 0.45/0.66          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))),
% 0.45/0.66      inference('demod', [status(thm)], ['26', '27'])).
% 0.45/0.66  thf('29', plain,
% 0.45/0.66      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.45/0.66         = (k6_relat_1 @ sk_A))),
% 0.45/0.66      inference('demod', [status(thm)], ['25', '28'])).
% 0.45/0.66  thf('30', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(t26_funct_2, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.66     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.45/0.66         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.66       ( ![E:$i]:
% 0.45/0.66         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.45/0.66             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.45/0.66           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 0.45/0.66             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 0.45/0.66               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 0.45/0.66  thf('31', plain,
% 0.45/0.66      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.45/0.66         (~ (v1_funct_1 @ X26)
% 0.45/0.66          | ~ (v1_funct_2 @ X26 @ X27 @ X28)
% 0.45/0.66          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.45/0.66          | ~ (v2_funct_1 @ (k1_partfun1 @ X29 @ X27 @ X27 @ X28 @ X30 @ X26))
% 0.45/0.66          | (v2_funct_1 @ X30)
% 0.45/0.66          | ((X28) = (k1_xboole_0))
% 0.45/0.66          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X27)))
% 0.45/0.66          | ~ (v1_funct_2 @ X30 @ X29 @ X27)
% 0.45/0.66          | ~ (v1_funct_1 @ X30))),
% 0.45/0.66      inference('cnf', [status(esa)], [t26_funct_2])).
% 0.45/0.66  thf('32', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.45/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.45/0.66          | ((sk_A) = (k1_xboole_0))
% 0.45/0.66          | (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.45/0.66          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.45/0.66          | ~ (v1_funct_1 @ sk_D))),
% 0.45/0.66      inference('sup-', [status(thm)], ['30', '31'])).
% 0.45/0.66  thf('33', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('34', plain, ((v1_funct_1 @ sk_D)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('35', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.45/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.45/0.66          | ((sk_A) = (k1_xboole_0))
% 0.45/0.66          | (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 0.45/0.66      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.45/0.66  thf('36', plain,
% 0.45/0.66      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 0.45/0.66        | (v2_funct_1 @ sk_C)
% 0.45/0.66        | ((sk_A) = (k1_xboole_0))
% 0.45/0.66        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.45/0.66        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.45/0.66        | ~ (v1_funct_1 @ sk_C))),
% 0.45/0.66      inference('sup-', [status(thm)], ['29', '35'])).
% 0.45/0.66  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 0.45/0.66  thf('37', plain, (![X12 : $i]: (v2_funct_1 @ (k6_relat_1 @ X12))),
% 0.45/0.66      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.45/0.66  thf('38', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('39', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('40', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('41', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.45/0.66      inference('demod', [status(thm)], ['36', '37', '38', '39', '40'])).
% 0.45/0.66  thf('42', plain, (~ (v2_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('43', plain, (((sk_A) = (k1_xboole_0))),
% 0.45/0.66      inference('clc', [status(thm)], ['41', '42'])).
% 0.45/0.66  thf(t113_zfmisc_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.45/0.66       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.45/0.66  thf('44', plain,
% 0.45/0.66      (![X4 : $i, X5 : $i]:
% 0.45/0.66         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.45/0.66  thf('45', plain,
% 0.45/0.66      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['44'])).
% 0.45/0.66  thf('46', plain, ((r1_tarski @ sk_C @ k1_xboole_0)),
% 0.45/0.66      inference('demod', [status(thm)], ['10', '43', '45'])).
% 0.45/0.66  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.45/0.66  thf('47', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.45/0.66      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.45/0.66  thf(t69_xboole_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.45/0.66       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.45/0.66  thf('48', plain,
% 0.45/0.66      (![X1 : $i, X2 : $i]:
% 0.45/0.66         (~ (r1_xboole_0 @ X1 @ X2)
% 0.45/0.66          | ~ (r1_tarski @ X1 @ X2)
% 0.45/0.66          | (v1_xboole_0 @ X1))),
% 0.45/0.66      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.45/0.66  thf('49', plain,
% 0.45/0.66      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['47', '48'])).
% 0.45/0.66  thf('50', plain, ((v1_xboole_0 @ sk_C)),
% 0.45/0.66      inference('sup-', [status(thm)], ['46', '49'])).
% 0.45/0.66  thf('51', plain, ($false), inference('demod', [status(thm)], ['7', '50'])).
% 0.45/0.66  
% 0.45/0.66  % SZS output end Refutation
% 0.45/0.66  
% 0.45/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

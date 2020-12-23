%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dJnoqoCRK6

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:30 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 116 expanded)
%              Number of leaves         :   34 (  48 expanded)
%              Depth                    :   15
%              Number of atoms          :  719 (1790 expanded)
%              Number of equality atoms :   20 (  47 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf('0',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_xboole_0 @ X6 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( v1_xboole_0 @ X8 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('4',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
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

thf('9',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X20 @ X21 @ X23 @ X24 @ X19 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('16',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( X14 = X17 )
      | ~ ( r2_relset_1 @ X15 @ X16 @ X14 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('19',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('20',plain,(
    ! [X25: $i] :
      ( ( k6_partfun1 @ X25 )
      = ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('21',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,(
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

thf('24',plain,(
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

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('30',plain,(
    ! [X13: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('31',plain,(
    ! [X25: $i] :
      ( ( k6_partfun1 @ X25 )
      = ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('32',plain,(
    ! [X13: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X13 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','32','33','34','35'])).

thf('37',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['36','37'])).

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

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('41',plain,(
    ! [X3: $i] :
      ( r1_xboole_0 @ X3 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('42',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['5','38','44'])).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('46',plain,(
    ! [X11: $i] :
      ( ( v1_funct_1 @ X11 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf(cc2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) ) ) )).

thf('47',plain,(
    ! [X12: $i] :
      ( ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('50',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_funct_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    v2_funct_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','51'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['0','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dJnoqoCRK6
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:28:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.46/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.66  % Solved by: fo/fo7.sh
% 0.46/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.66  % done 275 iterations in 0.213s
% 0.46/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.66  % SZS output start Refutation
% 0.46/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.66  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.46/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.66  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.46/0.66  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.66  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.66  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.66  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.46/0.66  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.46/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.66  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.66  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.66  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.46/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.66  thf(t37_funct_2, conjecture,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.66         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.66       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.46/0.66            ( ?[D:$i]:
% 0.46/0.66              ( ( r2_relset_1 @
% 0.46/0.66                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.46/0.66                  ( k6_partfun1 @ A ) ) & 
% 0.46/0.66                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) & 
% 0.46/0.66                ( v1_funct_2 @ D @ B @ A ) & ( v1_funct_1 @ D ) ) ) & 
% 0.46/0.66            ( ~( v2_funct_1 @ C ) ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.66    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.66        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.66            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.66          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.46/0.66               ( ?[D:$i]:
% 0.46/0.66                 ( ( r2_relset_1 @
% 0.46/0.66                     A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.46/0.66                     ( k6_partfun1 @ A ) ) & 
% 0.46/0.66                   ( m1_subset_1 @
% 0.46/0.66                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) & 
% 0.46/0.66                   ( v1_funct_2 @ D @ B @ A ) & ( v1_funct_1 @ D ) ) ) & 
% 0.46/0.66               ( ~( v2_funct_1 @ C ) ) ) ) ) )),
% 0.46/0.66    inference('cnf.neg', [status(esa)], [t37_funct_2])).
% 0.46/0.66  thf('0', plain, (~ (v2_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(fc4_zfmisc_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.46/0.66  thf('1', plain,
% 0.46/0.66      (![X6 : $i, X7 : $i]:
% 0.46/0.66         (~ (v1_xboole_0 @ X6) | (v1_xboole_0 @ (k2_zfmisc_1 @ X6 @ X7)))),
% 0.46/0.66      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 0.46/0.66  thf('2', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(cc1_subset_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( v1_xboole_0 @ A ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.46/0.66  thf('3', plain,
% 0.46/0.66      (![X8 : $i, X9 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.46/0.66          | (v1_xboole_0 @ X8)
% 0.46/0.66          | ~ (v1_xboole_0 @ X9))),
% 0.46/0.66      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.46/0.66  thf('4', plain,
% 0.46/0.66      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 0.46/0.66      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.66  thf('5', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C))),
% 0.46/0.66      inference('sup-', [status(thm)], ['1', '4'])).
% 0.46/0.66  thf('6', plain,
% 0.46/0.66      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.46/0.66        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.46/0.66        (k6_partfun1 @ sk_A))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('7', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('8', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(dt_k1_partfun1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.46/0.66     ( ( ( v1_funct_1 @ E ) & 
% 0.46/0.66         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.46/0.66         ( v1_funct_1 @ F ) & 
% 0.46/0.66         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.46/0.66       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.46/0.66         ( m1_subset_1 @
% 0.46/0.66           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.46/0.66           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.46/0.66  thf('9', plain,
% 0.46/0.66      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.46/0.66          | ~ (v1_funct_1 @ X19)
% 0.46/0.66          | ~ (v1_funct_1 @ X22)
% 0.46/0.66          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.46/0.66          | (m1_subset_1 @ (k1_partfun1 @ X20 @ X21 @ X23 @ X24 @ X19 @ X22) @ 
% 0.46/0.66             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X24))))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.46/0.66  thf('10', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.46/0.66           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.46/0.66          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.46/0.66          | ~ (v1_funct_1 @ X1)
% 0.46/0.66          | ~ (v1_funct_1 @ sk_C))),
% 0.46/0.66      inference('sup-', [status(thm)], ['8', '9'])).
% 0.46/0.66  thf('11', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('12', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.46/0.66           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.46/0.66          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.46/0.66          | ~ (v1_funct_1 @ X1))),
% 0.46/0.66      inference('demod', [status(thm)], ['10', '11'])).
% 0.46/0.66  thf('13', plain,
% 0.46/0.66      ((~ (v1_funct_1 @ sk_D)
% 0.46/0.66        | (m1_subset_1 @ 
% 0.46/0.66           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.46/0.66           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['7', '12'])).
% 0.46/0.66  thf('14', plain, ((v1_funct_1 @ sk_D)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('15', plain,
% 0.46/0.66      ((m1_subset_1 @ 
% 0.46/0.66        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.46/0.66        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['13', '14'])).
% 0.46/0.66  thf(redefinition_r2_relset_1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.66     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.46/0.66         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.66       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.46/0.66  thf('16', plain,
% 0.46/0.66      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.46/0.66          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.46/0.66          | ((X14) = (X17))
% 0.46/0.66          | ~ (r2_relset_1 @ X15 @ X16 @ X14 @ X17))),
% 0.46/0.66      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.46/0.66  thf('17', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.46/0.66             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.46/0.66          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.46/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['15', '16'])).
% 0.46/0.66  thf('18', plain,
% 0.46/0.66      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.46/0.66           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.46/0.66        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.46/0.66            = (k6_partfun1 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['6', '17'])).
% 0.46/0.66  thf(t29_relset_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( m1_subset_1 @
% 0.46/0.66       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.46/0.66  thf('19', plain,
% 0.46/0.66      (![X18 : $i]:
% 0.46/0.66         (m1_subset_1 @ (k6_relat_1 @ X18) @ 
% 0.46/0.66          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.46/0.66  thf(redefinition_k6_partfun1, axiom,
% 0.46/0.66    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.46/0.66  thf('20', plain, (![X25 : $i]: ((k6_partfun1 @ X25) = (k6_relat_1 @ X25))),
% 0.46/0.66      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.46/0.66  thf('21', plain,
% 0.46/0.66      (![X18 : $i]:
% 0.46/0.66         (m1_subset_1 @ (k6_partfun1 @ X18) @ 
% 0.46/0.66          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))),
% 0.46/0.66      inference('demod', [status(thm)], ['19', '20'])).
% 0.46/0.66  thf('22', plain,
% 0.46/0.66      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.46/0.66         = (k6_partfun1 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['18', '21'])).
% 0.46/0.66  thf('23', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(t26_funct_2, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.66     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.46/0.66         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.66       ( ![E:$i]:
% 0.46/0.66         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.46/0.66             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.46/0.66           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 0.46/0.66             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 0.46/0.66               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 0.46/0.66  thf('24', plain,
% 0.46/0.66      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.46/0.66         (~ (v1_funct_1 @ X26)
% 0.46/0.66          | ~ (v1_funct_2 @ X26 @ X27 @ X28)
% 0.46/0.66          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.46/0.66          | ~ (v2_funct_1 @ (k1_partfun1 @ X29 @ X27 @ X27 @ X28 @ X30 @ X26))
% 0.46/0.66          | (v2_funct_1 @ X30)
% 0.46/0.66          | ((X28) = (k1_xboole_0))
% 0.46/0.66          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X27)))
% 0.46/0.66          | ~ (v1_funct_2 @ X30 @ X29 @ X27)
% 0.46/0.66          | ~ (v1_funct_1 @ X30))),
% 0.46/0.66      inference('cnf', [status(esa)], [t26_funct_2])).
% 0.46/0.66  thf('25', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.46/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.46/0.66          | ((sk_A) = (k1_xboole_0))
% 0.46/0.66          | (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.46/0.66          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.46/0.66          | ~ (v1_funct_1 @ sk_D))),
% 0.46/0.66      inference('sup-', [status(thm)], ['23', '24'])).
% 0.46/0.66  thf('26', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('27', plain, ((v1_funct_1 @ sk_D)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('28', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.46/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.46/0.66          | ((sk_A) = (k1_xboole_0))
% 0.46/0.66          | (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 0.46/0.66      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.46/0.66  thf('29', plain,
% 0.46/0.66      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.46/0.66        | (v2_funct_1 @ sk_C)
% 0.46/0.66        | ((sk_A) = (k1_xboole_0))
% 0.46/0.66        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.46/0.66        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C))),
% 0.46/0.66      inference('sup-', [status(thm)], ['22', '28'])).
% 0.46/0.66  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 0.46/0.66  thf('30', plain, (![X13 : $i]: (v2_funct_1 @ (k6_relat_1 @ X13))),
% 0.46/0.66      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.46/0.66  thf('31', plain, (![X25 : $i]: ((k6_partfun1 @ X25) = (k6_relat_1 @ X25))),
% 0.46/0.66      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.46/0.66  thf('32', plain, (![X13 : $i]: (v2_funct_1 @ (k6_partfun1 @ X13))),
% 0.46/0.66      inference('demod', [status(thm)], ['30', '31'])).
% 0.46/0.66  thf('33', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('34', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('36', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['29', '32', '33', '34', '35'])).
% 0.46/0.66  thf('37', plain, (~ (v2_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('38', plain, (((sk_A) = (k1_xboole_0))),
% 0.46/0.66      inference('clc', [status(thm)], ['36', '37'])).
% 0.46/0.66  thf(d10_xboole_0, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.66  thf('39', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.46/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.66  thf('40', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.46/0.66      inference('simplify', [status(thm)], ['39'])).
% 0.46/0.66  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.46/0.66  thf('41', plain, (![X3 : $i]: (r1_xboole_0 @ X3 @ k1_xboole_0)),
% 0.46/0.66      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.46/0.66  thf(t69_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.46/0.66       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.46/0.66  thf('42', plain,
% 0.46/0.66      (![X4 : $i, X5 : $i]:
% 0.46/0.66         (~ (r1_xboole_0 @ X4 @ X5)
% 0.46/0.66          | ~ (r1_tarski @ X4 @ X5)
% 0.46/0.66          | (v1_xboole_0 @ X4))),
% 0.46/0.66      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.46/0.66  thf('43', plain,
% 0.46/0.66      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['41', '42'])).
% 0.46/0.66  thf('44', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.66      inference('sup-', [status(thm)], ['40', '43'])).
% 0.46/0.66  thf('45', plain, ((v1_xboole_0 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['5', '38', '44'])).
% 0.46/0.66  thf(cc1_funct_1, axiom,
% 0.46/0.66    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 0.46/0.66  thf('46', plain, (![X11 : $i]: ((v1_funct_1 @ X11) | ~ (v1_xboole_0 @ X11))),
% 0.46/0.66      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.46/0.66  thf(cc2_funct_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( v1_xboole_0 @ A ) & ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.66       ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) ))).
% 0.46/0.66  thf('47', plain,
% 0.46/0.66      (![X12 : $i]:
% 0.46/0.66         ((v2_funct_1 @ X12)
% 0.46/0.66          | ~ (v1_funct_1 @ X12)
% 0.46/0.66          | ~ (v1_relat_1 @ X12)
% 0.46/0.66          | ~ (v1_xboole_0 @ X12))),
% 0.46/0.66      inference('cnf', [status(esa)], [cc2_funct_1])).
% 0.46/0.66  thf('48', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_xboole_0 @ X0)
% 0.46/0.66          | ~ (v1_xboole_0 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | (v2_funct_1 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['46', '47'])).
% 0.46/0.66  thf('49', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((v2_funct_1 @ X0) | ~ (v1_relat_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['48'])).
% 0.46/0.66  thf(cc1_relat_1, axiom,
% 0.46/0.66    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.46/0.66  thf('50', plain, (![X10 : $i]: ((v1_relat_1 @ X10) | ~ (v1_xboole_0 @ X10))),
% 0.46/0.66      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.46/0.66  thf('51', plain, (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v2_funct_1 @ X0))),
% 0.46/0.66      inference('clc', [status(thm)], ['49', '50'])).
% 0.46/0.66  thf('52', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.66      inference('sup-', [status(thm)], ['45', '51'])).
% 0.46/0.66  thf('53', plain, ($false), inference('demod', [status(thm)], ['0', '52'])).
% 0.46/0.66  
% 0.46/0.66  % SZS output end Refutation
% 0.46/0.66  
% 0.46/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

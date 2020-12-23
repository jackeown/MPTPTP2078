%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.j0Q3hpKuQk

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:01 EST 2020

% Result     : Theorem 4.04s
% Output     : Refutation 4.04s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 263 expanded)
%              Number of leaves         :   40 (  95 expanded)
%              Depth                    :   13
%              Number of atoms          : 1214 (5212 expanded)
%              Number of equality atoms :   58 (  89 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('0',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('4',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('6',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ( v1_xboole_0 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k6_partfun1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k6_partfun1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('15',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('16',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( r2_relset_1 @ X20 @ X21 @ X19 @ X22 )
      | ( X19 != X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('17',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_relset_1 @ X20 @ X21 @ X22 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_relset_1 @ X1 @ X1 @ ( k6_partfun1 @ X1 ) @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X2 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( r2_relset_1 @ X2 @ X2 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t87_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( v3_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ ( k6_partfun1 @ A ) )
           => ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( v3_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ A )
              & ( v3_funct_2 @ C @ A @ A )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ ( k6_partfun1 @ A ) )
             => ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_funct_2])).

thf('22',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k2_funct_2 @ A @ B )
        = ( k2_funct_1 @ B ) ) ) )).

thf('24',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k2_funct_2 @ X33 @ X32 )
        = ( k2_funct_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) )
      | ~ ( v3_funct_2 @ X32 @ X33 @ X33 )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X33 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('25',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B )
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','29'])).

thf('31',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('35',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('38',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['31','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) )
        & ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A )
        & ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A )
        & ( m1_subset_1 @ ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ) )).

thf('41',plain,(
    ! [X28: $i,X29: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X28 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) )
      | ~ ( v3_funct_2 @ X29 @ X28 @ X28 )
      | ~ ( v1_funct_2 @ X29 @ X28 @ X28 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('42',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('48',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('49',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X13 ) ) )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('50',plain,
    ( ( v1_xboole_0 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['39','50'])).

thf('52',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_funct_2,axiom,(
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

thf('54',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( X38
        = ( k2_funct_1 @ X41 ) )
      | ~ ( r2_relset_1 @ X40 @ X40 @ ( k1_partfun1 @ X40 @ X39 @ X39 @ X40 @ X41 @ X38 ) @ ( k6_partfun1 @ X40 ) )
      | ( X39 = k1_xboole_0 )
      | ( X40 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X41 )
      | ( ( k2_relset_1 @ X40 @ X39 @ X41 )
       != X39 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) )
      | ~ ( v1_funct_2 @ X41 @ X40 @ X39 )
      | ~ ( v1_funct_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t36_funct_2])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('65',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('66',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) ) ) ) )).

thf('68',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_1 @ X23 )
      | ~ ( v3_funct_2 @ X23 @ X24 @ X25 )
      | ( v2_funct_2 @ X23 @ X25 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('69',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['69','70','71'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('73',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v2_funct_2 @ X27 @ X26 )
      | ( ( k2_relat_1 @ X27 )
        = X26 )
      | ~ ( v5_relat_1 @ X27 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('74',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('76',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('77',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('79',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v5_relat_1 @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('80',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['74','77','80'])).

thf('82',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['66','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_1 @ X23 )
      | ~ ( v3_funct_2 @ X23 @ X24 @ X25 )
      | ( v2_funct_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('85',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,
    ( ( sk_A != sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','61','62','63','82','88'])).

thf('90',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','29'])).

thf('92',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_relset_1 @ X20 @ X21 @ X22 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('95',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['92','95'])).

thf('97',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('98',plain,(
    $false ),
    inference(demod,[status(thm)],['51','96','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.j0Q3hpKuQk
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:21:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 4.04/4.26  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.04/4.26  % Solved by: fo/fo7.sh
% 4.04/4.26  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.04/4.26  % done 8170 iterations in 3.803s
% 4.04/4.26  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.04/4.26  % SZS output start Refutation
% 4.04/4.26  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 4.04/4.26  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 4.04/4.26  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 4.04/4.26  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.04/4.26  thf(sk_B_type, type, sk_B: $i).
% 4.04/4.26  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.04/4.26  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 4.04/4.26  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 4.04/4.26  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 4.04/4.26  thf(sk_A_type, type, sk_A: $i).
% 4.04/4.26  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.04/4.26  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 4.04/4.26  thf(sk_C_type, type, sk_C: $i).
% 4.04/4.26  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.04/4.26  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 4.04/4.26  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 4.04/4.26  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.04/4.26  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.04/4.26  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 4.04/4.26  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.04/4.26  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 4.04/4.26  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 4.04/4.26  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.04/4.26  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.04/4.26  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 4.04/4.26  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.04/4.26      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.04/4.26  thf(t8_boole, axiom,
% 4.04/4.26    (![A:$i,B:$i]:
% 4.04/4.26     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 4.04/4.26  thf('1', plain,
% 4.04/4.26      (![X0 : $i, X1 : $i]:
% 4.04/4.26         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 4.04/4.26      inference('cnf', [status(esa)], [t8_boole])).
% 4.04/4.26  thf('2', plain,
% 4.04/4.26      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 4.04/4.26      inference('sup-', [status(thm)], ['0', '1'])).
% 4.04/4.26  thf(t113_zfmisc_1, axiom,
% 4.04/4.26    (![A:$i,B:$i]:
% 4.04/4.26     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 4.04/4.26       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 4.04/4.26  thf('3', plain,
% 4.04/4.26      (![X3 : $i, X4 : $i]:
% 4.04/4.26         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 4.04/4.26      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 4.04/4.26  thf('4', plain,
% 4.04/4.26      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 4.04/4.26      inference('simplify', [status(thm)], ['3'])).
% 4.04/4.26  thf('5', plain,
% 4.04/4.26      (![X0 : $i, X1 : $i]:
% 4.04/4.26         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 4.04/4.26      inference('sup+', [status(thm)], ['2', '4'])).
% 4.04/4.26  thf(dt_k6_partfun1, axiom,
% 4.04/4.26    (![A:$i]:
% 4.04/4.26     ( ( m1_subset_1 @
% 4.04/4.26         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 4.04/4.26       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 4.04/4.26  thf('6', plain,
% 4.04/4.26      (![X31 : $i]:
% 4.04/4.26         (m1_subset_1 @ (k6_partfun1 @ X31) @ 
% 4.04/4.26          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 4.04/4.26      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 4.04/4.26  thf(cc1_subset_1, axiom,
% 4.04/4.26    (![A:$i]:
% 4.04/4.26     ( ( v1_xboole_0 @ A ) =>
% 4.04/4.26       ( ![B:$i]:
% 4.04/4.26         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 4.04/4.26  thf('7', plain,
% 4.04/4.26      (![X5 : $i, X6 : $i]:
% 4.04/4.26         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 4.04/4.26          | (v1_xboole_0 @ X5)
% 4.04/4.26          | ~ (v1_xboole_0 @ X6))),
% 4.04/4.26      inference('cnf', [status(esa)], [cc1_subset_1])).
% 4.04/4.26  thf('8', plain,
% 4.04/4.26      (![X0 : $i]:
% 4.04/4.26         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X0))
% 4.04/4.26          | (v1_xboole_0 @ (k6_partfun1 @ X0)))),
% 4.04/4.26      inference('sup-', [status(thm)], ['6', '7'])).
% 4.04/4.26  thf('9', plain,
% 4.04/4.26      (![X0 : $i]:
% 4.04/4.26         (~ (v1_xboole_0 @ k1_xboole_0)
% 4.04/4.26          | ~ (v1_xboole_0 @ X0)
% 4.04/4.26          | (v1_xboole_0 @ (k6_partfun1 @ X0)))),
% 4.04/4.26      inference('sup-', [status(thm)], ['5', '8'])).
% 4.04/4.26  thf('10', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.04/4.26      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.04/4.26  thf('11', plain,
% 4.04/4.26      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k6_partfun1 @ X0)))),
% 4.04/4.26      inference('demod', [status(thm)], ['9', '10'])).
% 4.04/4.26  thf('12', plain,
% 4.04/4.26      (![X0 : $i, X1 : $i]:
% 4.04/4.26         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 4.04/4.26      inference('cnf', [status(esa)], [t8_boole])).
% 4.04/4.26  thf('13', plain,
% 4.04/4.26      (![X0 : $i, X1 : $i]:
% 4.04/4.26         (~ (v1_xboole_0 @ X0)
% 4.04/4.26          | ((k6_partfun1 @ X0) = (X1))
% 4.04/4.26          | ~ (v1_xboole_0 @ X1))),
% 4.04/4.26      inference('sup-', [status(thm)], ['11', '12'])).
% 4.04/4.26  thf('14', plain,
% 4.04/4.26      (![X0 : $i, X1 : $i]:
% 4.04/4.26         (~ (v1_xboole_0 @ X0)
% 4.04/4.26          | ((k6_partfun1 @ X0) = (X1))
% 4.04/4.26          | ~ (v1_xboole_0 @ X1))),
% 4.04/4.26      inference('sup-', [status(thm)], ['11', '12'])).
% 4.04/4.26  thf('15', plain,
% 4.04/4.26      (![X31 : $i]:
% 4.04/4.26         (m1_subset_1 @ (k6_partfun1 @ X31) @ 
% 4.04/4.26          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 4.04/4.26      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 4.04/4.26  thf(redefinition_r2_relset_1, axiom,
% 4.04/4.26    (![A:$i,B:$i,C:$i,D:$i]:
% 4.04/4.26     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.04/4.26         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.04/4.26       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 4.04/4.26  thf('16', plain,
% 4.04/4.26      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 4.04/4.26         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 4.04/4.26          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 4.04/4.26          | (r2_relset_1 @ X20 @ X21 @ X19 @ X22)
% 4.04/4.26          | ((X19) != (X22)))),
% 4.04/4.26      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 4.04/4.26  thf('17', plain,
% 4.04/4.26      (![X20 : $i, X21 : $i, X22 : $i]:
% 4.04/4.26         ((r2_relset_1 @ X20 @ X21 @ X22 @ X22)
% 4.04/4.26          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 4.04/4.26      inference('simplify', [status(thm)], ['16'])).
% 4.04/4.26  thf('18', plain,
% 4.04/4.26      (![X0 : $i]:
% 4.04/4.26         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 4.04/4.26      inference('sup-', [status(thm)], ['15', '17'])).
% 4.04/4.26  thf('19', plain,
% 4.04/4.26      (![X0 : $i, X1 : $i]:
% 4.04/4.26         ((r2_relset_1 @ X1 @ X1 @ (k6_partfun1 @ X1) @ X0)
% 4.04/4.26          | ~ (v1_xboole_0 @ X0)
% 4.04/4.26          | ~ (v1_xboole_0 @ X1))),
% 4.04/4.26      inference('sup+', [status(thm)], ['14', '18'])).
% 4.04/4.26  thf('20', plain,
% 4.04/4.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.04/4.26         ((r2_relset_1 @ X2 @ X2 @ X0 @ X1)
% 4.04/4.26          | ~ (v1_xboole_0 @ X0)
% 4.04/4.26          | ~ (v1_xboole_0 @ X2)
% 4.04/4.26          | ~ (v1_xboole_0 @ X2)
% 4.04/4.26          | ~ (v1_xboole_0 @ X1))),
% 4.04/4.26      inference('sup+', [status(thm)], ['13', '19'])).
% 4.04/4.26  thf('21', plain,
% 4.04/4.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.04/4.26         (~ (v1_xboole_0 @ X1)
% 4.04/4.26          | ~ (v1_xboole_0 @ X2)
% 4.04/4.26          | ~ (v1_xboole_0 @ X0)
% 4.04/4.26          | (r2_relset_1 @ X2 @ X2 @ X0 @ X1))),
% 4.04/4.26      inference('simplify', [status(thm)], ['20'])).
% 4.04/4.26  thf(t87_funct_2, conjecture,
% 4.04/4.26    (![A:$i,B:$i]:
% 4.04/4.26     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 4.04/4.26         ( v3_funct_2 @ B @ A @ A ) & 
% 4.04/4.26         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 4.04/4.26       ( ![C:$i]:
% 4.04/4.26         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 4.04/4.26             ( v3_funct_2 @ C @ A @ A ) & 
% 4.04/4.26             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 4.04/4.26           ( ( r2_relset_1 @
% 4.04/4.26               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 4.04/4.26               ( k6_partfun1 @ A ) ) =>
% 4.04/4.26             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 4.04/4.26  thf(zf_stmt_0, negated_conjecture,
% 4.04/4.26    (~( ![A:$i,B:$i]:
% 4.04/4.26        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 4.04/4.26            ( v3_funct_2 @ B @ A @ A ) & 
% 4.04/4.26            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 4.04/4.26          ( ![C:$i]:
% 4.04/4.26            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 4.04/4.26                ( v3_funct_2 @ C @ A @ A ) & 
% 4.04/4.26                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 4.04/4.26              ( ( r2_relset_1 @
% 4.04/4.26                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 4.04/4.26                  ( k6_partfun1 @ A ) ) =>
% 4.04/4.26                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 4.04/4.26    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 4.04/4.26  thf('22', plain,
% 4.04/4.26      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B))),
% 4.04/4.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.04/4.26  thf('23', plain,
% 4.04/4.26      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.04/4.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.04/4.26  thf(redefinition_k2_funct_2, axiom,
% 4.04/4.26    (![A:$i,B:$i]:
% 4.04/4.26     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 4.04/4.26         ( v3_funct_2 @ B @ A @ A ) & 
% 4.04/4.26         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 4.04/4.26       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 4.04/4.26  thf('24', plain,
% 4.04/4.26      (![X32 : $i, X33 : $i]:
% 4.04/4.26         (((k2_funct_2 @ X33 @ X32) = (k2_funct_1 @ X32))
% 4.04/4.26          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))
% 4.04/4.26          | ~ (v3_funct_2 @ X32 @ X33 @ X33)
% 4.04/4.26          | ~ (v1_funct_2 @ X32 @ X33 @ X33)
% 4.04/4.26          | ~ (v1_funct_1 @ X32))),
% 4.04/4.26      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 4.04/4.26  thf('25', plain,
% 4.04/4.26      ((~ (v1_funct_1 @ sk_B)
% 4.04/4.26        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 4.04/4.26        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 4.04/4.26        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 4.04/4.26      inference('sup-', [status(thm)], ['23', '24'])).
% 4.04/4.26  thf('26', plain, ((v1_funct_1 @ sk_B)),
% 4.04/4.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.04/4.26  thf('27', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 4.04/4.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.04/4.26  thf('28', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 4.04/4.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.04/4.26  thf('29', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 4.04/4.26      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 4.04/4.26  thf('30', plain,
% 4.04/4.26      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 4.04/4.26      inference('demod', [status(thm)], ['22', '29'])).
% 4.04/4.26  thf('31', plain,
% 4.04/4.26      ((~ (v1_xboole_0 @ sk_C)
% 4.04/4.26        | ~ (v1_xboole_0 @ sk_A)
% 4.04/4.26        | ~ (v1_xboole_0 @ (k2_funct_1 @ sk_B)))),
% 4.04/4.26      inference('sup-', [status(thm)], ['21', '30'])).
% 4.04/4.26  thf('32', plain,
% 4.04/4.26      (![X0 : $i, X1 : $i]:
% 4.04/4.26         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 4.04/4.26      inference('sup+', [status(thm)], ['2', '4'])).
% 4.04/4.26  thf('33', plain,
% 4.04/4.26      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.04/4.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.04/4.26  thf('34', plain,
% 4.04/4.26      (![X5 : $i, X6 : $i]:
% 4.04/4.26         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 4.04/4.26          | (v1_xboole_0 @ X5)
% 4.04/4.26          | ~ (v1_xboole_0 @ X6))),
% 4.04/4.26      inference('cnf', [status(esa)], [cc1_subset_1])).
% 4.04/4.26  thf('35', plain,
% 4.04/4.26      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_xboole_0 @ sk_C))),
% 4.04/4.26      inference('sup-', [status(thm)], ['33', '34'])).
% 4.04/4.26  thf('36', plain,
% 4.04/4.26      ((~ (v1_xboole_0 @ k1_xboole_0)
% 4.04/4.26        | ~ (v1_xboole_0 @ sk_A)
% 4.04/4.26        | (v1_xboole_0 @ sk_C))),
% 4.04/4.26      inference('sup-', [status(thm)], ['32', '35'])).
% 4.04/4.26  thf('37', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.04/4.26      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.04/4.26  thf('38', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C))),
% 4.04/4.26      inference('demod', [status(thm)], ['36', '37'])).
% 4.04/4.26  thf('39', plain,
% 4.04/4.26      ((~ (v1_xboole_0 @ (k2_funct_1 @ sk_B)) | ~ (v1_xboole_0 @ sk_A))),
% 4.04/4.26      inference('clc', [status(thm)], ['31', '38'])).
% 4.04/4.26  thf('40', plain,
% 4.04/4.26      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.04/4.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.04/4.26  thf(dt_k2_funct_2, axiom,
% 4.04/4.26    (![A:$i,B:$i]:
% 4.04/4.26     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 4.04/4.26         ( v3_funct_2 @ B @ A @ A ) & 
% 4.04/4.26         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 4.04/4.26       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 4.04/4.26         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 4.04/4.26         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 4.04/4.26         ( m1_subset_1 @
% 4.04/4.26           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 4.04/4.26  thf('41', plain,
% 4.04/4.26      (![X28 : $i, X29 : $i]:
% 4.04/4.26         ((m1_subset_1 @ (k2_funct_2 @ X28 @ X29) @ 
% 4.04/4.26           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))
% 4.04/4.26          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))
% 4.04/4.26          | ~ (v3_funct_2 @ X29 @ X28 @ X28)
% 4.04/4.26          | ~ (v1_funct_2 @ X29 @ X28 @ X28)
% 4.04/4.26          | ~ (v1_funct_1 @ X29))),
% 4.04/4.26      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 4.04/4.26  thf('42', plain,
% 4.04/4.26      ((~ (v1_funct_1 @ sk_B)
% 4.04/4.26        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 4.04/4.26        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 4.04/4.26        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 4.04/4.26           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 4.04/4.26      inference('sup-', [status(thm)], ['40', '41'])).
% 4.04/4.26  thf('43', plain, ((v1_funct_1 @ sk_B)),
% 4.04/4.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.04/4.26  thf('44', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 4.04/4.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.04/4.26  thf('45', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 4.04/4.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.04/4.26  thf('46', plain,
% 4.04/4.26      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 4.04/4.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.04/4.26      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 4.04/4.26  thf('47', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 4.04/4.26      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 4.04/4.26  thf('48', plain,
% 4.04/4.26      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 4.04/4.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.04/4.26      inference('demod', [status(thm)], ['46', '47'])).
% 4.04/4.26  thf(cc4_relset_1, axiom,
% 4.04/4.26    (![A:$i,B:$i]:
% 4.04/4.26     ( ( v1_xboole_0 @ A ) =>
% 4.04/4.26       ( ![C:$i]:
% 4.04/4.26         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 4.04/4.26           ( v1_xboole_0 @ C ) ) ) ))).
% 4.04/4.26  thf('49', plain,
% 4.04/4.26      (![X13 : $i, X14 : $i, X15 : $i]:
% 4.04/4.26         (~ (v1_xboole_0 @ X13)
% 4.04/4.26          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X13)))
% 4.04/4.26          | (v1_xboole_0 @ X14))),
% 4.04/4.26      inference('cnf', [status(esa)], [cc4_relset_1])).
% 4.04/4.26  thf('50', plain,
% 4.04/4.26      (((v1_xboole_0 @ (k2_funct_1 @ sk_B)) | ~ (v1_xboole_0 @ sk_A))),
% 4.04/4.26      inference('sup-', [status(thm)], ['48', '49'])).
% 4.04/4.26  thf('51', plain, (~ (v1_xboole_0 @ sk_A)),
% 4.04/4.26      inference('clc', [status(thm)], ['39', '50'])).
% 4.04/4.26  thf('52', plain,
% 4.04/4.26      ((r2_relset_1 @ sk_A @ sk_A @ 
% 4.04/4.26        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 4.04/4.26        (k6_partfun1 @ sk_A))),
% 4.04/4.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.04/4.26  thf('53', plain,
% 4.04/4.26      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.04/4.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.04/4.26  thf(t36_funct_2, axiom,
% 4.04/4.26    (![A:$i,B:$i,C:$i]:
% 4.04/4.26     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.04/4.26         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.04/4.26       ( ![D:$i]:
% 4.04/4.26         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.04/4.26             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.04/4.26           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 4.04/4.26               ( r2_relset_1 @
% 4.04/4.26                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 4.04/4.26                 ( k6_partfun1 @ A ) ) & 
% 4.04/4.26               ( v2_funct_1 @ C ) ) =>
% 4.04/4.26             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 4.04/4.26               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 4.04/4.26  thf('54', plain,
% 4.04/4.26      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 4.04/4.26         (~ (v1_funct_1 @ X38)
% 4.04/4.26          | ~ (v1_funct_2 @ X38 @ X39 @ X40)
% 4.04/4.26          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 4.04/4.26          | ((X38) = (k2_funct_1 @ X41))
% 4.04/4.26          | ~ (r2_relset_1 @ X40 @ X40 @ 
% 4.04/4.26               (k1_partfun1 @ X40 @ X39 @ X39 @ X40 @ X41 @ X38) @ 
% 4.04/4.26               (k6_partfun1 @ X40))
% 4.04/4.26          | ((X39) = (k1_xboole_0))
% 4.04/4.26          | ((X40) = (k1_xboole_0))
% 4.04/4.26          | ~ (v2_funct_1 @ X41)
% 4.04/4.26          | ((k2_relset_1 @ X40 @ X39 @ X41) != (X39))
% 4.04/4.26          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39)))
% 4.04/4.26          | ~ (v1_funct_2 @ X41 @ X40 @ X39)
% 4.04/4.26          | ~ (v1_funct_1 @ X41))),
% 4.04/4.26      inference('cnf', [status(esa)], [t36_funct_2])).
% 4.04/4.26  thf('55', plain,
% 4.04/4.26      (![X0 : $i]:
% 4.04/4.26         (~ (v1_funct_1 @ X0)
% 4.04/4.26          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 4.04/4.26          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 4.04/4.26          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 4.04/4.26          | ~ (v2_funct_1 @ X0)
% 4.04/4.26          | ((sk_A) = (k1_xboole_0))
% 4.04/4.26          | ((sk_A) = (k1_xboole_0))
% 4.04/4.26          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 4.04/4.26               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 4.04/4.26               (k6_partfun1 @ sk_A))
% 4.04/4.26          | ((sk_C) = (k2_funct_1 @ X0))
% 4.04/4.26          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 4.04/4.26          | ~ (v1_funct_1 @ sk_C))),
% 4.04/4.26      inference('sup-', [status(thm)], ['53', '54'])).
% 4.04/4.26  thf('56', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 4.04/4.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.04/4.26  thf('57', plain, ((v1_funct_1 @ sk_C)),
% 4.04/4.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.04/4.26  thf('58', plain,
% 4.04/4.26      (![X0 : $i]:
% 4.04/4.26         (~ (v1_funct_1 @ X0)
% 4.04/4.26          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 4.04/4.26          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 4.04/4.26          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 4.04/4.26          | ~ (v2_funct_1 @ X0)
% 4.04/4.26          | ((sk_A) = (k1_xboole_0))
% 4.04/4.26          | ((sk_A) = (k1_xboole_0))
% 4.04/4.26          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 4.04/4.26               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 4.04/4.26               (k6_partfun1 @ sk_A))
% 4.04/4.26          | ((sk_C) = (k2_funct_1 @ X0)))),
% 4.04/4.26      inference('demod', [status(thm)], ['55', '56', '57'])).
% 4.04/4.26  thf('59', plain,
% 4.04/4.26      (![X0 : $i]:
% 4.04/4.26         (((sk_C) = (k2_funct_1 @ X0))
% 4.04/4.26          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 4.04/4.26               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 4.04/4.26               (k6_partfun1 @ sk_A))
% 4.04/4.26          | ((sk_A) = (k1_xboole_0))
% 4.04/4.26          | ~ (v2_funct_1 @ X0)
% 4.04/4.26          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 4.04/4.26          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 4.04/4.26          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 4.04/4.26          | ~ (v1_funct_1 @ X0))),
% 4.04/4.26      inference('simplify', [status(thm)], ['58'])).
% 4.04/4.26  thf('60', plain,
% 4.04/4.26      ((~ (v1_funct_1 @ sk_B)
% 4.04/4.26        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 4.04/4.26        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 4.04/4.26        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 4.04/4.26        | ~ (v2_funct_1 @ sk_B)
% 4.04/4.26        | ((sk_A) = (k1_xboole_0))
% 4.04/4.26        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 4.04/4.26      inference('sup-', [status(thm)], ['52', '59'])).
% 4.04/4.26  thf('61', plain, ((v1_funct_1 @ sk_B)),
% 4.04/4.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.04/4.26  thf('62', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 4.04/4.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.04/4.26  thf('63', plain,
% 4.04/4.26      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.04/4.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.04/4.26  thf('64', plain,
% 4.04/4.26      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.04/4.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.04/4.26  thf(redefinition_k2_relset_1, axiom,
% 4.04/4.26    (![A:$i,B:$i,C:$i]:
% 4.04/4.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.04/4.26       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 4.04/4.26  thf('65', plain,
% 4.04/4.26      (![X16 : $i, X17 : $i, X18 : $i]:
% 4.04/4.26         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 4.04/4.26          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 4.04/4.26      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.04/4.26  thf('66', plain,
% 4.04/4.26      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 4.04/4.26      inference('sup-', [status(thm)], ['64', '65'])).
% 4.04/4.26  thf('67', plain,
% 4.04/4.26      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.04/4.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.04/4.26  thf(cc2_funct_2, axiom,
% 4.04/4.26    (![A:$i,B:$i,C:$i]:
% 4.04/4.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.04/4.26       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 4.04/4.26         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 4.04/4.26  thf('68', plain,
% 4.04/4.26      (![X23 : $i, X24 : $i, X25 : $i]:
% 4.04/4.26         (~ (v1_funct_1 @ X23)
% 4.04/4.26          | ~ (v3_funct_2 @ X23 @ X24 @ X25)
% 4.04/4.26          | (v2_funct_2 @ X23 @ X25)
% 4.04/4.26          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 4.04/4.26      inference('cnf', [status(esa)], [cc2_funct_2])).
% 4.04/4.26  thf('69', plain,
% 4.04/4.26      (((v2_funct_2 @ sk_B @ sk_A)
% 4.04/4.26        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 4.04/4.26        | ~ (v1_funct_1 @ sk_B))),
% 4.04/4.26      inference('sup-', [status(thm)], ['67', '68'])).
% 4.04/4.26  thf('70', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 4.04/4.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.04/4.26  thf('71', plain, ((v1_funct_1 @ sk_B)),
% 4.04/4.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.04/4.26  thf('72', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 4.04/4.26      inference('demod', [status(thm)], ['69', '70', '71'])).
% 4.04/4.26  thf(d3_funct_2, axiom,
% 4.04/4.26    (![A:$i,B:$i]:
% 4.04/4.26     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 4.04/4.26       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 4.04/4.26  thf('73', plain,
% 4.04/4.26      (![X26 : $i, X27 : $i]:
% 4.04/4.26         (~ (v2_funct_2 @ X27 @ X26)
% 4.04/4.26          | ((k2_relat_1 @ X27) = (X26))
% 4.04/4.26          | ~ (v5_relat_1 @ X27 @ X26)
% 4.04/4.26          | ~ (v1_relat_1 @ X27))),
% 4.04/4.26      inference('cnf', [status(esa)], [d3_funct_2])).
% 4.04/4.26  thf('74', plain,
% 4.04/4.26      ((~ (v1_relat_1 @ sk_B)
% 4.04/4.26        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 4.04/4.26        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 4.04/4.26      inference('sup-', [status(thm)], ['72', '73'])).
% 4.04/4.26  thf('75', plain,
% 4.04/4.26      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.04/4.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.04/4.26  thf(cc1_relset_1, axiom,
% 4.04/4.26    (![A:$i,B:$i,C:$i]:
% 4.04/4.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.04/4.26       ( v1_relat_1 @ C ) ))).
% 4.04/4.26  thf('76', plain,
% 4.04/4.26      (![X7 : $i, X8 : $i, X9 : $i]:
% 4.04/4.26         ((v1_relat_1 @ X7)
% 4.04/4.26          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 4.04/4.26      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.04/4.26  thf('77', plain, ((v1_relat_1 @ sk_B)),
% 4.04/4.26      inference('sup-', [status(thm)], ['75', '76'])).
% 4.04/4.26  thf('78', plain,
% 4.04/4.26      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.04/4.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.04/4.26  thf(cc2_relset_1, axiom,
% 4.04/4.26    (![A:$i,B:$i,C:$i]:
% 4.04/4.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.04/4.26       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 4.04/4.26  thf('79', plain,
% 4.04/4.26      (![X10 : $i, X11 : $i, X12 : $i]:
% 4.04/4.26         ((v5_relat_1 @ X10 @ X12)
% 4.04/4.26          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 4.04/4.26      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.04/4.26  thf('80', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 4.04/4.26      inference('sup-', [status(thm)], ['78', '79'])).
% 4.04/4.26  thf('81', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 4.04/4.26      inference('demod', [status(thm)], ['74', '77', '80'])).
% 4.04/4.26  thf('82', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 4.04/4.26      inference('demod', [status(thm)], ['66', '81'])).
% 4.04/4.26  thf('83', plain,
% 4.04/4.26      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.04/4.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.04/4.26  thf('84', plain,
% 4.04/4.26      (![X23 : $i, X24 : $i, X25 : $i]:
% 4.04/4.26         (~ (v1_funct_1 @ X23)
% 4.04/4.26          | ~ (v3_funct_2 @ X23 @ X24 @ X25)
% 4.04/4.26          | (v2_funct_1 @ X23)
% 4.04/4.26          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 4.04/4.26      inference('cnf', [status(esa)], [cc2_funct_2])).
% 4.04/4.26  thf('85', plain,
% 4.04/4.26      (((v2_funct_1 @ sk_B)
% 4.04/4.26        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 4.04/4.26        | ~ (v1_funct_1 @ sk_B))),
% 4.04/4.26      inference('sup-', [status(thm)], ['83', '84'])).
% 4.04/4.26  thf('86', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 4.04/4.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.04/4.26  thf('87', plain, ((v1_funct_1 @ sk_B)),
% 4.04/4.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.04/4.26  thf('88', plain, ((v2_funct_1 @ sk_B)),
% 4.04/4.26      inference('demod', [status(thm)], ['85', '86', '87'])).
% 4.04/4.26  thf('89', plain,
% 4.04/4.26      ((((sk_A) != (sk_A))
% 4.04/4.26        | ((sk_A) = (k1_xboole_0))
% 4.04/4.26        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 4.04/4.26      inference('demod', [status(thm)], ['60', '61', '62', '63', '82', '88'])).
% 4.04/4.26  thf('90', plain,
% 4.04/4.26      ((((sk_C) = (k2_funct_1 @ sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 4.04/4.26      inference('simplify', [status(thm)], ['89'])).
% 4.04/4.26  thf('91', plain,
% 4.04/4.26      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 4.04/4.26      inference('demod', [status(thm)], ['22', '29'])).
% 4.04/4.26  thf('92', plain,
% 4.04/4.26      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 4.04/4.26      inference('sup-', [status(thm)], ['90', '91'])).
% 4.04/4.26  thf('93', plain,
% 4.04/4.26      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.04/4.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.04/4.26  thf('94', plain,
% 4.04/4.26      (![X20 : $i, X21 : $i, X22 : $i]:
% 4.04/4.26         ((r2_relset_1 @ X20 @ X21 @ X22 @ X22)
% 4.04/4.26          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 4.04/4.26      inference('simplify', [status(thm)], ['16'])).
% 4.04/4.26  thf('95', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 4.04/4.26      inference('sup-', [status(thm)], ['93', '94'])).
% 4.04/4.26  thf('96', plain, (((sk_A) = (k1_xboole_0))),
% 4.04/4.26      inference('demod', [status(thm)], ['92', '95'])).
% 4.04/4.26  thf('97', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.04/4.26      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.04/4.26  thf('98', plain, ($false),
% 4.04/4.26      inference('demod', [status(thm)], ['51', '96', '97'])).
% 4.04/4.26  
% 4.04/4.26  % SZS output end Refutation
% 4.04/4.26  
% 4.04/4.27  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IvslmhyEHL

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:04 EST 2020

% Result     : Theorem 3.25s
% Output     : Refutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 366 expanded)
%              Number of leaves         :   41 ( 123 expanded)
%              Depth                    :   15
%              Number of atoms          : 1283 (7553 expanded)
%              Number of equality atoms :   44 (  95 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('0',plain,(
    ! [X34: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X14 ) ) )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k6_relat_1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

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

thf('5',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_funct_1 @ ( k6_relat_1 @ X0 ) )
        | ~ ( v1_xboole_0 @ sk_C )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('8',plain,(
    ! [X5: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('9',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ sk_C )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(condensation,[status(thm)],['9'])).

thf('11',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('12',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('13',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('15',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( r2_relset_1 @ X45 @ X45 @ ( k1_partfun1 @ X45 @ X46 @ X46 @ X45 @ X44 @ X47 ) @ ( k6_partfun1 @ X45 ) )
      | ( ( k2_relset_1 @ X46 @ X45 @ X47 )
        = X45 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) )
      | ~ ( v1_funct_2 @ X47 @ X46 @ X45 )
      | ~ ( v1_funct_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('16',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('17',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( r2_relset_1 @ X45 @ X45 @ ( k1_partfun1 @ X45 @ X46 @ X46 @ X45 @ X44 @ X47 ) @ ( k6_relat_1 @ X45 ) )
      | ( ( k2_relset_1 @ X46 @ X45 @ X47 )
        = X45 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) )
      | ~ ( v1_funct_2 @ X47 @ X46 @ X45 )
      | ~ ( v1_funct_1 @ X47 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['13','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('24',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('25',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['22','25','26','27','28'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('30',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k2_relat_1 @ X36 )
       != X35 )
      | ( v2_funct_2 @ X36 @ X35 )
      | ~ ( v5_relat_1 @ X36 @ X35 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('31',plain,(
    ! [X36: $i] :
      ( ~ ( v1_relat_1 @ X36 )
      | ~ ( v5_relat_1 @ X36 @ ( k2_relat_1 @ X36 ) )
      | ( v2_funct_2 @ X36 @ ( k2_relat_1 @ X36 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('34',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v5_relat_1 @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('35',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['22','25','26','27','28'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('38',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('39',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['32','35','36','39'])).

thf('41',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('42',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('44',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['42','43'])).

thf('45',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['10','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X14 ) ) )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('48',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('51',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( ( k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40 )
        = ( k5_relat_1 @ X37 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
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

thf('59',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_funct_2 @ X48 @ X49 @ X50 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X51 @ X49 @ X49 @ X50 @ X52 @ X48 ) )
      | ( v2_funct_1 @ X52 )
      | ( X50 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X49 ) ) )
      | ~ ( v1_funct_2 @ X52 @ X51 @ X49 )
      | ~ ( v1_funct_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['57','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65','66','67'])).

thf('69',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['5'])).

thf('70',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['42','43'])).

thf('71',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference(clc,[status(thm)],['68','71'])).

thf('73',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('74',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('75',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( m1_subset_1 @ ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) )).

thf('78',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X16 @ X17 @ X19 @ X20 @ X15 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relset_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('83',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k4_relset_1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 )
        = ( k5_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k4_relset_1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','85'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('87',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( X30 = X33 )
      | ~ ( r2_relset_1 @ X31 @ X32 @ X30 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','88'])).

thf('90',plain,(
    ! [X34: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('91',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X5: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('93',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['72','91','92'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('94',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('95',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['48','93','94'])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['45','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IvslmhyEHL
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:17:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 3.25/3.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.25/3.47  % Solved by: fo/fo7.sh
% 3.25/3.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.25/3.47  % done 3519 iterations in 3.012s
% 3.25/3.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.25/3.47  % SZS output start Refutation
% 3.25/3.47  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.25/3.47  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.25/3.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.25/3.47  thf(sk_D_type, type, sk_D: $i).
% 3.25/3.47  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 3.25/3.47  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.25/3.47  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.25/3.47  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.25/3.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.25/3.47  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.25/3.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.25/3.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.25/3.47  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.25/3.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.25/3.47  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.25/3.47  thf(sk_C_type, type, sk_C: $i).
% 3.25/3.47  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.25/3.47  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 3.25/3.47  thf(sk_A_type, type, sk_A: $i).
% 3.25/3.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.25/3.47  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.25/3.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.25/3.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.25/3.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.25/3.47  thf(t29_relset_1, axiom,
% 3.25/3.47    (![A:$i]:
% 3.25/3.47     ( m1_subset_1 @
% 3.25/3.47       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 3.25/3.47  thf('0', plain,
% 3.25/3.47      (![X34 : $i]:
% 3.25/3.47         (m1_subset_1 @ (k6_relat_1 @ X34) @ 
% 3.25/3.47          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))),
% 3.25/3.47      inference('cnf', [status(esa)], [t29_relset_1])).
% 3.25/3.47  thf(cc3_relset_1, axiom,
% 3.25/3.47    (![A:$i,B:$i]:
% 3.25/3.47     ( ( v1_xboole_0 @ A ) =>
% 3.25/3.47       ( ![C:$i]:
% 3.25/3.47         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.25/3.47           ( v1_xboole_0 @ C ) ) ) ))).
% 3.25/3.47  thf('1', plain,
% 3.25/3.47      (![X12 : $i, X13 : $i, X14 : $i]:
% 3.25/3.47         (~ (v1_xboole_0 @ X12)
% 3.25/3.47          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X14)))
% 3.25/3.47          | (v1_xboole_0 @ X13))),
% 3.25/3.47      inference('cnf', [status(esa)], [cc3_relset_1])).
% 3.25/3.47  thf('2', plain,
% 3.25/3.47      (![X0 : $i]: ((v1_xboole_0 @ (k6_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 3.25/3.47      inference('sup-', [status(thm)], ['0', '1'])).
% 3.25/3.47  thf(t8_boole, axiom,
% 3.25/3.47    (![A:$i,B:$i]:
% 3.25/3.47     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 3.25/3.47  thf('3', plain,
% 3.25/3.47      (![X0 : $i, X1 : $i]:
% 3.25/3.47         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 3.25/3.47      inference('cnf', [status(esa)], [t8_boole])).
% 3.25/3.47  thf('4', plain,
% 3.25/3.47      (![X0 : $i, X1 : $i]:
% 3.25/3.47         (~ (v1_xboole_0 @ X0)
% 3.25/3.47          | ((k6_relat_1 @ X0) = (X1))
% 3.25/3.47          | ~ (v1_xboole_0 @ X1))),
% 3.25/3.47      inference('sup-', [status(thm)], ['2', '3'])).
% 3.25/3.47  thf(t29_funct_2, conjecture,
% 3.25/3.47    (![A:$i,B:$i,C:$i]:
% 3.25/3.47     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.25/3.47         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.25/3.47       ( ![D:$i]:
% 3.25/3.47         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.25/3.47             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.25/3.47           ( ( r2_relset_1 @
% 3.25/3.47               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.25/3.47               ( k6_partfun1 @ A ) ) =>
% 3.25/3.47             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 3.25/3.47  thf(zf_stmt_0, negated_conjecture,
% 3.25/3.47    (~( ![A:$i,B:$i,C:$i]:
% 3.25/3.47        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.25/3.47            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.25/3.47          ( ![D:$i]:
% 3.25/3.47            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.25/3.47                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.25/3.47              ( ( r2_relset_1 @
% 3.25/3.47                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.25/3.47                  ( k6_partfun1 @ A ) ) =>
% 3.25/3.47                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 3.25/3.47    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 3.25/3.47  thf('5', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 3.25/3.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.47  thf('6', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.25/3.47      inference('split', [status(esa)], ['5'])).
% 3.25/3.47  thf('7', plain,
% 3.25/3.47      ((![X0 : $i]:
% 3.25/3.47          (~ (v2_funct_1 @ (k6_relat_1 @ X0))
% 3.25/3.47           | ~ (v1_xboole_0 @ sk_C)
% 3.25/3.47           | ~ (v1_xboole_0 @ X0)))
% 3.25/3.47         <= (~ ((v2_funct_1 @ sk_C)))),
% 3.25/3.47      inference('sup-', [status(thm)], ['4', '6'])).
% 3.25/3.47  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 3.25/3.47  thf('8', plain, (![X5 : $i]: (v2_funct_1 @ (k6_relat_1 @ X5))),
% 3.25/3.47      inference('cnf', [status(esa)], [t52_funct_1])).
% 3.25/3.47  thf('9', plain,
% 3.25/3.47      ((![X0 : $i]: (~ (v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ X0)))
% 3.25/3.47         <= (~ ((v2_funct_1 @ sk_C)))),
% 3.25/3.47      inference('demod', [status(thm)], ['7', '8'])).
% 3.25/3.47  thf('10', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.25/3.47      inference('condensation', [status(thm)], ['9'])).
% 3.25/3.47  thf('11', plain,
% 3.25/3.47      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.25/3.47        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 3.25/3.47        (k6_partfun1 @ sk_A))),
% 3.25/3.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.47  thf(redefinition_k6_partfun1, axiom,
% 3.25/3.47    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 3.25/3.47  thf('12', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 3.25/3.47      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.25/3.47  thf('13', plain,
% 3.25/3.47      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.25/3.47        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 3.25/3.47        (k6_relat_1 @ sk_A))),
% 3.25/3.47      inference('demod', [status(thm)], ['11', '12'])).
% 3.25/3.47  thf('14', plain,
% 3.25/3.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.25/3.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.47  thf(t24_funct_2, axiom,
% 3.25/3.47    (![A:$i,B:$i,C:$i]:
% 3.25/3.47     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.25/3.47         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.25/3.47       ( ![D:$i]:
% 3.25/3.47         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.25/3.47             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.25/3.47           ( ( r2_relset_1 @
% 3.25/3.47               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 3.25/3.47               ( k6_partfun1 @ B ) ) =>
% 3.25/3.47             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 3.25/3.47  thf('15', plain,
% 3.25/3.47      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 3.25/3.47         (~ (v1_funct_1 @ X44)
% 3.25/3.47          | ~ (v1_funct_2 @ X44 @ X45 @ X46)
% 3.25/3.47          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 3.25/3.47          | ~ (r2_relset_1 @ X45 @ X45 @ 
% 3.25/3.47               (k1_partfun1 @ X45 @ X46 @ X46 @ X45 @ X44 @ X47) @ 
% 3.25/3.47               (k6_partfun1 @ X45))
% 3.25/3.47          | ((k2_relset_1 @ X46 @ X45 @ X47) = (X45))
% 3.25/3.47          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45)))
% 3.25/3.47          | ~ (v1_funct_2 @ X47 @ X46 @ X45)
% 3.25/3.47          | ~ (v1_funct_1 @ X47))),
% 3.25/3.47      inference('cnf', [status(esa)], [t24_funct_2])).
% 3.25/3.47  thf('16', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 3.25/3.47      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.25/3.47  thf('17', plain,
% 3.25/3.47      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 3.25/3.47         (~ (v1_funct_1 @ X44)
% 3.25/3.47          | ~ (v1_funct_2 @ X44 @ X45 @ X46)
% 3.25/3.47          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 3.25/3.47          | ~ (r2_relset_1 @ X45 @ X45 @ 
% 3.25/3.47               (k1_partfun1 @ X45 @ X46 @ X46 @ X45 @ X44 @ X47) @ 
% 3.25/3.47               (k6_relat_1 @ X45))
% 3.25/3.47          | ((k2_relset_1 @ X46 @ X45 @ X47) = (X45))
% 3.25/3.47          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45)))
% 3.25/3.47          | ~ (v1_funct_2 @ X47 @ X46 @ X45)
% 3.25/3.47          | ~ (v1_funct_1 @ X47))),
% 3.25/3.47      inference('demod', [status(thm)], ['15', '16'])).
% 3.25/3.47  thf('18', plain,
% 3.25/3.47      (![X0 : $i]:
% 3.25/3.47         (~ (v1_funct_1 @ X0)
% 3.25/3.47          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 3.25/3.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 3.25/3.47          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 3.25/3.47          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.25/3.47               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 3.25/3.47               (k6_relat_1 @ sk_A))
% 3.25/3.47          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 3.25/3.47          | ~ (v1_funct_1 @ sk_C))),
% 3.25/3.47      inference('sup-', [status(thm)], ['14', '17'])).
% 3.25/3.47  thf('19', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 3.25/3.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.47  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 3.25/3.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.47  thf('21', plain,
% 3.25/3.47      (![X0 : $i]:
% 3.25/3.47         (~ (v1_funct_1 @ X0)
% 3.25/3.47          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 3.25/3.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 3.25/3.47          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 3.25/3.47          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.25/3.47               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 3.25/3.47               (k6_relat_1 @ sk_A)))),
% 3.25/3.47      inference('demod', [status(thm)], ['18', '19', '20'])).
% 3.25/3.47  thf('22', plain,
% 3.25/3.47      ((((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (sk_A))
% 3.25/3.47        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 3.25/3.47        | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 3.25/3.47        | ~ (v1_funct_1 @ sk_D))),
% 3.25/3.47      inference('sup-', [status(thm)], ['13', '21'])).
% 3.25/3.47  thf('23', plain,
% 3.25/3.47      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.25/3.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.47  thf(redefinition_k2_relset_1, axiom,
% 3.25/3.47    (![A:$i,B:$i,C:$i]:
% 3.25/3.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.25/3.47       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.25/3.47  thf('24', plain,
% 3.25/3.47      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.25/3.47         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 3.25/3.47          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 3.25/3.47      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.25/3.47  thf('25', plain,
% 3.25/3.47      (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 3.25/3.47      inference('sup-', [status(thm)], ['23', '24'])).
% 3.25/3.47  thf('26', plain,
% 3.25/3.47      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.25/3.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.47  thf('27', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 3.25/3.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.47  thf('28', plain, ((v1_funct_1 @ sk_D)),
% 3.25/3.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.47  thf('29', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.25/3.47      inference('demod', [status(thm)], ['22', '25', '26', '27', '28'])).
% 3.25/3.47  thf(d3_funct_2, axiom,
% 3.25/3.47    (![A:$i,B:$i]:
% 3.25/3.47     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 3.25/3.47       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 3.25/3.47  thf('30', plain,
% 3.25/3.47      (![X35 : $i, X36 : $i]:
% 3.25/3.47         (((k2_relat_1 @ X36) != (X35))
% 3.25/3.47          | (v2_funct_2 @ X36 @ X35)
% 3.25/3.47          | ~ (v5_relat_1 @ X36 @ X35)
% 3.25/3.47          | ~ (v1_relat_1 @ X36))),
% 3.25/3.47      inference('cnf', [status(esa)], [d3_funct_2])).
% 3.25/3.47  thf('31', plain,
% 3.25/3.47      (![X36 : $i]:
% 3.25/3.47         (~ (v1_relat_1 @ X36)
% 3.25/3.47          | ~ (v5_relat_1 @ X36 @ (k2_relat_1 @ X36))
% 3.25/3.47          | (v2_funct_2 @ X36 @ (k2_relat_1 @ X36)))),
% 3.25/3.47      inference('simplify', [status(thm)], ['30'])).
% 3.25/3.47  thf('32', plain,
% 3.25/3.47      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 3.25/3.47        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 3.25/3.47        | ~ (v1_relat_1 @ sk_D))),
% 3.25/3.47      inference('sup-', [status(thm)], ['29', '31'])).
% 3.25/3.47  thf('33', plain,
% 3.25/3.47      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.25/3.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.47  thf(cc2_relset_1, axiom,
% 3.25/3.47    (![A:$i,B:$i,C:$i]:
% 3.25/3.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.25/3.47       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.25/3.47  thf('34', plain,
% 3.25/3.47      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.25/3.47         ((v5_relat_1 @ X9 @ X11)
% 3.25/3.47          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 3.25/3.47      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.25/3.47  thf('35', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 3.25/3.47      inference('sup-', [status(thm)], ['33', '34'])).
% 3.25/3.47  thf('36', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.25/3.47      inference('demod', [status(thm)], ['22', '25', '26', '27', '28'])).
% 3.25/3.47  thf('37', plain,
% 3.25/3.47      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.25/3.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.47  thf(cc1_relset_1, axiom,
% 3.25/3.47    (![A:$i,B:$i,C:$i]:
% 3.25/3.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.25/3.47       ( v1_relat_1 @ C ) ))).
% 3.25/3.47  thf('38', plain,
% 3.25/3.47      (![X6 : $i, X7 : $i, X8 : $i]:
% 3.25/3.47         ((v1_relat_1 @ X6)
% 3.25/3.47          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 3.25/3.47      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.25/3.47  thf('39', plain, ((v1_relat_1 @ sk_D)),
% 3.25/3.47      inference('sup-', [status(thm)], ['37', '38'])).
% 3.25/3.47  thf('40', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 3.25/3.47      inference('demod', [status(thm)], ['32', '35', '36', '39'])).
% 3.25/3.47  thf('41', plain,
% 3.25/3.47      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 3.25/3.47      inference('split', [status(esa)], ['5'])).
% 3.25/3.47  thf('42', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 3.25/3.47      inference('sup-', [status(thm)], ['40', '41'])).
% 3.25/3.47  thf('43', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 3.25/3.47      inference('split', [status(esa)], ['5'])).
% 3.25/3.47  thf('44', plain, (~ ((v2_funct_1 @ sk_C))),
% 3.25/3.47      inference('sat_resolution*', [status(thm)], ['42', '43'])).
% 3.25/3.47  thf('45', plain, (~ (v1_xboole_0 @ sk_C)),
% 3.25/3.47      inference('simpl_trail', [status(thm)], ['10', '44'])).
% 3.25/3.47  thf('46', plain,
% 3.25/3.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.25/3.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.47  thf('47', plain,
% 3.25/3.47      (![X12 : $i, X13 : $i, X14 : $i]:
% 3.25/3.47         (~ (v1_xboole_0 @ X12)
% 3.25/3.47          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X14)))
% 3.25/3.47          | (v1_xboole_0 @ X13))),
% 3.25/3.47      inference('cnf', [status(esa)], [cc3_relset_1])).
% 3.25/3.47  thf('48', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 3.25/3.47      inference('sup-', [status(thm)], ['46', '47'])).
% 3.25/3.47  thf('49', plain,
% 3.25/3.47      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.25/3.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.47  thf('50', plain,
% 3.25/3.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.25/3.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.47  thf(redefinition_k1_partfun1, axiom,
% 3.25/3.47    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.25/3.47     ( ( ( v1_funct_1 @ E ) & 
% 3.25/3.47         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.25/3.47         ( v1_funct_1 @ F ) & 
% 3.25/3.47         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.25/3.47       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 3.25/3.47  thf('51', plain,
% 3.25/3.47      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 3.25/3.47         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 3.25/3.47          | ~ (v1_funct_1 @ X37)
% 3.25/3.47          | ~ (v1_funct_1 @ X40)
% 3.25/3.47          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 3.25/3.47          | ((k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40)
% 3.25/3.47              = (k5_relat_1 @ X37 @ X40)))),
% 3.25/3.47      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 3.25/3.47  thf('52', plain,
% 3.25/3.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.25/3.47         (((k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C @ X0)
% 3.25/3.47            = (k5_relat_1 @ sk_C @ X0))
% 3.25/3.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.25/3.47          | ~ (v1_funct_1 @ X0)
% 3.25/3.47          | ~ (v1_funct_1 @ sk_C))),
% 3.25/3.47      inference('sup-', [status(thm)], ['50', '51'])).
% 3.25/3.47  thf('53', plain, ((v1_funct_1 @ sk_C)),
% 3.25/3.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.47  thf('54', plain,
% 3.25/3.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.25/3.47         (((k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C @ X0)
% 3.25/3.47            = (k5_relat_1 @ sk_C @ X0))
% 3.25/3.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.25/3.47          | ~ (v1_funct_1 @ X0))),
% 3.25/3.47      inference('demod', [status(thm)], ['52', '53'])).
% 3.25/3.47  thf('55', plain,
% 3.25/3.47      ((~ (v1_funct_1 @ sk_D)
% 3.25/3.47        | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 3.25/3.47            = (k5_relat_1 @ sk_C @ sk_D)))),
% 3.25/3.47      inference('sup-', [status(thm)], ['49', '54'])).
% 3.25/3.47  thf('56', plain, ((v1_funct_1 @ sk_D)),
% 3.25/3.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.47  thf('57', plain,
% 3.25/3.47      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 3.25/3.47         = (k5_relat_1 @ sk_C @ sk_D))),
% 3.25/3.47      inference('demod', [status(thm)], ['55', '56'])).
% 3.25/3.47  thf('58', plain,
% 3.25/3.47      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.25/3.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.47  thf(t26_funct_2, axiom,
% 3.25/3.47    (![A:$i,B:$i,C:$i,D:$i]:
% 3.25/3.47     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.25/3.47         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.25/3.47       ( ![E:$i]:
% 3.25/3.47         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.25/3.47             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.25/3.47           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 3.25/3.47             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 3.25/3.47               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 3.25/3.47  thf('59', plain,
% 3.25/3.47      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 3.25/3.47         (~ (v1_funct_1 @ X48)
% 3.25/3.47          | ~ (v1_funct_2 @ X48 @ X49 @ X50)
% 3.25/3.47          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 3.25/3.47          | ~ (v2_funct_1 @ (k1_partfun1 @ X51 @ X49 @ X49 @ X50 @ X52 @ X48))
% 3.25/3.47          | (v2_funct_1 @ X52)
% 3.25/3.47          | ((X50) = (k1_xboole_0))
% 3.25/3.47          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X49)))
% 3.25/3.47          | ~ (v1_funct_2 @ X52 @ X51 @ X49)
% 3.25/3.47          | ~ (v1_funct_1 @ X52))),
% 3.25/3.47      inference('cnf', [status(esa)], [t26_funct_2])).
% 3.25/3.47  thf('60', plain,
% 3.25/3.47      (![X0 : $i, X1 : $i]:
% 3.25/3.47         (~ (v1_funct_1 @ X0)
% 3.25/3.47          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 3.25/3.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 3.25/3.47          | ((sk_A) = (k1_xboole_0))
% 3.25/3.47          | (v2_funct_1 @ X0)
% 3.25/3.47          | ~ (v2_funct_1 @ 
% 3.25/3.47               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D))
% 3.25/3.47          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 3.25/3.47          | ~ (v1_funct_1 @ sk_D))),
% 3.25/3.47      inference('sup-', [status(thm)], ['58', '59'])).
% 3.25/3.47  thf('61', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 3.25/3.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.47  thf('62', plain, ((v1_funct_1 @ sk_D)),
% 3.25/3.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.47  thf('63', plain,
% 3.25/3.47      (![X0 : $i, X1 : $i]:
% 3.25/3.47         (~ (v1_funct_1 @ X0)
% 3.25/3.47          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 3.25/3.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 3.25/3.47          | ((sk_A) = (k1_xboole_0))
% 3.25/3.47          | (v2_funct_1 @ X0)
% 3.25/3.47          | ~ (v2_funct_1 @ 
% 3.25/3.47               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D)))),
% 3.25/3.47      inference('demod', [status(thm)], ['60', '61', '62'])).
% 3.25/3.47  thf('64', plain,
% 3.25/3.47      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 3.25/3.47        | (v2_funct_1 @ sk_C)
% 3.25/3.47        | ((sk_A) = (k1_xboole_0))
% 3.25/3.47        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 3.25/3.47        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 3.25/3.47        | ~ (v1_funct_1 @ sk_C))),
% 3.25/3.47      inference('sup-', [status(thm)], ['57', '63'])).
% 3.25/3.47  thf('65', plain,
% 3.25/3.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.25/3.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.47  thf('66', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 3.25/3.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.47  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 3.25/3.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.47  thf('68', plain,
% 3.25/3.47      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 3.25/3.47        | (v2_funct_1 @ sk_C)
% 3.25/3.47        | ((sk_A) = (k1_xboole_0)))),
% 3.25/3.47      inference('demod', [status(thm)], ['64', '65', '66', '67'])).
% 3.25/3.47  thf('69', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.25/3.47      inference('split', [status(esa)], ['5'])).
% 3.25/3.47  thf('70', plain, (~ ((v2_funct_1 @ sk_C))),
% 3.25/3.47      inference('sat_resolution*', [status(thm)], ['42', '43'])).
% 3.25/3.47  thf('71', plain, (~ (v2_funct_1 @ sk_C)),
% 3.25/3.47      inference('simpl_trail', [status(thm)], ['69', '70'])).
% 3.25/3.47  thf('72', plain,
% 3.25/3.47      ((((sk_A) = (k1_xboole_0)) | ~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D)))),
% 3.25/3.47      inference('clc', [status(thm)], ['68', '71'])).
% 3.25/3.47  thf('73', plain,
% 3.25/3.47      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.25/3.47        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 3.25/3.47        (k6_relat_1 @ sk_A))),
% 3.25/3.47      inference('demod', [status(thm)], ['11', '12'])).
% 3.25/3.47  thf('74', plain,
% 3.25/3.47      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 3.25/3.47         = (k5_relat_1 @ sk_C @ sk_D))),
% 3.25/3.47      inference('demod', [status(thm)], ['55', '56'])).
% 3.25/3.47  thf('75', plain,
% 3.25/3.47      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 3.25/3.47        (k6_relat_1 @ sk_A))),
% 3.25/3.47      inference('demod', [status(thm)], ['73', '74'])).
% 3.25/3.47  thf('76', plain,
% 3.25/3.47      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.25/3.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.47  thf('77', plain,
% 3.25/3.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.25/3.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.47  thf(dt_k4_relset_1, axiom,
% 3.25/3.47    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.25/3.47     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.25/3.47         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.25/3.47       ( m1_subset_1 @
% 3.25/3.47         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.25/3.47         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 3.25/3.47  thf('78', plain,
% 3.25/3.47      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 3.25/3.47         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 3.25/3.47          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 3.25/3.47          | (m1_subset_1 @ (k4_relset_1 @ X16 @ X17 @ X19 @ X20 @ X15 @ X18) @ 
% 3.25/3.47             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X20))))),
% 3.25/3.47      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 3.25/3.47  thf('79', plain,
% 3.25/3.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.25/3.47         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1) @ 
% 3.25/3.47           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.25/3.47          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 3.25/3.47      inference('sup-', [status(thm)], ['77', '78'])).
% 3.25/3.47  thf('80', plain,
% 3.25/3.47      ((m1_subset_1 @ 
% 3.25/3.47        (k4_relset_1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 3.25/3.47        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.25/3.47      inference('sup-', [status(thm)], ['76', '79'])).
% 3.25/3.47  thf('81', plain,
% 3.25/3.47      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.25/3.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.47  thf('82', plain,
% 3.25/3.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.25/3.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.47  thf(redefinition_k4_relset_1, axiom,
% 3.25/3.47    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.25/3.47     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.25/3.47         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.25/3.47       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 3.25/3.47  thf('83', plain,
% 3.25/3.47      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 3.25/3.47         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 3.25/3.47          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 3.25/3.47          | ((k4_relset_1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27)
% 3.25/3.47              = (k5_relat_1 @ X24 @ X27)))),
% 3.25/3.47      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 3.25/3.47  thf('84', plain,
% 3.25/3.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.25/3.47         (((k4_relset_1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C @ X0)
% 3.25/3.47            = (k5_relat_1 @ sk_C @ X0))
% 3.25/3.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 3.25/3.47      inference('sup-', [status(thm)], ['82', '83'])).
% 3.25/3.47  thf('85', plain,
% 3.25/3.47      (((k4_relset_1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 3.25/3.47         = (k5_relat_1 @ sk_C @ sk_D))),
% 3.25/3.47      inference('sup-', [status(thm)], ['81', '84'])).
% 3.25/3.47  thf('86', plain,
% 3.25/3.47      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 3.25/3.47        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.25/3.47      inference('demod', [status(thm)], ['80', '85'])).
% 3.25/3.47  thf(redefinition_r2_relset_1, axiom,
% 3.25/3.47    (![A:$i,B:$i,C:$i,D:$i]:
% 3.25/3.47     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.25/3.47         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.25/3.47       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.25/3.47  thf('87', plain,
% 3.25/3.47      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 3.25/3.47         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 3.25/3.47          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 3.25/3.47          | ((X30) = (X33))
% 3.25/3.47          | ~ (r2_relset_1 @ X31 @ X32 @ X30 @ X33))),
% 3.25/3.47      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.25/3.47  thf('88', plain,
% 3.25/3.47      (![X0 : $i]:
% 3.25/3.47         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 3.25/3.47          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 3.25/3.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.25/3.47      inference('sup-', [status(thm)], ['86', '87'])).
% 3.25/3.47  thf('89', plain,
% 3.25/3.47      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 3.25/3.47           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.25/3.47        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A)))),
% 3.25/3.47      inference('sup-', [status(thm)], ['75', '88'])).
% 3.25/3.47  thf('90', plain,
% 3.25/3.47      (![X34 : $i]:
% 3.25/3.47         (m1_subset_1 @ (k6_relat_1 @ X34) @ 
% 3.25/3.47          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))),
% 3.25/3.47      inference('cnf', [status(esa)], [t29_relset_1])).
% 3.25/3.47  thf('91', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 3.25/3.47      inference('demod', [status(thm)], ['89', '90'])).
% 3.25/3.47  thf('92', plain, (![X5 : $i]: (v2_funct_1 @ (k6_relat_1 @ X5))),
% 3.25/3.47      inference('cnf', [status(esa)], [t52_funct_1])).
% 3.25/3.47  thf('93', plain, (((sk_A) = (k1_xboole_0))),
% 3.25/3.47      inference('demod', [status(thm)], ['72', '91', '92'])).
% 3.25/3.47  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.25/3.47  thf('94', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.25/3.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.25/3.47  thf('95', plain, ((v1_xboole_0 @ sk_C)),
% 3.25/3.47      inference('demod', [status(thm)], ['48', '93', '94'])).
% 3.25/3.47  thf('96', plain, ($false), inference('demod', [status(thm)], ['45', '95'])).
% 3.25/3.47  
% 3.25/3.47  % SZS output end Refutation
% 3.25/3.47  
% 3.25/3.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

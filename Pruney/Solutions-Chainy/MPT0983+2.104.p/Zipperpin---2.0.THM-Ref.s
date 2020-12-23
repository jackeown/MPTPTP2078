%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yREJrYWnuA

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:17 EST 2020

% Result     : Theorem 5.99s
% Output     : Refutation 5.99s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 454 expanded)
%              Number of leaves         :   42 ( 149 expanded)
%              Depth                    :   14
%              Number of atoms          : 1240 (7723 expanded)
%              Number of equality atoms :   51 ( 143 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ( ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( r2_relset_1 @ X41 @ X41 @ ( k1_partfun1 @ X41 @ X42 @ X42 @ X41 @ X40 @ X43 ) @ ( k6_partfun1 @ X41 ) )
      | ( ( k2_relset_1 @ X42 @ X41 @ X43 )
        = X41 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X42 @ X41 )
      | ~ ( v1_funct_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
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
    ! [X31: $i,X32: $i] :
      ( ( ( k2_relat_1 @ X32 )
       != X31 )
      | ( v2_funct_2 @ X32 @ X31 )
      | ~ ( v5_relat_1 @ X32 @ X31 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('18',plain,(
    ! [X32: $i] :
      ( ~ ( v1_relat_1 @ X32 )
      | ~ ( v5_relat_1 @ X32 @ ( k2_relat_1 @ X32 ) )
      | ( v2_funct_2 @ X32 @ ( k2_relat_1 @ X32 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['19'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('21',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X16 ) @ X17 )
      | ( v5_relat_1 @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X32: $i] :
      ( ( v2_funct_2 @ X32 @ ( k2_relat_1 @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(clc,[status(thm)],['18','22'])).

thf('24',plain,
    ( ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['16','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('26',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('27',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('30',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['30','31'])).

thf('33',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('35',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('36',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('38',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C_1 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('42',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('49',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( X26 = X29 )
      | ~ ( r2_relset_1 @ X27 @ X28 @ X26 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','50'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('52',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('53',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('54',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,(
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

thf('57',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X47 @ X45 @ X45 @ X46 @ X48 @ X44 ) )
      | ( v2_funct_1 @ X48 )
      | ( X46 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X45 ) ) )
      | ~ ( v1_funct_2 @ X48 @ X47 @ X45 )
      | ~ ( v1_funct_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['55','61'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('63',plain,(
    ! [X19: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('64',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('65',plain,(
    ! [X19: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v2_funct_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','65','66','67','68'])).

thf('70',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','32'])).

thf('71',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['69','70'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('72',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('73',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['72'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('74',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('75',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('76',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('78',plain,(
    m1_subset_1 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('79',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k6_partfun1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('81',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('82',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k6_partfun1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_partfun1 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['74','82'])).

thf('84',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['75'])).

thf('85',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('86',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('87',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_partfun1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('89',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('90',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('91',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','93'])).

thf('95',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ X0 )
        = ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['87','96'])).

thf('98',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k6_partfun1 @ k1_xboole_0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['84','97'])).

thf('99',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('100',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('101',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['83','101'])).

thf('103',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['69','70'])).

thf('104',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('105',plain,(
    k1_xboole_0 = sk_C_1 ),
    inference(demod,[status(thm)],['38','71','73','102','103','104'])).

thf('106',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('107',plain,(
    ! [X19: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('108',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    $false ),
    inference(demod,[status(thm)],['33','105','108'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.09  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yREJrYWnuA
% 0.09/0.29  % Computer   : n009.cluster.edu
% 0.09/0.29  % Model      : x86_64 x86_64
% 0.09/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.29  % Memory     : 8042.1875MB
% 0.09/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.29  % CPULimit   : 60
% 0.09/0.29  % DateTime   : Tue Dec  1 12:00:26 EST 2020
% 0.09/0.29  % CPUTime    : 
% 0.09/0.29  % Running portfolio for 600 s
% 0.09/0.29  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.09/0.29  % Number of cores: 8
% 0.14/0.29  % Python version: Python 3.6.8
% 0.14/0.30  % Running in FO mode
% 5.99/6.21  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.99/6.21  % Solved by: fo/fo7.sh
% 5.99/6.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.99/6.21  % done 7930 iterations in 5.810s
% 5.99/6.21  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.99/6.21  % SZS output start Refutation
% 5.99/6.21  thf(sk_A_type, type, sk_A: $i).
% 5.99/6.21  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.99/6.21  thf(sk_C_1_type, type, sk_C_1: $i).
% 5.99/6.21  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.99/6.21  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 5.99/6.21  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 5.99/6.21  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 5.99/6.21  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 5.99/6.21  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 5.99/6.21  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 5.99/6.21  thf(sk_D_type, type, sk_D: $i).
% 5.99/6.21  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 5.99/6.21  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.99/6.21  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 5.99/6.21  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.99/6.21  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.99/6.21  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 5.99/6.21  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 5.99/6.21  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 5.99/6.21  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 5.99/6.21  thf(sk_B_type, type, sk_B: $i).
% 5.99/6.21  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.99/6.21  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 5.99/6.21  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.99/6.21  thf(t29_funct_2, conjecture,
% 5.99/6.21    (![A:$i,B:$i,C:$i]:
% 5.99/6.21     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.99/6.21         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.99/6.21       ( ![D:$i]:
% 5.99/6.21         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 5.99/6.21             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 5.99/6.21           ( ( r2_relset_1 @
% 5.99/6.21               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 5.99/6.21               ( k6_partfun1 @ A ) ) =>
% 5.99/6.21             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 5.99/6.21  thf(zf_stmt_0, negated_conjecture,
% 5.99/6.21    (~( ![A:$i,B:$i,C:$i]:
% 5.99/6.21        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.99/6.21            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.99/6.21          ( ![D:$i]:
% 5.99/6.21            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 5.99/6.21                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 5.99/6.21              ( ( r2_relset_1 @
% 5.99/6.21                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 5.99/6.21                  ( k6_partfun1 @ A ) ) =>
% 5.99/6.21                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 5.99/6.21    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 5.99/6.21  thf('0', plain, ((~ (v2_funct_1 @ sk_C_1) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 5.99/6.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.21  thf('1', plain, ((~ (v2_funct_1 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 5.99/6.21      inference('split', [status(esa)], ['0'])).
% 5.99/6.21  thf('2', plain,
% 5.99/6.21      ((r2_relset_1 @ sk_A @ sk_A @ 
% 5.99/6.21        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ 
% 5.99/6.21        (k6_partfun1 @ sk_A))),
% 5.99/6.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.21  thf('3', plain,
% 5.99/6.21      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.99/6.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.21  thf(t24_funct_2, axiom,
% 5.99/6.21    (![A:$i,B:$i,C:$i]:
% 5.99/6.21     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.99/6.21         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.99/6.21       ( ![D:$i]:
% 5.99/6.21         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 5.99/6.21             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 5.99/6.21           ( ( r2_relset_1 @
% 5.99/6.21               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 5.99/6.21               ( k6_partfun1 @ B ) ) =>
% 5.99/6.21             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 5.99/6.21  thf('4', plain,
% 5.99/6.21      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 5.99/6.21         (~ (v1_funct_1 @ X40)
% 5.99/6.21          | ~ (v1_funct_2 @ X40 @ X41 @ X42)
% 5.99/6.21          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 5.99/6.21          | ~ (r2_relset_1 @ X41 @ X41 @ 
% 5.99/6.21               (k1_partfun1 @ X41 @ X42 @ X42 @ X41 @ X40 @ X43) @ 
% 5.99/6.21               (k6_partfun1 @ X41))
% 5.99/6.21          | ((k2_relset_1 @ X42 @ X41 @ X43) = (X41))
% 5.99/6.21          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41)))
% 5.99/6.21          | ~ (v1_funct_2 @ X43 @ X42 @ X41)
% 5.99/6.21          | ~ (v1_funct_1 @ X43))),
% 5.99/6.21      inference('cnf', [status(esa)], [t24_funct_2])).
% 5.99/6.21  thf('5', plain,
% 5.99/6.21      (![X0 : $i]:
% 5.99/6.21         (~ (v1_funct_1 @ X0)
% 5.99/6.21          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 5.99/6.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 5.99/6.21          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 5.99/6.21          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 5.99/6.21               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 5.99/6.21               (k6_partfun1 @ sk_A))
% 5.99/6.21          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)
% 5.99/6.21          | ~ (v1_funct_1 @ sk_C_1))),
% 5.99/6.21      inference('sup-', [status(thm)], ['3', '4'])).
% 5.99/6.21  thf('6', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 5.99/6.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.21  thf('7', plain, ((v1_funct_1 @ sk_C_1)),
% 5.99/6.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.21  thf('8', plain,
% 5.99/6.21      (![X0 : $i]:
% 5.99/6.21         (~ (v1_funct_1 @ X0)
% 5.99/6.21          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 5.99/6.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 5.99/6.21          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 5.99/6.21          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 5.99/6.21               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 5.99/6.21               (k6_partfun1 @ sk_A)))),
% 5.99/6.21      inference('demod', [status(thm)], ['5', '6', '7'])).
% 5.99/6.21  thf('9', plain,
% 5.99/6.21      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 5.99/6.21        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 5.99/6.21        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 5.99/6.21        | ~ (v1_funct_1 @ sk_D))),
% 5.99/6.21      inference('sup-', [status(thm)], ['2', '8'])).
% 5.99/6.21  thf('10', plain,
% 5.99/6.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 5.99/6.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.21  thf(redefinition_k2_relset_1, axiom,
% 5.99/6.21    (![A:$i,B:$i,C:$i]:
% 5.99/6.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.99/6.21       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 5.99/6.21  thf('11', plain,
% 5.99/6.21      (![X23 : $i, X24 : $i, X25 : $i]:
% 5.99/6.21         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 5.99/6.21          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 5.99/6.21      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 5.99/6.21  thf('12', plain,
% 5.99/6.21      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 5.99/6.21      inference('sup-', [status(thm)], ['10', '11'])).
% 5.99/6.21  thf('13', plain,
% 5.99/6.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 5.99/6.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.21  thf('14', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 5.99/6.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.21  thf('15', plain, ((v1_funct_1 @ sk_D)),
% 5.99/6.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.21  thf('16', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 5.99/6.21      inference('demod', [status(thm)], ['9', '12', '13', '14', '15'])).
% 5.99/6.21  thf(d3_funct_2, axiom,
% 5.99/6.21    (![A:$i,B:$i]:
% 5.99/6.21     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 5.99/6.21       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 5.99/6.21  thf('17', plain,
% 5.99/6.21      (![X31 : $i, X32 : $i]:
% 5.99/6.21         (((k2_relat_1 @ X32) != (X31))
% 5.99/6.21          | (v2_funct_2 @ X32 @ X31)
% 5.99/6.21          | ~ (v5_relat_1 @ X32 @ X31)
% 5.99/6.21          | ~ (v1_relat_1 @ X32))),
% 5.99/6.21      inference('cnf', [status(esa)], [d3_funct_2])).
% 5.99/6.21  thf('18', plain,
% 5.99/6.21      (![X32 : $i]:
% 5.99/6.21         (~ (v1_relat_1 @ X32)
% 5.99/6.21          | ~ (v5_relat_1 @ X32 @ (k2_relat_1 @ X32))
% 5.99/6.21          | (v2_funct_2 @ X32 @ (k2_relat_1 @ X32)))),
% 5.99/6.21      inference('simplify', [status(thm)], ['17'])).
% 5.99/6.21  thf(d10_xboole_0, axiom,
% 5.99/6.21    (![A:$i,B:$i]:
% 5.99/6.21     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.99/6.21  thf('19', plain,
% 5.99/6.21      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 5.99/6.21      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.99/6.21  thf('20', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 5.99/6.21      inference('simplify', [status(thm)], ['19'])).
% 5.99/6.21  thf(d19_relat_1, axiom,
% 5.99/6.21    (![A:$i,B:$i]:
% 5.99/6.21     ( ( v1_relat_1 @ B ) =>
% 5.99/6.21       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 5.99/6.21  thf('21', plain,
% 5.99/6.21      (![X16 : $i, X17 : $i]:
% 5.99/6.21         (~ (r1_tarski @ (k2_relat_1 @ X16) @ X17)
% 5.99/6.21          | (v5_relat_1 @ X16 @ X17)
% 5.99/6.21          | ~ (v1_relat_1 @ X16))),
% 5.99/6.21      inference('cnf', [status(esa)], [d19_relat_1])).
% 5.99/6.21  thf('22', plain,
% 5.99/6.21      (![X0 : $i]:
% 5.99/6.21         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 5.99/6.21      inference('sup-', [status(thm)], ['20', '21'])).
% 5.99/6.21  thf('23', plain,
% 5.99/6.21      (![X32 : $i]:
% 5.99/6.21         ((v2_funct_2 @ X32 @ (k2_relat_1 @ X32)) | ~ (v1_relat_1 @ X32))),
% 5.99/6.21      inference('clc', [status(thm)], ['18', '22'])).
% 5.99/6.21  thf('24', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 5.99/6.21      inference('sup+', [status(thm)], ['16', '23'])).
% 5.99/6.21  thf('25', plain,
% 5.99/6.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 5.99/6.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.21  thf(cc1_relset_1, axiom,
% 5.99/6.21    (![A:$i,B:$i,C:$i]:
% 5.99/6.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.99/6.21       ( v1_relat_1 @ C ) ))).
% 5.99/6.21  thf('26', plain,
% 5.99/6.21      (![X20 : $i, X21 : $i, X22 : $i]:
% 5.99/6.21         ((v1_relat_1 @ X20)
% 5.99/6.21          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 5.99/6.21      inference('cnf', [status(esa)], [cc1_relset_1])).
% 5.99/6.21  thf('27', plain, ((v1_relat_1 @ sk_D)),
% 5.99/6.21      inference('sup-', [status(thm)], ['25', '26'])).
% 5.99/6.21  thf('28', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 5.99/6.21      inference('demod', [status(thm)], ['24', '27'])).
% 5.99/6.21  thf('29', plain,
% 5.99/6.21      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 5.99/6.21      inference('split', [status(esa)], ['0'])).
% 5.99/6.21  thf('30', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 5.99/6.21      inference('sup-', [status(thm)], ['28', '29'])).
% 5.99/6.21  thf('31', plain,
% 5.99/6.21      (~ ((v2_funct_1 @ sk_C_1)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 5.99/6.21      inference('split', [status(esa)], ['0'])).
% 5.99/6.21  thf('32', plain, (~ ((v2_funct_1 @ sk_C_1))),
% 5.99/6.21      inference('sat_resolution*', [status(thm)], ['30', '31'])).
% 5.99/6.21  thf('33', plain, (~ (v2_funct_1 @ sk_C_1)),
% 5.99/6.21      inference('simpl_trail', [status(thm)], ['1', '32'])).
% 5.99/6.21  thf('34', plain,
% 5.99/6.21      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.99/6.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.21  thf(t3_subset, axiom,
% 5.99/6.21    (![A:$i,B:$i]:
% 5.99/6.21     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 5.99/6.21  thf('35', plain,
% 5.99/6.21      (![X10 : $i, X11 : $i]:
% 5.99/6.21         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 5.99/6.21      inference('cnf', [status(esa)], [t3_subset])).
% 5.99/6.21  thf('36', plain, ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 5.99/6.21      inference('sup-', [status(thm)], ['34', '35'])).
% 5.99/6.21  thf('37', plain,
% 5.99/6.21      (![X4 : $i, X6 : $i]:
% 5.99/6.21         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 5.99/6.21      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.99/6.21  thf('38', plain,
% 5.99/6.21      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C_1)
% 5.99/6.21        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 5.99/6.21      inference('sup-', [status(thm)], ['36', '37'])).
% 5.99/6.21  thf('39', plain,
% 5.99/6.21      ((r2_relset_1 @ sk_A @ sk_A @ 
% 5.99/6.21        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ 
% 5.99/6.21        (k6_partfun1 @ sk_A))),
% 5.99/6.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.21  thf('40', plain,
% 5.99/6.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 5.99/6.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.21  thf('41', plain,
% 5.99/6.21      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.99/6.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.21  thf(dt_k1_partfun1, axiom,
% 5.99/6.21    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 5.99/6.21     ( ( ( v1_funct_1 @ E ) & 
% 5.99/6.21         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.99/6.21         ( v1_funct_1 @ F ) & 
% 5.99/6.21         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 5.99/6.21       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 5.99/6.21         ( m1_subset_1 @
% 5.99/6.21           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 5.99/6.21           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 5.99/6.21  thf('42', plain,
% 5.99/6.21      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 5.99/6.21         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 5.99/6.21          | ~ (v1_funct_1 @ X33)
% 5.99/6.21          | ~ (v1_funct_1 @ X36)
% 5.99/6.21          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 5.99/6.21          | (m1_subset_1 @ (k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36) @ 
% 5.99/6.21             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X38))))),
% 5.99/6.21      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 5.99/6.21  thf('43', plain,
% 5.99/6.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.99/6.21         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 5.99/6.21           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 5.99/6.21          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 5.99/6.21          | ~ (v1_funct_1 @ X1)
% 5.99/6.21          | ~ (v1_funct_1 @ sk_C_1))),
% 5.99/6.21      inference('sup-', [status(thm)], ['41', '42'])).
% 5.99/6.21  thf('44', plain, ((v1_funct_1 @ sk_C_1)),
% 5.99/6.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.21  thf('45', plain,
% 5.99/6.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.99/6.21         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 5.99/6.21           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 5.99/6.21          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 5.99/6.21          | ~ (v1_funct_1 @ X1))),
% 5.99/6.21      inference('demod', [status(thm)], ['43', '44'])).
% 5.99/6.21  thf('46', plain,
% 5.99/6.21      ((~ (v1_funct_1 @ sk_D)
% 5.99/6.21        | (m1_subset_1 @ 
% 5.99/6.21           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ 
% 5.99/6.21           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 5.99/6.21      inference('sup-', [status(thm)], ['40', '45'])).
% 5.99/6.21  thf('47', plain, ((v1_funct_1 @ sk_D)),
% 5.99/6.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.21  thf('48', plain,
% 5.99/6.21      ((m1_subset_1 @ 
% 5.99/6.21        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ 
% 5.99/6.21        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.99/6.21      inference('demod', [status(thm)], ['46', '47'])).
% 5.99/6.21  thf(redefinition_r2_relset_1, axiom,
% 5.99/6.21    (![A:$i,B:$i,C:$i,D:$i]:
% 5.99/6.21     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.99/6.21         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.99/6.21       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 5.99/6.21  thf('49', plain,
% 5.99/6.21      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 5.99/6.21         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 5.99/6.21          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 5.99/6.21          | ((X26) = (X29))
% 5.99/6.21          | ~ (r2_relset_1 @ X27 @ X28 @ X26 @ X29))),
% 5.99/6.21      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 5.99/6.21  thf('50', plain,
% 5.99/6.21      (![X0 : $i]:
% 5.99/6.21         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 5.99/6.21             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ X0)
% 5.99/6.21          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D) = (X0))
% 5.99/6.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 5.99/6.21      inference('sup-', [status(thm)], ['48', '49'])).
% 5.99/6.21  thf('51', plain,
% 5.99/6.21      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 5.99/6.21           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 5.99/6.21        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D)
% 5.99/6.21            = (k6_partfun1 @ sk_A)))),
% 5.99/6.21      inference('sup-', [status(thm)], ['39', '50'])).
% 5.99/6.21  thf(t29_relset_1, axiom,
% 5.99/6.21    (![A:$i]:
% 5.99/6.21     ( m1_subset_1 @
% 5.99/6.21       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 5.99/6.21  thf('52', plain,
% 5.99/6.21      (![X30 : $i]:
% 5.99/6.21         (m1_subset_1 @ (k6_relat_1 @ X30) @ 
% 5.99/6.21          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 5.99/6.21      inference('cnf', [status(esa)], [t29_relset_1])).
% 5.99/6.21  thf(redefinition_k6_partfun1, axiom,
% 5.99/6.21    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 5.99/6.21  thf('53', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 5.99/6.21      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.99/6.21  thf('54', plain,
% 5.99/6.21      (![X30 : $i]:
% 5.99/6.21         (m1_subset_1 @ (k6_partfun1 @ X30) @ 
% 5.99/6.21          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 5.99/6.21      inference('demod', [status(thm)], ['52', '53'])).
% 5.99/6.21  thf('55', plain,
% 5.99/6.21      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D)
% 5.99/6.21         = (k6_partfun1 @ sk_A))),
% 5.99/6.21      inference('demod', [status(thm)], ['51', '54'])).
% 5.99/6.21  thf('56', plain,
% 5.99/6.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 5.99/6.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.21  thf(t26_funct_2, axiom,
% 5.99/6.21    (![A:$i,B:$i,C:$i,D:$i]:
% 5.99/6.21     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 5.99/6.21         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.99/6.21       ( ![E:$i]:
% 5.99/6.21         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 5.99/6.21             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 5.99/6.21           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 5.99/6.21             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 5.99/6.21               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 5.99/6.21  thf('57', plain,
% 5.99/6.21      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 5.99/6.21         (~ (v1_funct_1 @ X44)
% 5.99/6.21          | ~ (v1_funct_2 @ X44 @ X45 @ X46)
% 5.99/6.21          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 5.99/6.21          | ~ (v2_funct_1 @ (k1_partfun1 @ X47 @ X45 @ X45 @ X46 @ X48 @ X44))
% 5.99/6.21          | (v2_funct_1 @ X48)
% 5.99/6.21          | ((X46) = (k1_xboole_0))
% 5.99/6.21          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X45)))
% 5.99/6.21          | ~ (v1_funct_2 @ X48 @ X47 @ X45)
% 5.99/6.21          | ~ (v1_funct_1 @ X48))),
% 5.99/6.21      inference('cnf', [status(esa)], [t26_funct_2])).
% 5.99/6.21  thf('58', plain,
% 5.99/6.21      (![X0 : $i, X1 : $i]:
% 5.99/6.21         (~ (v1_funct_1 @ X0)
% 5.99/6.21          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 5.99/6.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 5.99/6.21          | ((sk_A) = (k1_xboole_0))
% 5.99/6.21          | (v2_funct_1 @ X0)
% 5.99/6.21          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 5.99/6.21          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 5.99/6.21          | ~ (v1_funct_1 @ sk_D))),
% 5.99/6.21      inference('sup-', [status(thm)], ['56', '57'])).
% 5.99/6.21  thf('59', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 5.99/6.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.21  thf('60', plain, ((v1_funct_1 @ sk_D)),
% 5.99/6.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.21  thf('61', plain,
% 5.99/6.21      (![X0 : $i, X1 : $i]:
% 5.99/6.21         (~ (v1_funct_1 @ X0)
% 5.99/6.21          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 5.99/6.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 5.99/6.21          | ((sk_A) = (k1_xboole_0))
% 5.99/6.21          | (v2_funct_1 @ X0)
% 5.99/6.21          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 5.99/6.21      inference('demod', [status(thm)], ['58', '59', '60'])).
% 5.99/6.21  thf('62', plain,
% 5.99/6.21      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 5.99/6.21        | (v2_funct_1 @ sk_C_1)
% 5.99/6.21        | ((sk_A) = (k1_xboole_0))
% 5.99/6.21        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 5.99/6.21        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)
% 5.99/6.21        | ~ (v1_funct_1 @ sk_C_1))),
% 5.99/6.21      inference('sup-', [status(thm)], ['55', '61'])).
% 5.99/6.21  thf(fc4_funct_1, axiom,
% 5.99/6.21    (![A:$i]:
% 5.99/6.21     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 5.99/6.21       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 5.99/6.21  thf('63', plain, (![X19 : $i]: (v2_funct_1 @ (k6_relat_1 @ X19))),
% 5.99/6.21      inference('cnf', [status(esa)], [fc4_funct_1])).
% 5.99/6.21  thf('64', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 5.99/6.21      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.99/6.21  thf('65', plain, (![X19 : $i]: (v2_funct_1 @ (k6_partfun1 @ X19))),
% 5.99/6.21      inference('demod', [status(thm)], ['63', '64'])).
% 5.99/6.21  thf('66', plain,
% 5.99/6.21      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.99/6.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.21  thf('67', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 5.99/6.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.21  thf('68', plain, ((v1_funct_1 @ sk_C_1)),
% 5.99/6.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.21  thf('69', plain, (((v2_funct_1 @ sk_C_1) | ((sk_A) = (k1_xboole_0)))),
% 5.99/6.21      inference('demod', [status(thm)], ['62', '65', '66', '67', '68'])).
% 5.99/6.21  thf('70', plain, (~ (v2_funct_1 @ sk_C_1)),
% 5.99/6.21      inference('simpl_trail', [status(thm)], ['1', '32'])).
% 5.99/6.21  thf('71', plain, (((sk_A) = (k1_xboole_0))),
% 5.99/6.21      inference('clc', [status(thm)], ['69', '70'])).
% 5.99/6.21  thf(t113_zfmisc_1, axiom,
% 5.99/6.21    (![A:$i,B:$i]:
% 5.99/6.21     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 5.99/6.21       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 5.99/6.21  thf('72', plain,
% 5.99/6.21      (![X8 : $i, X9 : $i]:
% 5.99/6.21         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 5.99/6.21      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 5.99/6.21  thf('73', plain,
% 5.99/6.21      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 5.99/6.21      inference('simplify', [status(thm)], ['72'])).
% 5.99/6.21  thf(d3_tarski, axiom,
% 5.99/6.21    (![A:$i,B:$i]:
% 5.99/6.21     ( ( r1_tarski @ A @ B ) <=>
% 5.99/6.21       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 5.99/6.21  thf('74', plain,
% 5.99/6.21      (![X1 : $i, X3 : $i]:
% 5.99/6.21         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 5.99/6.21      inference('cnf', [status(esa)], [d3_tarski])).
% 5.99/6.21  thf('75', plain,
% 5.99/6.21      (![X8 : $i, X9 : $i]:
% 5.99/6.21         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 5.99/6.21      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 5.99/6.21  thf('76', plain,
% 5.99/6.21      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 5.99/6.21      inference('simplify', [status(thm)], ['75'])).
% 5.99/6.21  thf('77', plain,
% 5.99/6.21      (![X30 : $i]:
% 5.99/6.21         (m1_subset_1 @ (k6_partfun1 @ X30) @ 
% 5.99/6.21          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 5.99/6.21      inference('demod', [status(thm)], ['52', '53'])).
% 5.99/6.21  thf('78', plain,
% 5.99/6.21      ((m1_subset_1 @ (k6_partfun1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 5.99/6.21      inference('sup+', [status(thm)], ['76', '77'])).
% 5.99/6.21  thf(t5_subset, axiom,
% 5.99/6.21    (![A:$i,B:$i,C:$i]:
% 5.99/6.21     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 5.99/6.21          ( v1_xboole_0 @ C ) ) ))).
% 5.99/6.21  thf('79', plain,
% 5.99/6.21      (![X13 : $i, X14 : $i, X15 : $i]:
% 5.99/6.21         (~ (r2_hidden @ X13 @ X14)
% 5.99/6.21          | ~ (v1_xboole_0 @ X15)
% 5.99/6.21          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 5.99/6.21      inference('cnf', [status(esa)], [t5_subset])).
% 5.99/6.21  thf('80', plain,
% 5.99/6.21      (![X0 : $i]:
% 5.99/6.21         (~ (v1_xboole_0 @ k1_xboole_0)
% 5.99/6.21          | ~ (r2_hidden @ X0 @ (k6_partfun1 @ k1_xboole_0)))),
% 5.99/6.21      inference('sup-', [status(thm)], ['78', '79'])).
% 5.99/6.21  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 5.99/6.21  thf('81', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.99/6.21      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 5.99/6.21  thf('82', plain,
% 5.99/6.21      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k6_partfun1 @ k1_xboole_0))),
% 5.99/6.21      inference('demod', [status(thm)], ['80', '81'])).
% 5.99/6.21  thf('83', plain,
% 5.99/6.21      (![X0 : $i]: (r1_tarski @ (k6_partfun1 @ k1_xboole_0) @ X0)),
% 5.99/6.21      inference('sup-', [status(thm)], ['74', '82'])).
% 5.99/6.21  thf('84', plain,
% 5.99/6.21      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 5.99/6.21      inference('simplify', [status(thm)], ['75'])).
% 5.99/6.21  thf('85', plain,
% 5.99/6.21      (![X30 : $i]:
% 5.99/6.21         (m1_subset_1 @ (k6_partfun1 @ X30) @ 
% 5.99/6.21          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 5.99/6.21      inference('demod', [status(thm)], ['52', '53'])).
% 5.99/6.21  thf('86', plain,
% 5.99/6.21      (![X10 : $i, X11 : $i]:
% 5.99/6.21         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 5.99/6.21      inference('cnf', [status(esa)], [t3_subset])).
% 5.99/6.21  thf('87', plain,
% 5.99/6.21      (![X0 : $i]: (r1_tarski @ (k6_partfun1 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))),
% 5.99/6.21      inference('sup-', [status(thm)], ['85', '86'])).
% 5.99/6.21  thf('88', plain,
% 5.99/6.21      (![X1 : $i, X3 : $i]:
% 5.99/6.21         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 5.99/6.21      inference('cnf', [status(esa)], [d3_tarski])).
% 5.99/6.21  thf('89', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 5.99/6.21      inference('simplify', [status(thm)], ['19'])).
% 5.99/6.21  thf('90', plain,
% 5.99/6.21      (![X10 : $i, X12 : $i]:
% 5.99/6.21         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 5.99/6.21      inference('cnf', [status(esa)], [t3_subset])).
% 5.99/6.21  thf('91', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 5.99/6.21      inference('sup-', [status(thm)], ['89', '90'])).
% 5.99/6.21  thf('92', plain,
% 5.99/6.21      (![X13 : $i, X14 : $i, X15 : $i]:
% 5.99/6.21         (~ (r2_hidden @ X13 @ X14)
% 5.99/6.21          | ~ (v1_xboole_0 @ X15)
% 5.99/6.21          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 5.99/6.21      inference('cnf', [status(esa)], [t5_subset])).
% 5.99/6.21  thf('93', plain,
% 5.99/6.21      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 5.99/6.21      inference('sup-', [status(thm)], ['91', '92'])).
% 5.99/6.21  thf('94', plain,
% 5.99/6.21      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 5.99/6.21      inference('sup-', [status(thm)], ['88', '93'])).
% 5.99/6.21  thf('95', plain,
% 5.99/6.21      (![X4 : $i, X6 : $i]:
% 5.99/6.21         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 5.99/6.21      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.99/6.21  thf('96', plain,
% 5.99/6.21      (![X0 : $i, X1 : $i]:
% 5.99/6.21         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 5.99/6.21      inference('sup-', [status(thm)], ['94', '95'])).
% 5.99/6.21  thf('97', plain,
% 5.99/6.21      (![X0 : $i]:
% 5.99/6.21         (((k6_partfun1 @ X0) = (k2_zfmisc_1 @ X0 @ X0))
% 5.99/6.21          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X0)))),
% 5.99/6.21      inference('sup-', [status(thm)], ['87', '96'])).
% 5.99/6.21  thf('98', plain,
% 5.99/6.21      ((~ (v1_xboole_0 @ k1_xboole_0)
% 5.99/6.21        | ((k6_partfun1 @ k1_xboole_0)
% 5.99/6.21            = (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 5.99/6.21      inference('sup-', [status(thm)], ['84', '97'])).
% 5.99/6.21  thf('99', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.99/6.21      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 5.99/6.21  thf('100', plain,
% 5.99/6.21      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 5.99/6.21      inference('simplify', [status(thm)], ['72'])).
% 5.99/6.21  thf('101', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 5.99/6.21      inference('demod', [status(thm)], ['98', '99', '100'])).
% 5.99/6.21  thf('102', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 5.99/6.21      inference('demod', [status(thm)], ['83', '101'])).
% 5.99/6.21  thf('103', plain, (((sk_A) = (k1_xboole_0))),
% 5.99/6.21      inference('clc', [status(thm)], ['69', '70'])).
% 5.99/6.21  thf('104', plain,
% 5.99/6.21      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 5.99/6.21      inference('simplify', [status(thm)], ['72'])).
% 5.99/6.21  thf('105', plain, (((k1_xboole_0) = (sk_C_1))),
% 5.99/6.21      inference('demod', [status(thm)], ['38', '71', '73', '102', '103', '104'])).
% 5.99/6.21  thf('106', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 5.99/6.21      inference('demod', [status(thm)], ['98', '99', '100'])).
% 5.99/6.21  thf('107', plain, (![X19 : $i]: (v2_funct_1 @ (k6_partfun1 @ X19))),
% 5.99/6.21      inference('demod', [status(thm)], ['63', '64'])).
% 5.99/6.21  thf('108', plain, ((v2_funct_1 @ k1_xboole_0)),
% 5.99/6.21      inference('sup+', [status(thm)], ['106', '107'])).
% 5.99/6.21  thf('109', plain, ($false),
% 5.99/6.21      inference('demod', [status(thm)], ['33', '105', '108'])).
% 5.99/6.21  
% 5.99/6.21  % SZS output end Refutation
% 5.99/6.21  
% 5.99/6.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

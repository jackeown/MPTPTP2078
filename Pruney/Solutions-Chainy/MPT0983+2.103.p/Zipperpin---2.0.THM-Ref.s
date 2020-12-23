%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KNeNVv32g7

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:17 EST 2020

% Result     : Theorem 3.92s
% Output     : Refutation 4.00s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 467 expanded)
%              Number of leaves         :   43 ( 153 expanded)
%              Depth                    :   14
%              Number of atoms          : 1278 (7918 expanded)
%              Number of equality atoms :   50 ( 142 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

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

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('4',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
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

thf('6',plain,(
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

thf('7',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('8',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( r2_relset_1 @ X41 @ X41 @ ( k1_partfun1 @ X41 @ X42 @ X42 @ X41 @ X40 @ X43 ) @ ( k6_relat_1 @ X41 ) )
      | ( ( k2_relset_1 @ X42 @ X41 @ X43 )
        = X41 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X42 @ X41 )
      | ~ ( v1_funct_1 @ X43 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['4','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('15',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('16',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['13','16','17','18','19'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['21'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('23',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X16 ) @ X17 )
      | ( v5_relat_1 @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('25',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k2_relat_1 @ X30 )
       != X29 )
      | ( v2_funct_2 @ X30 @ X29 )
      | ~ ( v5_relat_1 @ X30 @ X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('26',plain,(
    ! [X30: $i] :
      ( ~ ( v1_relat_1 @ X30 )
      | ~ ( v5_relat_1 @ X30 @ ( k2_relat_1 @ X30 ) )
      | ( v2_funct_2 @ X30 @ ( k2_relat_1 @ X30 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['20','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('31',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('32',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('40',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('41',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('43',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C_1 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
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

thf('47',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X32 @ X33 @ X35 @ X36 @ X31 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['45','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('54',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( X25 = X28 )
      | ~ ( r2_relset_1 @ X26 @ X27 @ X25 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','55'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('57',plain,(
    ! [X38: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('58',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('59',plain,(
    ! [X38: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('61',plain,(
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

thf('62',plain,(
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

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['60','66'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('68',plain,(
    ! [X18: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('69',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v2_funct_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','68','69','70','71'])).

thf('73',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','37'])).

thf('74',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['72','73'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('75',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('76',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['75'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('77',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('78',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('79',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X38: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('81',plain,(
    m1_subset_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('82',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k6_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('84',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('85',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k6_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    m1_subset_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('87',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('88',plain,(
    r1_tarski @ ( k6_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('90',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('91',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('92',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','94'])).

thf('96',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ( k6_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','97'])).

thf('99',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('100',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['85','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['77','101'])).

thf('103',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['72','73'])).

thf('104',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['75'])).

thf('105',plain,(
    k1_xboole_0 = sk_C_1 ),
    inference(demod,[status(thm)],['43','74','76','102','103','104'])).

thf('106',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['98','99'])).

thf('107',plain,(
    ! [X18: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('108',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    $false ),
    inference(demod,[status(thm)],['38','105','108'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KNeNVv32g7
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:32:20 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 3.92/4.17  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.92/4.17  % Solved by: fo/fo7.sh
% 3.92/4.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.92/4.17  % done 5745 iterations in 3.737s
% 3.92/4.17  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.92/4.17  % SZS output start Refutation
% 3.92/4.17  thf(sk_A_type, type, sk_A: $i).
% 3.92/4.17  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.92/4.17  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.92/4.17  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.92/4.17  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.92/4.17  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.92/4.17  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 3.92/4.17  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.92/4.17  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 3.92/4.17  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.92/4.17  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.92/4.17  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.92/4.17  thf(sk_B_type, type, sk_B: $i).
% 3.92/4.17  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.92/4.17  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.92/4.17  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.92/4.17  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.92/4.17  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.92/4.17  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.92/4.17  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.92/4.17  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.92/4.17  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.92/4.17  thf(sk_D_type, type, sk_D: $i).
% 3.92/4.17  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.92/4.17  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.92/4.17  thf(t29_funct_2, conjecture,
% 3.92/4.17    (![A:$i,B:$i,C:$i]:
% 3.92/4.17     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.92/4.17         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.92/4.17       ( ![D:$i]:
% 3.92/4.17         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.92/4.17             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.92/4.17           ( ( r2_relset_1 @
% 3.92/4.17               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.92/4.17               ( k6_partfun1 @ A ) ) =>
% 3.92/4.17             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 3.92/4.17  thf(zf_stmt_0, negated_conjecture,
% 3.92/4.17    (~( ![A:$i,B:$i,C:$i]:
% 3.92/4.17        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.92/4.17            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.92/4.17          ( ![D:$i]:
% 3.92/4.17            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.92/4.17                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.92/4.17              ( ( r2_relset_1 @
% 3.92/4.17                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.92/4.17                  ( k6_partfun1 @ A ) ) =>
% 3.92/4.17                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 3.92/4.17    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 3.92/4.17  thf('0', plain, ((~ (v2_funct_1 @ sk_C_1) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 3.92/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.92/4.17  thf('1', plain, ((~ (v2_funct_1 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 3.92/4.17      inference('split', [status(esa)], ['0'])).
% 3.92/4.17  thf('2', plain,
% 3.92/4.17      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.92/4.17        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ 
% 3.92/4.17        (k6_partfun1 @ sk_A))),
% 3.92/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.92/4.17  thf(redefinition_k6_partfun1, axiom,
% 3.92/4.17    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 3.92/4.17  thf('3', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 3.92/4.17      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.92/4.17  thf('4', plain,
% 3.92/4.17      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.92/4.17        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ 
% 3.92/4.17        (k6_relat_1 @ sk_A))),
% 3.92/4.17      inference('demod', [status(thm)], ['2', '3'])).
% 3.92/4.17  thf('5', plain,
% 3.92/4.17      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.92/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.92/4.17  thf(t24_funct_2, axiom,
% 3.92/4.17    (![A:$i,B:$i,C:$i]:
% 3.92/4.17     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.92/4.17         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.92/4.17       ( ![D:$i]:
% 3.92/4.17         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.92/4.17             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.92/4.17           ( ( r2_relset_1 @
% 3.92/4.17               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 3.92/4.17               ( k6_partfun1 @ B ) ) =>
% 3.92/4.17             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 3.92/4.17  thf('6', plain,
% 3.92/4.17      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 3.92/4.17         (~ (v1_funct_1 @ X40)
% 3.92/4.17          | ~ (v1_funct_2 @ X40 @ X41 @ X42)
% 3.92/4.17          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 3.92/4.17          | ~ (r2_relset_1 @ X41 @ X41 @ 
% 3.92/4.17               (k1_partfun1 @ X41 @ X42 @ X42 @ X41 @ X40 @ X43) @ 
% 3.92/4.17               (k6_partfun1 @ X41))
% 3.92/4.17          | ((k2_relset_1 @ X42 @ X41 @ X43) = (X41))
% 3.92/4.17          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41)))
% 3.92/4.17          | ~ (v1_funct_2 @ X43 @ X42 @ X41)
% 3.92/4.17          | ~ (v1_funct_1 @ X43))),
% 3.92/4.17      inference('cnf', [status(esa)], [t24_funct_2])).
% 3.92/4.17  thf('7', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 3.92/4.17      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.92/4.17  thf('8', plain,
% 3.92/4.17      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 3.92/4.17         (~ (v1_funct_1 @ X40)
% 3.92/4.17          | ~ (v1_funct_2 @ X40 @ X41 @ X42)
% 3.92/4.17          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 3.92/4.17          | ~ (r2_relset_1 @ X41 @ X41 @ 
% 3.92/4.17               (k1_partfun1 @ X41 @ X42 @ X42 @ X41 @ X40 @ X43) @ 
% 3.92/4.17               (k6_relat_1 @ X41))
% 3.92/4.17          | ((k2_relset_1 @ X42 @ X41 @ X43) = (X41))
% 3.92/4.17          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41)))
% 3.92/4.17          | ~ (v1_funct_2 @ X43 @ X42 @ X41)
% 3.92/4.17          | ~ (v1_funct_1 @ X43))),
% 3.92/4.17      inference('demod', [status(thm)], ['6', '7'])).
% 3.92/4.17  thf('9', plain,
% 3.92/4.17      (![X0 : $i]:
% 3.92/4.17         (~ (v1_funct_1 @ X0)
% 3.92/4.17          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 3.92/4.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.92/4.17          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 3.92/4.17          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.92/4.17               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 3.92/4.17               (k6_relat_1 @ sk_A))
% 3.92/4.17          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)
% 3.92/4.17          | ~ (v1_funct_1 @ sk_C_1))),
% 3.92/4.17      inference('sup-', [status(thm)], ['5', '8'])).
% 4.00/4.17  thf('10', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 4.00/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.17  thf('11', plain, ((v1_funct_1 @ sk_C_1)),
% 4.00/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.17  thf('12', plain,
% 4.00/4.17      (![X0 : $i]:
% 4.00/4.17         (~ (v1_funct_1 @ X0)
% 4.00/4.17          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 4.00/4.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 4.00/4.17          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 4.00/4.17          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 4.00/4.17               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 4.00/4.17               (k6_relat_1 @ sk_A)))),
% 4.00/4.17      inference('demod', [status(thm)], ['9', '10', '11'])).
% 4.00/4.17  thf('13', plain,
% 4.00/4.17      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 4.00/4.17        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 4.00/4.17        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 4.00/4.17        | ~ (v1_funct_1 @ sk_D))),
% 4.00/4.17      inference('sup-', [status(thm)], ['4', '12'])).
% 4.00/4.17  thf('14', plain,
% 4.00/4.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.00/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.17  thf(redefinition_k2_relset_1, axiom,
% 4.00/4.17    (![A:$i,B:$i,C:$i]:
% 4.00/4.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.00/4.17       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 4.00/4.17  thf('15', plain,
% 4.00/4.17      (![X22 : $i, X23 : $i, X24 : $i]:
% 4.00/4.17         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 4.00/4.17          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 4.00/4.17      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.00/4.17  thf('16', plain,
% 4.00/4.17      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 4.00/4.17      inference('sup-', [status(thm)], ['14', '15'])).
% 4.00/4.17  thf('17', plain,
% 4.00/4.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.00/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.17  thf('18', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 4.00/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.17  thf('19', plain, ((v1_funct_1 @ sk_D)),
% 4.00/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.17  thf('20', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 4.00/4.17      inference('demod', [status(thm)], ['13', '16', '17', '18', '19'])).
% 4.00/4.17  thf(d10_xboole_0, axiom,
% 4.00/4.17    (![A:$i,B:$i]:
% 4.00/4.17     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.00/4.17  thf('21', plain,
% 4.00/4.17      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 4.00/4.17      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.00/4.17  thf('22', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 4.00/4.17      inference('simplify', [status(thm)], ['21'])).
% 4.00/4.17  thf(d19_relat_1, axiom,
% 4.00/4.17    (![A:$i,B:$i]:
% 4.00/4.17     ( ( v1_relat_1 @ B ) =>
% 4.00/4.17       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 4.00/4.17  thf('23', plain,
% 4.00/4.17      (![X16 : $i, X17 : $i]:
% 4.00/4.17         (~ (r1_tarski @ (k2_relat_1 @ X16) @ X17)
% 4.00/4.17          | (v5_relat_1 @ X16 @ X17)
% 4.00/4.17          | ~ (v1_relat_1 @ X16))),
% 4.00/4.17      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.00/4.17  thf('24', plain,
% 4.00/4.17      (![X0 : $i]:
% 4.00/4.17         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 4.00/4.17      inference('sup-', [status(thm)], ['22', '23'])).
% 4.00/4.17  thf(d3_funct_2, axiom,
% 4.00/4.17    (![A:$i,B:$i]:
% 4.00/4.17     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 4.00/4.17       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 4.00/4.17  thf('25', plain,
% 4.00/4.17      (![X29 : $i, X30 : $i]:
% 4.00/4.17         (((k2_relat_1 @ X30) != (X29))
% 4.00/4.17          | (v2_funct_2 @ X30 @ X29)
% 4.00/4.17          | ~ (v5_relat_1 @ X30 @ X29)
% 4.00/4.17          | ~ (v1_relat_1 @ X30))),
% 4.00/4.17      inference('cnf', [status(esa)], [d3_funct_2])).
% 4.00/4.17  thf('26', plain,
% 4.00/4.17      (![X30 : $i]:
% 4.00/4.17         (~ (v1_relat_1 @ X30)
% 4.00/4.17          | ~ (v5_relat_1 @ X30 @ (k2_relat_1 @ X30))
% 4.00/4.17          | (v2_funct_2 @ X30 @ (k2_relat_1 @ X30)))),
% 4.00/4.17      inference('simplify', [status(thm)], ['25'])).
% 4.00/4.17  thf('27', plain,
% 4.00/4.17      (![X0 : $i]:
% 4.00/4.17         (~ (v1_relat_1 @ X0)
% 4.00/4.17          | (v2_funct_2 @ X0 @ (k2_relat_1 @ X0))
% 4.00/4.17          | ~ (v1_relat_1 @ X0))),
% 4.00/4.17      inference('sup-', [status(thm)], ['24', '26'])).
% 4.00/4.17  thf('28', plain,
% 4.00/4.17      (![X0 : $i]:
% 4.00/4.17         ((v2_funct_2 @ X0 @ (k2_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 4.00/4.17      inference('simplify', [status(thm)], ['27'])).
% 4.00/4.17  thf('29', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 4.00/4.17      inference('sup+', [status(thm)], ['20', '28'])).
% 4.00/4.17  thf('30', plain,
% 4.00/4.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.00/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.17  thf(cc1_relset_1, axiom,
% 4.00/4.17    (![A:$i,B:$i,C:$i]:
% 4.00/4.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.00/4.17       ( v1_relat_1 @ C ) ))).
% 4.00/4.17  thf('31', plain,
% 4.00/4.17      (![X19 : $i, X20 : $i, X21 : $i]:
% 4.00/4.17         ((v1_relat_1 @ X19)
% 4.00/4.17          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 4.00/4.17      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.00/4.17  thf('32', plain, ((v1_relat_1 @ sk_D)),
% 4.00/4.17      inference('sup-', [status(thm)], ['30', '31'])).
% 4.00/4.17  thf('33', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 4.00/4.17      inference('demod', [status(thm)], ['29', '32'])).
% 4.00/4.17  thf('34', plain,
% 4.00/4.17      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 4.00/4.17      inference('split', [status(esa)], ['0'])).
% 4.00/4.17  thf('35', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 4.00/4.17      inference('sup-', [status(thm)], ['33', '34'])).
% 4.00/4.17  thf('36', plain,
% 4.00/4.17      (~ ((v2_funct_1 @ sk_C_1)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 4.00/4.17      inference('split', [status(esa)], ['0'])).
% 4.00/4.17  thf('37', plain, (~ ((v2_funct_1 @ sk_C_1))),
% 4.00/4.17      inference('sat_resolution*', [status(thm)], ['35', '36'])).
% 4.00/4.17  thf('38', plain, (~ (v2_funct_1 @ sk_C_1)),
% 4.00/4.17      inference('simpl_trail', [status(thm)], ['1', '37'])).
% 4.00/4.17  thf('39', plain,
% 4.00/4.17      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.00/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.17  thf(t3_subset, axiom,
% 4.00/4.17    (![A:$i,B:$i]:
% 4.00/4.17     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.00/4.17  thf('40', plain,
% 4.00/4.17      (![X10 : $i, X11 : $i]:
% 4.00/4.17         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 4.00/4.17      inference('cnf', [status(esa)], [t3_subset])).
% 4.00/4.17  thf('41', plain, ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 4.00/4.17      inference('sup-', [status(thm)], ['39', '40'])).
% 4.00/4.17  thf('42', plain,
% 4.00/4.17      (![X4 : $i, X6 : $i]:
% 4.00/4.17         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 4.00/4.17      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.00/4.17  thf('43', plain,
% 4.00/4.17      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C_1)
% 4.00/4.17        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 4.00/4.17      inference('sup-', [status(thm)], ['41', '42'])).
% 4.00/4.17  thf('44', plain,
% 4.00/4.17      ((r2_relset_1 @ sk_A @ sk_A @ 
% 4.00/4.17        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ 
% 4.00/4.17        (k6_relat_1 @ sk_A))),
% 4.00/4.17      inference('demod', [status(thm)], ['2', '3'])).
% 4.00/4.17  thf('45', plain,
% 4.00/4.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.00/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.17  thf('46', plain,
% 4.00/4.17      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.00/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.17  thf(dt_k1_partfun1, axiom,
% 4.00/4.17    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.00/4.17     ( ( ( v1_funct_1 @ E ) & 
% 4.00/4.17         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.00/4.17         ( v1_funct_1 @ F ) & 
% 4.00/4.17         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 4.00/4.17       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 4.00/4.17         ( m1_subset_1 @
% 4.00/4.17           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 4.00/4.17           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 4.00/4.17  thf('47', plain,
% 4.00/4.17      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 4.00/4.17         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 4.00/4.17          | ~ (v1_funct_1 @ X31)
% 4.00/4.17          | ~ (v1_funct_1 @ X34)
% 4.00/4.17          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 4.00/4.17          | (m1_subset_1 @ (k1_partfun1 @ X32 @ X33 @ X35 @ X36 @ X31 @ X34) @ 
% 4.00/4.17             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X36))))),
% 4.00/4.17      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 4.00/4.17  thf('48', plain,
% 4.00/4.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.00/4.17         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 4.00/4.17           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 4.00/4.17          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 4.00/4.17          | ~ (v1_funct_1 @ X1)
% 4.00/4.17          | ~ (v1_funct_1 @ sk_C_1))),
% 4.00/4.17      inference('sup-', [status(thm)], ['46', '47'])).
% 4.00/4.17  thf('49', plain, ((v1_funct_1 @ sk_C_1)),
% 4.00/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.17  thf('50', plain,
% 4.00/4.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.00/4.17         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 4.00/4.17           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 4.00/4.17          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 4.00/4.17          | ~ (v1_funct_1 @ X1))),
% 4.00/4.17      inference('demod', [status(thm)], ['48', '49'])).
% 4.00/4.17  thf('51', plain,
% 4.00/4.17      ((~ (v1_funct_1 @ sk_D)
% 4.00/4.17        | (m1_subset_1 @ 
% 4.00/4.17           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ 
% 4.00/4.17           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 4.00/4.17      inference('sup-', [status(thm)], ['45', '50'])).
% 4.00/4.17  thf('52', plain, ((v1_funct_1 @ sk_D)),
% 4.00/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.17  thf('53', plain,
% 4.00/4.17      ((m1_subset_1 @ 
% 4.00/4.17        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ 
% 4.00/4.17        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.00/4.17      inference('demod', [status(thm)], ['51', '52'])).
% 4.00/4.17  thf(redefinition_r2_relset_1, axiom,
% 4.00/4.17    (![A:$i,B:$i,C:$i,D:$i]:
% 4.00/4.17     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.00/4.17         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.00/4.17       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 4.00/4.17  thf('54', plain,
% 4.00/4.17      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 4.00/4.17         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 4.00/4.17          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 4.00/4.17          | ((X25) = (X28))
% 4.00/4.17          | ~ (r2_relset_1 @ X26 @ X27 @ X25 @ X28))),
% 4.00/4.17      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 4.00/4.17  thf('55', plain,
% 4.00/4.17      (![X0 : $i]:
% 4.00/4.17         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 4.00/4.17             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ X0)
% 4.00/4.17          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D) = (X0))
% 4.00/4.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 4.00/4.17      inference('sup-', [status(thm)], ['53', '54'])).
% 4.00/4.17  thf('56', plain,
% 4.00/4.17      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 4.00/4.17           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 4.00/4.17        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D)
% 4.00/4.17            = (k6_relat_1 @ sk_A)))),
% 4.00/4.17      inference('sup-', [status(thm)], ['44', '55'])).
% 4.00/4.17  thf(dt_k6_partfun1, axiom,
% 4.00/4.17    (![A:$i]:
% 4.00/4.17     ( ( m1_subset_1 @
% 4.00/4.17         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 4.00/4.17       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 4.00/4.17  thf('57', plain,
% 4.00/4.17      (![X38 : $i]:
% 4.00/4.17         (m1_subset_1 @ (k6_partfun1 @ X38) @ 
% 4.00/4.17          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X38)))),
% 4.00/4.17      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 4.00/4.17  thf('58', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 4.00/4.17      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.00/4.17  thf('59', plain,
% 4.00/4.17      (![X38 : $i]:
% 4.00/4.17         (m1_subset_1 @ (k6_relat_1 @ X38) @ 
% 4.00/4.17          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X38)))),
% 4.00/4.17      inference('demod', [status(thm)], ['57', '58'])).
% 4.00/4.17  thf('60', plain,
% 4.00/4.17      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D)
% 4.00/4.17         = (k6_relat_1 @ sk_A))),
% 4.00/4.17      inference('demod', [status(thm)], ['56', '59'])).
% 4.00/4.17  thf('61', plain,
% 4.00/4.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.00/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.17  thf(t26_funct_2, axiom,
% 4.00/4.17    (![A:$i,B:$i,C:$i,D:$i]:
% 4.00/4.17     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 4.00/4.17         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.00/4.17       ( ![E:$i]:
% 4.00/4.17         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 4.00/4.17             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 4.00/4.17           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 4.00/4.17             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 4.00/4.17               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 4.00/4.17  thf('62', plain,
% 4.00/4.17      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 4.00/4.17         (~ (v1_funct_1 @ X44)
% 4.00/4.17          | ~ (v1_funct_2 @ X44 @ X45 @ X46)
% 4.00/4.17          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 4.00/4.17          | ~ (v2_funct_1 @ (k1_partfun1 @ X47 @ X45 @ X45 @ X46 @ X48 @ X44))
% 4.00/4.17          | (v2_funct_1 @ X48)
% 4.00/4.17          | ((X46) = (k1_xboole_0))
% 4.00/4.17          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X45)))
% 4.00/4.17          | ~ (v1_funct_2 @ X48 @ X47 @ X45)
% 4.00/4.17          | ~ (v1_funct_1 @ X48))),
% 4.00/4.17      inference('cnf', [status(esa)], [t26_funct_2])).
% 4.00/4.17  thf('63', plain,
% 4.00/4.17      (![X0 : $i, X1 : $i]:
% 4.00/4.17         (~ (v1_funct_1 @ X0)
% 4.00/4.17          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 4.00/4.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 4.00/4.17          | ((sk_A) = (k1_xboole_0))
% 4.00/4.17          | (v2_funct_1 @ X0)
% 4.00/4.17          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 4.00/4.17          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 4.00/4.17          | ~ (v1_funct_1 @ sk_D))),
% 4.00/4.17      inference('sup-', [status(thm)], ['61', '62'])).
% 4.00/4.17  thf('64', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 4.00/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.17  thf('65', plain, ((v1_funct_1 @ sk_D)),
% 4.00/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.17  thf('66', plain,
% 4.00/4.17      (![X0 : $i, X1 : $i]:
% 4.00/4.17         (~ (v1_funct_1 @ X0)
% 4.00/4.17          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 4.00/4.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 4.00/4.17          | ((sk_A) = (k1_xboole_0))
% 4.00/4.17          | (v2_funct_1 @ X0)
% 4.00/4.17          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 4.00/4.17      inference('demod', [status(thm)], ['63', '64', '65'])).
% 4.00/4.17  thf('67', plain,
% 4.00/4.17      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 4.00/4.17        | (v2_funct_1 @ sk_C_1)
% 4.00/4.17        | ((sk_A) = (k1_xboole_0))
% 4.00/4.17        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 4.00/4.17        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)
% 4.00/4.17        | ~ (v1_funct_1 @ sk_C_1))),
% 4.00/4.17      inference('sup-', [status(thm)], ['60', '66'])).
% 4.00/4.17  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 4.00/4.17  thf('68', plain, (![X18 : $i]: (v2_funct_1 @ (k6_relat_1 @ X18))),
% 4.00/4.17      inference('cnf', [status(esa)], [t52_funct_1])).
% 4.00/4.17  thf('69', plain,
% 4.00/4.17      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.00/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.17  thf('70', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 4.00/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.17  thf('71', plain, ((v1_funct_1 @ sk_C_1)),
% 4.00/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.17  thf('72', plain, (((v2_funct_1 @ sk_C_1) | ((sk_A) = (k1_xboole_0)))),
% 4.00/4.17      inference('demod', [status(thm)], ['67', '68', '69', '70', '71'])).
% 4.00/4.17  thf('73', plain, (~ (v2_funct_1 @ sk_C_1)),
% 4.00/4.17      inference('simpl_trail', [status(thm)], ['1', '37'])).
% 4.00/4.17  thf('74', plain, (((sk_A) = (k1_xboole_0))),
% 4.00/4.17      inference('clc', [status(thm)], ['72', '73'])).
% 4.00/4.17  thf(t113_zfmisc_1, axiom,
% 4.00/4.17    (![A:$i,B:$i]:
% 4.00/4.17     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 4.00/4.17       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 4.00/4.17  thf('75', plain,
% 4.00/4.17      (![X8 : $i, X9 : $i]:
% 4.00/4.17         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 4.00/4.17      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 4.00/4.17  thf('76', plain,
% 4.00/4.17      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 4.00/4.17      inference('simplify', [status(thm)], ['75'])).
% 4.00/4.17  thf(d3_tarski, axiom,
% 4.00/4.17    (![A:$i,B:$i]:
% 4.00/4.17     ( ( r1_tarski @ A @ B ) <=>
% 4.00/4.17       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 4.00/4.17  thf('77', plain,
% 4.00/4.17      (![X1 : $i, X3 : $i]:
% 4.00/4.17         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 4.00/4.17      inference('cnf', [status(esa)], [d3_tarski])).
% 4.00/4.17  thf('78', plain,
% 4.00/4.17      (![X8 : $i, X9 : $i]:
% 4.00/4.17         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 4.00/4.17      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 4.00/4.17  thf('79', plain,
% 4.00/4.17      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 4.00/4.17      inference('simplify', [status(thm)], ['78'])).
% 4.00/4.17  thf('80', plain,
% 4.00/4.17      (![X38 : $i]:
% 4.00/4.17         (m1_subset_1 @ (k6_relat_1 @ X38) @ 
% 4.00/4.17          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X38)))),
% 4.00/4.17      inference('demod', [status(thm)], ['57', '58'])).
% 4.00/4.17  thf('81', plain,
% 4.00/4.17      ((m1_subset_1 @ (k6_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 4.00/4.17      inference('sup+', [status(thm)], ['79', '80'])).
% 4.00/4.17  thf(t5_subset, axiom,
% 4.00/4.17    (![A:$i,B:$i,C:$i]:
% 4.00/4.17     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 4.00/4.17          ( v1_xboole_0 @ C ) ) ))).
% 4.00/4.17  thf('82', plain,
% 4.00/4.17      (![X13 : $i, X14 : $i, X15 : $i]:
% 4.00/4.17         (~ (r2_hidden @ X13 @ X14)
% 4.00/4.17          | ~ (v1_xboole_0 @ X15)
% 4.00/4.17          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 4.00/4.17      inference('cnf', [status(esa)], [t5_subset])).
% 4.00/4.17  thf('83', plain,
% 4.00/4.17      (![X0 : $i]:
% 4.00/4.17         (~ (v1_xboole_0 @ k1_xboole_0)
% 4.00/4.17          | ~ (r2_hidden @ X0 @ (k6_relat_1 @ k1_xboole_0)))),
% 4.00/4.17      inference('sup-', [status(thm)], ['81', '82'])).
% 4.00/4.17  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 4.00/4.17  thf('84', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.00/4.17      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.00/4.17  thf('85', plain,
% 4.00/4.17      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k6_relat_1 @ k1_xboole_0))),
% 4.00/4.17      inference('demod', [status(thm)], ['83', '84'])).
% 4.00/4.17  thf('86', plain,
% 4.00/4.17      ((m1_subset_1 @ (k6_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 4.00/4.17      inference('sup+', [status(thm)], ['79', '80'])).
% 4.00/4.17  thf('87', plain,
% 4.00/4.17      (![X10 : $i, X11 : $i]:
% 4.00/4.17         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 4.00/4.17      inference('cnf', [status(esa)], [t3_subset])).
% 4.00/4.17  thf('88', plain, ((r1_tarski @ (k6_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 4.00/4.17      inference('sup-', [status(thm)], ['86', '87'])).
% 4.00/4.17  thf('89', plain,
% 4.00/4.17      (![X1 : $i, X3 : $i]:
% 4.00/4.17         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 4.00/4.17      inference('cnf', [status(esa)], [d3_tarski])).
% 4.00/4.17  thf('90', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 4.00/4.17      inference('simplify', [status(thm)], ['21'])).
% 4.00/4.17  thf('91', plain,
% 4.00/4.17      (![X10 : $i, X12 : $i]:
% 4.00/4.17         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 4.00/4.17      inference('cnf', [status(esa)], [t3_subset])).
% 4.00/4.17  thf('92', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 4.00/4.17      inference('sup-', [status(thm)], ['90', '91'])).
% 4.00/4.17  thf('93', plain,
% 4.00/4.17      (![X13 : $i, X14 : $i, X15 : $i]:
% 4.00/4.17         (~ (r2_hidden @ X13 @ X14)
% 4.00/4.17          | ~ (v1_xboole_0 @ X15)
% 4.00/4.17          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 4.00/4.17      inference('cnf', [status(esa)], [t5_subset])).
% 4.00/4.17  thf('94', plain,
% 4.00/4.17      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 4.00/4.17      inference('sup-', [status(thm)], ['92', '93'])).
% 4.00/4.17  thf('95', plain,
% 4.00/4.17      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 4.00/4.17      inference('sup-', [status(thm)], ['89', '94'])).
% 4.00/4.17  thf('96', plain,
% 4.00/4.17      (![X4 : $i, X6 : $i]:
% 4.00/4.17         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 4.00/4.17      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.00/4.17  thf('97', plain,
% 4.00/4.17      (![X0 : $i, X1 : $i]:
% 4.00/4.17         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 4.00/4.17      inference('sup-', [status(thm)], ['95', '96'])).
% 4.00/4.17  thf('98', plain,
% 4.00/4.17      ((((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 4.00/4.17        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 4.00/4.17      inference('sup-', [status(thm)], ['88', '97'])).
% 4.00/4.17  thf('99', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.00/4.17      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.00/4.17  thf('100', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.00/4.17      inference('demod', [status(thm)], ['98', '99'])).
% 4.00/4.17  thf('101', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 4.00/4.17      inference('demod', [status(thm)], ['85', '100'])).
% 4.00/4.17  thf('102', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 4.00/4.17      inference('sup-', [status(thm)], ['77', '101'])).
% 4.00/4.17  thf('103', plain, (((sk_A) = (k1_xboole_0))),
% 4.00/4.17      inference('clc', [status(thm)], ['72', '73'])).
% 4.00/4.17  thf('104', plain,
% 4.00/4.17      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 4.00/4.17      inference('simplify', [status(thm)], ['75'])).
% 4.00/4.17  thf('105', plain, (((k1_xboole_0) = (sk_C_1))),
% 4.00/4.17      inference('demod', [status(thm)], ['43', '74', '76', '102', '103', '104'])).
% 4.00/4.17  thf('106', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.00/4.17      inference('demod', [status(thm)], ['98', '99'])).
% 4.00/4.17  thf('107', plain, (![X18 : $i]: (v2_funct_1 @ (k6_relat_1 @ X18))),
% 4.00/4.17      inference('cnf', [status(esa)], [t52_funct_1])).
% 4.00/4.17  thf('108', plain, ((v2_funct_1 @ k1_xboole_0)),
% 4.00/4.17      inference('sup+', [status(thm)], ['106', '107'])).
% 4.00/4.17  thf('109', plain, ($false),
% 4.00/4.17      inference('demod', [status(thm)], ['38', '105', '108'])).
% 4.00/4.17  
% 4.00/4.17  % SZS output end Refutation
% 4.00/4.17  
% 4.00/4.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

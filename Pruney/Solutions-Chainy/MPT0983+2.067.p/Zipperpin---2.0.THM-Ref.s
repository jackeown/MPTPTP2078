%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZUEhxix7qI

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:11 EST 2020

% Result     : Theorem 10.23s
% Output     : Refutation 10.23s
% Verified   : 
% Statistics : Number of formulae       :  186 ( 751 expanded)
%              Number of leaves         :   47 ( 231 expanded)
%              Depth                    :   18
%              Number of atoms          : 1560 (15738 expanded)
%              Number of equality atoms :   78 ( 236 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
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

thf('4',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( ( k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42 )
        = ( k5_relat_1 @ X39 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
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

thf('12',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ~ ( r2_relset_1 @ X47 @ X47 @ ( k1_partfun1 @ X47 @ X48 @ X48 @ X47 @ X46 @ X49 ) @ ( k6_partfun1 @ X47 ) )
      | ( ( k2_relset_1 @ X48 @ X47 @ X49 )
        = X47 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X47 ) ) )
      | ~ ( v1_funct_2 @ X49 @ X48 @ X47 )
      | ~ ( v1_funct_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('19',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('20',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relat_1 @ sk_D )
      = sk_A ) ),
    inference(demod,[status(thm)],['17','20','21','22','23'])).

thf('25',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('27',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['24','27'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('29',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k2_relat_1 @ X32 )
       != X31 )
      | ( v2_funct_2 @ X32 @ X31 )
      | ~ ( v5_relat_1 @ X32 @ X31 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('30',plain,(
    ! [X32: $i] :
      ( ~ ( v1_relat_1 @ X32 )
      | ~ ( v5_relat_1 @ X32 @ ( k2_relat_1 @ X32 ) )
      | ( v2_funct_2 @ X32 @ ( k2_relat_1 @ X32 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('33',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v5_relat_1 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('34',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['24','27'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('37',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('38',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['31','34','35','38'])).

thf('40',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('41',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('43',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','43'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('45',plain,(
    ! [X14: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X14 ) ) @ X14 )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('46',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('47',plain,(
    ! [X14: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X14 ) ) @ X14 )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('49',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('51',plain,(
    ! [X12: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('52',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('53',plain,(
    ! [X12: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X12 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('54',plain,(
    ! [X11: $i] :
      ( ( ( k1_relat_1 @ X11 )
       != k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k6_partfun1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('56',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('57',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('58',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X15 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k6_partfun1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['55','58'])).

thf('60',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','60'])).

thf('62',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('66',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['64','65'])).

thf(fc12_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ B ) )
     => ( ( v1_xboole_0 @ ( k5_relat_1 @ A @ B ) )
        & ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) ) )).

thf('67',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_xboole_0 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[fc12_relat_1])).

thf('68',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = X2 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k5_relat_1 @ X1 @ sk_C )
        = X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k5_relat_1 @ X1 @ sk_C )
        = ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','70'])).

thf('72',plain,(
    ! [X16: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('73',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('74',plain,(
    ! [X16: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X16 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ X0 @ sk_C ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['71','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ X0 @ sk_C ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['75'])).

thf('77',plain,
    ( ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_xboole_0 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['47','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['64','65'])).

thf('79',plain,
    ( ( v2_funct_1 @ sk_C )
    | ~ ( v1_xboole_0 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('81',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
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

thf('83',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['81','86'])).

thf('88',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('91',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('92',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( X26 = X29 )
      | ~ ( r2_relset_1 @ X27 @ X28 @ X26 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','93'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('95',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('96',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('97',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['94','97'])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('99',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) ) @ ( k1_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('100',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,(
    ! [X12: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X12 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('104',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('106',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['104','105'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('107',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('108',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['64','65'])).

thf('110',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['94','97'])).

thf('112',plain,(
    ! [X12: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X12 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('113',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['36','37'])).

thf('114',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['64','65'])).

thf('115',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['102','103','110','111','112','113','114'])).

thf('116',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('117',plain,(
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

thf('118',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X52 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X53 @ X51 @ X51 @ X52 @ X54 @ X50 ) )
      | ( v2_funct_1 @ X54 )
      | ( X52 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X51 ) ) )
      | ~ ( v1_funct_2 @ X54 @ X53 @ X51 )
      | ~ ( v1_funct_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('123',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['116','122'])).

thf('124',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['123','124','125','126'])).

thf('128',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['94','97'])).

thf('129',plain,(
    ! [X16: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X16 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('130',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('131',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','43'])).

thf('132',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['115','132'])).

thf('134',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['59'])).

thf('135',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('136',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['79','133','134','135'])).

thf('137',plain,(
    $false ),
    inference(demod,[status(thm)],['44','136'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZUEhxix7qI
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:39:52 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 10.23/10.41  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 10.23/10.41  % Solved by: fo/fo7.sh
% 10.23/10.41  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 10.23/10.41  % done 12749 iterations in 9.948s
% 10.23/10.41  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 10.23/10.41  % SZS output start Refutation
% 10.23/10.41  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 10.23/10.41  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 10.23/10.41  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 10.23/10.41  thf(sk_D_type, type, sk_D: $i).
% 10.23/10.41  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 10.23/10.41  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 10.23/10.41  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 10.23/10.41  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 10.23/10.41  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 10.23/10.41  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 10.23/10.41  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 10.23/10.41  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 10.23/10.41  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 10.23/10.41  thf(sk_B_type, type, sk_B: $i).
% 10.23/10.41  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 10.23/10.41  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 10.23/10.41  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 10.23/10.41  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 10.23/10.41  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 10.23/10.41  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 10.23/10.41  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 10.23/10.41  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 10.23/10.41  thf(sk_C_type, type, sk_C: $i).
% 10.23/10.41  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 10.23/10.41  thf(sk_A_type, type, sk_A: $i).
% 10.23/10.41  thf(t29_funct_2, conjecture,
% 10.23/10.41    (![A:$i,B:$i,C:$i]:
% 10.23/10.41     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 10.23/10.41         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.23/10.41       ( ![D:$i]:
% 10.23/10.41         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 10.23/10.41             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 10.23/10.41           ( ( r2_relset_1 @
% 10.23/10.41               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 10.23/10.41               ( k6_partfun1 @ A ) ) =>
% 10.23/10.41             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 10.23/10.41  thf(zf_stmt_0, negated_conjecture,
% 10.23/10.41    (~( ![A:$i,B:$i,C:$i]:
% 10.23/10.41        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 10.23/10.41            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.23/10.41          ( ![D:$i]:
% 10.23/10.41            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 10.23/10.41                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 10.23/10.41              ( ( r2_relset_1 @
% 10.23/10.41                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 10.23/10.41                  ( k6_partfun1 @ A ) ) =>
% 10.23/10.41                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 10.23/10.41    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 10.23/10.41  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 10.23/10.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.41  thf('1', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 10.23/10.41      inference('split', [status(esa)], ['0'])).
% 10.23/10.41  thf('2', plain,
% 10.23/10.41      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 10.23/10.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.41  thf('3', plain,
% 10.23/10.41      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.23/10.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.41  thf(redefinition_k1_partfun1, axiom,
% 10.23/10.41    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 10.23/10.41     ( ( ( v1_funct_1 @ E ) & 
% 10.23/10.41         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 10.23/10.41         ( v1_funct_1 @ F ) & 
% 10.23/10.41         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 10.23/10.41       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 10.23/10.41  thf('4', plain,
% 10.23/10.41      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 10.23/10.41         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 10.23/10.41          | ~ (v1_funct_1 @ X39)
% 10.23/10.41          | ~ (v1_funct_1 @ X42)
% 10.23/10.41          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 10.23/10.41          | ((k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42)
% 10.23/10.41              = (k5_relat_1 @ X39 @ X42)))),
% 10.23/10.41      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 10.23/10.41  thf('5', plain,
% 10.23/10.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.23/10.41         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 10.23/10.41            = (k5_relat_1 @ sk_C @ X0))
% 10.23/10.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 10.23/10.41          | ~ (v1_funct_1 @ X0)
% 10.23/10.41          | ~ (v1_funct_1 @ sk_C))),
% 10.23/10.41      inference('sup-', [status(thm)], ['3', '4'])).
% 10.23/10.41  thf('6', plain, ((v1_funct_1 @ sk_C)),
% 10.23/10.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.41  thf('7', plain,
% 10.23/10.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.23/10.41         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 10.23/10.41            = (k5_relat_1 @ sk_C @ X0))
% 10.23/10.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 10.23/10.41          | ~ (v1_funct_1 @ X0))),
% 10.23/10.41      inference('demod', [status(thm)], ['5', '6'])).
% 10.23/10.41  thf('8', plain,
% 10.23/10.41      ((~ (v1_funct_1 @ sk_D)
% 10.23/10.41        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 10.23/10.41            = (k5_relat_1 @ sk_C @ sk_D)))),
% 10.23/10.41      inference('sup-', [status(thm)], ['2', '7'])).
% 10.23/10.41  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 10.23/10.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.41  thf('10', plain,
% 10.23/10.41      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 10.23/10.41         = (k5_relat_1 @ sk_C @ sk_D))),
% 10.23/10.41      inference('demod', [status(thm)], ['8', '9'])).
% 10.23/10.41  thf('11', plain,
% 10.23/10.41      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.23/10.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.41  thf(t24_funct_2, axiom,
% 10.23/10.41    (![A:$i,B:$i,C:$i]:
% 10.23/10.41     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 10.23/10.41         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.23/10.41       ( ![D:$i]:
% 10.23/10.41         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 10.23/10.41             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 10.23/10.41           ( ( r2_relset_1 @
% 10.23/10.41               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 10.23/10.41               ( k6_partfun1 @ B ) ) =>
% 10.23/10.41             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 10.23/10.41  thf('12', plain,
% 10.23/10.41      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 10.23/10.41         (~ (v1_funct_1 @ X46)
% 10.23/10.41          | ~ (v1_funct_2 @ X46 @ X47 @ X48)
% 10.23/10.41          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 10.23/10.41          | ~ (r2_relset_1 @ X47 @ X47 @ 
% 10.23/10.41               (k1_partfun1 @ X47 @ X48 @ X48 @ X47 @ X46 @ X49) @ 
% 10.23/10.41               (k6_partfun1 @ X47))
% 10.23/10.41          | ((k2_relset_1 @ X48 @ X47 @ X49) = (X47))
% 10.23/10.41          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X47)))
% 10.23/10.41          | ~ (v1_funct_2 @ X49 @ X48 @ X47)
% 10.23/10.41          | ~ (v1_funct_1 @ X49))),
% 10.23/10.41      inference('cnf', [status(esa)], [t24_funct_2])).
% 10.23/10.41  thf('13', plain,
% 10.23/10.41      (![X0 : $i]:
% 10.23/10.41         (~ (v1_funct_1 @ X0)
% 10.23/10.41          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 10.23/10.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 10.23/10.41          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 10.23/10.41          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 10.23/10.41               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 10.23/10.41               (k6_partfun1 @ sk_A))
% 10.23/10.41          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 10.23/10.41          | ~ (v1_funct_1 @ sk_C))),
% 10.23/10.41      inference('sup-', [status(thm)], ['11', '12'])).
% 10.23/10.41  thf('14', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 10.23/10.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.41  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 10.23/10.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.41  thf('16', plain,
% 10.23/10.41      (![X0 : $i]:
% 10.23/10.41         (~ (v1_funct_1 @ X0)
% 10.23/10.41          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 10.23/10.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 10.23/10.41          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 10.23/10.41          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 10.23/10.41               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 10.23/10.41               (k6_partfun1 @ sk_A)))),
% 10.23/10.41      inference('demod', [status(thm)], ['13', '14', '15'])).
% 10.23/10.41  thf('17', plain,
% 10.23/10.41      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 10.23/10.41           (k6_partfun1 @ sk_A))
% 10.23/10.41        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 10.23/10.41        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 10.23/10.41        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 10.23/10.41        | ~ (v1_funct_1 @ sk_D))),
% 10.23/10.41      inference('sup-', [status(thm)], ['10', '16'])).
% 10.23/10.41  thf('18', plain,
% 10.23/10.41      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 10.23/10.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.41  thf(redefinition_k2_relset_1, axiom,
% 10.23/10.41    (![A:$i,B:$i,C:$i]:
% 10.23/10.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.23/10.41       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 10.23/10.41  thf('19', plain,
% 10.23/10.41      (![X23 : $i, X24 : $i, X25 : $i]:
% 10.23/10.41         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 10.23/10.41          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 10.23/10.41      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 10.23/10.41  thf('20', plain,
% 10.23/10.41      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 10.23/10.41      inference('sup-', [status(thm)], ['18', '19'])).
% 10.23/10.41  thf('21', plain,
% 10.23/10.41      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 10.23/10.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.41  thf('22', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 10.23/10.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.41  thf('23', plain, ((v1_funct_1 @ sk_D)),
% 10.23/10.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.41  thf('24', plain,
% 10.23/10.41      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 10.23/10.41           (k6_partfun1 @ sk_A))
% 10.23/10.41        | ((k2_relat_1 @ sk_D) = (sk_A)))),
% 10.23/10.41      inference('demod', [status(thm)], ['17', '20', '21', '22', '23'])).
% 10.23/10.41  thf('25', plain,
% 10.23/10.41      ((r2_relset_1 @ sk_A @ sk_A @ 
% 10.23/10.41        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 10.23/10.41        (k6_partfun1 @ sk_A))),
% 10.23/10.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.41  thf('26', plain,
% 10.23/10.41      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 10.23/10.41         = (k5_relat_1 @ sk_C @ sk_D))),
% 10.23/10.41      inference('demod', [status(thm)], ['8', '9'])).
% 10.23/10.41  thf('27', plain,
% 10.23/10.41      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 10.23/10.41        (k6_partfun1 @ sk_A))),
% 10.23/10.41      inference('demod', [status(thm)], ['25', '26'])).
% 10.23/10.41  thf('28', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 10.23/10.41      inference('demod', [status(thm)], ['24', '27'])).
% 10.23/10.41  thf(d3_funct_2, axiom,
% 10.23/10.41    (![A:$i,B:$i]:
% 10.23/10.41     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 10.23/10.41       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 10.23/10.41  thf('29', plain,
% 10.23/10.41      (![X31 : $i, X32 : $i]:
% 10.23/10.41         (((k2_relat_1 @ X32) != (X31))
% 10.23/10.41          | (v2_funct_2 @ X32 @ X31)
% 10.23/10.41          | ~ (v5_relat_1 @ X32 @ X31)
% 10.23/10.41          | ~ (v1_relat_1 @ X32))),
% 10.23/10.41      inference('cnf', [status(esa)], [d3_funct_2])).
% 10.23/10.41  thf('30', plain,
% 10.23/10.41      (![X32 : $i]:
% 10.23/10.41         (~ (v1_relat_1 @ X32)
% 10.23/10.41          | ~ (v5_relat_1 @ X32 @ (k2_relat_1 @ X32))
% 10.23/10.41          | (v2_funct_2 @ X32 @ (k2_relat_1 @ X32)))),
% 10.23/10.41      inference('simplify', [status(thm)], ['29'])).
% 10.23/10.41  thf('31', plain,
% 10.23/10.41      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 10.23/10.41        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 10.23/10.41        | ~ (v1_relat_1 @ sk_D))),
% 10.23/10.41      inference('sup-', [status(thm)], ['28', '30'])).
% 10.23/10.41  thf('32', plain,
% 10.23/10.41      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 10.23/10.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.41  thf(cc2_relset_1, axiom,
% 10.23/10.41    (![A:$i,B:$i,C:$i]:
% 10.23/10.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.23/10.41       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 10.23/10.41  thf('33', plain,
% 10.23/10.41      (![X20 : $i, X21 : $i, X22 : $i]:
% 10.23/10.41         ((v5_relat_1 @ X20 @ X22)
% 10.23/10.41          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 10.23/10.41      inference('cnf', [status(esa)], [cc2_relset_1])).
% 10.23/10.41  thf('34', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 10.23/10.41      inference('sup-', [status(thm)], ['32', '33'])).
% 10.23/10.41  thf('35', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 10.23/10.41      inference('demod', [status(thm)], ['24', '27'])).
% 10.23/10.41  thf('36', plain,
% 10.23/10.41      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 10.23/10.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.41  thf(cc1_relset_1, axiom,
% 10.23/10.41    (![A:$i,B:$i,C:$i]:
% 10.23/10.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.23/10.41       ( v1_relat_1 @ C ) ))).
% 10.23/10.41  thf('37', plain,
% 10.23/10.41      (![X17 : $i, X18 : $i, X19 : $i]:
% 10.23/10.41         ((v1_relat_1 @ X17)
% 10.23/10.41          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 10.23/10.41      inference('cnf', [status(esa)], [cc1_relset_1])).
% 10.23/10.41  thf('38', plain, ((v1_relat_1 @ sk_D)),
% 10.23/10.41      inference('sup-', [status(thm)], ['36', '37'])).
% 10.23/10.41  thf('39', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 10.23/10.41      inference('demod', [status(thm)], ['31', '34', '35', '38'])).
% 10.23/10.41  thf('40', plain,
% 10.23/10.41      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 10.23/10.41      inference('split', [status(esa)], ['0'])).
% 10.23/10.41  thf('41', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 10.23/10.41      inference('sup-', [status(thm)], ['39', '40'])).
% 10.23/10.41  thf('42', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 10.23/10.41      inference('split', [status(esa)], ['0'])).
% 10.23/10.41  thf('43', plain, (~ ((v2_funct_1 @ sk_C))),
% 10.23/10.41      inference('sat_resolution*', [status(thm)], ['41', '42'])).
% 10.23/10.41  thf('44', plain, (~ (v2_funct_1 @ sk_C)),
% 10.23/10.41      inference('simpl_trail', [status(thm)], ['1', '43'])).
% 10.23/10.41  thf(t78_relat_1, axiom,
% 10.23/10.41    (![A:$i]:
% 10.23/10.41     ( ( v1_relat_1 @ A ) =>
% 10.23/10.41       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 10.23/10.41  thf('45', plain,
% 10.23/10.41      (![X14 : $i]:
% 10.23/10.41         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X14)) @ X14) = (X14))
% 10.23/10.41          | ~ (v1_relat_1 @ X14))),
% 10.23/10.41      inference('cnf', [status(esa)], [t78_relat_1])).
% 10.23/10.41  thf(redefinition_k6_partfun1, axiom,
% 10.23/10.41    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 10.23/10.41  thf('46', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 10.23/10.41      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 10.23/10.41  thf('47', plain,
% 10.23/10.41      (![X14 : $i]:
% 10.23/10.41         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X14)) @ X14) = (X14))
% 10.23/10.41          | ~ (v1_relat_1 @ X14))),
% 10.23/10.41      inference('demod', [status(thm)], ['45', '46'])).
% 10.23/10.41  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 10.23/10.41  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 10.23/10.41      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 10.23/10.41  thf(t8_boole, axiom,
% 10.23/10.41    (![A:$i,B:$i]:
% 10.23/10.41     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 10.23/10.41  thf('49', plain,
% 10.23/10.41      (![X3 : $i, X4 : $i]:
% 10.23/10.41         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 10.23/10.41      inference('cnf', [status(esa)], [t8_boole])).
% 10.23/10.41  thf('50', plain,
% 10.23/10.41      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 10.23/10.41      inference('sup-', [status(thm)], ['48', '49'])).
% 10.23/10.41  thf(t71_relat_1, axiom,
% 10.23/10.41    (![A:$i]:
% 10.23/10.41     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 10.23/10.41       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 10.23/10.41  thf('51', plain, (![X12 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 10.23/10.41      inference('cnf', [status(esa)], [t71_relat_1])).
% 10.23/10.41  thf('52', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 10.23/10.41      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 10.23/10.41  thf('53', plain, (![X12 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X12)) = (X12))),
% 10.23/10.41      inference('demod', [status(thm)], ['51', '52'])).
% 10.23/10.41  thf(t64_relat_1, axiom,
% 10.23/10.41    (![A:$i]:
% 10.23/10.41     ( ( v1_relat_1 @ A ) =>
% 10.23/10.41       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 10.23/10.41           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 10.23/10.41         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 10.23/10.41  thf('54', plain,
% 10.23/10.41      (![X11 : $i]:
% 10.23/10.41         (((k1_relat_1 @ X11) != (k1_xboole_0))
% 10.23/10.41          | ((X11) = (k1_xboole_0))
% 10.23/10.41          | ~ (v1_relat_1 @ X11))),
% 10.23/10.41      inference('cnf', [status(esa)], [t64_relat_1])).
% 10.23/10.41  thf('55', plain,
% 10.23/10.41      (![X0 : $i]:
% 10.23/10.41         (((X0) != (k1_xboole_0))
% 10.23/10.41          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 10.23/10.41          | ((k6_partfun1 @ X0) = (k1_xboole_0)))),
% 10.23/10.41      inference('sup-', [status(thm)], ['53', '54'])).
% 10.23/10.41  thf(fc4_funct_1, axiom,
% 10.23/10.41    (![A:$i]:
% 10.23/10.41     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 10.23/10.41       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 10.23/10.41  thf('56', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 10.23/10.41      inference('cnf', [status(esa)], [fc4_funct_1])).
% 10.23/10.41  thf('57', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 10.23/10.41      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 10.23/10.41  thf('58', plain, (![X15 : $i]: (v1_relat_1 @ (k6_partfun1 @ X15))),
% 10.23/10.41      inference('demod', [status(thm)], ['56', '57'])).
% 10.23/10.41  thf('59', plain,
% 10.23/10.41      (![X0 : $i]:
% 10.23/10.41         (((X0) != (k1_xboole_0)) | ((k6_partfun1 @ X0) = (k1_xboole_0)))),
% 10.23/10.41      inference('demod', [status(thm)], ['55', '58'])).
% 10.23/10.41  thf('60', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 10.23/10.41      inference('simplify', [status(thm)], ['59'])).
% 10.23/10.41  thf('61', plain,
% 10.23/10.41      (![X0 : $i]:
% 10.23/10.41         (((k6_partfun1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 10.23/10.41      inference('sup+', [status(thm)], ['50', '60'])).
% 10.23/10.41  thf('62', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 10.23/10.41      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 10.23/10.41  thf('63', plain,
% 10.23/10.41      (![X0 : $i]: ((v1_xboole_0 @ (k6_partfun1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 10.23/10.41      inference('sup+', [status(thm)], ['61', '62'])).
% 10.23/10.41  thf('64', plain,
% 10.23/10.41      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.23/10.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.41  thf('65', plain,
% 10.23/10.41      (![X17 : $i, X18 : $i, X19 : $i]:
% 10.23/10.41         ((v1_relat_1 @ X17)
% 10.23/10.41          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 10.23/10.41      inference('cnf', [status(esa)], [cc1_relset_1])).
% 10.23/10.41  thf('66', plain, ((v1_relat_1 @ sk_C)),
% 10.23/10.41      inference('sup-', [status(thm)], ['64', '65'])).
% 10.23/10.41  thf(fc12_relat_1, axiom,
% 10.23/10.41    (![A:$i,B:$i]:
% 10.23/10.41     ( ( ( v1_xboole_0 @ A ) & ( v1_relat_1 @ B ) ) =>
% 10.23/10.41       ( ( v1_xboole_0 @ ( k5_relat_1 @ A @ B ) ) & 
% 10.23/10.41         ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) ))).
% 10.23/10.41  thf('67', plain,
% 10.23/10.41      (![X7 : $i, X8 : $i]:
% 10.23/10.41         (~ (v1_xboole_0 @ X7)
% 10.23/10.41          | ~ (v1_relat_1 @ X8)
% 10.23/10.41          | (v1_xboole_0 @ (k5_relat_1 @ X7 @ X8)))),
% 10.23/10.41      inference('cnf', [status(esa)], [fc12_relat_1])).
% 10.23/10.41  thf('68', plain,
% 10.23/10.41      (![X3 : $i, X4 : $i]:
% 10.23/10.41         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 10.23/10.41      inference('cnf', [status(esa)], [t8_boole])).
% 10.23/10.41  thf('69', plain,
% 10.23/10.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.23/10.41         (~ (v1_relat_1 @ X0)
% 10.23/10.41          | ~ (v1_xboole_0 @ X1)
% 10.23/10.41          | ((k5_relat_1 @ X1 @ X0) = (X2))
% 10.23/10.41          | ~ (v1_xboole_0 @ X2))),
% 10.23/10.41      inference('sup-', [status(thm)], ['67', '68'])).
% 10.23/10.41  thf('70', plain,
% 10.23/10.41      (![X0 : $i, X1 : $i]:
% 10.23/10.41         (~ (v1_xboole_0 @ X0)
% 10.23/10.41          | ((k5_relat_1 @ X1 @ sk_C) = (X0))
% 10.23/10.41          | ~ (v1_xboole_0 @ X1))),
% 10.23/10.41      inference('sup-', [status(thm)], ['66', '69'])).
% 10.23/10.41  thf('71', plain,
% 10.23/10.41      (![X0 : $i, X1 : $i]:
% 10.23/10.41         (~ (v1_xboole_0 @ X0)
% 10.23/10.41          | ~ (v1_xboole_0 @ X1)
% 10.23/10.41          | ((k5_relat_1 @ X1 @ sk_C) = (k6_partfun1 @ X0)))),
% 10.23/10.41      inference('sup-', [status(thm)], ['63', '70'])).
% 10.23/10.41  thf('72', plain, (![X16 : $i]: (v2_funct_1 @ (k6_relat_1 @ X16))),
% 10.23/10.41      inference('cnf', [status(esa)], [fc4_funct_1])).
% 10.23/10.41  thf('73', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 10.23/10.41      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 10.23/10.41  thf('74', plain, (![X16 : $i]: (v2_funct_1 @ (k6_partfun1 @ X16))),
% 10.23/10.41      inference('demod', [status(thm)], ['72', '73'])).
% 10.23/10.41  thf('75', plain,
% 10.23/10.41      (![X0 : $i, X1 : $i]:
% 10.23/10.41         ((v2_funct_1 @ (k5_relat_1 @ X0 @ sk_C))
% 10.23/10.41          | ~ (v1_xboole_0 @ X0)
% 10.23/10.41          | ~ (v1_xboole_0 @ X1))),
% 10.23/10.41      inference('sup+', [status(thm)], ['71', '74'])).
% 10.23/10.41  thf('76', plain,
% 10.23/10.41      (![X0 : $i]:
% 10.23/10.41         ((v2_funct_1 @ (k5_relat_1 @ X0 @ sk_C)) | ~ (v1_xboole_0 @ X0))),
% 10.23/10.41      inference('condensation', [status(thm)], ['75'])).
% 10.23/10.41  thf('77', plain,
% 10.23/10.41      (((v2_funct_1 @ sk_C)
% 10.23/10.41        | ~ (v1_relat_1 @ sk_C)
% 10.23/10.41        | ~ (v1_xboole_0 @ (k6_partfun1 @ (k1_relat_1 @ sk_C))))),
% 10.23/10.41      inference('sup+', [status(thm)], ['47', '76'])).
% 10.23/10.41  thf('78', plain, ((v1_relat_1 @ sk_C)),
% 10.23/10.41      inference('sup-', [status(thm)], ['64', '65'])).
% 10.23/10.41  thf('79', plain,
% 10.23/10.41      (((v2_funct_1 @ sk_C)
% 10.23/10.41        | ~ (v1_xboole_0 @ (k6_partfun1 @ (k1_relat_1 @ sk_C))))),
% 10.23/10.41      inference('demod', [status(thm)], ['77', '78'])).
% 10.23/10.41  thf('80', plain,
% 10.23/10.41      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 10.23/10.41        (k6_partfun1 @ sk_A))),
% 10.23/10.41      inference('demod', [status(thm)], ['25', '26'])).
% 10.23/10.41  thf('81', plain,
% 10.23/10.41      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 10.23/10.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.41  thf('82', plain,
% 10.23/10.41      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.23/10.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.41  thf(dt_k1_partfun1, axiom,
% 10.23/10.41    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 10.23/10.41     ( ( ( v1_funct_1 @ E ) & 
% 10.23/10.41         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 10.23/10.41         ( v1_funct_1 @ F ) & 
% 10.23/10.41         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 10.23/10.41       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 10.23/10.41         ( m1_subset_1 @
% 10.23/10.41           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 10.23/10.41           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 10.23/10.41  thf('83', plain,
% 10.23/10.41      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 10.23/10.41         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 10.23/10.41          | ~ (v1_funct_1 @ X33)
% 10.23/10.41          | ~ (v1_funct_1 @ X36)
% 10.23/10.41          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 10.23/10.41          | (m1_subset_1 @ (k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36) @ 
% 10.23/10.41             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X38))))),
% 10.23/10.41      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 10.23/10.41  thf('84', plain,
% 10.23/10.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.23/10.41         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 10.23/10.41           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 10.23/10.41          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 10.23/10.41          | ~ (v1_funct_1 @ X1)
% 10.23/10.41          | ~ (v1_funct_1 @ sk_C))),
% 10.23/10.41      inference('sup-', [status(thm)], ['82', '83'])).
% 10.23/10.41  thf('85', plain, ((v1_funct_1 @ sk_C)),
% 10.23/10.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.41  thf('86', plain,
% 10.23/10.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.23/10.41         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 10.23/10.41           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 10.23/10.41          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 10.23/10.41          | ~ (v1_funct_1 @ X1))),
% 10.23/10.41      inference('demod', [status(thm)], ['84', '85'])).
% 10.23/10.41  thf('87', plain,
% 10.23/10.41      ((~ (v1_funct_1 @ sk_D)
% 10.23/10.41        | (m1_subset_1 @ 
% 10.23/10.41           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 10.23/10.41           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 10.23/10.41      inference('sup-', [status(thm)], ['81', '86'])).
% 10.23/10.41  thf('88', plain, ((v1_funct_1 @ sk_D)),
% 10.23/10.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.41  thf('89', plain,
% 10.23/10.41      ((m1_subset_1 @ 
% 10.23/10.41        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 10.23/10.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.23/10.41      inference('demod', [status(thm)], ['87', '88'])).
% 10.23/10.41  thf('90', plain,
% 10.23/10.41      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 10.23/10.41         = (k5_relat_1 @ sk_C @ sk_D))),
% 10.23/10.41      inference('demod', [status(thm)], ['8', '9'])).
% 10.23/10.41  thf('91', plain,
% 10.23/10.41      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 10.23/10.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.23/10.41      inference('demod', [status(thm)], ['89', '90'])).
% 10.23/10.41  thf(redefinition_r2_relset_1, axiom,
% 10.23/10.41    (![A:$i,B:$i,C:$i,D:$i]:
% 10.23/10.41     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 10.23/10.41         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.23/10.41       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 10.23/10.41  thf('92', plain,
% 10.23/10.41      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 10.23/10.41         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 10.23/10.41          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 10.23/10.41          | ((X26) = (X29))
% 10.23/10.41          | ~ (r2_relset_1 @ X27 @ X28 @ X26 @ X29))),
% 10.23/10.41      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 10.23/10.41  thf('93', plain,
% 10.23/10.41      (![X0 : $i]:
% 10.23/10.41         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 10.23/10.41          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 10.23/10.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 10.23/10.41      inference('sup-', [status(thm)], ['91', '92'])).
% 10.23/10.41  thf('94', plain,
% 10.23/10.41      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 10.23/10.41           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 10.23/10.41        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 10.23/10.41      inference('sup-', [status(thm)], ['80', '93'])).
% 10.23/10.41  thf(t29_relset_1, axiom,
% 10.23/10.41    (![A:$i]:
% 10.23/10.41     ( m1_subset_1 @
% 10.23/10.41       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 10.23/10.41  thf('95', plain,
% 10.23/10.41      (![X30 : $i]:
% 10.23/10.41         (m1_subset_1 @ (k6_relat_1 @ X30) @ 
% 10.23/10.41          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 10.23/10.41      inference('cnf', [status(esa)], [t29_relset_1])).
% 10.23/10.41  thf('96', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 10.23/10.41      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 10.23/10.41  thf('97', plain,
% 10.23/10.41      (![X30 : $i]:
% 10.23/10.41         (m1_subset_1 @ (k6_partfun1 @ X30) @ 
% 10.23/10.41          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 10.23/10.41      inference('demod', [status(thm)], ['95', '96'])).
% 10.23/10.41  thf('98', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 10.23/10.41      inference('demod', [status(thm)], ['94', '97'])).
% 10.23/10.41  thf(t44_relat_1, axiom,
% 10.23/10.41    (![A:$i]:
% 10.23/10.41     ( ( v1_relat_1 @ A ) =>
% 10.23/10.41       ( ![B:$i]:
% 10.23/10.41         ( ( v1_relat_1 @ B ) =>
% 10.23/10.41           ( r1_tarski @
% 10.23/10.41             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 10.23/10.41  thf('99', plain,
% 10.23/10.41      (![X9 : $i, X10 : $i]:
% 10.23/10.41         (~ (v1_relat_1 @ X9)
% 10.23/10.41          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X10 @ X9)) @ 
% 10.23/10.41             (k1_relat_1 @ X10))
% 10.23/10.41          | ~ (v1_relat_1 @ X10))),
% 10.23/10.41      inference('cnf', [status(esa)], [t44_relat_1])).
% 10.23/10.41  thf(d10_xboole_0, axiom,
% 10.23/10.41    (![A:$i,B:$i]:
% 10.23/10.41     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 10.23/10.41  thf('100', plain,
% 10.23/10.41      (![X0 : $i, X2 : $i]:
% 10.23/10.41         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 10.23/10.41      inference('cnf', [status(esa)], [d10_xboole_0])).
% 10.23/10.41  thf('101', plain,
% 10.23/10.41      (![X0 : $i, X1 : $i]:
% 10.23/10.41         (~ (v1_relat_1 @ X0)
% 10.23/10.41          | ~ (v1_relat_1 @ X1)
% 10.23/10.41          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ 
% 10.23/10.41               (k1_relat_1 @ (k5_relat_1 @ X0 @ X1)))
% 10.23/10.41          | ((k1_relat_1 @ X0) = (k1_relat_1 @ (k5_relat_1 @ X0 @ X1))))),
% 10.23/10.41      inference('sup-', [status(thm)], ['99', '100'])).
% 10.23/10.41  thf('102', plain,
% 10.23/10.41      ((~ (r1_tarski @ (k1_relat_1 @ sk_C) @ 
% 10.23/10.41           (k1_relat_1 @ (k6_partfun1 @ sk_A)))
% 10.23/10.41        | ((k1_relat_1 @ sk_C) = (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 10.23/10.41        | ~ (v1_relat_1 @ sk_D)
% 10.23/10.41        | ~ (v1_relat_1 @ sk_C))),
% 10.23/10.41      inference('sup-', [status(thm)], ['98', '101'])).
% 10.23/10.41  thf('103', plain,
% 10.23/10.41      (![X12 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X12)) = (X12))),
% 10.23/10.41      inference('demod', [status(thm)], ['51', '52'])).
% 10.23/10.41  thf('104', plain,
% 10.23/10.41      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.23/10.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.41  thf('105', plain,
% 10.23/10.41      (![X20 : $i, X21 : $i, X22 : $i]:
% 10.23/10.41         ((v4_relat_1 @ X20 @ X21)
% 10.23/10.41          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 10.23/10.41      inference('cnf', [status(esa)], [cc2_relset_1])).
% 10.23/10.41  thf('106', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 10.23/10.41      inference('sup-', [status(thm)], ['104', '105'])).
% 10.23/10.41  thf(d18_relat_1, axiom,
% 10.23/10.41    (![A:$i,B:$i]:
% 10.23/10.41     ( ( v1_relat_1 @ B ) =>
% 10.23/10.41       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 10.23/10.41  thf('107', plain,
% 10.23/10.41      (![X5 : $i, X6 : $i]:
% 10.23/10.41         (~ (v4_relat_1 @ X5 @ X6)
% 10.23/10.41          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 10.23/10.41          | ~ (v1_relat_1 @ X5))),
% 10.23/10.41      inference('cnf', [status(esa)], [d18_relat_1])).
% 10.23/10.41  thf('108', plain,
% 10.23/10.41      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 10.23/10.41      inference('sup-', [status(thm)], ['106', '107'])).
% 10.23/10.41  thf('109', plain, ((v1_relat_1 @ sk_C)),
% 10.23/10.41      inference('sup-', [status(thm)], ['64', '65'])).
% 10.23/10.41  thf('110', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 10.23/10.41      inference('demod', [status(thm)], ['108', '109'])).
% 10.23/10.41  thf('111', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 10.23/10.41      inference('demod', [status(thm)], ['94', '97'])).
% 10.23/10.41  thf('112', plain,
% 10.23/10.41      (![X12 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X12)) = (X12))),
% 10.23/10.41      inference('demod', [status(thm)], ['51', '52'])).
% 10.23/10.41  thf('113', plain, ((v1_relat_1 @ sk_D)),
% 10.23/10.41      inference('sup-', [status(thm)], ['36', '37'])).
% 10.23/10.41  thf('114', plain, ((v1_relat_1 @ sk_C)),
% 10.23/10.41      inference('sup-', [status(thm)], ['64', '65'])).
% 10.23/10.41  thf('115', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 10.23/10.41      inference('demod', [status(thm)],
% 10.23/10.41                ['102', '103', '110', '111', '112', '113', '114'])).
% 10.23/10.41  thf('116', plain,
% 10.23/10.41      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 10.23/10.41         = (k5_relat_1 @ sk_C @ sk_D))),
% 10.23/10.41      inference('demod', [status(thm)], ['8', '9'])).
% 10.23/10.41  thf('117', plain,
% 10.23/10.41      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 10.23/10.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.41  thf(t26_funct_2, axiom,
% 10.23/10.41    (![A:$i,B:$i,C:$i,D:$i]:
% 10.23/10.41     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 10.23/10.41         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.23/10.41       ( ![E:$i]:
% 10.23/10.41         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 10.23/10.41             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 10.23/10.41           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 10.23/10.41             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 10.23/10.41               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 10.23/10.41  thf('118', plain,
% 10.23/10.41      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 10.23/10.41         (~ (v1_funct_1 @ X50)
% 10.23/10.41          | ~ (v1_funct_2 @ X50 @ X51 @ X52)
% 10.23/10.41          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 10.23/10.41          | ~ (v2_funct_1 @ (k1_partfun1 @ X53 @ X51 @ X51 @ X52 @ X54 @ X50))
% 10.23/10.41          | (v2_funct_1 @ X54)
% 10.23/10.41          | ((X52) = (k1_xboole_0))
% 10.23/10.41          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X51)))
% 10.23/10.41          | ~ (v1_funct_2 @ X54 @ X53 @ X51)
% 10.23/10.41          | ~ (v1_funct_1 @ X54))),
% 10.23/10.41      inference('cnf', [status(esa)], [t26_funct_2])).
% 10.23/10.41  thf('119', plain,
% 10.23/10.41      (![X0 : $i, X1 : $i]:
% 10.23/10.41         (~ (v1_funct_1 @ X0)
% 10.23/10.41          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 10.23/10.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 10.23/10.41          | ((sk_A) = (k1_xboole_0))
% 10.23/10.41          | (v2_funct_1 @ X0)
% 10.23/10.41          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 10.23/10.41          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 10.23/10.41          | ~ (v1_funct_1 @ sk_D))),
% 10.23/10.41      inference('sup-', [status(thm)], ['117', '118'])).
% 10.23/10.41  thf('120', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 10.23/10.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.41  thf('121', plain, ((v1_funct_1 @ sk_D)),
% 10.23/10.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.41  thf('122', plain,
% 10.23/10.41      (![X0 : $i, X1 : $i]:
% 10.23/10.41         (~ (v1_funct_1 @ X0)
% 10.23/10.41          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 10.23/10.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 10.23/10.41          | ((sk_A) = (k1_xboole_0))
% 10.23/10.41          | (v2_funct_1 @ X0)
% 10.23/10.41          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 10.23/10.41      inference('demod', [status(thm)], ['119', '120', '121'])).
% 10.23/10.41  thf('123', plain,
% 10.23/10.41      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 10.23/10.41        | (v2_funct_1 @ sk_C)
% 10.23/10.41        | ((sk_A) = (k1_xboole_0))
% 10.23/10.41        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 10.23/10.41        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 10.23/10.41        | ~ (v1_funct_1 @ sk_C))),
% 10.23/10.41      inference('sup-', [status(thm)], ['116', '122'])).
% 10.23/10.41  thf('124', plain,
% 10.23/10.41      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.23/10.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.41  thf('125', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 10.23/10.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.41  thf('126', plain, ((v1_funct_1 @ sk_C)),
% 10.23/10.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.23/10.41  thf('127', plain,
% 10.23/10.41      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 10.23/10.41        | (v2_funct_1 @ sk_C)
% 10.23/10.41        | ((sk_A) = (k1_xboole_0)))),
% 10.23/10.41      inference('demod', [status(thm)], ['123', '124', '125', '126'])).
% 10.23/10.41  thf('128', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 10.23/10.41      inference('demod', [status(thm)], ['94', '97'])).
% 10.23/10.41  thf('129', plain, (![X16 : $i]: (v2_funct_1 @ (k6_partfun1 @ X16))),
% 10.23/10.41      inference('demod', [status(thm)], ['72', '73'])).
% 10.23/10.41  thf('130', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 10.23/10.41      inference('demod', [status(thm)], ['127', '128', '129'])).
% 10.23/10.41  thf('131', plain, (~ (v2_funct_1 @ sk_C)),
% 10.23/10.41      inference('simpl_trail', [status(thm)], ['1', '43'])).
% 10.23/10.41  thf('132', plain, (((sk_A) = (k1_xboole_0))),
% 10.23/10.41      inference('clc', [status(thm)], ['130', '131'])).
% 10.23/10.41  thf('133', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 10.23/10.41      inference('demod', [status(thm)], ['115', '132'])).
% 10.23/10.41  thf('134', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 10.23/10.41      inference('simplify', [status(thm)], ['59'])).
% 10.23/10.41  thf('135', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 10.23/10.41      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 10.23/10.41  thf('136', plain, ((v2_funct_1 @ sk_C)),
% 10.23/10.41      inference('demod', [status(thm)], ['79', '133', '134', '135'])).
% 10.23/10.41  thf('137', plain, ($false), inference('demod', [status(thm)], ['44', '136'])).
% 10.23/10.41  
% 10.23/10.41  % SZS output end Refutation
% 10.23/10.41  
% 10.23/10.42  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

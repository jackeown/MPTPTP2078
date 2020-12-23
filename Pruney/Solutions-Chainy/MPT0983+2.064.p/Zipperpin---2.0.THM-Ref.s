%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wmOXbyyPzZ

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:11 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 582 expanded)
%              Number of leaves         :   42 ( 185 expanded)
%              Depth                    :   17
%              Number of atoms          : 1309 (12396 expanded)
%              Number of equality atoms :   48 ( 157 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( ( k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41 )
        = ( k5_relat_1 @ X38 @ X41 ) ) ) ),
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
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( r2_relset_1 @ X46 @ X46 @ ( k1_partfun1 @ X46 @ X47 @ X47 @ X46 @ X45 @ X48 ) @ ( k6_partfun1 @ X46 ) )
      | ( ( k2_relset_1 @ X47 @ X46 @ X48 )
        = X46 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) )
      | ~ ( v1_funct_2 @ X48 @ X47 @ X46 )
      | ~ ( v1_funct_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('13',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('14',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( r2_relset_1 @ X46 @ X46 @ ( k1_partfun1 @ X46 @ X47 @ X47 @ X46 @ X45 @ X48 ) @ ( k6_relat_1 @ X46 ) )
      | ( ( k2_relset_1 @ X47 @ X46 @ X48 )
        = X46 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) )
      | ~ ( v1_funct_2 @ X48 @ X47 @ X46 )
      | ~ ( v1_funct_1 @ X48 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('20',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('22',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('24',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('26',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('27',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['19','24','27','28','29','30'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('32',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k2_relat_1 @ X29 )
       != X28 )
      | ( v2_funct_2 @ X29 @ X28 )
      | ~ ( v5_relat_1 @ X29 @ X28 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('33',plain,(
    ! [X29: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ~ ( v5_relat_1 @ X29 @ ( k2_relat_1 @ X29 ) )
      | ( v2_funct_2 @ X29 @ ( k2_relat_1 @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('36',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v5_relat_1 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('37',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['19','24','27','28','29','30'])).

thf('39',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('40',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('41',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['34','37','38','41'])).

thf('43',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('44',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('46',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','46'])).

thf('48',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
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

thf('51',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('58',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('59',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( X24 = X27 )
      | ~ ( r2_relset_1 @ X25 @ X26 @ X24 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','60'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('62',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('63',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('64',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['61','64'])).

thf(t27_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k1_relat_1 @ B ) )
           => ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) )).

thf('66',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( r1_tarski @ ( k2_relat_1 @ X11 ) @ ( k1_relat_1 @ X12 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X11 @ X12 ) )
       != ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t27_funct_1])).

thf('67',plain,
    ( ( ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('68',plain,(
    ! [X7: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X7 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('69',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['39','40'])).

thf('70',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('74',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( sk_A
     != ( k1_relat_1 @ sk_C ) )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['67','68','69','70','71','74'])).

thf('76',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['61','64'])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('77',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) ) @ ( k1_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('78',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,(
    ! [X7: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X7 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v4_relat_1 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('84',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['82','83'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('85',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v4_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('86',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['72','73'])).

thf('88',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['61','64'])).

thf('90',plain,(
    ! [X7: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X7 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('91',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['39','40'])).

thf('92',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['72','73'])).

thf('93',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['80','81','88','89','90','91','92'])).

thf('94',plain,
    ( ( sk_A != sk_A )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['75','93'])).

thf('95',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['94'])).

thf(t47_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) )
           => ( v2_funct_1 @ B ) ) ) ) )).

thf('96',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( v2_funct_1 @ X13 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X13 ) @ ( k1_relat_1 @ X14 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X13 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t47_funct_1])).

thf('97',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['39','40'])).

thf('99',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['61','64'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('101',plain,(
    ! [X10: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('102',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['72','73'])).

thf('104',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['97','98','99','100','101','102','103'])).

thf('105',plain,(
    $false ),
    inference(demod,[status(thm)],['47','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wmOXbyyPzZ
% 0.13/0.35  % Computer   : n003.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:31:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.35/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.54  % Solved by: fo/fo7.sh
% 0.35/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.54  % done 195 iterations in 0.067s
% 0.35/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.54  % SZS output start Refutation
% 0.35/0.54  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.35/0.54  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.35/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.35/0.54  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.35/0.54  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.35/0.54  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.35/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.54  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.35/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.54  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.35/0.54  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.35/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.54  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.35/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.35/0.54  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.35/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.35/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.54  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.35/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.35/0.54  thf(t29_funct_2, conjecture,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.35/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.54       ( ![D:$i]:
% 0.35/0.54         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.35/0.54             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.35/0.54           ( ( r2_relset_1 @
% 0.35/0.54               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.35/0.54               ( k6_partfun1 @ A ) ) =>
% 0.35/0.54             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 0.35/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.35/0.54        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.35/0.54            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.54          ( ![D:$i]:
% 0.35/0.54            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.35/0.54                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.35/0.54              ( ( r2_relset_1 @
% 0.35/0.54                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.35/0.54                  ( k6_partfun1 @ A ) ) =>
% 0.35/0.54                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 0.35/0.54    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 0.35/0.54  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('1', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.35/0.54      inference('split', [status(esa)], ['0'])).
% 0.35/0.54  thf('2', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('3', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(redefinition_k1_partfun1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.35/0.54     ( ( ( v1_funct_1 @ E ) & 
% 0.35/0.54         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.35/0.54         ( v1_funct_1 @ F ) & 
% 0.35/0.54         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.35/0.54       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.35/0.54  thf('4', plain,
% 0.35/0.54      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.35/0.54          | ~ (v1_funct_1 @ X38)
% 0.35/0.54          | ~ (v1_funct_1 @ X41)
% 0.35/0.54          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 0.35/0.54          | ((k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41)
% 0.35/0.54              = (k5_relat_1 @ X38 @ X41)))),
% 0.35/0.54      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.35/0.54  thf('5', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.54         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.35/0.54            = (k5_relat_1 @ sk_C @ X0))
% 0.35/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.35/0.54          | ~ (v1_funct_1 @ X0)
% 0.35/0.54          | ~ (v1_funct_1 @ sk_C))),
% 0.35/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.35/0.54  thf('6', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('7', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.54         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.35/0.54            = (k5_relat_1 @ sk_C @ X0))
% 0.35/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.35/0.54          | ~ (v1_funct_1 @ X0))),
% 0.35/0.54      inference('demod', [status(thm)], ['5', '6'])).
% 0.35/0.54  thf('8', plain,
% 0.35/0.54      ((~ (v1_funct_1 @ sk_D)
% 0.35/0.54        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.35/0.54            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['2', '7'])).
% 0.35/0.54  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('10', plain,
% 0.35/0.54      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.35/0.54         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.35/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.35/0.54  thf('11', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(t24_funct_2, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.35/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.54       ( ![D:$i]:
% 0.35/0.54         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.35/0.54             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.35/0.54           ( ( r2_relset_1 @
% 0.35/0.54               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.35/0.54               ( k6_partfun1 @ B ) ) =>
% 0.35/0.54             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.35/0.54  thf('12', plain,
% 0.35/0.54      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.35/0.54         (~ (v1_funct_1 @ X45)
% 0.35/0.54          | ~ (v1_funct_2 @ X45 @ X46 @ X47)
% 0.35/0.54          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 0.35/0.54          | ~ (r2_relset_1 @ X46 @ X46 @ 
% 0.35/0.54               (k1_partfun1 @ X46 @ X47 @ X47 @ X46 @ X45 @ X48) @ 
% 0.35/0.54               (k6_partfun1 @ X46))
% 0.35/0.54          | ((k2_relset_1 @ X47 @ X46 @ X48) = (X46))
% 0.35/0.54          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46)))
% 0.35/0.54          | ~ (v1_funct_2 @ X48 @ X47 @ X46)
% 0.35/0.54          | ~ (v1_funct_1 @ X48))),
% 0.35/0.54      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.35/0.54  thf(redefinition_k6_partfun1, axiom,
% 0.35/0.54    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.35/0.54  thf('13', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 0.35/0.54      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.35/0.54  thf('14', plain,
% 0.35/0.54      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.35/0.54         (~ (v1_funct_1 @ X45)
% 0.35/0.54          | ~ (v1_funct_2 @ X45 @ X46 @ X47)
% 0.35/0.54          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 0.35/0.54          | ~ (r2_relset_1 @ X46 @ X46 @ 
% 0.35/0.54               (k1_partfun1 @ X46 @ X47 @ X47 @ X46 @ X45 @ X48) @ 
% 0.35/0.54               (k6_relat_1 @ X46))
% 0.35/0.54          | ((k2_relset_1 @ X47 @ X46 @ X48) = (X46))
% 0.35/0.54          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46)))
% 0.35/0.54          | ~ (v1_funct_2 @ X48 @ X47 @ X46)
% 0.35/0.54          | ~ (v1_funct_1 @ X48))),
% 0.35/0.54      inference('demod', [status(thm)], ['12', '13'])).
% 0.35/0.54  thf('15', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (~ (v1_funct_1 @ X0)
% 0.35/0.54          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.35/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.35/0.54          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.35/0.54          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.35/0.54               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.35/0.54               (k6_relat_1 @ sk_A))
% 0.35/0.54          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.35/0.54          | ~ (v1_funct_1 @ sk_C))),
% 0.35/0.54      inference('sup-', [status(thm)], ['11', '14'])).
% 0.35/0.54  thf('16', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('18', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (~ (v1_funct_1 @ X0)
% 0.35/0.54          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.35/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.35/0.54          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.35/0.54          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.35/0.54               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.35/0.54               (k6_relat_1 @ sk_A)))),
% 0.35/0.54      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.35/0.54  thf('19', plain,
% 0.35/0.54      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.35/0.54           (k6_relat_1 @ sk_A))
% 0.35/0.54        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.35/0.54        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.35/0.54        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.35/0.54        | ~ (v1_funct_1 @ sk_D))),
% 0.35/0.54      inference('sup-', [status(thm)], ['10', '18'])).
% 0.35/0.54  thf('20', plain,
% 0.35/0.54      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.35/0.54        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.35/0.54        (k6_partfun1 @ sk_A))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('21', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 0.35/0.54      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.35/0.54  thf('22', plain,
% 0.35/0.54      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.35/0.54        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.35/0.54        (k6_relat_1 @ sk_A))),
% 0.35/0.54      inference('demod', [status(thm)], ['20', '21'])).
% 0.35/0.54  thf('23', plain,
% 0.35/0.54      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.35/0.54         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.35/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.35/0.54  thf('24', plain,
% 0.35/0.54      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.35/0.54        (k6_relat_1 @ sk_A))),
% 0.35/0.54      inference('demod', [status(thm)], ['22', '23'])).
% 0.35/0.54  thf('25', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(redefinition_k2_relset_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.54       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.35/0.54  thf('26', plain,
% 0.35/0.54      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.35/0.54         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 0.35/0.54          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.35/0.54      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.35/0.54  thf('27', plain,
% 0.35/0.54      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.35/0.54      inference('sup-', [status(thm)], ['25', '26'])).
% 0.35/0.54  thf('28', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('29', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('30', plain, ((v1_funct_1 @ sk_D)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('31', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.35/0.54      inference('demod', [status(thm)], ['19', '24', '27', '28', '29', '30'])).
% 0.35/0.54  thf(d3_funct_2, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.35/0.54       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.35/0.54  thf('32', plain,
% 0.35/0.54      (![X28 : $i, X29 : $i]:
% 0.35/0.54         (((k2_relat_1 @ X29) != (X28))
% 0.35/0.54          | (v2_funct_2 @ X29 @ X28)
% 0.35/0.54          | ~ (v5_relat_1 @ X29 @ X28)
% 0.35/0.54          | ~ (v1_relat_1 @ X29))),
% 0.35/0.54      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.35/0.54  thf('33', plain,
% 0.35/0.54      (![X29 : $i]:
% 0.35/0.54         (~ (v1_relat_1 @ X29)
% 0.35/0.54          | ~ (v5_relat_1 @ X29 @ (k2_relat_1 @ X29))
% 0.35/0.54          | (v2_funct_2 @ X29 @ (k2_relat_1 @ X29)))),
% 0.35/0.54      inference('simplify', [status(thm)], ['32'])).
% 0.35/0.54  thf('34', plain,
% 0.35/0.54      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 0.35/0.54        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 0.35/0.54        | ~ (v1_relat_1 @ sk_D))),
% 0.35/0.54      inference('sup-', [status(thm)], ['31', '33'])).
% 0.35/0.54  thf('35', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(cc2_relset_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.54       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.35/0.54  thf('36', plain,
% 0.35/0.54      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.35/0.54         ((v5_relat_1 @ X18 @ X20)
% 0.35/0.54          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.35/0.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.35/0.54  thf('37', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 0.35/0.54      inference('sup-', [status(thm)], ['35', '36'])).
% 0.35/0.54  thf('38', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.35/0.54      inference('demod', [status(thm)], ['19', '24', '27', '28', '29', '30'])).
% 0.35/0.54  thf('39', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(cc1_relset_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.54       ( v1_relat_1 @ C ) ))).
% 0.35/0.54  thf('40', plain,
% 0.35/0.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.35/0.54         ((v1_relat_1 @ X15)
% 0.35/0.54          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.35/0.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.35/0.54  thf('41', plain, ((v1_relat_1 @ sk_D)),
% 0.35/0.54      inference('sup-', [status(thm)], ['39', '40'])).
% 0.35/0.54  thf('42', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 0.35/0.54      inference('demod', [status(thm)], ['34', '37', '38', '41'])).
% 0.35/0.54  thf('43', plain,
% 0.35/0.54      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 0.35/0.54      inference('split', [status(esa)], ['0'])).
% 0.35/0.54  thf('44', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['42', '43'])).
% 0.35/0.54  thf('45', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 0.35/0.54      inference('split', [status(esa)], ['0'])).
% 0.35/0.54  thf('46', plain, (~ ((v2_funct_1 @ sk_C))),
% 0.35/0.54      inference('sat_resolution*', [status(thm)], ['44', '45'])).
% 0.35/0.54  thf('47', plain, (~ (v2_funct_1 @ sk_C)),
% 0.35/0.54      inference('simpl_trail', [status(thm)], ['1', '46'])).
% 0.35/0.54  thf('48', plain,
% 0.35/0.54      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.35/0.54        (k6_relat_1 @ sk_A))),
% 0.35/0.54      inference('demod', [status(thm)], ['22', '23'])).
% 0.35/0.54  thf('49', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('50', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(dt_k1_partfun1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.35/0.54     ( ( ( v1_funct_1 @ E ) & 
% 0.35/0.54         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.35/0.54         ( v1_funct_1 @ F ) & 
% 0.35/0.54         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.35/0.54       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.35/0.54         ( m1_subset_1 @
% 0.35/0.54           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.35/0.54           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.35/0.54  thf('51', plain,
% 0.35/0.54      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.35/0.54          | ~ (v1_funct_1 @ X30)
% 0.35/0.54          | ~ (v1_funct_1 @ X33)
% 0.35/0.54          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.35/0.54          | (m1_subset_1 @ (k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33) @ 
% 0.35/0.54             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X35))))),
% 0.35/0.54      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.35/0.54  thf('52', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.54         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.35/0.54           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.35/0.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.35/0.54          | ~ (v1_funct_1 @ X1)
% 0.35/0.54          | ~ (v1_funct_1 @ sk_C))),
% 0.35/0.54      inference('sup-', [status(thm)], ['50', '51'])).
% 0.35/0.54  thf('53', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('54', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.54         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.35/0.54           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.35/0.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.35/0.54          | ~ (v1_funct_1 @ X1))),
% 0.35/0.54      inference('demod', [status(thm)], ['52', '53'])).
% 0.35/0.54  thf('55', plain,
% 0.35/0.54      ((~ (v1_funct_1 @ sk_D)
% 0.35/0.54        | (m1_subset_1 @ 
% 0.35/0.54           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.35/0.54           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['49', '54'])).
% 0.35/0.54  thf('56', plain, ((v1_funct_1 @ sk_D)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('57', plain,
% 0.35/0.54      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.35/0.54         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.35/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.35/0.54  thf('58', plain,
% 0.35/0.54      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.35/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.35/0.54      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.35/0.54  thf(redefinition_r2_relset_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.54     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.35/0.54         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.54       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.35/0.54  thf('59', plain,
% 0.35/0.54      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.35/0.54          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.35/0.54          | ((X24) = (X27))
% 0.35/0.54          | ~ (r2_relset_1 @ X25 @ X26 @ X24 @ X27))),
% 0.35/0.54      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.35/0.54  thf('60', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 0.35/0.54          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 0.35/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['58', '59'])).
% 0.35/0.54  thf('61', plain,
% 0.35/0.54      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 0.35/0.54           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.35/0.54        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['48', '60'])).
% 0.35/0.54  thf(dt_k6_partfun1, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( m1_subset_1 @
% 0.35/0.54         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.35/0.54       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.35/0.54  thf('62', plain,
% 0.35/0.54      (![X37 : $i]:
% 0.35/0.54         (m1_subset_1 @ (k6_partfun1 @ X37) @ 
% 0.35/0.54          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))),
% 0.35/0.54      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.35/0.54  thf('63', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 0.35/0.54      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.35/0.54  thf('64', plain,
% 0.35/0.54      (![X37 : $i]:
% 0.35/0.54         (m1_subset_1 @ (k6_relat_1 @ X37) @ 
% 0.35/0.54          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))),
% 0.35/0.54      inference('demod', [status(thm)], ['62', '63'])).
% 0.35/0.54  thf('65', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 0.35/0.54      inference('demod', [status(thm)], ['61', '64'])).
% 0.35/0.54  thf(t27_funct_1, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.35/0.54           ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k1_relat_1 @ B ) ) =>
% 0.35/0.54             ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.35/0.54  thf('66', plain,
% 0.35/0.54      (![X11 : $i, X12 : $i]:
% 0.35/0.54         (~ (v1_relat_1 @ X11)
% 0.35/0.54          | ~ (v1_funct_1 @ X11)
% 0.35/0.54          | (r1_tarski @ (k2_relat_1 @ X11) @ (k1_relat_1 @ X12))
% 0.35/0.54          | ((k1_relat_1 @ (k5_relat_1 @ X11 @ X12)) != (k1_relat_1 @ X11))
% 0.35/0.54          | ~ (v1_funct_1 @ X12)
% 0.35/0.54          | ~ (v1_relat_1 @ X12))),
% 0.35/0.54      inference('cnf', [status(esa)], [t27_funct_1])).
% 0.35/0.54  thf('67', plain,
% 0.35/0.54      ((((k1_relat_1 @ (k6_relat_1 @ sk_A)) != (k1_relat_1 @ sk_C))
% 0.35/0.54        | ~ (v1_relat_1 @ sk_D)
% 0.35/0.54        | ~ (v1_funct_1 @ sk_D)
% 0.35/0.54        | (r1_tarski @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_D))
% 0.35/0.54        | ~ (v1_funct_1 @ sk_C)
% 0.35/0.54        | ~ (v1_relat_1 @ sk_C))),
% 0.35/0.54      inference('sup-', [status(thm)], ['65', '66'])).
% 0.35/0.54  thf(t71_relat_1, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.35/0.54       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.35/0.54  thf('68', plain, (![X7 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X7)) = (X7))),
% 0.35/0.54      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.35/0.54  thf('69', plain, ((v1_relat_1 @ sk_D)),
% 0.35/0.54      inference('sup-', [status(thm)], ['39', '40'])).
% 0.35/0.54  thf('70', plain, ((v1_funct_1 @ sk_D)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('71', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('72', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('73', plain,
% 0.35/0.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.35/0.54         ((v1_relat_1 @ X15)
% 0.35/0.54          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.35/0.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.35/0.54  thf('74', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.54      inference('sup-', [status(thm)], ['72', '73'])).
% 0.35/0.54  thf('75', plain,
% 0.35/0.54      ((((sk_A) != (k1_relat_1 @ sk_C))
% 0.35/0.54        | (r1_tarski @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_D)))),
% 0.35/0.54      inference('demod', [status(thm)], ['67', '68', '69', '70', '71', '74'])).
% 0.35/0.54  thf('76', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 0.35/0.54      inference('demod', [status(thm)], ['61', '64'])).
% 0.35/0.54  thf(t44_relat_1, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( v1_relat_1 @ A ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( v1_relat_1 @ B ) =>
% 0.35/0.54           ( r1_tarski @
% 0.35/0.54             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.35/0.54  thf('77', plain,
% 0.35/0.54      (![X5 : $i, X6 : $i]:
% 0.35/0.54         (~ (v1_relat_1 @ X5)
% 0.35/0.54          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X6 @ X5)) @ 
% 0.35/0.54             (k1_relat_1 @ X6))
% 0.35/0.54          | ~ (v1_relat_1 @ X6))),
% 0.35/0.54      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.35/0.54  thf(d10_xboole_0, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.35/0.54  thf('78', plain,
% 0.35/0.54      (![X0 : $i, X2 : $i]:
% 0.35/0.54         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.35/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.35/0.54  thf('79', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (~ (v1_relat_1 @ X0)
% 0.35/0.54          | ~ (v1_relat_1 @ X1)
% 0.35/0.54          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.35/0.54               (k1_relat_1 @ (k5_relat_1 @ X0 @ X1)))
% 0.35/0.54          | ((k1_relat_1 @ X0) = (k1_relat_1 @ (k5_relat_1 @ X0 @ X1))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['77', '78'])).
% 0.35/0.54  thf('80', plain,
% 0.35/0.54      ((~ (r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_relat_1 @ (k6_relat_1 @ sk_A)))
% 0.35/0.54        | ((k1_relat_1 @ sk_C) = (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 0.35/0.54        | ~ (v1_relat_1 @ sk_D)
% 0.35/0.54        | ~ (v1_relat_1 @ sk_C))),
% 0.35/0.54      inference('sup-', [status(thm)], ['76', '79'])).
% 0.35/0.54  thf('81', plain, (![X7 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X7)) = (X7))),
% 0.35/0.54      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.35/0.54  thf('82', plain,
% 0.35/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('83', plain,
% 0.35/0.54      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.35/0.54         ((v4_relat_1 @ X18 @ X19)
% 0.35/0.54          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.35/0.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.35/0.54  thf('84', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.35/0.54      inference('sup-', [status(thm)], ['82', '83'])).
% 0.35/0.54  thf(d18_relat_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( v1_relat_1 @ B ) =>
% 0.35/0.54       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.35/0.54  thf('85', plain,
% 0.35/0.54      (![X3 : $i, X4 : $i]:
% 0.35/0.54         (~ (v4_relat_1 @ X3 @ X4)
% 0.35/0.54          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 0.35/0.54          | ~ (v1_relat_1 @ X3))),
% 0.35/0.54      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.35/0.54  thf('86', plain,
% 0.35/0.54      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['84', '85'])).
% 0.35/0.54  thf('87', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.54      inference('sup-', [status(thm)], ['72', '73'])).
% 0.35/0.54  thf('88', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.35/0.54      inference('demod', [status(thm)], ['86', '87'])).
% 0.35/0.54  thf('89', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 0.35/0.54      inference('demod', [status(thm)], ['61', '64'])).
% 0.35/0.54  thf('90', plain, (![X7 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X7)) = (X7))),
% 0.35/0.54      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.35/0.54  thf('91', plain, ((v1_relat_1 @ sk_D)),
% 0.35/0.54      inference('sup-', [status(thm)], ['39', '40'])).
% 0.35/0.54  thf('92', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.54      inference('sup-', [status(thm)], ['72', '73'])).
% 0.35/0.54  thf('93', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.35/0.54      inference('demod', [status(thm)],
% 0.35/0.54                ['80', '81', '88', '89', '90', '91', '92'])).
% 0.35/0.54  thf('94', plain,
% 0.35/0.54      ((((sk_A) != (sk_A))
% 0.35/0.54        | (r1_tarski @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_D)))),
% 0.35/0.54      inference('demod', [status(thm)], ['75', '93'])).
% 0.35/0.54  thf('95', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_D))),
% 0.35/0.54      inference('simplify', [status(thm)], ['94'])).
% 0.35/0.54  thf(t47_funct_1, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.35/0.54           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.35/0.54               ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) =>
% 0.35/0.54             ( v2_funct_1 @ B ) ) ) ) ))).
% 0.35/0.54  thf('96', plain,
% 0.35/0.54      (![X13 : $i, X14 : $i]:
% 0.35/0.54         (~ (v1_relat_1 @ X13)
% 0.35/0.54          | ~ (v1_funct_1 @ X13)
% 0.35/0.54          | (v2_funct_1 @ X13)
% 0.35/0.54          | ~ (r1_tarski @ (k2_relat_1 @ X13) @ (k1_relat_1 @ X14))
% 0.35/0.54          | ~ (v2_funct_1 @ (k5_relat_1 @ X13 @ X14))
% 0.35/0.54          | ~ (v1_funct_1 @ X14)
% 0.35/0.54          | ~ (v1_relat_1 @ X14))),
% 0.35/0.54      inference('cnf', [status(esa)], [t47_funct_1])).
% 0.35/0.54  thf('97', plain,
% 0.35/0.54      ((~ (v1_relat_1 @ sk_D)
% 0.35/0.54        | ~ (v1_funct_1 @ sk_D)
% 0.35/0.54        | ~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 0.35/0.54        | (v2_funct_1 @ sk_C)
% 0.35/0.54        | ~ (v1_funct_1 @ sk_C)
% 0.35/0.54        | ~ (v1_relat_1 @ sk_C))),
% 0.35/0.54      inference('sup-', [status(thm)], ['95', '96'])).
% 0.35/0.54  thf('98', plain, ((v1_relat_1 @ sk_D)),
% 0.35/0.54      inference('sup-', [status(thm)], ['39', '40'])).
% 0.35/0.54  thf('99', plain, ((v1_funct_1 @ sk_D)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('100', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 0.35/0.54      inference('demod', [status(thm)], ['61', '64'])).
% 0.35/0.54  thf(fc4_funct_1, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.35/0.54       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.35/0.54  thf('101', plain, (![X10 : $i]: (v2_funct_1 @ (k6_relat_1 @ X10))),
% 0.35/0.54      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.35/0.54  thf('102', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('103', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.54      inference('sup-', [status(thm)], ['72', '73'])).
% 0.35/0.54  thf('104', plain, ((v2_funct_1 @ sk_C)),
% 0.35/0.54      inference('demod', [status(thm)],
% 0.35/0.54                ['97', '98', '99', '100', '101', '102', '103'])).
% 0.35/0.54  thf('105', plain, ($false), inference('demod', [status(thm)], ['47', '104'])).
% 0.35/0.54  
% 0.35/0.54  % SZS output end Refutation
% 0.35/0.54  
% 0.35/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

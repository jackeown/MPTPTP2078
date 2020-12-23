%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WDtJGUhmpx

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:12 EST 2020

% Result     : Theorem 19.52s
% Output     : Refutation 19.52s
% Verified   : 
% Statistics : Number of formulae       :  197 ( 683 expanded)
%              Number of leaves         :   46 ( 224 expanded)
%              Depth                    :   16
%              Number of atoms          : 1837 (13896 expanded)
%              Number of equality atoms :   74 ( 190 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t88_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ ( k6_partfun1 @ A ) )
        & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ ( k6_partfun1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( v3_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ ( k6_partfun1 @ A ) )
          & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ ( k6_partfun1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t88_funct_2])).

thf('0',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X49: $i,X50: $i] :
      ( ( ( k2_funct_2 @ X50 @ X49 )
        = ( k2_funct_1 @ X49 ) )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X50 ) ) )
      | ~ ( v3_funct_2 @ X49 @ X50 @ X50 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X50 )
      | ~ ( v1_funct_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('4',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B )
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('9',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
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

thf('12',plain,(
    ! [X39: $i,X40: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X39 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) )
      | ~ ( v3_funct_2 @ X40 @ X39 @ X39 )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X39 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('18',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( ( k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46 )
        = ( k5_relat_1 @ X43 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X39: $i,X40: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X39 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) )
      | ~ ( v3_funct_2 @ X40 @ X39 @ X39 )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X39 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('22',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['22','23','24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','26'])).

thf('28',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('29',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
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

thf('34',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_1 @ X26 )
      | ~ ( v3_funct_2 @ X26 @ X27 @ X28 )
      | ( v2_funct_2 @ X26 @ X28 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('35',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['35','36','37'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('39',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v2_funct_2 @ X38 @ X37 )
      | ( ( k2_relat_1 @ X38 )
        = X37 )
      | ~ ( v5_relat_1 @ X38 @ X37 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('42',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('43',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('45',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v5_relat_1 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('46',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['40','43','46'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('48',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X12 ) @ X12 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('49',plain,(
    ! [X51: $i] :
      ( ( k6_partfun1 @ X51 )
      = ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('50',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X12 ) @ X12 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('51',plain,(
    ! [X42: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['47','52'])).

thf('54',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['40','43','46'])).

thf('55',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_1 @ X26 )
      | ~ ( v3_funct_2 @ X26 @ X27 @ X28 )
      | ( v2_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('57',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['41','42'])).

thf('63',plain,(
    m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54','60','61','62'])).

thf('64',plain,(
    ! [X42: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('65',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( X22 = X25 )
      | ~ ( r2_relset_1 @ X23 @ X24 @ X22 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      | ( ( k6_partfun1 @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k6_partfun1 @ sk_A )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['40','43','46'])).

thf('69',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X12 ) @ X12 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('70',plain,(
    ! [X42: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('71',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( r2_relset_1 @ X23 @ X24 @ X22 @ X25 )
      | ( X22 != X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('72',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_relset_1 @ X23 @ X24 @ X25 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r2_relset_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['69','73'])).

thf('75',plain,
    ( ( r2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) @ ( k6_partfun1 @ ( k2_relat_1 @ sk_B ) ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['68','74'])).

thf('76',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['40','43','46'])).

thf('77',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['40','43','46'])).

thf('78',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('79',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['41','42'])).

thf('81',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['75','76','77','78','79','80'])).

thf('82',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['67','81'])).

thf('83',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','82'])).

thf('84',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('85',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('86',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','72'])).

thf('89',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('91',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['9','91'])).

thf('93',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('94',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('95',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( ( k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46 )
        = ( k5_relat_1 @ X43 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['95','100'])).

thf('102',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['22','23','24','25'])).

thf('103',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('104',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('106',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('107',plain,
    ( ~ ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('109',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('110',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ~ ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['107','110'])).

thf('112',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('113',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('114',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('116',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X30 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('117',plain,(
    ! [X29: $i] :
      ( zip_tseitin_0 @ X29 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['115','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['118'])).

thf('120',plain,(
    zip_tseitin_1 @ sk_B @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['114','119'])).

thf('121',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['111','120'])).

thf('122',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k5_relat_1 @ X12 @ ( k2_funct_1 @ X12 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('123',plain,(
    ! [X51: $i] :
      ( ( k6_partfun1 @ X51 )
      = ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('124',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k5_relat_1 @ X12 @ ( k2_funct_1 @ X12 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X42: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,
    ( ( m1_subset_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['121','126'])).

thf('128',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['111','120'])).

thf('129',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('130',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['41','42'])).

thf('132',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['127','128','129','130','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      | ( ( k6_partfun1 @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('134',plain,
    ( ( ( k6_partfun1 @ sk_A )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['111','120'])).

thf('136',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k5_relat_1 @ X12 @ ( k2_funct_1 @ X12 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('137',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','72'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( r2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['136','137'])).

thf('139',plain,
    ( ( r2_relset_1 @ sk_A @ ( k1_relat_1 @ sk_B ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['135','138'])).

thf('140',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['111','120'])).

thf('141',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['111','120'])).

thf('142',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('143',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['41','42'])).

thf('145',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['139','140','141','142','143','144'])).

thf('146',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['134','145'])).

thf('147',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['101','104','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','72'])).

thf('149',plain,(
    $false ),
    inference(demod,[status(thm)],['92','147','148'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WDtJGUhmpx
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:42:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 19.52/19.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 19.52/19.71  % Solved by: fo/fo7.sh
% 19.52/19.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 19.52/19.71  % done 5473 iterations in 19.239s
% 19.52/19.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 19.52/19.71  % SZS output start Refutation
% 19.52/19.71  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 19.52/19.71  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 19.52/19.71  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 19.52/19.71  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 19.52/19.71  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 19.52/19.71  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 19.52/19.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 19.52/19.71  thf(sk_A_type, type, sk_A: $i).
% 19.52/19.71  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 19.52/19.71  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 19.52/19.71  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 19.52/19.71  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 19.52/19.71  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 19.52/19.71  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 19.52/19.71  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 19.52/19.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 19.52/19.71  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 19.52/19.71  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 19.52/19.71  thf(sk_B_type, type, sk_B: $i).
% 19.52/19.71  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 19.52/19.71  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 19.52/19.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 19.52/19.71  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 19.52/19.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 19.52/19.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 19.52/19.71  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 19.52/19.71  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 19.52/19.71  thf(t88_funct_2, conjecture,
% 19.52/19.71    (![A:$i,B:$i]:
% 19.52/19.71     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 19.52/19.71         ( v3_funct_2 @ B @ A @ A ) & 
% 19.52/19.71         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 19.52/19.71       ( ( r2_relset_1 @
% 19.52/19.71           A @ A @ 
% 19.52/19.71           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 19.52/19.71           ( k6_partfun1 @ A ) ) & 
% 19.52/19.71         ( r2_relset_1 @
% 19.52/19.71           A @ A @ 
% 19.52/19.71           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 19.52/19.71           ( k6_partfun1 @ A ) ) ) ))).
% 19.52/19.71  thf(zf_stmt_0, negated_conjecture,
% 19.52/19.71    (~( ![A:$i,B:$i]:
% 19.52/19.71        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 19.52/19.71            ( v3_funct_2 @ B @ A @ A ) & 
% 19.52/19.71            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 19.52/19.71          ( ( r2_relset_1 @
% 19.52/19.71              A @ A @ 
% 19.52/19.71              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 19.52/19.71              ( k6_partfun1 @ A ) ) & 
% 19.52/19.71            ( r2_relset_1 @
% 19.52/19.71              A @ A @ 
% 19.52/19.71              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 19.52/19.71              ( k6_partfun1 @ A ) ) ) ) )),
% 19.52/19.71    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 19.52/19.71  thf('0', plain,
% 19.52/19.71      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 19.52/19.71           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 19.52/19.71            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 19.52/19.71           (k6_partfun1 @ sk_A))
% 19.52/19.71        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 19.52/19.71             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 19.52/19.71              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 19.52/19.71             (k6_partfun1 @ sk_A)))),
% 19.52/19.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.52/19.71  thf('1', plain,
% 19.52/19.71      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 19.52/19.71           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 19.52/19.71            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 19.52/19.71           (k6_partfun1 @ sk_A)))
% 19.52/19.71         <= (~
% 19.52/19.71             ((r2_relset_1 @ sk_A @ sk_A @ 
% 19.52/19.71               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 19.52/19.71                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 19.52/19.71               (k6_partfun1 @ sk_A))))),
% 19.52/19.71      inference('split', [status(esa)], ['0'])).
% 19.52/19.71  thf('2', plain,
% 19.52/19.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 19.52/19.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.52/19.71  thf(redefinition_k2_funct_2, axiom,
% 19.52/19.71    (![A:$i,B:$i]:
% 19.52/19.71     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 19.52/19.71         ( v3_funct_2 @ B @ A @ A ) & 
% 19.52/19.71         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 19.52/19.71       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 19.52/19.71  thf('3', plain,
% 19.52/19.71      (![X49 : $i, X50 : $i]:
% 19.52/19.71         (((k2_funct_2 @ X50 @ X49) = (k2_funct_1 @ X49))
% 19.52/19.71          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X50)))
% 19.52/19.71          | ~ (v3_funct_2 @ X49 @ X50 @ X50)
% 19.52/19.71          | ~ (v1_funct_2 @ X49 @ X50 @ X50)
% 19.52/19.71          | ~ (v1_funct_1 @ X49))),
% 19.52/19.71      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 19.52/19.71  thf('4', plain,
% 19.52/19.71      ((~ (v1_funct_1 @ sk_B)
% 19.52/19.71        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 19.52/19.71        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 19.52/19.71        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 19.52/19.71      inference('sup-', [status(thm)], ['2', '3'])).
% 19.52/19.71  thf('5', plain, ((v1_funct_1 @ sk_B)),
% 19.52/19.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.52/19.71  thf('6', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 19.52/19.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.52/19.71  thf('7', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 19.52/19.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.52/19.71  thf('8', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 19.52/19.71      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 19.52/19.71  thf('9', plain,
% 19.52/19.71      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 19.52/19.71           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 19.52/19.71            (k2_funct_1 @ sk_B)) @ 
% 19.52/19.71           (k6_partfun1 @ sk_A)))
% 19.52/19.71         <= (~
% 19.52/19.71             ((r2_relset_1 @ sk_A @ sk_A @ 
% 19.52/19.71               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 19.52/19.71                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 19.52/19.71               (k6_partfun1 @ sk_A))))),
% 19.52/19.71      inference('demod', [status(thm)], ['1', '8'])).
% 19.52/19.71  thf('10', plain,
% 19.52/19.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 19.52/19.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.52/19.71  thf('11', plain,
% 19.52/19.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 19.52/19.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.52/19.71  thf(dt_k2_funct_2, axiom,
% 19.52/19.71    (![A:$i,B:$i]:
% 19.52/19.71     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 19.52/19.71         ( v3_funct_2 @ B @ A @ A ) & 
% 19.52/19.71         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 19.52/19.71       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 19.52/19.71         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 19.52/19.71         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 19.52/19.71         ( m1_subset_1 @
% 19.52/19.71           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 19.52/19.71  thf('12', plain,
% 19.52/19.71      (![X39 : $i, X40 : $i]:
% 19.52/19.71         ((m1_subset_1 @ (k2_funct_2 @ X39 @ X40) @ 
% 19.52/19.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))
% 19.52/19.71          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))
% 19.52/19.71          | ~ (v3_funct_2 @ X40 @ X39 @ X39)
% 19.52/19.71          | ~ (v1_funct_2 @ X40 @ X39 @ X39)
% 19.52/19.71          | ~ (v1_funct_1 @ X40))),
% 19.52/19.71      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 19.52/19.71  thf('13', plain,
% 19.52/19.71      ((~ (v1_funct_1 @ sk_B)
% 19.52/19.71        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 19.52/19.71        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 19.52/19.71        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 19.52/19.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 19.52/19.71      inference('sup-', [status(thm)], ['11', '12'])).
% 19.52/19.71  thf('14', plain, ((v1_funct_1 @ sk_B)),
% 19.52/19.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.52/19.71  thf('15', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 19.52/19.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.52/19.71  thf('16', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 19.52/19.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.52/19.71  thf('17', plain,
% 19.52/19.71      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 19.52/19.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 19.52/19.71      inference('demod', [status(thm)], ['13', '14', '15', '16'])).
% 19.52/19.71  thf(redefinition_k1_partfun1, axiom,
% 19.52/19.71    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 19.52/19.71     ( ( ( v1_funct_1 @ E ) & 
% 19.52/19.71         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 19.52/19.71         ( v1_funct_1 @ F ) & 
% 19.52/19.71         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 19.52/19.71       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 19.52/19.71  thf('18', plain,
% 19.52/19.71      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 19.52/19.71         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 19.52/19.71          | ~ (v1_funct_1 @ X43)
% 19.52/19.71          | ~ (v1_funct_1 @ X46)
% 19.52/19.71          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 19.52/19.71          | ((k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46)
% 19.52/19.71              = (k5_relat_1 @ X43 @ X46)))),
% 19.52/19.71      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 19.52/19.71  thf('19', plain,
% 19.52/19.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.52/19.71         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 19.52/19.71            X0) = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ X0))
% 19.52/19.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 19.52/19.71          | ~ (v1_funct_1 @ X0)
% 19.52/19.71          | ~ (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 19.52/19.71      inference('sup-', [status(thm)], ['17', '18'])).
% 19.52/19.71  thf('20', plain,
% 19.52/19.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 19.52/19.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.52/19.71  thf('21', plain,
% 19.52/19.71      (![X39 : $i, X40 : $i]:
% 19.52/19.71         ((v1_funct_1 @ (k2_funct_2 @ X39 @ X40))
% 19.52/19.71          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))
% 19.52/19.71          | ~ (v3_funct_2 @ X40 @ X39 @ X39)
% 19.52/19.71          | ~ (v1_funct_2 @ X40 @ X39 @ X39)
% 19.52/19.71          | ~ (v1_funct_1 @ X40))),
% 19.52/19.71      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 19.52/19.71  thf('22', plain,
% 19.52/19.71      ((~ (v1_funct_1 @ sk_B)
% 19.52/19.71        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 19.52/19.71        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 19.52/19.71        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 19.52/19.71      inference('sup-', [status(thm)], ['20', '21'])).
% 19.52/19.71  thf('23', plain, ((v1_funct_1 @ sk_B)),
% 19.52/19.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.52/19.71  thf('24', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 19.52/19.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.52/19.71  thf('25', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 19.52/19.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.52/19.71  thf('26', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 19.52/19.71      inference('demod', [status(thm)], ['22', '23', '24', '25'])).
% 19.52/19.71  thf('27', plain,
% 19.52/19.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.52/19.71         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 19.52/19.71            X0) = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ X0))
% 19.52/19.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 19.52/19.71          | ~ (v1_funct_1 @ X0))),
% 19.52/19.71      inference('demod', [status(thm)], ['19', '26'])).
% 19.52/19.71  thf('28', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 19.52/19.71      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 19.52/19.71  thf('29', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 19.52/19.71      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 19.52/19.71  thf('30', plain,
% 19.52/19.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.52/19.71         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 19.52/19.71            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 19.52/19.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 19.52/19.71          | ~ (v1_funct_1 @ X0))),
% 19.52/19.71      inference('demod', [status(thm)], ['27', '28', '29'])).
% 19.52/19.71  thf('31', plain,
% 19.52/19.71      ((~ (v1_funct_1 @ sk_B)
% 19.52/19.71        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 19.52/19.71            sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 19.52/19.71      inference('sup-', [status(thm)], ['10', '30'])).
% 19.52/19.71  thf('32', plain, ((v1_funct_1 @ sk_B)),
% 19.52/19.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.52/19.71  thf('33', plain,
% 19.52/19.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 19.52/19.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.52/19.71  thf(cc2_funct_2, axiom,
% 19.52/19.71    (![A:$i,B:$i,C:$i]:
% 19.52/19.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 19.52/19.71       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 19.52/19.71         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 19.52/19.71  thf('34', plain,
% 19.52/19.71      (![X26 : $i, X27 : $i, X28 : $i]:
% 19.52/19.71         (~ (v1_funct_1 @ X26)
% 19.52/19.71          | ~ (v3_funct_2 @ X26 @ X27 @ X28)
% 19.52/19.71          | (v2_funct_2 @ X26 @ X28)
% 19.52/19.71          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 19.52/19.71      inference('cnf', [status(esa)], [cc2_funct_2])).
% 19.52/19.71  thf('35', plain,
% 19.52/19.71      (((v2_funct_2 @ sk_B @ sk_A)
% 19.52/19.71        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 19.52/19.71        | ~ (v1_funct_1 @ sk_B))),
% 19.52/19.71      inference('sup-', [status(thm)], ['33', '34'])).
% 19.52/19.71  thf('36', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 19.52/19.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.52/19.71  thf('37', plain, ((v1_funct_1 @ sk_B)),
% 19.52/19.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.52/19.71  thf('38', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 19.52/19.71      inference('demod', [status(thm)], ['35', '36', '37'])).
% 19.52/19.71  thf(d3_funct_2, axiom,
% 19.52/19.71    (![A:$i,B:$i]:
% 19.52/19.71     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 19.52/19.71       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 19.52/19.71  thf('39', plain,
% 19.52/19.71      (![X37 : $i, X38 : $i]:
% 19.52/19.71         (~ (v2_funct_2 @ X38 @ X37)
% 19.52/19.71          | ((k2_relat_1 @ X38) = (X37))
% 19.52/19.71          | ~ (v5_relat_1 @ X38 @ X37)
% 19.52/19.71          | ~ (v1_relat_1 @ X38))),
% 19.52/19.71      inference('cnf', [status(esa)], [d3_funct_2])).
% 19.52/19.71  thf('40', plain,
% 19.52/19.71      ((~ (v1_relat_1 @ sk_B)
% 19.52/19.71        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 19.52/19.71        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 19.52/19.71      inference('sup-', [status(thm)], ['38', '39'])).
% 19.52/19.71  thf('41', plain,
% 19.52/19.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 19.52/19.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.52/19.71  thf(cc1_relset_1, axiom,
% 19.52/19.71    (![A:$i,B:$i,C:$i]:
% 19.52/19.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 19.52/19.71       ( v1_relat_1 @ C ) ))).
% 19.52/19.71  thf('42', plain,
% 19.52/19.71      (![X13 : $i, X14 : $i, X15 : $i]:
% 19.52/19.71         ((v1_relat_1 @ X13)
% 19.52/19.71          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 19.52/19.71      inference('cnf', [status(esa)], [cc1_relset_1])).
% 19.52/19.71  thf('43', plain, ((v1_relat_1 @ sk_B)),
% 19.52/19.71      inference('sup-', [status(thm)], ['41', '42'])).
% 19.52/19.71  thf('44', plain,
% 19.52/19.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 19.52/19.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.52/19.71  thf(cc2_relset_1, axiom,
% 19.52/19.71    (![A:$i,B:$i,C:$i]:
% 19.52/19.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 19.52/19.71       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 19.52/19.71  thf('45', plain,
% 19.52/19.71      (![X16 : $i, X17 : $i, X18 : $i]:
% 19.52/19.71         ((v5_relat_1 @ X16 @ X18)
% 19.52/19.71          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 19.52/19.71      inference('cnf', [status(esa)], [cc2_relset_1])).
% 19.52/19.71  thf('46', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 19.52/19.71      inference('sup-', [status(thm)], ['44', '45'])).
% 19.52/19.71  thf('47', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 19.52/19.71      inference('demod', [status(thm)], ['40', '43', '46'])).
% 19.52/19.71  thf(t61_funct_1, axiom,
% 19.52/19.71    (![A:$i]:
% 19.52/19.71     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 19.52/19.71       ( ( v2_funct_1 @ A ) =>
% 19.52/19.71         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 19.52/19.71             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 19.52/19.71           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 19.52/19.71             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 19.52/19.71  thf('48', plain,
% 19.52/19.71      (![X12 : $i]:
% 19.52/19.71         (~ (v2_funct_1 @ X12)
% 19.52/19.71          | ((k5_relat_1 @ (k2_funct_1 @ X12) @ X12)
% 19.52/19.71              = (k6_relat_1 @ (k2_relat_1 @ X12)))
% 19.52/19.71          | ~ (v1_funct_1 @ X12)
% 19.52/19.71          | ~ (v1_relat_1 @ X12))),
% 19.52/19.71      inference('cnf', [status(esa)], [t61_funct_1])).
% 19.52/19.71  thf(redefinition_k6_partfun1, axiom,
% 19.52/19.71    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 19.52/19.71  thf('49', plain, (![X51 : $i]: ((k6_partfun1 @ X51) = (k6_relat_1 @ X51))),
% 19.52/19.71      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 19.52/19.71  thf('50', plain,
% 19.52/19.71      (![X12 : $i]:
% 19.52/19.71         (~ (v2_funct_1 @ X12)
% 19.52/19.71          | ((k5_relat_1 @ (k2_funct_1 @ X12) @ X12)
% 19.52/19.71              = (k6_partfun1 @ (k2_relat_1 @ X12)))
% 19.52/19.71          | ~ (v1_funct_1 @ X12)
% 19.52/19.71          | ~ (v1_relat_1 @ X12))),
% 19.52/19.71      inference('demod', [status(thm)], ['48', '49'])).
% 19.52/19.71  thf(dt_k6_partfun1, axiom,
% 19.52/19.71    (![A:$i]:
% 19.52/19.71     ( ( m1_subset_1 @
% 19.52/19.71         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 19.52/19.71       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 19.52/19.71  thf('51', plain,
% 19.52/19.71      (![X42 : $i]:
% 19.52/19.71         (m1_subset_1 @ (k6_partfun1 @ X42) @ 
% 19.52/19.71          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X42)))),
% 19.52/19.71      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 19.52/19.71  thf('52', plain,
% 19.52/19.71      (![X0 : $i]:
% 19.52/19.71         ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0) @ 
% 19.52/19.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 19.52/19.71          | ~ (v1_relat_1 @ X0)
% 19.52/19.71          | ~ (v1_funct_1 @ X0)
% 19.52/19.71          | ~ (v2_funct_1 @ X0))),
% 19.52/19.71      inference('sup+', [status(thm)], ['50', '51'])).
% 19.52/19.71  thf('53', plain,
% 19.52/19.71      (((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 19.52/19.71         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))
% 19.52/19.71        | ~ (v2_funct_1 @ sk_B)
% 19.52/19.71        | ~ (v1_funct_1 @ sk_B)
% 19.52/19.71        | ~ (v1_relat_1 @ sk_B))),
% 19.52/19.71      inference('sup+', [status(thm)], ['47', '52'])).
% 19.52/19.71  thf('54', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 19.52/19.71      inference('demod', [status(thm)], ['40', '43', '46'])).
% 19.52/19.71  thf('55', plain,
% 19.52/19.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 19.52/19.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.52/19.71  thf('56', plain,
% 19.52/19.71      (![X26 : $i, X27 : $i, X28 : $i]:
% 19.52/19.71         (~ (v1_funct_1 @ X26)
% 19.52/19.71          | ~ (v3_funct_2 @ X26 @ X27 @ X28)
% 19.52/19.71          | (v2_funct_1 @ X26)
% 19.52/19.71          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 19.52/19.71      inference('cnf', [status(esa)], [cc2_funct_2])).
% 19.52/19.71  thf('57', plain,
% 19.52/19.71      (((v2_funct_1 @ sk_B)
% 19.52/19.71        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 19.52/19.71        | ~ (v1_funct_1 @ sk_B))),
% 19.52/19.71      inference('sup-', [status(thm)], ['55', '56'])).
% 19.52/19.71  thf('58', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 19.52/19.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.52/19.71  thf('59', plain, ((v1_funct_1 @ sk_B)),
% 19.52/19.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.52/19.71  thf('60', plain, ((v2_funct_1 @ sk_B)),
% 19.52/19.71      inference('demod', [status(thm)], ['57', '58', '59'])).
% 19.52/19.71  thf('61', plain, ((v1_funct_1 @ sk_B)),
% 19.52/19.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.52/19.71  thf('62', plain, ((v1_relat_1 @ sk_B)),
% 19.52/19.71      inference('sup-', [status(thm)], ['41', '42'])).
% 19.52/19.71  thf('63', plain,
% 19.52/19.71      ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 19.52/19.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 19.52/19.71      inference('demod', [status(thm)], ['53', '54', '60', '61', '62'])).
% 19.52/19.71  thf('64', plain,
% 19.52/19.71      (![X42 : $i]:
% 19.52/19.71         (m1_subset_1 @ (k6_partfun1 @ X42) @ 
% 19.52/19.71          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X42)))),
% 19.52/19.71      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 19.52/19.71  thf(redefinition_r2_relset_1, axiom,
% 19.52/19.71    (![A:$i,B:$i,C:$i,D:$i]:
% 19.52/19.71     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 19.52/19.71         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 19.52/19.71       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 19.52/19.71  thf('65', plain,
% 19.52/19.71      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 19.52/19.71         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 19.52/19.71          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 19.52/19.71          | ((X22) = (X25))
% 19.52/19.71          | ~ (r2_relset_1 @ X23 @ X24 @ X22 @ X25))),
% 19.52/19.71      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 19.52/19.71  thf('66', plain,
% 19.52/19.71      (![X0 : $i, X1 : $i]:
% 19.52/19.71         (~ (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 19.52/19.71          | ((k6_partfun1 @ X0) = (X1))
% 19.52/19.71          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0))))),
% 19.52/19.71      inference('sup-', [status(thm)], ['64', '65'])).
% 19.52/19.71  thf('67', plain,
% 19.52/19.71      ((((k6_partfun1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))
% 19.52/19.71        | ~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 19.52/19.71             (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 19.52/19.71      inference('sup-', [status(thm)], ['63', '66'])).
% 19.52/19.71  thf('68', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 19.52/19.71      inference('demod', [status(thm)], ['40', '43', '46'])).
% 19.52/19.71  thf('69', plain,
% 19.52/19.71      (![X12 : $i]:
% 19.52/19.71         (~ (v2_funct_1 @ X12)
% 19.52/19.71          | ((k5_relat_1 @ (k2_funct_1 @ X12) @ X12)
% 19.52/19.71              = (k6_partfun1 @ (k2_relat_1 @ X12)))
% 19.52/19.71          | ~ (v1_funct_1 @ X12)
% 19.52/19.71          | ~ (v1_relat_1 @ X12))),
% 19.52/19.71      inference('demod', [status(thm)], ['48', '49'])).
% 19.52/19.71  thf('70', plain,
% 19.52/19.71      (![X42 : $i]:
% 19.52/19.71         (m1_subset_1 @ (k6_partfun1 @ X42) @ 
% 19.52/19.71          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X42)))),
% 19.52/19.71      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 19.52/19.71  thf('71', plain,
% 19.52/19.71      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 19.52/19.71         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 19.52/19.71          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 19.52/19.71          | (r2_relset_1 @ X23 @ X24 @ X22 @ X25)
% 19.52/19.71          | ((X22) != (X25)))),
% 19.52/19.71      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 19.52/19.71  thf('72', plain,
% 19.52/19.71      (![X23 : $i, X24 : $i, X25 : $i]:
% 19.52/19.71         ((r2_relset_1 @ X23 @ X24 @ X25 @ X25)
% 19.52/19.71          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 19.52/19.71      inference('simplify', [status(thm)], ['71'])).
% 19.52/19.71  thf('73', plain,
% 19.52/19.71      (![X0 : $i]:
% 19.52/19.71         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 19.52/19.71      inference('sup-', [status(thm)], ['70', '72'])).
% 19.52/19.71  thf('74', plain,
% 19.52/19.71      (![X0 : $i]:
% 19.52/19.71         ((r2_relset_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 19.52/19.71           (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 19.52/19.71           (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 19.52/19.71          | ~ (v1_relat_1 @ X0)
% 19.52/19.71          | ~ (v1_funct_1 @ X0)
% 19.52/19.71          | ~ (v2_funct_1 @ X0))),
% 19.52/19.71      inference('sup+', [status(thm)], ['69', '73'])).
% 19.52/19.71  thf('75', plain,
% 19.52/19.71      (((r2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B) @ 
% 19.52/19.71         (k6_partfun1 @ (k2_relat_1 @ sk_B)) @ 
% 19.52/19.71         (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))
% 19.52/19.71        | ~ (v2_funct_1 @ sk_B)
% 19.52/19.71        | ~ (v1_funct_1 @ sk_B)
% 19.52/19.71        | ~ (v1_relat_1 @ sk_B))),
% 19.52/19.71      inference('sup+', [status(thm)], ['68', '74'])).
% 19.52/19.71  thf('76', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 19.52/19.71      inference('demod', [status(thm)], ['40', '43', '46'])).
% 19.52/19.71  thf('77', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 19.52/19.71      inference('demod', [status(thm)], ['40', '43', '46'])).
% 19.52/19.71  thf('78', plain, ((v2_funct_1 @ sk_B)),
% 19.52/19.71      inference('demod', [status(thm)], ['57', '58', '59'])).
% 19.52/19.71  thf('79', plain, ((v1_funct_1 @ sk_B)),
% 19.52/19.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.52/19.71  thf('80', plain, ((v1_relat_1 @ sk_B)),
% 19.52/19.71      inference('sup-', [status(thm)], ['41', '42'])).
% 19.52/19.71  thf('81', plain,
% 19.52/19.71      ((r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 19.52/19.71        (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 19.52/19.71      inference('demod', [status(thm)], ['75', '76', '77', '78', '79', '80'])).
% 19.52/19.71  thf('82', plain,
% 19.52/19.71      (((k6_partfun1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 19.52/19.71      inference('demod', [status(thm)], ['67', '81'])).
% 19.52/19.71  thf('83', plain,
% 19.52/19.71      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 19.52/19.71         = (k6_partfun1 @ sk_A))),
% 19.52/19.71      inference('demod', [status(thm)], ['31', '32', '82'])).
% 19.52/19.71  thf('84', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 19.52/19.71      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 19.52/19.71  thf('85', plain,
% 19.52/19.71      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 19.52/19.71           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 19.52/19.71            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 19.52/19.71           (k6_partfun1 @ sk_A)))
% 19.52/19.71         <= (~
% 19.52/19.71             ((r2_relset_1 @ sk_A @ sk_A @ 
% 19.52/19.71               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 19.52/19.71                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 19.52/19.71               (k6_partfun1 @ sk_A))))),
% 19.52/19.71      inference('split', [status(esa)], ['0'])).
% 19.52/19.71  thf('86', plain,
% 19.52/19.71      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 19.52/19.71           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 19.52/19.71            sk_B) @ 
% 19.52/19.71           (k6_partfun1 @ sk_A)))
% 19.52/19.71         <= (~
% 19.52/19.71             ((r2_relset_1 @ sk_A @ sk_A @ 
% 19.52/19.71               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 19.52/19.71                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 19.52/19.71               (k6_partfun1 @ sk_A))))),
% 19.52/19.71      inference('sup-', [status(thm)], ['84', '85'])).
% 19.52/19.71  thf('87', plain,
% 19.52/19.71      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 19.52/19.71           (k6_partfun1 @ sk_A)))
% 19.52/19.71         <= (~
% 19.52/19.71             ((r2_relset_1 @ sk_A @ sk_A @ 
% 19.52/19.71               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 19.52/19.71                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 19.52/19.71               (k6_partfun1 @ sk_A))))),
% 19.52/19.71      inference('sup-', [status(thm)], ['83', '86'])).
% 19.52/19.71  thf('88', plain,
% 19.52/19.71      (![X0 : $i]:
% 19.52/19.71         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 19.52/19.71      inference('sup-', [status(thm)], ['70', '72'])).
% 19.52/19.71  thf('89', plain,
% 19.52/19.71      (((r2_relset_1 @ sk_A @ sk_A @ 
% 19.52/19.71         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 19.52/19.71          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 19.52/19.71         (k6_partfun1 @ sk_A)))),
% 19.52/19.71      inference('demod', [status(thm)], ['87', '88'])).
% 19.52/19.71  thf('90', plain,
% 19.52/19.71      (~
% 19.52/19.71       ((r2_relset_1 @ sk_A @ sk_A @ 
% 19.52/19.71         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 19.52/19.71          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 19.52/19.71         (k6_partfun1 @ sk_A))) | 
% 19.52/19.71       ~
% 19.52/19.71       ((r2_relset_1 @ sk_A @ sk_A @ 
% 19.52/19.71         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 19.52/19.71          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 19.52/19.71         (k6_partfun1 @ sk_A)))),
% 19.52/19.71      inference('split', [status(esa)], ['0'])).
% 19.52/19.71  thf('91', plain,
% 19.52/19.71      (~
% 19.52/19.71       ((r2_relset_1 @ sk_A @ sk_A @ 
% 19.52/19.71         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 19.52/19.71          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 19.52/19.71         (k6_partfun1 @ sk_A)))),
% 19.52/19.71      inference('sat_resolution*', [status(thm)], ['89', '90'])).
% 19.52/19.71  thf('92', plain,
% 19.52/19.71      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 19.52/19.71          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 19.52/19.71          (k6_partfun1 @ sk_A))),
% 19.52/19.71      inference('simpl_trail', [status(thm)], ['9', '91'])).
% 19.52/19.71  thf('93', plain,
% 19.52/19.71      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 19.52/19.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 19.52/19.71      inference('demod', [status(thm)], ['13', '14', '15', '16'])).
% 19.52/19.71  thf('94', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 19.52/19.71      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 19.52/19.71  thf('95', plain,
% 19.52/19.71      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 19.52/19.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 19.52/19.71      inference('demod', [status(thm)], ['93', '94'])).
% 19.52/19.71  thf('96', plain,
% 19.52/19.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 19.52/19.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.52/19.71  thf('97', plain,
% 19.52/19.71      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 19.52/19.71         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 19.52/19.71          | ~ (v1_funct_1 @ X43)
% 19.52/19.71          | ~ (v1_funct_1 @ X46)
% 19.52/19.71          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 19.52/19.71          | ((k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46)
% 19.52/19.71              = (k5_relat_1 @ X43 @ X46)))),
% 19.52/19.71      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 19.52/19.71  thf('98', plain,
% 19.52/19.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.52/19.71         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 19.52/19.71            = (k5_relat_1 @ sk_B @ X0))
% 19.52/19.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 19.52/19.71          | ~ (v1_funct_1 @ X0)
% 19.52/19.71          | ~ (v1_funct_1 @ sk_B))),
% 19.52/19.71      inference('sup-', [status(thm)], ['96', '97'])).
% 19.52/19.71  thf('99', plain, ((v1_funct_1 @ sk_B)),
% 19.52/19.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.52/19.71  thf('100', plain,
% 19.52/19.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.52/19.71         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 19.52/19.71            = (k5_relat_1 @ sk_B @ X0))
% 19.52/19.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 19.52/19.71          | ~ (v1_funct_1 @ X0))),
% 19.52/19.71      inference('demod', [status(thm)], ['98', '99'])).
% 19.52/19.71  thf('101', plain,
% 19.52/19.71      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 19.52/19.71        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 19.52/19.71            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 19.52/19.71      inference('sup-', [status(thm)], ['95', '100'])).
% 19.52/19.71  thf('102', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 19.52/19.71      inference('demod', [status(thm)], ['22', '23', '24', '25'])).
% 19.52/19.71  thf('103', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 19.52/19.71      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 19.52/19.71  thf('104', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 19.52/19.71      inference('demod', [status(thm)], ['102', '103'])).
% 19.52/19.71  thf('105', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 19.52/19.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.52/19.71  thf(d1_funct_2, axiom,
% 19.52/19.71    (![A:$i,B:$i,C:$i]:
% 19.52/19.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 19.52/19.71       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 19.52/19.71           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 19.52/19.71             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 19.52/19.71         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 19.52/19.71           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 19.52/19.71             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 19.52/19.71  thf(zf_stmt_1, axiom,
% 19.52/19.71    (![C:$i,B:$i,A:$i]:
% 19.52/19.71     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 19.52/19.71       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 19.52/19.71  thf('106', plain,
% 19.52/19.71      (![X31 : $i, X32 : $i, X33 : $i]:
% 19.52/19.71         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 19.52/19.71          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 19.52/19.71          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 19.52/19.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 19.52/19.71  thf('107', plain,
% 19.52/19.71      ((~ (zip_tseitin_1 @ sk_B @ sk_A @ sk_A)
% 19.52/19.71        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_A @ sk_B)))),
% 19.52/19.71      inference('sup-', [status(thm)], ['105', '106'])).
% 19.52/19.71  thf('108', plain,
% 19.52/19.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 19.52/19.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.52/19.71  thf(redefinition_k1_relset_1, axiom,
% 19.52/19.71    (![A:$i,B:$i,C:$i]:
% 19.52/19.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 19.52/19.71       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 19.52/19.71  thf('109', plain,
% 19.52/19.71      (![X19 : $i, X20 : $i, X21 : $i]:
% 19.52/19.71         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 19.52/19.71          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 19.52/19.71      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 19.52/19.71  thf('110', plain,
% 19.52/19.71      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 19.52/19.71      inference('sup-', [status(thm)], ['108', '109'])).
% 19.52/19.71  thf('111', plain,
% 19.52/19.71      ((~ (zip_tseitin_1 @ sk_B @ sk_A @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_B)))),
% 19.52/19.71      inference('demod', [status(thm)], ['107', '110'])).
% 19.52/19.71  thf('112', plain,
% 19.52/19.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 19.52/19.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.52/19.71  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 19.52/19.71  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 19.52/19.71  thf(zf_stmt_4, axiom,
% 19.52/19.71    (![B:$i,A:$i]:
% 19.52/19.71     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 19.52/19.71       ( zip_tseitin_0 @ B @ A ) ))).
% 19.52/19.71  thf(zf_stmt_5, axiom,
% 19.52/19.71    (![A:$i,B:$i,C:$i]:
% 19.52/19.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 19.52/19.71       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 19.52/19.71         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 19.52/19.71           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 19.52/19.71             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 19.52/19.71  thf('113', plain,
% 19.52/19.71      (![X34 : $i, X35 : $i, X36 : $i]:
% 19.52/19.71         (~ (zip_tseitin_0 @ X34 @ X35)
% 19.52/19.71          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 19.52/19.71          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 19.52/19.71      inference('cnf', [status(esa)], [zf_stmt_5])).
% 19.52/19.71  thf('114', plain,
% 19.52/19.71      (((zip_tseitin_1 @ sk_B @ sk_A @ sk_A) | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 19.52/19.71      inference('sup-', [status(thm)], ['112', '113'])).
% 19.52/19.71  thf('115', plain,
% 19.52/19.71      (![X29 : $i, X30 : $i]:
% 19.52/19.71         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 19.52/19.71      inference('cnf', [status(esa)], [zf_stmt_4])).
% 19.52/19.71  thf('116', plain,
% 19.52/19.71      (![X29 : $i, X30 : $i]:
% 19.52/19.71         ((zip_tseitin_0 @ X29 @ X30) | ((X30) != (k1_xboole_0)))),
% 19.52/19.71      inference('cnf', [status(esa)], [zf_stmt_4])).
% 19.52/19.71  thf('117', plain, (![X29 : $i]: (zip_tseitin_0 @ X29 @ k1_xboole_0)),
% 19.52/19.71      inference('simplify', [status(thm)], ['116'])).
% 19.52/19.71  thf('118', plain,
% 19.52/19.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.52/19.71         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 19.52/19.71      inference('sup+', [status(thm)], ['115', '117'])).
% 19.52/19.71  thf('119', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 19.52/19.71      inference('eq_fact', [status(thm)], ['118'])).
% 19.52/19.71  thf('120', plain, ((zip_tseitin_1 @ sk_B @ sk_A @ sk_A)),
% 19.52/19.71      inference('demod', [status(thm)], ['114', '119'])).
% 19.52/19.71  thf('121', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 19.52/19.71      inference('demod', [status(thm)], ['111', '120'])).
% 19.52/19.71  thf('122', plain,
% 19.52/19.71      (![X12 : $i]:
% 19.52/19.71         (~ (v2_funct_1 @ X12)
% 19.52/19.71          | ((k5_relat_1 @ X12 @ (k2_funct_1 @ X12))
% 19.52/19.71              = (k6_relat_1 @ (k1_relat_1 @ X12)))
% 19.52/19.71          | ~ (v1_funct_1 @ X12)
% 19.52/19.71          | ~ (v1_relat_1 @ X12))),
% 19.52/19.71      inference('cnf', [status(esa)], [t61_funct_1])).
% 19.52/19.71  thf('123', plain, (![X51 : $i]: ((k6_partfun1 @ X51) = (k6_relat_1 @ X51))),
% 19.52/19.71      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 19.52/19.71  thf('124', plain,
% 19.52/19.71      (![X12 : $i]:
% 19.52/19.71         (~ (v2_funct_1 @ X12)
% 19.52/19.71          | ((k5_relat_1 @ X12 @ (k2_funct_1 @ X12))
% 19.52/19.71              = (k6_partfun1 @ (k1_relat_1 @ X12)))
% 19.52/19.71          | ~ (v1_funct_1 @ X12)
% 19.52/19.71          | ~ (v1_relat_1 @ X12))),
% 19.52/19.71      inference('demod', [status(thm)], ['122', '123'])).
% 19.52/19.71  thf('125', plain,
% 19.52/19.71      (![X42 : $i]:
% 19.52/19.71         (m1_subset_1 @ (k6_partfun1 @ X42) @ 
% 19.52/19.71          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X42)))),
% 19.52/19.71      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 19.52/19.71  thf('126', plain,
% 19.52/19.71      (![X0 : $i]:
% 19.52/19.71         ((m1_subset_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ 
% 19.52/19.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 19.52/19.71          | ~ (v1_relat_1 @ X0)
% 19.52/19.71          | ~ (v1_funct_1 @ X0)
% 19.52/19.71          | ~ (v2_funct_1 @ X0))),
% 19.52/19.71      inference('sup+', [status(thm)], ['124', '125'])).
% 19.52/19.71  thf('127', plain,
% 19.52/19.71      (((m1_subset_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 19.52/19.71         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_relat_1 @ sk_B))))
% 19.52/19.71        | ~ (v2_funct_1 @ sk_B)
% 19.52/19.71        | ~ (v1_funct_1 @ sk_B)
% 19.52/19.71        | ~ (v1_relat_1 @ sk_B))),
% 19.52/19.71      inference('sup+', [status(thm)], ['121', '126'])).
% 19.52/19.71  thf('128', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 19.52/19.71      inference('demod', [status(thm)], ['111', '120'])).
% 19.52/19.71  thf('129', plain, ((v2_funct_1 @ sk_B)),
% 19.52/19.71      inference('demod', [status(thm)], ['57', '58', '59'])).
% 19.52/19.71  thf('130', plain, ((v1_funct_1 @ sk_B)),
% 19.52/19.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.52/19.71  thf('131', plain, ((v1_relat_1 @ sk_B)),
% 19.52/19.71      inference('sup-', [status(thm)], ['41', '42'])).
% 19.52/19.71  thf('132', plain,
% 19.52/19.71      ((m1_subset_1 @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ 
% 19.52/19.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 19.52/19.71      inference('demod', [status(thm)], ['127', '128', '129', '130', '131'])).
% 19.52/19.71  thf('133', plain,
% 19.52/19.71      (![X0 : $i, X1 : $i]:
% 19.52/19.71         (~ (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 19.52/19.71          | ((k6_partfun1 @ X0) = (X1))
% 19.52/19.71          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0))))),
% 19.52/19.71      inference('sup-', [status(thm)], ['64', '65'])).
% 19.52/19.71  thf('134', plain,
% 19.52/19.71      ((((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))
% 19.52/19.71        | ~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 19.52/19.71             (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 19.52/19.71      inference('sup-', [status(thm)], ['132', '133'])).
% 19.52/19.71  thf('135', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 19.52/19.71      inference('demod', [status(thm)], ['111', '120'])).
% 19.52/19.71  thf('136', plain,
% 19.52/19.71      (![X12 : $i]:
% 19.52/19.71         (~ (v2_funct_1 @ X12)
% 19.52/19.71          | ((k5_relat_1 @ X12 @ (k2_funct_1 @ X12))
% 19.52/19.71              = (k6_partfun1 @ (k1_relat_1 @ X12)))
% 19.52/19.71          | ~ (v1_funct_1 @ X12)
% 19.52/19.71          | ~ (v1_relat_1 @ X12))),
% 19.52/19.71      inference('demod', [status(thm)], ['122', '123'])).
% 19.52/19.71  thf('137', plain,
% 19.52/19.71      (![X0 : $i]:
% 19.52/19.71         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 19.52/19.71      inference('sup-', [status(thm)], ['70', '72'])).
% 19.52/19.71  thf('138', plain,
% 19.52/19.71      (![X0 : $i]:
% 19.52/19.71         ((r2_relset_1 @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0) @ 
% 19.52/19.71           (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 19.52/19.71           (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 19.52/19.71          | ~ (v1_relat_1 @ X0)
% 19.52/19.71          | ~ (v1_funct_1 @ X0)
% 19.52/19.71          | ~ (v2_funct_1 @ X0))),
% 19.52/19.71      inference('sup+', [status(thm)], ['136', '137'])).
% 19.52/19.71  thf('139', plain,
% 19.52/19.71      (((r2_relset_1 @ sk_A @ (k1_relat_1 @ sk_B) @ 
% 19.52/19.71         (k6_partfun1 @ (k1_relat_1 @ sk_B)) @ 
% 19.52/19.71         (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))
% 19.52/19.71        | ~ (v2_funct_1 @ sk_B)
% 19.52/19.71        | ~ (v1_funct_1 @ sk_B)
% 19.52/19.71        | ~ (v1_relat_1 @ sk_B))),
% 19.52/19.71      inference('sup+', [status(thm)], ['135', '138'])).
% 19.52/19.71  thf('140', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 19.52/19.71      inference('demod', [status(thm)], ['111', '120'])).
% 19.52/19.71  thf('141', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 19.52/19.71      inference('demod', [status(thm)], ['111', '120'])).
% 19.52/19.71  thf('142', plain, ((v2_funct_1 @ sk_B)),
% 19.52/19.71      inference('demod', [status(thm)], ['57', '58', '59'])).
% 19.52/19.71  thf('143', plain, ((v1_funct_1 @ sk_B)),
% 19.52/19.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.52/19.71  thf('144', plain, ((v1_relat_1 @ sk_B)),
% 19.52/19.71      inference('sup-', [status(thm)], ['41', '42'])).
% 19.52/19.71  thf('145', plain,
% 19.52/19.71      ((r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 19.52/19.71        (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 19.52/19.71      inference('demod', [status(thm)],
% 19.52/19.71                ['139', '140', '141', '142', '143', '144'])).
% 19.52/19.71  thf('146', plain,
% 19.52/19.71      (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 19.52/19.71      inference('demod', [status(thm)], ['134', '145'])).
% 19.52/19.71  thf('147', plain,
% 19.52/19.71      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 19.52/19.71         = (k6_partfun1 @ sk_A))),
% 19.52/19.71      inference('demod', [status(thm)], ['101', '104', '146'])).
% 19.52/19.71  thf('148', plain,
% 19.52/19.71      (![X0 : $i]:
% 19.52/19.71         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 19.52/19.71      inference('sup-', [status(thm)], ['70', '72'])).
% 19.52/19.71  thf('149', plain, ($false),
% 19.52/19.71      inference('demod', [status(thm)], ['92', '147', '148'])).
% 19.52/19.71  
% 19.52/19.71  % SZS output end Refutation
% 19.52/19.71  
% 19.52/19.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1sbeCAsZdy

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:05 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  184 (1551 expanded)
%              Number of leaves         :   34 ( 467 expanded)
%              Depth                    :   16
%              Number of atoms          : 1489 (40957 expanded)
%              Number of equality atoms :   95 ( 557 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
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

thf('2',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_funct_2 @ X22 @ X21 )
        = ( k2_funct_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) )
      | ~ ( v3_funct_2 @ X21 @ X22 @ X22 )
      | ~ ( v1_funct_2 @ X21 @ X22 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B )
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('8',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('9',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( X27
        = ( k2_funct_1 @ X30 ) )
      | ~ ( r2_relset_1 @ X29 @ X29 @ ( k1_partfun1 @ X29 @ X28 @ X28 @ X29 @ X30 @ X27 ) @ ( k6_partfun1 @ X29 ) )
      | ( X28 = k1_xboole_0 )
      | ( X29 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X30 )
      | ( ( k2_relset_1 @ X29 @ X28 @ X30 )
       != X28 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t36_funct_2])).

thf('12',plain,(
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
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
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
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
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
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('22',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_relset_1 @ X8 @ X9 @ X7 )
        = ( k2_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('23',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
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

thf('25',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( v3_funct_2 @ X14 @ X15 @ X16 )
      | ( v2_funct_2 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('26',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['26','27','28'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('30',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_funct_2 @ X18 @ X17 )
      | ( ( k2_relat_1 @ X18 )
        = X17 )
      | ~ ( v5_relat_1 @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('33',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('36',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v5_relat_1 @ X4 @ X6 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('37',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['31','34','37'])).

thf('39',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['23','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( v3_funct_2 @ X14 @ X15 @ X16 )
      | ( v2_funct_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('42',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ( sk_A != sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','19','20','39','45'])).

thf('47',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('49',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('51',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ( r2_relset_1 @ X11 @ X12 @ X10 @ X13 )
      | ( X10 != X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('52',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r2_relset_1 @ X11 @ X12 @ X13 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','53'])).

thf('55',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','53'])).

thf('56',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( v3_funct_2 @ X14 @ X15 @ X16 )
      | ( v2_funct_2 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('59',plain,
    ( ( v2_funct_2 @ sk_C @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v2_funct_2 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_funct_2 @ X18 @ X17 )
      | ( ( k2_relat_1 @ X18 )
        = X17 )
      | ~ ( v5_relat_1 @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('64',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v5_relat_1 @ sk_C @ sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('67',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v5_relat_1 @ X4 @ X6 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('70',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['64','67','70'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('72',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('73',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['65','66'])).

thf('75',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','53'])).

thf('77',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['31','34','37'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('81',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['32','33'])).

thf('83',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','53'])).

thf('85',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
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

thf('88',plain,(
    ! [X19: $i,X20: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) )
      | ~ ( v3_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('89',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['89','90','91','92'])).

thf('94',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('95',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( v3_funct_2 @ X14 @ X15 @ X16 )
      | ( v2_funct_2 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('97',plain,
    ( ( v2_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X19 @ X20 ) @ X19 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) )
      | ~ ( v3_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('100',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('105',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['100','101','102','103','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) )
      | ~ ( v3_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('108',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['108','109','110','111'])).

thf('113',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('114',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    v2_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['97','105','114'])).

thf('116',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_funct_2 @ X18 @ X17 )
      | ( ( k2_relat_1 @ X18 )
        = X17 )
      | ~ ( v5_relat_1 @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('117',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['89','90','91','92'])).

thf('119',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('120',plain,(
    v1_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('122',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['89','90','91','92'])).

thf('124',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v5_relat_1 @ X4 @ X6 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('125',plain,(
    v5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('127',plain,(
    v5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['117','122','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('130',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k2_funct_1 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('132',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_funct_1 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','53'])).

thf('134',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_funct_1 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( k2_funct_1 @ sk_B )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['85'])).

thf('137',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','78','86','137'])).

thf('139',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r2_relset_1 @ X11 @ X12 @ X13 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('141',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','53'])).

thf('143',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','53'])).

thf('144',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('145',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['85'])).

thf('146',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['85'])).

thf('147',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['144','145','146'])).

thf('148',plain,(
    $false ),
    inference(demod,[status(thm)],['138','147'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1sbeCAsZdy
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:48:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.38/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.59  % Solved by: fo/fo7.sh
% 0.38/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.59  % done 355 iterations in 0.129s
% 0.38/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.59  % SZS output start Refutation
% 0.38/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.59  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.38/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.59  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.38/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.59  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.38/0.59  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.38/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.59  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.38/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.59  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.38/0.59  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.38/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.59  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.38/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.59  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.38/0.59  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.38/0.59  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.38/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.59  thf(t87_funct_2, conjecture,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.38/0.59         ( v3_funct_2 @ B @ A @ A ) & 
% 0.38/0.59         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.38/0.59       ( ![C:$i]:
% 0.38/0.59         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.38/0.59             ( v3_funct_2 @ C @ A @ A ) & 
% 0.38/0.59             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.38/0.59           ( ( r2_relset_1 @
% 0.38/0.59               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.38/0.59               ( k6_partfun1 @ A ) ) =>
% 0.38/0.59             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 0.38/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.59    (~( ![A:$i,B:$i]:
% 0.38/0.59        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.38/0.59            ( v3_funct_2 @ B @ A @ A ) & 
% 0.38/0.59            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.38/0.59          ( ![C:$i]:
% 0.38/0.59            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.38/0.59                ( v3_funct_2 @ C @ A @ A ) & 
% 0.38/0.59                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.38/0.59              ( ( r2_relset_1 @
% 0.38/0.59                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.38/0.59                  ( k6_partfun1 @ A ) ) =>
% 0.38/0.59                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 0.38/0.59    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 0.38/0.59  thf('0', plain,
% 0.38/0.59      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('1', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(redefinition_k2_funct_2, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.38/0.59         ( v3_funct_2 @ B @ A @ A ) & 
% 0.38/0.59         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.38/0.59       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.38/0.59  thf('2', plain,
% 0.38/0.59      (![X21 : $i, X22 : $i]:
% 0.38/0.59         (((k2_funct_2 @ X22 @ X21) = (k2_funct_1 @ X21))
% 0.38/0.59          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))
% 0.38/0.59          | ~ (v3_funct_2 @ X21 @ X22 @ X22)
% 0.38/0.59          | ~ (v1_funct_2 @ X21 @ X22 @ X22)
% 0.38/0.59          | ~ (v1_funct_1 @ X21))),
% 0.38/0.59      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.38/0.59  thf('3', plain,
% 0.38/0.59      ((~ (v1_funct_1 @ sk_B)
% 0.38/0.59        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.38/0.59        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.38/0.59        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.59  thf('4', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('5', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('6', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('7', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.38/0.59      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.38/0.59  thf('8', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.38/0.59      inference('demod', [status(thm)], ['0', '7'])).
% 0.38/0.59  thf('9', plain,
% 0.38/0.59      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.38/0.59        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.38/0.59        (k6_partfun1 @ sk_A))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('10', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(t36_funct_2, axiom,
% 0.38/0.59    (![A:$i,B:$i,C:$i]:
% 0.38/0.59     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.59       ( ![D:$i]:
% 0.38/0.59         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.38/0.59             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.38/0.59           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.38/0.59               ( r2_relset_1 @
% 0.38/0.59                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.38/0.59                 ( k6_partfun1 @ A ) ) & 
% 0.38/0.59               ( v2_funct_1 @ C ) ) =>
% 0.38/0.59             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.38/0.59               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.38/0.59  thf('11', plain,
% 0.38/0.59      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.38/0.59         (~ (v1_funct_1 @ X27)
% 0.38/0.59          | ~ (v1_funct_2 @ X27 @ X28 @ X29)
% 0.38/0.59          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.38/0.59          | ((X27) = (k2_funct_1 @ X30))
% 0.38/0.59          | ~ (r2_relset_1 @ X29 @ X29 @ 
% 0.38/0.59               (k1_partfun1 @ X29 @ X28 @ X28 @ X29 @ X30 @ X27) @ 
% 0.38/0.59               (k6_partfun1 @ X29))
% 0.38/0.59          | ((X28) = (k1_xboole_0))
% 0.38/0.59          | ((X29) = (k1_xboole_0))
% 0.38/0.59          | ~ (v2_funct_1 @ X30)
% 0.38/0.59          | ((k2_relset_1 @ X29 @ X28 @ X30) != (X28))
% 0.38/0.59          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 0.38/0.59          | ~ (v1_funct_2 @ X30 @ X29 @ X28)
% 0.38/0.59          | ~ (v1_funct_1 @ X30))),
% 0.38/0.59      inference('cnf', [status(esa)], [t36_funct_2])).
% 0.38/0.59  thf('12', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.38/0.59          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.38/0.59          | ~ (v2_funct_1 @ X0)
% 0.38/0.59          | ((sk_A) = (k1_xboole_0))
% 0.38/0.59          | ((sk_A) = (k1_xboole_0))
% 0.38/0.59          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.38/0.59               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.38/0.59               (k6_partfun1 @ sk_A))
% 0.38/0.59          | ((sk_C) = (k2_funct_1 @ X0))
% 0.38/0.59          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.38/0.59          | ~ (v1_funct_1 @ sk_C))),
% 0.38/0.59      inference('sup-', [status(thm)], ['10', '11'])).
% 0.38/0.59  thf('13', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('14', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('15', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (~ (v1_funct_1 @ X0)
% 0.38/0.59          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.38/0.59          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.38/0.59          | ~ (v2_funct_1 @ X0)
% 0.38/0.59          | ((sk_A) = (k1_xboole_0))
% 0.38/0.59          | ((sk_A) = (k1_xboole_0))
% 0.38/0.59          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.38/0.59               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.38/0.59               (k6_partfun1 @ sk_A))
% 0.38/0.59          | ((sk_C) = (k2_funct_1 @ X0)))),
% 0.38/0.59      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.38/0.59  thf('16', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (((sk_C) = (k2_funct_1 @ X0))
% 0.38/0.59          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.38/0.59               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.38/0.59               (k6_partfun1 @ sk_A))
% 0.38/0.59          | ((sk_A) = (k1_xboole_0))
% 0.38/0.59          | ~ (v2_funct_1 @ X0)
% 0.38/0.59          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.38/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.38/0.59          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.38/0.59          | ~ (v1_funct_1 @ X0))),
% 0.38/0.59      inference('simplify', [status(thm)], ['15'])).
% 0.38/0.59  thf('17', plain,
% 0.38/0.59      ((~ (v1_funct_1 @ sk_B)
% 0.38/0.59        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.38/0.59        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.38/0.59        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 0.38/0.59        | ~ (v2_funct_1 @ sk_B)
% 0.38/0.59        | ((sk_A) = (k1_xboole_0))
% 0.38/0.59        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['9', '16'])).
% 0.38/0.59  thf('18', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('19', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('20', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('21', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(redefinition_k2_relset_1, axiom,
% 0.38/0.59    (![A:$i,B:$i,C:$i]:
% 0.38/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.59       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.38/0.59  thf('22', plain,
% 0.38/0.59      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.38/0.59         (((k2_relset_1 @ X8 @ X9 @ X7) = (k2_relat_1 @ X7))
% 0.38/0.59          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.38/0.59      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.38/0.59  thf('23', plain,
% 0.38/0.59      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 0.38/0.59      inference('sup-', [status(thm)], ['21', '22'])).
% 0.38/0.59  thf('24', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(cc2_funct_2, axiom,
% 0.38/0.59    (![A:$i,B:$i,C:$i]:
% 0.38/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.59       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.38/0.59         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.38/0.59  thf('25', plain,
% 0.38/0.59      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.38/0.59         (~ (v1_funct_1 @ X14)
% 0.38/0.59          | ~ (v3_funct_2 @ X14 @ X15 @ X16)
% 0.38/0.59          | (v2_funct_2 @ X14 @ X16)
% 0.38/0.59          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.38/0.59      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.38/0.59  thf('26', plain,
% 0.38/0.59      (((v2_funct_2 @ sk_B @ sk_A)
% 0.38/0.59        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.38/0.59        | ~ (v1_funct_1 @ sk_B))),
% 0.38/0.59      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.59  thf('27', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('28', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('29', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 0.38/0.59      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.38/0.59  thf(d3_funct_2, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.38/0.59       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.38/0.59  thf('30', plain,
% 0.38/0.59      (![X17 : $i, X18 : $i]:
% 0.38/0.59         (~ (v2_funct_2 @ X18 @ X17)
% 0.38/0.59          | ((k2_relat_1 @ X18) = (X17))
% 0.38/0.59          | ~ (v5_relat_1 @ X18 @ X17)
% 0.38/0.59          | ~ (v1_relat_1 @ X18))),
% 0.38/0.59      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.38/0.59  thf('31', plain,
% 0.38/0.59      ((~ (v1_relat_1 @ sk_B)
% 0.38/0.59        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 0.38/0.59        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['29', '30'])).
% 0.38/0.59  thf('32', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(cc1_relset_1, axiom,
% 0.38/0.59    (![A:$i,B:$i,C:$i]:
% 0.38/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.59       ( v1_relat_1 @ C ) ))).
% 0.38/0.59  thf('33', plain,
% 0.38/0.59      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.59         ((v1_relat_1 @ X1)
% 0.38/0.59          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3))))),
% 0.38/0.59      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.38/0.59  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.59      inference('sup-', [status(thm)], ['32', '33'])).
% 0.38/0.59  thf('35', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(cc2_relset_1, axiom,
% 0.38/0.59    (![A:$i,B:$i,C:$i]:
% 0.38/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.59       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.38/0.59  thf('36', plain,
% 0.38/0.59      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.38/0.59         ((v5_relat_1 @ X4 @ X6)
% 0.38/0.59          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.38/0.59      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.38/0.59  thf('37', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 0.38/0.59      inference('sup-', [status(thm)], ['35', '36'])).
% 0.38/0.59  thf('38', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.38/0.59      inference('demod', [status(thm)], ['31', '34', '37'])).
% 0.38/0.59  thf('39', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 0.38/0.59      inference('demod', [status(thm)], ['23', '38'])).
% 0.38/0.59  thf('40', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('41', plain,
% 0.38/0.59      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.38/0.59         (~ (v1_funct_1 @ X14)
% 0.38/0.59          | ~ (v3_funct_2 @ X14 @ X15 @ X16)
% 0.38/0.59          | (v2_funct_1 @ X14)
% 0.38/0.59          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.38/0.59      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.38/0.59  thf('42', plain,
% 0.38/0.59      (((v2_funct_1 @ sk_B)
% 0.38/0.59        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.38/0.59        | ~ (v1_funct_1 @ sk_B))),
% 0.38/0.59      inference('sup-', [status(thm)], ['40', '41'])).
% 0.38/0.59  thf('43', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('44', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('45', plain, ((v2_funct_1 @ sk_B)),
% 0.38/0.59      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.38/0.59  thf('46', plain,
% 0.38/0.59      ((((sk_A) != (sk_A))
% 0.38/0.59        | ((sk_A) = (k1_xboole_0))
% 0.38/0.59        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 0.38/0.59      inference('demod', [status(thm)], ['17', '18', '19', '20', '39', '45'])).
% 0.38/0.59  thf('47', plain,
% 0.38/0.59      ((((sk_C) = (k2_funct_1 @ sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 0.38/0.59      inference('simplify', [status(thm)], ['46'])).
% 0.38/0.59  thf('48', plain,
% 0.38/0.59      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.38/0.59      inference('demod', [status(thm)], ['0', '7'])).
% 0.38/0.59  thf('49', plain,
% 0.38/0.59      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['47', '48'])).
% 0.38/0.59  thf('50', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(redefinition_r2_relset_1, axiom,
% 0.38/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.59     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.38/0.59         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.59       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.38/0.59  thf('51', plain,
% 0.38/0.59      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.38/0.59         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.38/0.59          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.38/0.59          | (r2_relset_1 @ X11 @ X12 @ X10 @ X13)
% 0.38/0.59          | ((X10) != (X13)))),
% 0.38/0.59      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.38/0.59  thf('52', plain,
% 0.38/0.59      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.38/0.59         ((r2_relset_1 @ X11 @ X12 @ X13 @ X13)
% 0.38/0.59          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.38/0.59      inference('simplify', [status(thm)], ['51'])).
% 0.38/0.59  thf('53', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 0.38/0.59      inference('sup-', [status(thm)], ['50', '52'])).
% 0.38/0.59  thf('54', plain, (((sk_A) = (k1_xboole_0))),
% 0.38/0.59      inference('demod', [status(thm)], ['49', '53'])).
% 0.38/0.59  thf('55', plain, (((sk_A) = (k1_xboole_0))),
% 0.38/0.59      inference('demod', [status(thm)], ['49', '53'])).
% 0.38/0.59  thf('56', plain,
% 0.38/0.59      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.38/0.59      inference('demod', [status(thm)], ['8', '54', '55'])).
% 0.38/0.59  thf('57', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('58', plain,
% 0.38/0.59      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.38/0.59         (~ (v1_funct_1 @ X14)
% 0.38/0.59          | ~ (v3_funct_2 @ X14 @ X15 @ X16)
% 0.38/0.59          | (v2_funct_2 @ X14 @ X16)
% 0.38/0.59          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.38/0.59      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.38/0.59  thf('59', plain,
% 0.38/0.59      (((v2_funct_2 @ sk_C @ sk_A)
% 0.38/0.59        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.38/0.59        | ~ (v1_funct_1 @ sk_C))),
% 0.38/0.59      inference('sup-', [status(thm)], ['57', '58'])).
% 0.38/0.59  thf('60', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('62', plain, ((v2_funct_2 @ sk_C @ sk_A)),
% 0.38/0.59      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.38/0.59  thf('63', plain,
% 0.38/0.59      (![X17 : $i, X18 : $i]:
% 0.38/0.59         (~ (v2_funct_2 @ X18 @ X17)
% 0.38/0.59          | ((k2_relat_1 @ X18) = (X17))
% 0.38/0.59          | ~ (v5_relat_1 @ X18 @ X17)
% 0.38/0.59          | ~ (v1_relat_1 @ X18))),
% 0.38/0.59      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.38/0.59  thf('64', plain,
% 0.38/0.59      ((~ (v1_relat_1 @ sk_C)
% 0.38/0.59        | ~ (v5_relat_1 @ sk_C @ sk_A)
% 0.38/0.59        | ((k2_relat_1 @ sk_C) = (sk_A)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['62', '63'])).
% 0.38/0.59  thf('65', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('66', plain,
% 0.38/0.59      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.59         ((v1_relat_1 @ X1)
% 0.38/0.59          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3))))),
% 0.38/0.59      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.38/0.59  thf('67', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.59      inference('sup-', [status(thm)], ['65', '66'])).
% 0.38/0.59  thf('68', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('69', plain,
% 0.38/0.59      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.38/0.59         ((v5_relat_1 @ X4 @ X6)
% 0.38/0.59          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.38/0.59      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.38/0.59  thf('70', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.38/0.59      inference('sup-', [status(thm)], ['68', '69'])).
% 0.38/0.59  thf('71', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.38/0.59      inference('demod', [status(thm)], ['64', '67', '70'])).
% 0.38/0.59  thf(t64_relat_1, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( v1_relat_1 @ A ) =>
% 0.38/0.59       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.38/0.59           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.59         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.38/0.59  thf('72', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.38/0.59          | ((X0) = (k1_xboole_0))
% 0.38/0.59          | ~ (v1_relat_1 @ X0))),
% 0.38/0.59      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.38/0.59  thf('73', plain,
% 0.38/0.59      ((((sk_A) != (k1_xboole_0))
% 0.38/0.59        | ~ (v1_relat_1 @ sk_C)
% 0.38/0.59        | ((sk_C) = (k1_xboole_0)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['71', '72'])).
% 0.38/0.59  thf('74', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.59      inference('sup-', [status(thm)], ['65', '66'])).
% 0.38/0.59  thf('75', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.38/0.59      inference('demod', [status(thm)], ['73', '74'])).
% 0.38/0.59  thf('76', plain, (((sk_A) = (k1_xboole_0))),
% 0.38/0.59      inference('demod', [status(thm)], ['49', '53'])).
% 0.38/0.59  thf('77', plain,
% 0.38/0.59      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.38/0.59      inference('demod', [status(thm)], ['75', '76'])).
% 0.38/0.59  thf('78', plain, (((sk_C) = (k1_xboole_0))),
% 0.38/0.59      inference('simplify', [status(thm)], ['77'])).
% 0.38/0.59  thf('79', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.38/0.59      inference('demod', [status(thm)], ['31', '34', '37'])).
% 0.38/0.59  thf('80', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.38/0.59          | ((X0) = (k1_xboole_0))
% 0.38/0.59          | ~ (v1_relat_1 @ X0))),
% 0.38/0.59      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.38/0.59  thf('81', plain,
% 0.38/0.59      ((((sk_A) != (k1_xboole_0))
% 0.38/0.59        | ~ (v1_relat_1 @ sk_B)
% 0.38/0.59        | ((sk_B) = (k1_xboole_0)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['79', '80'])).
% 0.38/0.59  thf('82', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.59      inference('sup-', [status(thm)], ['32', '33'])).
% 0.38/0.59  thf('83', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.38/0.59      inference('demod', [status(thm)], ['81', '82'])).
% 0.38/0.59  thf('84', plain, (((sk_A) = (k1_xboole_0))),
% 0.38/0.59      inference('demod', [status(thm)], ['49', '53'])).
% 0.38/0.59  thf('85', plain,
% 0.38/0.59      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.38/0.59      inference('demod', [status(thm)], ['83', '84'])).
% 0.38/0.59  thf('86', plain, (((sk_B) = (k1_xboole_0))),
% 0.38/0.59      inference('simplify', [status(thm)], ['85'])).
% 0.38/0.59  thf('87', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(dt_k2_funct_2, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.38/0.59         ( v3_funct_2 @ B @ A @ A ) & 
% 0.38/0.59         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.38/0.59       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 0.38/0.59         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.38/0.59         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.38/0.59         ( m1_subset_1 @
% 0.38/0.59           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 0.38/0.59  thf('88', plain,
% 0.38/0.59      (![X19 : $i, X20 : $i]:
% 0.38/0.59         ((m1_subset_1 @ (k2_funct_2 @ X19 @ X20) @ 
% 0.38/0.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))
% 0.38/0.59          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))
% 0.38/0.59          | ~ (v3_funct_2 @ X20 @ X19 @ X19)
% 0.38/0.59          | ~ (v1_funct_2 @ X20 @ X19 @ X19)
% 0.38/0.59          | ~ (v1_funct_1 @ X20))),
% 0.38/0.59      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.38/0.59  thf('89', plain,
% 0.38/0.59      ((~ (v1_funct_1 @ sk_B)
% 0.38/0.59        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.38/0.59        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.38/0.59        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.38/0.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.38/0.59      inference('sup-', [status(thm)], ['87', '88'])).
% 0.38/0.59  thf('90', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('91', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('92', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('93', plain,
% 0.38/0.59      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.38/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.59      inference('demod', [status(thm)], ['89', '90', '91', '92'])).
% 0.38/0.59  thf('94', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.38/0.59      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.38/0.59  thf('95', plain,
% 0.38/0.59      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.38/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.59      inference('demod', [status(thm)], ['93', '94'])).
% 0.38/0.59  thf('96', plain,
% 0.38/0.59      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.38/0.59         (~ (v1_funct_1 @ X14)
% 0.38/0.59          | ~ (v3_funct_2 @ X14 @ X15 @ X16)
% 0.38/0.59          | (v2_funct_2 @ X14 @ X16)
% 0.38/0.59          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.38/0.59      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.38/0.59  thf('97', plain,
% 0.38/0.59      (((v2_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A)
% 0.38/0.59        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.38/0.59        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['95', '96'])).
% 0.38/0.59  thf('98', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('99', plain,
% 0.38/0.59      (![X19 : $i, X20 : $i]:
% 0.38/0.59         ((v3_funct_2 @ (k2_funct_2 @ X19 @ X20) @ X19 @ X19)
% 0.38/0.59          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))
% 0.38/0.59          | ~ (v3_funct_2 @ X20 @ X19 @ X19)
% 0.38/0.59          | ~ (v1_funct_2 @ X20 @ X19 @ X19)
% 0.38/0.59          | ~ (v1_funct_1 @ X20))),
% 0.38/0.59      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.38/0.59  thf('100', plain,
% 0.38/0.59      ((~ (v1_funct_1 @ sk_B)
% 0.38/0.59        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.38/0.59        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.38/0.59        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['98', '99'])).
% 0.38/0.59  thf('101', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('102', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('103', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('104', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.38/0.59      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.38/0.59  thf('105', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.38/0.59      inference('demod', [status(thm)], ['100', '101', '102', '103', '104'])).
% 0.38/0.59  thf('106', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('107', plain,
% 0.38/0.59      (![X19 : $i, X20 : $i]:
% 0.38/0.59         ((v1_funct_1 @ (k2_funct_2 @ X19 @ X20))
% 0.38/0.59          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))
% 0.38/0.59          | ~ (v3_funct_2 @ X20 @ X19 @ X19)
% 0.38/0.59          | ~ (v1_funct_2 @ X20 @ X19 @ X19)
% 0.38/0.59          | ~ (v1_funct_1 @ X20))),
% 0.38/0.59      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.38/0.59  thf('108', plain,
% 0.38/0.59      ((~ (v1_funct_1 @ sk_B)
% 0.38/0.59        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.38/0.59        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.38/0.59        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['106', '107'])).
% 0.38/0.59  thf('109', plain, ((v1_funct_1 @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('110', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('111', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('112', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.38/0.59      inference('demod', [status(thm)], ['108', '109', '110', '111'])).
% 0.38/0.59  thf('113', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.38/0.59      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.38/0.59  thf('114', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.38/0.59      inference('demod', [status(thm)], ['112', '113'])).
% 0.38/0.59  thf('115', plain, ((v2_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A)),
% 0.38/0.59      inference('demod', [status(thm)], ['97', '105', '114'])).
% 0.38/0.59  thf('116', plain,
% 0.38/0.59      (![X17 : $i, X18 : $i]:
% 0.38/0.59         (~ (v2_funct_2 @ X18 @ X17)
% 0.38/0.59          | ((k2_relat_1 @ X18) = (X17))
% 0.38/0.59          | ~ (v5_relat_1 @ X18 @ X17)
% 0.38/0.59          | ~ (v1_relat_1 @ X18))),
% 0.38/0.59      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.38/0.59  thf('117', plain,
% 0.38/0.59      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.38/0.59        | ~ (v5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)
% 0.38/0.59        | ((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['115', '116'])).
% 0.38/0.59  thf('118', plain,
% 0.38/0.59      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.38/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.59      inference('demod', [status(thm)], ['89', '90', '91', '92'])).
% 0.38/0.59  thf('119', plain,
% 0.38/0.59      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.59         ((v1_relat_1 @ X1)
% 0.38/0.59          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3))))),
% 0.38/0.59      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.38/0.59  thf('120', plain, ((v1_relat_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.38/0.59      inference('sup-', [status(thm)], ['118', '119'])).
% 0.38/0.59  thf('121', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.38/0.59      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.38/0.59  thf('122', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 0.38/0.59      inference('demod', [status(thm)], ['120', '121'])).
% 0.38/0.59  thf('123', plain,
% 0.38/0.59      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.38/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.59      inference('demod', [status(thm)], ['89', '90', '91', '92'])).
% 0.38/0.59  thf('124', plain,
% 0.38/0.59      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.38/0.59         ((v5_relat_1 @ X4 @ X6)
% 0.38/0.59          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.38/0.59      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.38/0.59  thf('125', plain, ((v5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A)),
% 0.38/0.59      inference('sup-', [status(thm)], ['123', '124'])).
% 0.38/0.59  thf('126', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.38/0.59      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.38/0.59  thf('127', plain, ((v5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)),
% 0.38/0.59      inference('demod', [status(thm)], ['125', '126'])).
% 0.38/0.59  thf('128', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 0.38/0.59      inference('demod', [status(thm)], ['117', '122', '127'])).
% 0.38/0.59  thf('129', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.38/0.59          | ((X0) = (k1_xboole_0))
% 0.38/0.59          | ~ (v1_relat_1 @ X0))),
% 0.38/0.59      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.38/0.59  thf('130', plain,
% 0.38/0.59      ((((sk_A) != (k1_xboole_0))
% 0.38/0.59        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.38/0.59        | ((k2_funct_1 @ sk_B) = (k1_xboole_0)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['128', '129'])).
% 0.38/0.59  thf('131', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 0.38/0.59      inference('demod', [status(thm)], ['120', '121'])).
% 0.38/0.59  thf('132', plain,
% 0.38/0.59      ((((sk_A) != (k1_xboole_0)) | ((k2_funct_1 @ sk_B) = (k1_xboole_0)))),
% 0.38/0.59      inference('demod', [status(thm)], ['130', '131'])).
% 0.38/0.59  thf('133', plain, (((sk_A) = (k1_xboole_0))),
% 0.38/0.59      inference('demod', [status(thm)], ['49', '53'])).
% 0.38/0.59  thf('134', plain,
% 0.38/0.59      ((((k1_xboole_0) != (k1_xboole_0))
% 0.38/0.59        | ((k2_funct_1 @ sk_B) = (k1_xboole_0)))),
% 0.38/0.59      inference('demod', [status(thm)], ['132', '133'])).
% 0.38/0.59  thf('135', plain, (((k2_funct_1 @ sk_B) = (k1_xboole_0))),
% 0.38/0.59      inference('simplify', [status(thm)], ['134'])).
% 0.38/0.59  thf('136', plain, (((sk_B) = (k1_xboole_0))),
% 0.38/0.59      inference('simplify', [status(thm)], ['85'])).
% 0.38/0.59  thf('137', plain, (((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.59      inference('demod', [status(thm)], ['135', '136'])).
% 0.38/0.59  thf('138', plain,
% 0.38/0.59      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.38/0.59      inference('demod', [status(thm)], ['56', '78', '86', '137'])).
% 0.38/0.59  thf('139', plain,
% 0.38/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('140', plain,
% 0.38/0.59      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.38/0.59         ((r2_relset_1 @ X11 @ X12 @ X13 @ X13)
% 0.38/0.59          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.38/0.59      inference('simplify', [status(thm)], ['51'])).
% 0.38/0.59  thf('141', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 0.38/0.59      inference('sup-', [status(thm)], ['139', '140'])).
% 0.38/0.59  thf('142', plain, (((sk_A) = (k1_xboole_0))),
% 0.38/0.59      inference('demod', [status(thm)], ['49', '53'])).
% 0.38/0.59  thf('143', plain, (((sk_A) = (k1_xboole_0))),
% 0.38/0.59      inference('demod', [status(thm)], ['49', '53'])).
% 0.38/0.59  thf('144', plain, ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_B)),
% 0.38/0.59      inference('demod', [status(thm)], ['141', '142', '143'])).
% 0.38/0.59  thf('145', plain, (((sk_B) = (k1_xboole_0))),
% 0.38/0.59      inference('simplify', [status(thm)], ['85'])).
% 0.38/0.59  thf('146', plain, (((sk_B) = (k1_xboole_0))),
% 0.38/0.59      inference('simplify', [status(thm)], ['85'])).
% 0.38/0.59  thf('147', plain,
% 0.38/0.59      ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.38/0.59      inference('demod', [status(thm)], ['144', '145', '146'])).
% 0.38/0.59  thf('148', plain, ($false), inference('demod', [status(thm)], ['138', '147'])).
% 0.38/0.59  
% 0.38/0.59  % SZS output end Refutation
% 0.38/0.59  
% 0.38/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

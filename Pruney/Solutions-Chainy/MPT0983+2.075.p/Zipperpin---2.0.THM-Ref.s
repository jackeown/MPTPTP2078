%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ff6QMX6cnG

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:13 EST 2020

% Result     : Theorem 5.85s
% Output     : Refutation 5.85s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 479 expanded)
%              Number of leaves         :   42 ( 157 expanded)
%              Depth                    :   14
%              Number of atoms          : 1101 (10133 expanded)
%              Number of equality atoms :   47 ( 120 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

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
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
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

thf('4',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( r2_relset_1 @ X37 @ X37 @ ( k1_partfun1 @ X37 @ X38 @ X38 @ X37 @ X36 @ X39 ) @ ( k6_partfun1 @ X37 ) )
      | ( ( k2_relset_1 @ X38 @ X37 @ X39 )
        = X37 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X38 @ X37 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,
    ( ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('12',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
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
    ! [X27: $i,X28: $i] :
      ( ( ( k2_relat_1 @ X28 )
       != X27 )
      | ( v2_funct_2 @ X28 @ X27 )
      | ~ ( v5_relat_1 @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('18',plain,(
    ! [X28: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ~ ( v5_relat_1 @ X28 @ ( k2_relat_1 @ X28 ) )
      | ( v2_funct_2 @ X28 @ ( k2_relat_1 @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v5_relat_1 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('22',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['9','12','13','14','15'])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('25',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('26',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['19','22','23','26'])).

thf('28',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('34',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('41',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('48',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( X22 = X25 )
      | ~ ( r2_relset_1 @ X23 @ X24 @ X22 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','49'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('51',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('52',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('53',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['50','53'])).

thf('55',plain,(
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

thf('56',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X43 @ X41 @ X41 @ X42 @ X44 @ X40 ) )
      | ( v2_funct_1 @ X44 )
      | ( X42 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X41 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X43 @ X41 )
      | ~ ( v1_funct_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['54','60'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('62',plain,(
    ! [X12: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('63',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('64',plain,(
    ! [X12: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X12 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

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
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','64','65','66','67'])).

thf('69',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','31'])).

thf('70',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['68','69'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('71',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('72',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['71'])).

thf(rc2_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v1_xboole_0 @ B )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('73',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( sk_B @ X7 ) @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('74',plain,(
    ! [X7: $i] :
      ( v1_xboole_0 @ ( sk_B @ X7 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('75',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( sk_B @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('79',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['68','69'])).

thf('81',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('82',plain,(
    k1_xboole_0 = sk_C ),
    inference(demod,[status(thm)],['37','70','72','79','80','81'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('83',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('84',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('85',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X12: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X12 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('87',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    $false ),
    inference(demod,[status(thm)],['32','82','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ff6QMX6cnG
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:22:08 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 5.85/6.10  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.85/6.10  % Solved by: fo/fo7.sh
% 5.85/6.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.85/6.10  % done 7871 iterations in 5.631s
% 5.85/6.10  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.85/6.10  % SZS output start Refutation
% 5.85/6.10  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 5.85/6.10  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 5.85/6.10  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.85/6.10  thf(sk_A_type, type, sk_A: $i).
% 5.85/6.10  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 5.85/6.10  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 5.85/6.10  thf(sk_B_1_type, type, sk_B_1: $i).
% 5.85/6.10  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 5.85/6.10  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 5.85/6.10  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 5.85/6.10  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.85/6.10  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 5.85/6.10  thf(sk_D_type, type, sk_D: $i).
% 5.85/6.10  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.85/6.10  thf(sk_C_type, type, sk_C: $i).
% 5.85/6.10  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 5.85/6.10  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 5.85/6.10  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 5.85/6.10  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.85/6.10  thf(sk_B_type, type, sk_B: $i > $i).
% 5.85/6.10  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.85/6.10  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 5.85/6.10  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.85/6.10  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 5.85/6.10  thf(t29_funct_2, conjecture,
% 5.85/6.10    (![A:$i,B:$i,C:$i]:
% 5.85/6.10     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.85/6.10         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.85/6.10       ( ![D:$i]:
% 5.85/6.10         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 5.85/6.10             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 5.85/6.10           ( ( r2_relset_1 @
% 5.85/6.10               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 5.85/6.10               ( k6_partfun1 @ A ) ) =>
% 5.85/6.10             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 5.85/6.10  thf(zf_stmt_0, negated_conjecture,
% 5.85/6.10    (~( ![A:$i,B:$i,C:$i]:
% 5.85/6.10        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.85/6.10            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.85/6.10          ( ![D:$i]:
% 5.85/6.10            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 5.85/6.10                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 5.85/6.10              ( ( r2_relset_1 @
% 5.85/6.10                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 5.85/6.10                  ( k6_partfun1 @ A ) ) =>
% 5.85/6.10                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 5.85/6.10    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 5.85/6.10  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 5.85/6.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.85/6.10  thf('1', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 5.85/6.10      inference('split', [status(esa)], ['0'])).
% 5.85/6.10  thf('2', plain,
% 5.85/6.10      ((r2_relset_1 @ sk_A @ sk_A @ 
% 5.85/6.10        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 5.85/6.10        (k6_partfun1 @ sk_A))),
% 5.85/6.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.85/6.10  thf('3', plain,
% 5.85/6.10      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.85/6.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.85/6.10  thf(t24_funct_2, axiom,
% 5.85/6.10    (![A:$i,B:$i,C:$i]:
% 5.85/6.10     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.85/6.10         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.85/6.10       ( ![D:$i]:
% 5.85/6.10         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 5.85/6.10             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 5.85/6.10           ( ( r2_relset_1 @
% 5.85/6.10               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 5.85/6.10               ( k6_partfun1 @ B ) ) =>
% 5.85/6.10             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 5.85/6.10  thf('4', plain,
% 5.85/6.10      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 5.85/6.10         (~ (v1_funct_1 @ X36)
% 5.85/6.10          | ~ (v1_funct_2 @ X36 @ X37 @ X38)
% 5.85/6.10          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 5.85/6.10          | ~ (r2_relset_1 @ X37 @ X37 @ 
% 5.85/6.10               (k1_partfun1 @ X37 @ X38 @ X38 @ X37 @ X36 @ X39) @ 
% 5.85/6.10               (k6_partfun1 @ X37))
% 5.85/6.10          | ((k2_relset_1 @ X38 @ X37 @ X39) = (X37))
% 5.85/6.10          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 5.85/6.10          | ~ (v1_funct_2 @ X39 @ X38 @ X37)
% 5.85/6.10          | ~ (v1_funct_1 @ X39))),
% 5.85/6.10      inference('cnf', [status(esa)], [t24_funct_2])).
% 5.85/6.10  thf('5', plain,
% 5.85/6.10      (![X0 : $i]:
% 5.85/6.10         (~ (v1_funct_1 @ X0)
% 5.85/6.10          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 5.85/6.10          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 5.85/6.10          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 5.85/6.10          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 5.85/6.10               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 5.85/6.10               (k6_partfun1 @ sk_A))
% 5.85/6.10          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 5.85/6.10          | ~ (v1_funct_1 @ sk_C))),
% 5.85/6.10      inference('sup-', [status(thm)], ['3', '4'])).
% 5.85/6.10  thf('6', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 5.85/6.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.85/6.10  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 5.85/6.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.85/6.10  thf('8', plain,
% 5.85/6.10      (![X0 : $i]:
% 5.85/6.10         (~ (v1_funct_1 @ X0)
% 5.85/6.10          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 5.85/6.10          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 5.85/6.10          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 5.85/6.10          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 5.85/6.10               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 5.85/6.10               (k6_partfun1 @ sk_A)))),
% 5.85/6.10      inference('demod', [status(thm)], ['5', '6', '7'])).
% 5.85/6.10  thf('9', plain,
% 5.85/6.10      ((((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (sk_A))
% 5.85/6.10        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 5.85/6.10        | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 5.85/6.10        | ~ (v1_funct_1 @ sk_D))),
% 5.85/6.10      inference('sup-', [status(thm)], ['2', '8'])).
% 5.85/6.10  thf('10', plain,
% 5.85/6.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 5.85/6.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.85/6.10  thf(redefinition_k2_relset_1, axiom,
% 5.85/6.10    (![A:$i,B:$i,C:$i]:
% 5.85/6.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.85/6.10       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 5.85/6.10  thf('11', plain,
% 5.85/6.10      (![X19 : $i, X20 : $i, X21 : $i]:
% 5.85/6.10         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 5.85/6.10          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 5.85/6.10      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 5.85/6.10  thf('12', plain,
% 5.85/6.10      (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 5.85/6.10      inference('sup-', [status(thm)], ['10', '11'])).
% 5.85/6.10  thf('13', plain,
% 5.85/6.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 5.85/6.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.85/6.10  thf('14', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 5.85/6.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.85/6.10  thf('15', plain, ((v1_funct_1 @ sk_D)),
% 5.85/6.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.85/6.10  thf('16', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 5.85/6.10      inference('demod', [status(thm)], ['9', '12', '13', '14', '15'])).
% 5.85/6.10  thf(d3_funct_2, axiom,
% 5.85/6.10    (![A:$i,B:$i]:
% 5.85/6.10     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 5.85/6.10       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 5.85/6.10  thf('17', plain,
% 5.85/6.10      (![X27 : $i, X28 : $i]:
% 5.85/6.10         (((k2_relat_1 @ X28) != (X27))
% 5.85/6.10          | (v2_funct_2 @ X28 @ X27)
% 5.85/6.10          | ~ (v5_relat_1 @ X28 @ X27)
% 5.85/6.10          | ~ (v1_relat_1 @ X28))),
% 5.85/6.10      inference('cnf', [status(esa)], [d3_funct_2])).
% 5.85/6.10  thf('18', plain,
% 5.85/6.10      (![X28 : $i]:
% 5.85/6.10         (~ (v1_relat_1 @ X28)
% 5.85/6.10          | ~ (v5_relat_1 @ X28 @ (k2_relat_1 @ X28))
% 5.85/6.10          | (v2_funct_2 @ X28 @ (k2_relat_1 @ X28)))),
% 5.85/6.10      inference('simplify', [status(thm)], ['17'])).
% 5.85/6.10  thf('19', plain,
% 5.85/6.10      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 5.85/6.10        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 5.85/6.10        | ~ (v1_relat_1 @ sk_D))),
% 5.85/6.10      inference('sup-', [status(thm)], ['16', '18'])).
% 5.85/6.10  thf('20', plain,
% 5.85/6.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 5.85/6.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.85/6.10  thf(cc2_relset_1, axiom,
% 5.85/6.10    (![A:$i,B:$i,C:$i]:
% 5.85/6.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.85/6.10       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 5.85/6.10  thf('21', plain,
% 5.85/6.10      (![X16 : $i, X17 : $i, X18 : $i]:
% 5.85/6.10         ((v5_relat_1 @ X16 @ X18)
% 5.85/6.10          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 5.85/6.10      inference('cnf', [status(esa)], [cc2_relset_1])).
% 5.85/6.10  thf('22', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 5.85/6.10      inference('sup-', [status(thm)], ['20', '21'])).
% 5.85/6.10  thf('23', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 5.85/6.10      inference('demod', [status(thm)], ['9', '12', '13', '14', '15'])).
% 5.85/6.10  thf('24', plain,
% 5.85/6.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 5.85/6.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.85/6.10  thf(cc1_relset_1, axiom,
% 5.85/6.10    (![A:$i,B:$i,C:$i]:
% 5.85/6.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.85/6.10       ( v1_relat_1 @ C ) ))).
% 5.85/6.10  thf('25', plain,
% 5.85/6.10      (![X13 : $i, X14 : $i, X15 : $i]:
% 5.85/6.10         ((v1_relat_1 @ X13)
% 5.85/6.10          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 5.85/6.10      inference('cnf', [status(esa)], [cc1_relset_1])).
% 5.85/6.10  thf('26', plain, ((v1_relat_1 @ sk_D)),
% 5.85/6.10      inference('sup-', [status(thm)], ['24', '25'])).
% 5.85/6.10  thf('27', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 5.85/6.10      inference('demod', [status(thm)], ['19', '22', '23', '26'])).
% 5.85/6.10  thf('28', plain,
% 5.85/6.10      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 5.85/6.10      inference('split', [status(esa)], ['0'])).
% 5.85/6.10  thf('29', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 5.85/6.10      inference('sup-', [status(thm)], ['27', '28'])).
% 5.85/6.10  thf('30', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 5.85/6.10      inference('split', [status(esa)], ['0'])).
% 5.85/6.10  thf('31', plain, (~ ((v2_funct_1 @ sk_C))),
% 5.85/6.10      inference('sat_resolution*', [status(thm)], ['29', '30'])).
% 5.85/6.10  thf('32', plain, (~ (v2_funct_1 @ sk_C)),
% 5.85/6.10      inference('simpl_trail', [status(thm)], ['1', '31'])).
% 5.85/6.10  thf('33', plain,
% 5.85/6.10      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.85/6.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.85/6.10  thf(t3_subset, axiom,
% 5.85/6.10    (![A:$i,B:$i]:
% 5.85/6.10     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 5.85/6.10  thf('34', plain,
% 5.85/6.10      (![X8 : $i, X9 : $i]:
% 5.85/6.10         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 5.85/6.10      inference('cnf', [status(esa)], [t3_subset])).
% 5.85/6.10  thf('35', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 5.85/6.10      inference('sup-', [status(thm)], ['33', '34'])).
% 5.85/6.10  thf(d10_xboole_0, axiom,
% 5.85/6.10    (![A:$i,B:$i]:
% 5.85/6.10     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.85/6.10  thf('36', plain,
% 5.85/6.10      (![X1 : $i, X3 : $i]:
% 5.85/6.10         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 5.85/6.10      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.85/6.10  thf('37', plain,
% 5.85/6.10      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C)
% 5.85/6.10        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_C)))),
% 5.85/6.10      inference('sup-', [status(thm)], ['35', '36'])).
% 5.85/6.10  thf('38', plain,
% 5.85/6.10      ((r2_relset_1 @ sk_A @ sk_A @ 
% 5.85/6.10        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 5.85/6.10        (k6_partfun1 @ sk_A))),
% 5.85/6.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.85/6.10  thf('39', plain,
% 5.85/6.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 5.85/6.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.85/6.10  thf('40', plain,
% 5.85/6.10      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.85/6.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.85/6.10  thf(dt_k1_partfun1, axiom,
% 5.85/6.10    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 5.85/6.10     ( ( ( v1_funct_1 @ E ) & 
% 5.85/6.10         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.85/6.10         ( v1_funct_1 @ F ) & 
% 5.85/6.10         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 5.85/6.10       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 5.85/6.10         ( m1_subset_1 @
% 5.85/6.10           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 5.85/6.10           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 5.85/6.10  thf('41', plain,
% 5.85/6.10      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 5.85/6.10         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 5.85/6.10          | ~ (v1_funct_1 @ X29)
% 5.85/6.10          | ~ (v1_funct_1 @ X32)
% 5.85/6.10          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 5.85/6.10          | (m1_subset_1 @ (k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32) @ 
% 5.85/6.10             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X34))))),
% 5.85/6.10      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 5.85/6.10  thf('42', plain,
% 5.85/6.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.85/6.10         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1) @ 
% 5.85/6.10           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 5.85/6.10          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 5.85/6.10          | ~ (v1_funct_1 @ X1)
% 5.85/6.10          | ~ (v1_funct_1 @ sk_C))),
% 5.85/6.10      inference('sup-', [status(thm)], ['40', '41'])).
% 5.85/6.10  thf('43', plain, ((v1_funct_1 @ sk_C)),
% 5.85/6.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.85/6.10  thf('44', plain,
% 5.85/6.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.85/6.10         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1) @ 
% 5.85/6.10           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 5.85/6.10          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 5.85/6.10          | ~ (v1_funct_1 @ X1))),
% 5.85/6.10      inference('demod', [status(thm)], ['42', '43'])).
% 5.85/6.10  thf('45', plain,
% 5.85/6.10      ((~ (v1_funct_1 @ sk_D)
% 5.85/6.10        | (m1_subset_1 @ 
% 5.85/6.10           (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 5.85/6.10           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 5.85/6.10      inference('sup-', [status(thm)], ['39', '44'])).
% 5.85/6.10  thf('46', plain, ((v1_funct_1 @ sk_D)),
% 5.85/6.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.85/6.10  thf('47', plain,
% 5.85/6.10      ((m1_subset_1 @ 
% 5.85/6.10        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 5.85/6.10        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.85/6.10      inference('demod', [status(thm)], ['45', '46'])).
% 5.85/6.10  thf(redefinition_r2_relset_1, axiom,
% 5.85/6.10    (![A:$i,B:$i,C:$i,D:$i]:
% 5.85/6.10     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.85/6.10         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.85/6.10       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 5.85/6.10  thf('48', plain,
% 5.85/6.10      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 5.85/6.10         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 5.85/6.10          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 5.85/6.10          | ((X22) = (X25))
% 5.85/6.10          | ~ (r2_relset_1 @ X23 @ X24 @ X22 @ X25))),
% 5.85/6.10      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 5.85/6.10  thf('49', plain,
% 5.85/6.10      (![X0 : $i]:
% 5.85/6.10         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 5.85/6.10             (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ X0)
% 5.85/6.10          | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) = (X0))
% 5.85/6.10          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 5.85/6.10      inference('sup-', [status(thm)], ['47', '48'])).
% 5.85/6.10  thf('50', plain,
% 5.85/6.10      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 5.85/6.10           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 5.85/6.10        | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 5.85/6.10            = (k6_partfun1 @ sk_A)))),
% 5.85/6.10      inference('sup-', [status(thm)], ['38', '49'])).
% 5.85/6.10  thf(t29_relset_1, axiom,
% 5.85/6.10    (![A:$i]:
% 5.85/6.10     ( m1_subset_1 @
% 5.85/6.10       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 5.85/6.10  thf('51', plain,
% 5.85/6.10      (![X26 : $i]:
% 5.85/6.10         (m1_subset_1 @ (k6_relat_1 @ X26) @ 
% 5.85/6.10          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X26)))),
% 5.85/6.10      inference('cnf', [status(esa)], [t29_relset_1])).
% 5.85/6.10  thf(redefinition_k6_partfun1, axiom,
% 5.85/6.10    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 5.85/6.10  thf('52', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 5.85/6.10      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.85/6.10  thf('53', plain,
% 5.85/6.10      (![X26 : $i]:
% 5.85/6.10         (m1_subset_1 @ (k6_partfun1 @ X26) @ 
% 5.85/6.10          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X26)))),
% 5.85/6.10      inference('demod', [status(thm)], ['51', '52'])).
% 5.85/6.10  thf('54', plain,
% 5.85/6.10      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 5.85/6.10         = (k6_partfun1 @ sk_A))),
% 5.85/6.10      inference('demod', [status(thm)], ['50', '53'])).
% 5.85/6.10  thf('55', plain,
% 5.85/6.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 5.85/6.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.85/6.10  thf(t26_funct_2, axiom,
% 5.85/6.10    (![A:$i,B:$i,C:$i,D:$i]:
% 5.85/6.10     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 5.85/6.10         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.85/6.10       ( ![E:$i]:
% 5.85/6.10         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 5.85/6.10             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 5.85/6.10           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 5.85/6.10             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 5.85/6.10               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 5.85/6.10  thf('56', plain,
% 5.85/6.10      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 5.85/6.10         (~ (v1_funct_1 @ X40)
% 5.85/6.10          | ~ (v1_funct_2 @ X40 @ X41 @ X42)
% 5.85/6.10          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 5.85/6.10          | ~ (v2_funct_1 @ (k1_partfun1 @ X43 @ X41 @ X41 @ X42 @ X44 @ X40))
% 5.85/6.10          | (v2_funct_1 @ X44)
% 5.85/6.10          | ((X42) = (k1_xboole_0))
% 5.85/6.10          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X41)))
% 5.85/6.10          | ~ (v1_funct_2 @ X44 @ X43 @ X41)
% 5.85/6.10          | ~ (v1_funct_1 @ X44))),
% 5.85/6.10      inference('cnf', [status(esa)], [t26_funct_2])).
% 5.85/6.10  thf('57', plain,
% 5.85/6.10      (![X0 : $i, X1 : $i]:
% 5.85/6.10         (~ (v1_funct_1 @ X0)
% 5.85/6.10          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 5.85/6.10          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 5.85/6.10          | ((sk_A) = (k1_xboole_0))
% 5.85/6.10          | (v2_funct_1 @ X0)
% 5.85/6.10          | ~ (v2_funct_1 @ 
% 5.85/6.10               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D))
% 5.85/6.10          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 5.85/6.10          | ~ (v1_funct_1 @ sk_D))),
% 5.85/6.10      inference('sup-', [status(thm)], ['55', '56'])).
% 5.85/6.10  thf('58', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 5.85/6.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.85/6.10  thf('59', plain, ((v1_funct_1 @ sk_D)),
% 5.85/6.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.85/6.10  thf('60', plain,
% 5.85/6.10      (![X0 : $i, X1 : $i]:
% 5.85/6.10         (~ (v1_funct_1 @ X0)
% 5.85/6.10          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 5.85/6.10          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 5.85/6.10          | ((sk_A) = (k1_xboole_0))
% 5.85/6.10          | (v2_funct_1 @ X0)
% 5.85/6.10          | ~ (v2_funct_1 @ 
% 5.85/6.10               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D)))),
% 5.85/6.10      inference('demod', [status(thm)], ['57', '58', '59'])).
% 5.85/6.10  thf('61', plain,
% 5.85/6.10      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 5.85/6.10        | (v2_funct_1 @ sk_C)
% 5.85/6.10        | ((sk_A) = (k1_xboole_0))
% 5.85/6.10        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 5.85/6.10        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 5.85/6.10        | ~ (v1_funct_1 @ sk_C))),
% 5.85/6.10      inference('sup-', [status(thm)], ['54', '60'])).
% 5.85/6.10  thf(fc4_funct_1, axiom,
% 5.85/6.10    (![A:$i]:
% 5.85/6.10     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 5.85/6.10       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 5.85/6.10  thf('62', plain, (![X12 : $i]: (v2_funct_1 @ (k6_relat_1 @ X12))),
% 5.85/6.10      inference('cnf', [status(esa)], [fc4_funct_1])).
% 5.85/6.10  thf('63', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 5.85/6.10      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.85/6.10  thf('64', plain, (![X12 : $i]: (v2_funct_1 @ (k6_partfun1 @ X12))),
% 5.85/6.10      inference('demod', [status(thm)], ['62', '63'])).
% 5.85/6.10  thf('65', plain,
% 5.85/6.10      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.85/6.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.85/6.10  thf('66', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 5.85/6.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.85/6.10  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 5.85/6.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.85/6.10  thf('68', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 5.85/6.10      inference('demod', [status(thm)], ['61', '64', '65', '66', '67'])).
% 5.85/6.10  thf('69', plain, (~ (v2_funct_1 @ sk_C)),
% 5.85/6.10      inference('simpl_trail', [status(thm)], ['1', '31'])).
% 5.85/6.10  thf('70', plain, (((sk_A) = (k1_xboole_0))),
% 5.85/6.10      inference('clc', [status(thm)], ['68', '69'])).
% 5.85/6.10  thf(t113_zfmisc_1, axiom,
% 5.85/6.10    (![A:$i,B:$i]:
% 5.85/6.10     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 5.85/6.10       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 5.85/6.10  thf('71', plain,
% 5.85/6.10      (![X5 : $i, X6 : $i]:
% 5.85/6.10         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 5.85/6.10      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 5.85/6.10  thf('72', plain,
% 5.85/6.10      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 5.85/6.10      inference('simplify', [status(thm)], ['71'])).
% 5.85/6.10  thf(rc2_subset_1, axiom,
% 5.85/6.10    (![A:$i]:
% 5.85/6.10     ( ?[B:$i]:
% 5.85/6.10       ( ( v1_xboole_0 @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 5.85/6.10  thf('73', plain,
% 5.85/6.10      (![X7 : $i]: (m1_subset_1 @ (sk_B @ X7) @ (k1_zfmisc_1 @ X7))),
% 5.85/6.10      inference('cnf', [status(esa)], [rc2_subset_1])).
% 5.85/6.10  thf('74', plain, (![X7 : $i]: (v1_xboole_0 @ (sk_B @ X7))),
% 5.85/6.10      inference('cnf', [status(esa)], [rc2_subset_1])).
% 5.85/6.10  thf(l13_xboole_0, axiom,
% 5.85/6.10    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 5.85/6.10  thf('75', plain,
% 5.85/6.10      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 5.85/6.10      inference('cnf', [status(esa)], [l13_xboole_0])).
% 5.85/6.10  thf('76', plain, (![X0 : $i]: ((sk_B @ X0) = (k1_xboole_0))),
% 5.85/6.10      inference('sup-', [status(thm)], ['74', '75'])).
% 5.85/6.10  thf('77', plain,
% 5.85/6.10      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 5.85/6.10      inference('demod', [status(thm)], ['73', '76'])).
% 5.85/6.10  thf('78', plain,
% 5.85/6.10      (![X8 : $i, X9 : $i]:
% 5.85/6.10         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 5.85/6.10      inference('cnf', [status(esa)], [t3_subset])).
% 5.85/6.10  thf('79', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 5.85/6.10      inference('sup-', [status(thm)], ['77', '78'])).
% 5.85/6.10  thf('80', plain, (((sk_A) = (k1_xboole_0))),
% 5.85/6.10      inference('clc', [status(thm)], ['68', '69'])).
% 5.85/6.10  thf('81', plain,
% 5.85/6.10      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 5.85/6.10      inference('simplify', [status(thm)], ['71'])).
% 5.85/6.10  thf('82', plain, (((k1_xboole_0) = (sk_C))),
% 5.85/6.10      inference('demod', [status(thm)], ['37', '70', '72', '79', '80', '81'])).
% 5.85/6.10  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 5.85/6.10  thf('83', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 5.85/6.10      inference('cnf', [status(esa)], [t81_relat_1])).
% 5.85/6.10  thf('84', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 5.85/6.10      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.85/6.10  thf('85', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 5.85/6.10      inference('demod', [status(thm)], ['83', '84'])).
% 5.85/6.10  thf('86', plain, (![X12 : $i]: (v2_funct_1 @ (k6_partfun1 @ X12))),
% 5.85/6.10      inference('demod', [status(thm)], ['62', '63'])).
% 5.85/6.10  thf('87', plain, ((v2_funct_1 @ k1_xboole_0)),
% 5.85/6.10      inference('sup+', [status(thm)], ['85', '86'])).
% 5.85/6.10  thf('88', plain, ($false),
% 5.85/6.10      inference('demod', [status(thm)], ['32', '82', '87'])).
% 5.85/6.10  
% 5.85/6.10  % SZS output end Refutation
% 5.85/6.10  
% 5.85/6.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

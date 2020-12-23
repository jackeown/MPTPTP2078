%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.koPezPvWGV

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:20 EST 2020

% Result     : Theorem 4.28s
% Output     : Refutation 4.28s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 503 expanded)
%              Number of leaves         :   45 ( 161 expanded)
%              Depth                    :   19
%              Number of atoms          : 1311 (9510 expanded)
%              Number of equality atoms :   45 ( 119 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
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

thf('4',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
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

thf('12',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ( ( k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44 )
        = ( k5_relat_1 @ X41 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9','18'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('20',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('22',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('23',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('24',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X20 @ X19 ) ) @ ( k2_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('25',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ( v5_relat_1 @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( v5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( v5_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('32',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('37',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    v5_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['27','32','37'])).

thf('39',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v5_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('42',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('43',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('44',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
    | ( ( k2_relat_1 @ sk_D )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('47',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9','18'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('49',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( X28 = X31 )
      | ~ ( r2_relset_1 @ X29 @ X30 @ X28 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('52',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('53',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('54',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['51','54'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('56',plain,(
    ! [X22: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('57',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('58',plain,(
    ! [X22: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X22 ) )
      = X22 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('60',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v5_relat_1 @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('61',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v5_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('63',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['30','31'])).

thf('65',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('67',plain,(
    ! [X22: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X22 ) )
      = X22 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('68',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['44','55','58','65','66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('70',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ( v5_relat_1 @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('73',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k2_relat_1 @ X34 )
       != X33 )
      | ( v2_funct_2 @ X34 @ X33 )
      | ~ ( v5_relat_1 @ X34 @ X33 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('74',plain,(
    ! [X34: $i] :
      ( ~ ( v1_relat_1 @ X34 )
      | ~ ( v5_relat_1 @ X34 @ ( k2_relat_1 @ X34 ) )
      | ( v2_funct_2 @ X34 @ ( k2_relat_1 @ X34 ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['68','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['30','31'])).

thf('79',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( $false
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['1','79'])).

thf('81',plain,(
    ! [X22: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X22 ) )
      = X22 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('82',plain,(
    ! [X18: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('84',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('85',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('86',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X23 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['83','86'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('88',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 )
      | ( X4 = X5 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k6_partfun1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('91',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_funct_1 @ ( k6_partfun1 @ X0 ) )
        | ~ ( v1_xboole_0 @ sk_C )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X24: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('93',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('94',plain,(
    ! [X24: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X24 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ sk_C )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['91','94'])).

thf('96',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(condensation,[status(thm)],['95'])).

thf('97',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('98',plain,(
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

thf('99',plain,(
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

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['97','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['104','105','106','107'])).

thf('109',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('110',plain,(
    ! [X24: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X24 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('111',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('113',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('114',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('115',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('116',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_xboole_0 @ X10 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('117',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['114','117'])).

thf('119',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_C ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['113','118'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('120',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('121',plain,
    ( ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['96','121'])).

thf('123',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('124',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['122','123'])).

thf('125',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['80','124'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.koPezPvWGV
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:31:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.28/4.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.28/4.48  % Solved by: fo/fo7.sh
% 4.28/4.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.28/4.48  % done 3330 iterations in 4.024s
% 4.28/4.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.28/4.48  % SZS output start Refutation
% 4.28/4.48  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 4.28/4.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.28/4.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.28/4.48  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 4.28/4.48  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 4.28/4.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.28/4.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.28/4.48  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 4.28/4.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.28/4.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.28/4.48  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 4.28/4.48  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 4.28/4.48  thf(sk_A_type, type, sk_A: $i).
% 4.28/4.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.28/4.48  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 4.28/4.48  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 4.28/4.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.28/4.48  thf(sk_D_type, type, sk_D: $i).
% 4.28/4.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.28/4.48  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 4.28/4.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.28/4.48  thf(sk_C_type, type, sk_C: $i).
% 4.28/4.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.28/4.48  thf(sk_B_type, type, sk_B: $i).
% 4.28/4.48  thf(t29_funct_2, conjecture,
% 4.28/4.48    (![A:$i,B:$i,C:$i]:
% 4.28/4.48     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.28/4.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.28/4.48       ( ![D:$i]:
% 4.28/4.48         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.28/4.48             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.28/4.48           ( ( r2_relset_1 @
% 4.28/4.48               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 4.28/4.48               ( k6_partfun1 @ A ) ) =>
% 4.28/4.48             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 4.28/4.48  thf(zf_stmt_0, negated_conjecture,
% 4.28/4.48    (~( ![A:$i,B:$i,C:$i]:
% 4.28/4.48        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.28/4.48            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.28/4.48          ( ![D:$i]:
% 4.28/4.48            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.28/4.48                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.28/4.48              ( ( r2_relset_1 @
% 4.28/4.48                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 4.28/4.48                  ( k6_partfun1 @ A ) ) =>
% 4.28/4.48                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 4.28/4.48    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 4.28/4.48  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf('1', plain,
% 4.28/4.48      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 4.28/4.48      inference('split', [status(esa)], ['0'])).
% 4.28/4.48  thf('2', plain,
% 4.28/4.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf('3', plain,
% 4.28/4.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf(dt_k1_partfun1, axiom,
% 4.28/4.48    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.28/4.48     ( ( ( v1_funct_1 @ E ) & 
% 4.28/4.48         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.28/4.48         ( v1_funct_1 @ F ) & 
% 4.28/4.48         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 4.28/4.48       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 4.28/4.48         ( m1_subset_1 @
% 4.28/4.48           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 4.28/4.48           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 4.28/4.48  thf('4', plain,
% 4.28/4.48      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 4.28/4.48         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 4.28/4.48          | ~ (v1_funct_1 @ X35)
% 4.28/4.48          | ~ (v1_funct_1 @ X38)
% 4.28/4.48          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 4.28/4.48          | (m1_subset_1 @ (k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38) @ 
% 4.28/4.48             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X40))))),
% 4.28/4.48      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 4.28/4.48  thf('5', plain,
% 4.28/4.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.28/4.48         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 4.28/4.48           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 4.28/4.48          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 4.28/4.48          | ~ (v1_funct_1 @ X1)
% 4.28/4.48          | ~ (v1_funct_1 @ sk_C))),
% 4.28/4.48      inference('sup-', [status(thm)], ['3', '4'])).
% 4.28/4.48  thf('6', plain, ((v1_funct_1 @ sk_C)),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf('7', plain,
% 4.28/4.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.28/4.48         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 4.28/4.48           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 4.28/4.48          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 4.28/4.48          | ~ (v1_funct_1 @ X1))),
% 4.28/4.48      inference('demod', [status(thm)], ['5', '6'])).
% 4.28/4.48  thf('8', plain,
% 4.28/4.48      ((~ (v1_funct_1 @ sk_D)
% 4.28/4.48        | (m1_subset_1 @ 
% 4.28/4.48           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 4.28/4.48           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 4.28/4.48      inference('sup-', [status(thm)], ['2', '7'])).
% 4.28/4.48  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf('10', plain,
% 4.28/4.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf('11', plain,
% 4.28/4.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf(redefinition_k1_partfun1, axiom,
% 4.28/4.48    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.28/4.48     ( ( ( v1_funct_1 @ E ) & 
% 4.28/4.48         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.28/4.48         ( v1_funct_1 @ F ) & 
% 4.28/4.48         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 4.28/4.48       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 4.28/4.48  thf('12', plain,
% 4.28/4.48      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 4.28/4.48         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 4.28/4.48          | ~ (v1_funct_1 @ X41)
% 4.28/4.48          | ~ (v1_funct_1 @ X44)
% 4.28/4.48          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 4.28/4.48          | ((k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44)
% 4.28/4.48              = (k5_relat_1 @ X41 @ X44)))),
% 4.28/4.48      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 4.28/4.48  thf('13', plain,
% 4.28/4.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.28/4.48         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 4.28/4.48            = (k5_relat_1 @ sk_C @ X0))
% 4.28/4.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 4.28/4.48          | ~ (v1_funct_1 @ X0)
% 4.28/4.48          | ~ (v1_funct_1 @ sk_C))),
% 4.28/4.48      inference('sup-', [status(thm)], ['11', '12'])).
% 4.28/4.48  thf('14', plain, ((v1_funct_1 @ sk_C)),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf('15', plain,
% 4.28/4.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.28/4.48         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 4.28/4.48            = (k5_relat_1 @ sk_C @ X0))
% 4.28/4.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 4.28/4.48          | ~ (v1_funct_1 @ X0))),
% 4.28/4.48      inference('demod', [status(thm)], ['13', '14'])).
% 4.28/4.48  thf('16', plain,
% 4.28/4.48      ((~ (v1_funct_1 @ sk_D)
% 4.28/4.48        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.28/4.48            = (k5_relat_1 @ sk_C @ sk_D)))),
% 4.28/4.48      inference('sup-', [status(thm)], ['10', '15'])).
% 4.28/4.48  thf('17', plain, ((v1_funct_1 @ sk_D)),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf('18', plain,
% 4.28/4.48      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.28/4.48         = (k5_relat_1 @ sk_C @ sk_D))),
% 4.28/4.48      inference('demod', [status(thm)], ['16', '17'])).
% 4.28/4.48  thf('19', plain,
% 4.28/4.48      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 4.28/4.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.28/4.48      inference('demod', [status(thm)], ['8', '9', '18'])).
% 4.28/4.48  thf(cc2_relat_1, axiom,
% 4.28/4.48    (![A:$i]:
% 4.28/4.48     ( ( v1_relat_1 @ A ) =>
% 4.28/4.48       ( ![B:$i]:
% 4.28/4.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 4.28/4.48  thf('20', plain,
% 4.28/4.48      (![X12 : $i, X13 : $i]:
% 4.28/4.48         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 4.28/4.48          | (v1_relat_1 @ X12)
% 4.28/4.48          | ~ (v1_relat_1 @ X13))),
% 4.28/4.48      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.28/4.48  thf('21', plain,
% 4.28/4.48      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 4.28/4.48        | (v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))),
% 4.28/4.48      inference('sup-', [status(thm)], ['19', '20'])).
% 4.28/4.48  thf(fc6_relat_1, axiom,
% 4.28/4.48    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 4.28/4.48  thf('22', plain,
% 4.28/4.48      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 4.28/4.48      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.28/4.48  thf('23', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))),
% 4.28/4.48      inference('demod', [status(thm)], ['21', '22'])).
% 4.28/4.48  thf(t45_relat_1, axiom,
% 4.28/4.48    (![A:$i]:
% 4.28/4.48     ( ( v1_relat_1 @ A ) =>
% 4.28/4.48       ( ![B:$i]:
% 4.28/4.48         ( ( v1_relat_1 @ B ) =>
% 4.28/4.48           ( r1_tarski @
% 4.28/4.48             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 4.28/4.48  thf('24', plain,
% 4.28/4.48      (![X19 : $i, X20 : $i]:
% 4.28/4.48         (~ (v1_relat_1 @ X19)
% 4.28/4.48          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X20 @ X19)) @ 
% 4.28/4.48             (k2_relat_1 @ X19))
% 4.28/4.48          | ~ (v1_relat_1 @ X20))),
% 4.28/4.48      inference('cnf', [status(esa)], [t45_relat_1])).
% 4.28/4.48  thf(d19_relat_1, axiom,
% 4.28/4.48    (![A:$i,B:$i]:
% 4.28/4.48     ( ( v1_relat_1 @ B ) =>
% 4.28/4.48       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 4.28/4.48  thf('25', plain,
% 4.28/4.48      (![X14 : $i, X15 : $i]:
% 4.28/4.48         (~ (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 4.28/4.48          | (v5_relat_1 @ X14 @ X15)
% 4.28/4.48          | ~ (v1_relat_1 @ X14))),
% 4.28/4.48      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.28/4.48  thf('26', plain,
% 4.28/4.48      (![X0 : $i, X1 : $i]:
% 4.28/4.48         (~ (v1_relat_1 @ X1)
% 4.28/4.48          | ~ (v1_relat_1 @ X0)
% 4.28/4.48          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 4.28/4.48          | (v5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 4.28/4.48      inference('sup-', [status(thm)], ['24', '25'])).
% 4.28/4.48  thf('27', plain,
% 4.28/4.48      (((v5_relat_1 @ (k5_relat_1 @ sk_C @ sk_D) @ (k2_relat_1 @ sk_D))
% 4.28/4.48        | ~ (v1_relat_1 @ sk_D)
% 4.28/4.48        | ~ (v1_relat_1 @ sk_C))),
% 4.28/4.48      inference('sup-', [status(thm)], ['23', '26'])).
% 4.28/4.48  thf('28', plain,
% 4.28/4.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf('29', plain,
% 4.28/4.48      (![X12 : $i, X13 : $i]:
% 4.28/4.48         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 4.28/4.48          | (v1_relat_1 @ X12)
% 4.28/4.48          | ~ (v1_relat_1 @ X13))),
% 4.28/4.48      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.28/4.48  thf('30', plain,
% 4.28/4.48      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 4.28/4.48      inference('sup-', [status(thm)], ['28', '29'])).
% 4.28/4.48  thf('31', plain,
% 4.28/4.48      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 4.28/4.48      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.28/4.48  thf('32', plain, ((v1_relat_1 @ sk_D)),
% 4.28/4.48      inference('demod', [status(thm)], ['30', '31'])).
% 4.28/4.48  thf('33', plain,
% 4.28/4.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf('34', plain,
% 4.28/4.48      (![X12 : $i, X13 : $i]:
% 4.28/4.48         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 4.28/4.48          | (v1_relat_1 @ X12)
% 4.28/4.48          | ~ (v1_relat_1 @ X13))),
% 4.28/4.48      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.28/4.48  thf('35', plain,
% 4.28/4.48      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 4.28/4.48      inference('sup-', [status(thm)], ['33', '34'])).
% 4.28/4.48  thf('36', plain,
% 4.28/4.48      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 4.28/4.48      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.28/4.48  thf('37', plain, ((v1_relat_1 @ sk_C)),
% 4.28/4.48      inference('demod', [status(thm)], ['35', '36'])).
% 4.28/4.48  thf('38', plain,
% 4.28/4.48      ((v5_relat_1 @ (k5_relat_1 @ sk_C @ sk_D) @ (k2_relat_1 @ sk_D))),
% 4.28/4.48      inference('demod', [status(thm)], ['27', '32', '37'])).
% 4.28/4.48  thf('39', plain,
% 4.28/4.48      (![X14 : $i, X15 : $i]:
% 4.28/4.48         (~ (v5_relat_1 @ X14 @ X15)
% 4.28/4.48          | (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 4.28/4.48          | ~ (v1_relat_1 @ X14))),
% 4.28/4.48      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.28/4.48  thf('40', plain,
% 4.28/4.48      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 4.28/4.48        | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ 
% 4.28/4.48           (k2_relat_1 @ sk_D)))),
% 4.28/4.48      inference('sup-', [status(thm)], ['38', '39'])).
% 4.28/4.48  thf('41', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))),
% 4.28/4.48      inference('demod', [status(thm)], ['21', '22'])).
% 4.28/4.48  thf('42', plain,
% 4.28/4.48      ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ 
% 4.28/4.48        (k2_relat_1 @ sk_D))),
% 4.28/4.48      inference('demod', [status(thm)], ['40', '41'])).
% 4.28/4.48  thf(d10_xboole_0, axiom,
% 4.28/4.48    (![A:$i,B:$i]:
% 4.28/4.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.28/4.48  thf('43', plain,
% 4.28/4.48      (![X0 : $i, X2 : $i]:
% 4.28/4.48         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 4.28/4.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.28/4.48  thf('44', plain,
% 4.28/4.48      ((~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 4.28/4.48           (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 4.28/4.48        | ((k2_relat_1 @ sk_D) = (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))))),
% 4.28/4.48      inference('sup-', [status(thm)], ['42', '43'])).
% 4.28/4.48  thf('45', plain,
% 4.28/4.48      ((r2_relset_1 @ sk_A @ sk_A @ 
% 4.28/4.48        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 4.28/4.48        (k6_partfun1 @ sk_A))),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf('46', plain,
% 4.28/4.48      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.28/4.48         = (k5_relat_1 @ sk_C @ sk_D))),
% 4.28/4.48      inference('demod', [status(thm)], ['16', '17'])).
% 4.28/4.48  thf('47', plain,
% 4.28/4.48      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 4.28/4.48        (k6_partfun1 @ sk_A))),
% 4.28/4.48      inference('demod', [status(thm)], ['45', '46'])).
% 4.28/4.48  thf('48', plain,
% 4.28/4.48      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 4.28/4.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.28/4.48      inference('demod', [status(thm)], ['8', '9', '18'])).
% 4.28/4.48  thf(redefinition_r2_relset_1, axiom,
% 4.28/4.48    (![A:$i,B:$i,C:$i,D:$i]:
% 4.28/4.48     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.28/4.48         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.28/4.48       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 4.28/4.48  thf('49', plain,
% 4.28/4.48      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 4.28/4.48         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 4.28/4.48          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 4.28/4.48          | ((X28) = (X31))
% 4.28/4.48          | ~ (r2_relset_1 @ X29 @ X30 @ X28 @ X31))),
% 4.28/4.48      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 4.28/4.48  thf('50', plain,
% 4.28/4.48      (![X0 : $i]:
% 4.28/4.48         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 4.28/4.48          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 4.28/4.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 4.28/4.48      inference('sup-', [status(thm)], ['48', '49'])).
% 4.28/4.48  thf('51', plain,
% 4.28/4.48      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 4.28/4.48           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 4.28/4.48        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 4.28/4.48      inference('sup-', [status(thm)], ['47', '50'])).
% 4.28/4.48  thf(t29_relset_1, axiom,
% 4.28/4.48    (![A:$i]:
% 4.28/4.48     ( m1_subset_1 @
% 4.28/4.48       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 4.28/4.48  thf('52', plain,
% 4.28/4.48      (![X32 : $i]:
% 4.28/4.48         (m1_subset_1 @ (k6_relat_1 @ X32) @ 
% 4.28/4.48          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 4.28/4.48      inference('cnf', [status(esa)], [t29_relset_1])).
% 4.28/4.48  thf(redefinition_k6_partfun1, axiom,
% 4.28/4.48    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 4.28/4.48  thf('53', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 4.28/4.48      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.28/4.48  thf('54', plain,
% 4.28/4.48      (![X32 : $i]:
% 4.28/4.48         (m1_subset_1 @ (k6_partfun1 @ X32) @ 
% 4.28/4.48          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 4.28/4.48      inference('demod', [status(thm)], ['52', '53'])).
% 4.28/4.48  thf('55', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 4.28/4.48      inference('demod', [status(thm)], ['51', '54'])).
% 4.28/4.48  thf(t71_relat_1, axiom,
% 4.28/4.48    (![A:$i]:
% 4.28/4.48     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 4.28/4.48       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 4.28/4.48  thf('56', plain, (![X22 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 4.28/4.48      inference('cnf', [status(esa)], [t71_relat_1])).
% 4.28/4.48  thf('57', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 4.28/4.48      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.28/4.48  thf('58', plain, (![X22 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X22)) = (X22))),
% 4.28/4.48      inference('demod', [status(thm)], ['56', '57'])).
% 4.28/4.48  thf('59', plain,
% 4.28/4.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf(cc2_relset_1, axiom,
% 4.28/4.48    (![A:$i,B:$i,C:$i]:
% 4.28/4.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.28/4.48       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 4.28/4.48  thf('60', plain,
% 4.28/4.48      (![X25 : $i, X26 : $i, X27 : $i]:
% 4.28/4.48         ((v5_relat_1 @ X25 @ X27)
% 4.28/4.48          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 4.28/4.48      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.28/4.48  thf('61', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 4.28/4.48      inference('sup-', [status(thm)], ['59', '60'])).
% 4.28/4.48  thf('62', plain,
% 4.28/4.48      (![X14 : $i, X15 : $i]:
% 4.28/4.48         (~ (v5_relat_1 @ X14 @ X15)
% 4.28/4.48          | (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 4.28/4.48          | ~ (v1_relat_1 @ X14))),
% 4.28/4.48      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.28/4.48  thf('63', plain,
% 4.28/4.48      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 4.28/4.48      inference('sup-', [status(thm)], ['61', '62'])).
% 4.28/4.48  thf('64', plain, ((v1_relat_1 @ sk_D)),
% 4.28/4.48      inference('demod', [status(thm)], ['30', '31'])).
% 4.28/4.48  thf('65', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 4.28/4.48      inference('demod', [status(thm)], ['63', '64'])).
% 4.28/4.48  thf('66', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 4.28/4.48      inference('demod', [status(thm)], ['51', '54'])).
% 4.28/4.48  thf('67', plain, (![X22 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X22)) = (X22))),
% 4.28/4.48      inference('demod', [status(thm)], ['56', '57'])).
% 4.28/4.48  thf('68', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 4.28/4.48      inference('demod', [status(thm)], ['44', '55', '58', '65', '66', '67'])).
% 4.28/4.48  thf('69', plain,
% 4.28/4.48      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 4.28/4.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.28/4.48  thf('70', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 4.28/4.48      inference('simplify', [status(thm)], ['69'])).
% 4.28/4.48  thf('71', plain,
% 4.28/4.48      (![X14 : $i, X15 : $i]:
% 4.28/4.48         (~ (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 4.28/4.48          | (v5_relat_1 @ X14 @ X15)
% 4.28/4.48          | ~ (v1_relat_1 @ X14))),
% 4.28/4.48      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.28/4.48  thf('72', plain,
% 4.28/4.48      (![X0 : $i]:
% 4.28/4.48         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 4.28/4.48      inference('sup-', [status(thm)], ['70', '71'])).
% 4.28/4.48  thf(d3_funct_2, axiom,
% 4.28/4.48    (![A:$i,B:$i]:
% 4.28/4.48     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 4.28/4.48       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 4.28/4.48  thf('73', plain,
% 4.28/4.48      (![X33 : $i, X34 : $i]:
% 4.28/4.48         (((k2_relat_1 @ X34) != (X33))
% 4.28/4.48          | (v2_funct_2 @ X34 @ X33)
% 4.28/4.48          | ~ (v5_relat_1 @ X34 @ X33)
% 4.28/4.48          | ~ (v1_relat_1 @ X34))),
% 4.28/4.48      inference('cnf', [status(esa)], [d3_funct_2])).
% 4.28/4.48  thf('74', plain,
% 4.28/4.48      (![X34 : $i]:
% 4.28/4.48         (~ (v1_relat_1 @ X34)
% 4.28/4.48          | ~ (v5_relat_1 @ X34 @ (k2_relat_1 @ X34))
% 4.28/4.48          | (v2_funct_2 @ X34 @ (k2_relat_1 @ X34)))),
% 4.28/4.48      inference('simplify', [status(thm)], ['73'])).
% 4.28/4.48  thf('75', plain,
% 4.28/4.48      (![X0 : $i]:
% 4.28/4.48         (~ (v1_relat_1 @ X0)
% 4.28/4.48          | (v2_funct_2 @ X0 @ (k2_relat_1 @ X0))
% 4.28/4.48          | ~ (v1_relat_1 @ X0))),
% 4.28/4.48      inference('sup-', [status(thm)], ['72', '74'])).
% 4.28/4.48  thf('76', plain,
% 4.28/4.48      (![X0 : $i]:
% 4.28/4.48         ((v2_funct_2 @ X0 @ (k2_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 4.28/4.48      inference('simplify', [status(thm)], ['75'])).
% 4.28/4.48  thf('77', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 4.28/4.48      inference('sup+', [status(thm)], ['68', '76'])).
% 4.28/4.48  thf('78', plain, ((v1_relat_1 @ sk_D)),
% 4.28/4.48      inference('demod', [status(thm)], ['30', '31'])).
% 4.28/4.48  thf('79', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 4.28/4.48      inference('demod', [status(thm)], ['77', '78'])).
% 4.28/4.48  thf('80', plain, (($false) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 4.28/4.48      inference('demod', [status(thm)], ['1', '79'])).
% 4.28/4.48  thf('81', plain, (![X22 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X22)) = (X22))),
% 4.28/4.48      inference('demod', [status(thm)], ['56', '57'])).
% 4.28/4.48  thf(fc9_relat_1, axiom,
% 4.28/4.48    (![A:$i]:
% 4.28/4.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 4.28/4.48       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 4.28/4.48  thf('82', plain,
% 4.28/4.48      (![X18 : $i]:
% 4.28/4.48         (~ (v1_xboole_0 @ (k2_relat_1 @ X18))
% 4.28/4.48          | ~ (v1_relat_1 @ X18)
% 4.28/4.48          | (v1_xboole_0 @ X18))),
% 4.28/4.48      inference('cnf', [status(esa)], [fc9_relat_1])).
% 4.28/4.48  thf('83', plain,
% 4.28/4.48      (![X0 : $i]:
% 4.28/4.48         (~ (v1_xboole_0 @ X0)
% 4.28/4.48          | (v1_xboole_0 @ (k6_partfun1 @ X0))
% 4.28/4.48          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 4.28/4.48      inference('sup-', [status(thm)], ['81', '82'])).
% 4.28/4.48  thf(fc4_funct_1, axiom,
% 4.28/4.48    (![A:$i]:
% 4.28/4.48     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 4.28/4.48       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 4.28/4.48  thf('84', plain, (![X23 : $i]: (v1_relat_1 @ (k6_relat_1 @ X23))),
% 4.28/4.48      inference('cnf', [status(esa)], [fc4_funct_1])).
% 4.28/4.48  thf('85', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 4.28/4.48      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.28/4.48  thf('86', plain, (![X23 : $i]: (v1_relat_1 @ (k6_partfun1 @ X23))),
% 4.28/4.48      inference('demod', [status(thm)], ['84', '85'])).
% 4.28/4.48  thf('87', plain,
% 4.28/4.48      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k6_partfun1 @ X0)))),
% 4.28/4.48      inference('demod', [status(thm)], ['83', '86'])).
% 4.28/4.48  thf(t8_boole, axiom,
% 4.28/4.48    (![A:$i,B:$i]:
% 4.28/4.48     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 4.28/4.48  thf('88', plain,
% 4.28/4.48      (![X4 : $i, X5 : $i]:
% 4.28/4.48         (~ (v1_xboole_0 @ X4) | ~ (v1_xboole_0 @ X5) | ((X4) = (X5)))),
% 4.28/4.48      inference('cnf', [status(esa)], [t8_boole])).
% 4.28/4.48  thf('89', plain,
% 4.28/4.48      (![X0 : $i, X1 : $i]:
% 4.28/4.48         (~ (v1_xboole_0 @ X0)
% 4.28/4.48          | ((k6_partfun1 @ X0) = (X1))
% 4.28/4.48          | ~ (v1_xboole_0 @ X1))),
% 4.28/4.48      inference('sup-', [status(thm)], ['87', '88'])).
% 4.28/4.48  thf('90', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 4.28/4.48      inference('split', [status(esa)], ['0'])).
% 4.28/4.48  thf('91', plain,
% 4.28/4.48      ((![X0 : $i]:
% 4.28/4.48          (~ (v2_funct_1 @ (k6_partfun1 @ X0))
% 4.28/4.48           | ~ (v1_xboole_0 @ sk_C)
% 4.28/4.48           | ~ (v1_xboole_0 @ X0)))
% 4.28/4.48         <= (~ ((v2_funct_1 @ sk_C)))),
% 4.28/4.48      inference('sup-', [status(thm)], ['89', '90'])).
% 4.28/4.48  thf('92', plain, (![X24 : $i]: (v2_funct_1 @ (k6_relat_1 @ X24))),
% 4.28/4.48      inference('cnf', [status(esa)], [fc4_funct_1])).
% 4.28/4.48  thf('93', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 4.28/4.48      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.28/4.48  thf('94', plain, (![X24 : $i]: (v2_funct_1 @ (k6_partfun1 @ X24))),
% 4.28/4.48      inference('demod', [status(thm)], ['92', '93'])).
% 4.28/4.48  thf('95', plain,
% 4.28/4.48      ((![X0 : $i]: (~ (v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ X0)))
% 4.28/4.48         <= (~ ((v2_funct_1 @ sk_C)))),
% 4.28/4.48      inference('demod', [status(thm)], ['91', '94'])).
% 4.28/4.48  thf('96', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 4.28/4.48      inference('condensation', [status(thm)], ['95'])).
% 4.28/4.48  thf('97', plain,
% 4.28/4.48      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.28/4.48         = (k5_relat_1 @ sk_C @ sk_D))),
% 4.28/4.48      inference('demod', [status(thm)], ['16', '17'])).
% 4.28/4.48  thf('98', plain,
% 4.28/4.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf(t26_funct_2, axiom,
% 4.28/4.48    (![A:$i,B:$i,C:$i,D:$i]:
% 4.28/4.48     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 4.28/4.48         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.28/4.48       ( ![E:$i]:
% 4.28/4.48         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 4.28/4.48             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 4.28/4.48           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 4.28/4.48             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 4.28/4.48               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 4.28/4.48  thf('99', plain,
% 4.28/4.48      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 4.28/4.48         (~ (v1_funct_1 @ X48)
% 4.28/4.48          | ~ (v1_funct_2 @ X48 @ X49 @ X50)
% 4.28/4.48          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 4.28/4.48          | ~ (v2_funct_1 @ (k1_partfun1 @ X51 @ X49 @ X49 @ X50 @ X52 @ X48))
% 4.28/4.48          | (v2_funct_1 @ X52)
% 4.28/4.48          | ((X50) = (k1_xboole_0))
% 4.28/4.48          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X49)))
% 4.28/4.48          | ~ (v1_funct_2 @ X52 @ X51 @ X49)
% 4.28/4.48          | ~ (v1_funct_1 @ X52))),
% 4.28/4.48      inference('cnf', [status(esa)], [t26_funct_2])).
% 4.28/4.48  thf('100', plain,
% 4.28/4.48      (![X0 : $i, X1 : $i]:
% 4.28/4.48         (~ (v1_funct_1 @ X0)
% 4.28/4.48          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 4.28/4.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 4.28/4.48          | ((sk_A) = (k1_xboole_0))
% 4.28/4.48          | (v2_funct_1 @ X0)
% 4.28/4.48          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 4.28/4.48          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 4.28/4.48          | ~ (v1_funct_1 @ sk_D))),
% 4.28/4.48      inference('sup-', [status(thm)], ['98', '99'])).
% 4.28/4.48  thf('101', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf('102', plain, ((v1_funct_1 @ sk_D)),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf('103', plain,
% 4.28/4.48      (![X0 : $i, X1 : $i]:
% 4.28/4.48         (~ (v1_funct_1 @ X0)
% 4.28/4.48          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 4.28/4.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 4.28/4.48          | ((sk_A) = (k1_xboole_0))
% 4.28/4.48          | (v2_funct_1 @ X0)
% 4.28/4.48          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 4.28/4.48      inference('demod', [status(thm)], ['100', '101', '102'])).
% 4.28/4.48  thf('104', plain,
% 4.28/4.48      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 4.28/4.48        | (v2_funct_1 @ sk_C)
% 4.28/4.48        | ((sk_A) = (k1_xboole_0))
% 4.28/4.48        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 4.28/4.48        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 4.28/4.48        | ~ (v1_funct_1 @ sk_C))),
% 4.28/4.48      inference('sup-', [status(thm)], ['97', '103'])).
% 4.28/4.48  thf('105', plain,
% 4.28/4.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf('106', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf('107', plain, ((v1_funct_1 @ sk_C)),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf('108', plain,
% 4.28/4.48      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 4.28/4.48        | (v2_funct_1 @ sk_C)
% 4.28/4.48        | ((sk_A) = (k1_xboole_0)))),
% 4.28/4.48      inference('demod', [status(thm)], ['104', '105', '106', '107'])).
% 4.28/4.48  thf('109', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 4.28/4.48      inference('demod', [status(thm)], ['51', '54'])).
% 4.28/4.48  thf('110', plain, (![X24 : $i]: (v2_funct_1 @ (k6_partfun1 @ X24))),
% 4.28/4.48      inference('demod', [status(thm)], ['92', '93'])).
% 4.28/4.48  thf('111', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 4.28/4.48      inference('demod', [status(thm)], ['108', '109', '110'])).
% 4.28/4.48  thf('112', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 4.28/4.48      inference('split', [status(esa)], ['0'])).
% 4.28/4.48  thf('113', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 4.28/4.48      inference('sup-', [status(thm)], ['111', '112'])).
% 4.28/4.48  thf(fc4_zfmisc_1, axiom,
% 4.28/4.48    (![A:$i,B:$i]:
% 4.28/4.48     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 4.28/4.48  thf('114', plain,
% 4.28/4.48      (![X8 : $i, X9 : $i]:
% 4.28/4.48         (~ (v1_xboole_0 @ X8) | (v1_xboole_0 @ (k2_zfmisc_1 @ X8 @ X9)))),
% 4.28/4.48      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 4.28/4.48  thf('115', plain,
% 4.28/4.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf(cc1_subset_1, axiom,
% 4.28/4.48    (![A:$i]:
% 4.28/4.48     ( ( v1_xboole_0 @ A ) =>
% 4.28/4.48       ( ![B:$i]:
% 4.28/4.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 4.28/4.48  thf('116', plain,
% 4.28/4.48      (![X10 : $i, X11 : $i]:
% 4.28/4.48         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 4.28/4.48          | (v1_xboole_0 @ X10)
% 4.28/4.48          | ~ (v1_xboole_0 @ X11))),
% 4.28/4.48      inference('cnf', [status(esa)], [cc1_subset_1])).
% 4.28/4.48  thf('117', plain,
% 4.28/4.48      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 4.28/4.48      inference('sup-', [status(thm)], ['115', '116'])).
% 4.28/4.48  thf('118', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C))),
% 4.28/4.48      inference('sup-', [status(thm)], ['114', '117'])).
% 4.28/4.48  thf('119', plain,
% 4.28/4.48      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_C)))
% 4.28/4.48         <= (~ ((v2_funct_1 @ sk_C)))),
% 4.28/4.48      inference('sup-', [status(thm)], ['113', '118'])).
% 4.28/4.48  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 4.28/4.48  thf('120', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.28/4.48      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.28/4.48  thf('121', plain, (((v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 4.28/4.48      inference('demod', [status(thm)], ['119', '120'])).
% 4.28/4.48  thf('122', plain, (((v2_funct_1 @ sk_C))),
% 4.28/4.48      inference('demod', [status(thm)], ['96', '121'])).
% 4.28/4.48  thf('123', plain, (~ ((v2_funct_2 @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_C))),
% 4.28/4.48      inference('split', [status(esa)], ['0'])).
% 4.28/4.48  thf('124', plain, (~ ((v2_funct_2 @ sk_D @ sk_A))),
% 4.28/4.48      inference('sat_resolution*', [status(thm)], ['122', '123'])).
% 4.28/4.48  thf('125', plain, ($false),
% 4.28/4.48      inference('simpl_trail', [status(thm)], ['80', '124'])).
% 4.28/4.48  
% 4.28/4.48  % SZS output end Refutation
% 4.28/4.48  
% 4.32/4.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

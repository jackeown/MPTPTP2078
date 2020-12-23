%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hyMUDzrODr

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:19 EST 2020

% Result     : Theorem 3.45s
% Output     : Refutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 496 expanded)
%              Number of leaves         :   48 ( 160 expanded)
%              Depth                    :   19
%              Number of atoms          : 1316 (9479 expanded)
%              Number of equality atoms :   42 ( 107 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

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
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X41 ) ) ) ) ),
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
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ( ( k1_partfun1 @ X45 @ X46 @ X48 @ X49 @ X44 @ X47 )
        = ( k5_relat_1 @ X44 @ X47 ) ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('22',plain,(
    ! [X19: $i,X20: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X22 @ X21 ) ) @ ( k2_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('25',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ X18 )
      | ( v5_relat_1 @ X17 @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X19: $i,X20: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('32',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X19: $i,X20: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('37',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    v5_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['27','32','37'])).

thf('39',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v5_relat_1 @ X17 @ X18 )
      | ( r1_tarski @ ( k2_relat_1 @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( X30 = X33 )
      | ~ ( r2_relset_1 @ X31 @ X32 @ X30 @ X33 ) ) ),
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

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('52',plain,(
    ! [X43: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('53',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('54',plain,(
    ! [X25: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('55',plain,(
    ! [X50: $i] :
      ( ( k6_partfun1 @ X50 )
      = ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('56',plain,(
    ! [X25: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X25 ) )
      = X25 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('58',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v5_relat_1 @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('59',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v5_relat_1 @ X17 @ X18 )
      | ( r1_tarski @ ( k2_relat_1 @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('61',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['30','31'])).

thf('63',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('65',plain,(
    ! [X25: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X25 ) )
      = X25 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('66',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['44','53','56','63','64','65'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('67',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k2_relat_1 @ X35 )
       != X34 )
      | ( v2_funct_2 @ X35 @ X34 )
      | ~ ( v5_relat_1 @ X35 @ X34 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('68',plain,(
    ! [X35: $i] :
      ( ~ ( v1_relat_1 @ X35 )
      | ~ ( v5_relat_1 @ X35 @ ( k2_relat_1 @ X35 ) )
      | ( v2_funct_2 @ X35 @ ( k2_relat_1 @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

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
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ X18 )
      | ( v5_relat_1 @ X17 @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X35: $i] :
      ( ( v2_funct_2 @ X35 @ ( k2_relat_1 @ X35 ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(clc,[status(thm)],['68','72'])).

thf('74',plain,
    ( ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['66','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['30','31'])).

thf('76',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( $false
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['1','76'])).

thf(fc3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ B )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('78',plain,(
    ! [X9: $i,X10: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X9 @ X10 ) )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf('79',plain,(
    ! [X43: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('80',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_xboole_0 @ X13 )
      | ~ ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ( v1_xboole_0 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('83',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_xboole_0 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ( X7 = X8 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k6_partfun1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('86',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_funct_1 @ ( k6_partfun1 @ X0 ) )
        | ~ ( v1_xboole_0 @ sk_C )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('87',plain,(
    ! [X26: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('88',plain,(
    ! [X50: $i] :
      ( ( k6_partfun1 @ X50 )
      = ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('89',plain,(
    ! [X26: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X26 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ sk_C )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['86','89'])).

thf('91',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(condensation,[status(thm)],['90'])).

thf('92',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('93',plain,(
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

thf('94',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_2 @ X51 @ X52 @ X53 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X54 @ X52 @ X52 @ X53 @ X55 @ X51 ) )
      | ( v2_funct_1 @ X55 )
      | ( X53 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X52 ) ) )
      | ~ ( v1_funct_2 @ X55 @ X54 @ X52 )
      | ~ ( v1_funct_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['92','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['99','100','101','102'])).

thf('104',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('105',plain,(
    ! [X26: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X26 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('106',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('108',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('109',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_xboole_0 @ X11 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('110',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_xboole_0 @ X13 )
      | ~ ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('112',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['109','112'])).

thf('114',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_C ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['108','113'])).

thf('115',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['69'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('116',plain,(
    ! [X4: $i] :
      ( r1_xboole_0 @ X4 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('117',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['115','118'])).

thf('120',plain,
    ( ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['114','119'])).

thf('121',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['91','120'])).

thf('122',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('123',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['121','122'])).

thf('124',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['77','123'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hyMUDzrODr
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 13:26:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 3.45/3.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.45/3.65  % Solved by: fo/fo7.sh
% 3.45/3.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.45/3.65  % done 3366 iterations in 3.181s
% 3.45/3.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.45/3.65  % SZS output start Refutation
% 3.45/3.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.45/3.65  thf(sk_D_type, type, sk_D: $i).
% 3.45/3.65  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 3.45/3.65  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 3.45/3.65  thf(sk_C_type, type, sk_C: $i).
% 3.45/3.65  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.45/3.65  thf(sk_B_type, type, sk_B: $i).
% 3.45/3.65  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.45/3.65  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 3.45/3.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.45/3.65  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.45/3.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.45/3.65  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.45/3.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.45/3.65  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.45/3.65  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.45/3.65  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.45/3.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.45/3.65  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.45/3.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.45/3.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.45/3.65  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.45/3.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.45/3.65  thf(sk_A_type, type, sk_A: $i).
% 3.45/3.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.45/3.65  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.45/3.65  thf(t29_funct_2, conjecture,
% 3.45/3.65    (![A:$i,B:$i,C:$i]:
% 3.45/3.65     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.45/3.65         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.45/3.65       ( ![D:$i]:
% 3.45/3.65         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.45/3.65             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.45/3.65           ( ( r2_relset_1 @
% 3.45/3.65               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.45/3.65               ( k6_partfun1 @ A ) ) =>
% 3.45/3.65             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 3.45/3.65  thf(zf_stmt_0, negated_conjecture,
% 3.45/3.65    (~( ![A:$i,B:$i,C:$i]:
% 3.45/3.65        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.45/3.65            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.45/3.65          ( ![D:$i]:
% 3.45/3.65            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.45/3.65                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.45/3.65              ( ( r2_relset_1 @
% 3.45/3.65                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.45/3.65                  ( k6_partfun1 @ A ) ) =>
% 3.45/3.65                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 3.45/3.65    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 3.45/3.65  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.65  thf('1', plain,
% 3.45/3.65      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 3.45/3.65      inference('split', [status(esa)], ['0'])).
% 3.45/3.65  thf('2', plain,
% 3.45/3.65      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.65  thf('3', plain,
% 3.45/3.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.65  thf(dt_k1_partfun1, axiom,
% 3.45/3.65    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.45/3.65     ( ( ( v1_funct_1 @ E ) & 
% 3.45/3.65         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.45/3.65         ( v1_funct_1 @ F ) & 
% 3.45/3.65         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.45/3.65       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 3.45/3.65         ( m1_subset_1 @
% 3.45/3.65           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.45/3.65           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 3.45/3.65  thf('4', plain,
% 3.45/3.65      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 3.45/3.65         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 3.45/3.65          | ~ (v1_funct_1 @ X36)
% 3.45/3.65          | ~ (v1_funct_1 @ X39)
% 3.45/3.65          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 3.45/3.65          | (m1_subset_1 @ (k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39) @ 
% 3.45/3.65             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X41))))),
% 3.45/3.65      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.45/3.65  thf('5', plain,
% 3.45/3.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.45/3.65         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.45/3.65           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.45/3.65          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.45/3.65          | ~ (v1_funct_1 @ X1)
% 3.45/3.65          | ~ (v1_funct_1 @ sk_C))),
% 3.45/3.65      inference('sup-', [status(thm)], ['3', '4'])).
% 3.45/3.65  thf('6', plain, ((v1_funct_1 @ sk_C)),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.65  thf('7', plain,
% 3.45/3.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.45/3.65         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.45/3.65           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.45/3.65          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.45/3.65          | ~ (v1_funct_1 @ X1))),
% 3.45/3.65      inference('demod', [status(thm)], ['5', '6'])).
% 3.45/3.65  thf('8', plain,
% 3.45/3.65      ((~ (v1_funct_1 @ sk_D)
% 3.45/3.65        | (m1_subset_1 @ 
% 3.45/3.65           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.45/3.65           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.45/3.65      inference('sup-', [status(thm)], ['2', '7'])).
% 3.45/3.65  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.65  thf('10', plain,
% 3.45/3.65      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.65  thf('11', plain,
% 3.45/3.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.65  thf(redefinition_k1_partfun1, axiom,
% 3.45/3.65    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.45/3.65     ( ( ( v1_funct_1 @ E ) & 
% 3.45/3.65         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.45/3.65         ( v1_funct_1 @ F ) & 
% 3.45/3.65         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.45/3.65       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 3.45/3.65  thf('12', plain,
% 3.45/3.65      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 3.45/3.65         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 3.45/3.65          | ~ (v1_funct_1 @ X44)
% 3.45/3.65          | ~ (v1_funct_1 @ X47)
% 3.45/3.65          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 3.45/3.65          | ((k1_partfun1 @ X45 @ X46 @ X48 @ X49 @ X44 @ X47)
% 3.45/3.65              = (k5_relat_1 @ X44 @ X47)))),
% 3.45/3.65      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 3.45/3.65  thf('13', plain,
% 3.45/3.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.45/3.65         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 3.45/3.65            = (k5_relat_1 @ sk_C @ X0))
% 3.45/3.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.45/3.65          | ~ (v1_funct_1 @ X0)
% 3.45/3.65          | ~ (v1_funct_1 @ sk_C))),
% 3.45/3.65      inference('sup-', [status(thm)], ['11', '12'])).
% 3.45/3.65  thf('14', plain, ((v1_funct_1 @ sk_C)),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.65  thf('15', plain,
% 3.45/3.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.45/3.65         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 3.45/3.65            = (k5_relat_1 @ sk_C @ X0))
% 3.45/3.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.45/3.65          | ~ (v1_funct_1 @ X0))),
% 3.45/3.65      inference('demod', [status(thm)], ['13', '14'])).
% 3.45/3.65  thf('16', plain,
% 3.45/3.65      ((~ (v1_funct_1 @ sk_D)
% 3.45/3.65        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.45/3.65            = (k5_relat_1 @ sk_C @ sk_D)))),
% 3.45/3.65      inference('sup-', [status(thm)], ['10', '15'])).
% 3.45/3.65  thf('17', plain, ((v1_funct_1 @ sk_D)),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.65  thf('18', plain,
% 3.45/3.65      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.45/3.65         = (k5_relat_1 @ sk_C @ sk_D))),
% 3.45/3.65      inference('demod', [status(thm)], ['16', '17'])).
% 3.45/3.65  thf('19', plain,
% 3.45/3.65      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 3.45/3.65        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.45/3.65      inference('demod', [status(thm)], ['8', '9', '18'])).
% 3.45/3.65  thf(cc2_relat_1, axiom,
% 3.45/3.65    (![A:$i]:
% 3.45/3.65     ( ( v1_relat_1 @ A ) =>
% 3.45/3.65       ( ![B:$i]:
% 3.45/3.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 3.45/3.65  thf('20', plain,
% 3.45/3.65      (![X15 : $i, X16 : $i]:
% 3.45/3.65         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 3.45/3.65          | (v1_relat_1 @ X15)
% 3.45/3.65          | ~ (v1_relat_1 @ X16))),
% 3.45/3.65      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.45/3.65  thf('21', plain,
% 3.45/3.65      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 3.45/3.65        | (v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))),
% 3.45/3.65      inference('sup-', [status(thm)], ['19', '20'])).
% 3.45/3.65  thf(fc6_relat_1, axiom,
% 3.45/3.65    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 3.45/3.65  thf('22', plain,
% 3.45/3.65      (![X19 : $i, X20 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X19 @ X20))),
% 3.45/3.65      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.45/3.65  thf('23', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))),
% 3.45/3.65      inference('demod', [status(thm)], ['21', '22'])).
% 3.45/3.65  thf(t45_relat_1, axiom,
% 3.45/3.65    (![A:$i]:
% 3.45/3.65     ( ( v1_relat_1 @ A ) =>
% 3.45/3.65       ( ![B:$i]:
% 3.45/3.65         ( ( v1_relat_1 @ B ) =>
% 3.45/3.65           ( r1_tarski @
% 3.45/3.65             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 3.45/3.65  thf('24', plain,
% 3.45/3.65      (![X21 : $i, X22 : $i]:
% 3.45/3.65         (~ (v1_relat_1 @ X21)
% 3.45/3.65          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X22 @ X21)) @ 
% 3.45/3.65             (k2_relat_1 @ X21))
% 3.45/3.65          | ~ (v1_relat_1 @ X22))),
% 3.45/3.65      inference('cnf', [status(esa)], [t45_relat_1])).
% 3.45/3.65  thf(d19_relat_1, axiom,
% 3.45/3.65    (![A:$i,B:$i]:
% 3.45/3.65     ( ( v1_relat_1 @ B ) =>
% 3.45/3.65       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 3.45/3.65  thf('25', plain,
% 3.45/3.65      (![X17 : $i, X18 : $i]:
% 3.45/3.65         (~ (r1_tarski @ (k2_relat_1 @ X17) @ X18)
% 3.45/3.65          | (v5_relat_1 @ X17 @ X18)
% 3.45/3.65          | ~ (v1_relat_1 @ X17))),
% 3.45/3.65      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.45/3.65  thf('26', plain,
% 3.45/3.65      (![X0 : $i, X1 : $i]:
% 3.45/3.65         (~ (v1_relat_1 @ X1)
% 3.45/3.65          | ~ (v1_relat_1 @ X0)
% 3.45/3.65          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 3.45/3.65          | (v5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 3.45/3.65      inference('sup-', [status(thm)], ['24', '25'])).
% 3.45/3.65  thf('27', plain,
% 3.45/3.65      (((v5_relat_1 @ (k5_relat_1 @ sk_C @ sk_D) @ (k2_relat_1 @ sk_D))
% 3.45/3.65        | ~ (v1_relat_1 @ sk_D)
% 3.45/3.65        | ~ (v1_relat_1 @ sk_C))),
% 3.45/3.65      inference('sup-', [status(thm)], ['23', '26'])).
% 3.45/3.65  thf('28', plain,
% 3.45/3.65      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.65  thf('29', plain,
% 3.45/3.65      (![X15 : $i, X16 : $i]:
% 3.45/3.65         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 3.45/3.65          | (v1_relat_1 @ X15)
% 3.45/3.65          | ~ (v1_relat_1 @ X16))),
% 3.45/3.65      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.45/3.65  thf('30', plain,
% 3.45/3.65      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 3.45/3.65      inference('sup-', [status(thm)], ['28', '29'])).
% 3.45/3.65  thf('31', plain,
% 3.45/3.65      (![X19 : $i, X20 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X19 @ X20))),
% 3.45/3.65      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.45/3.65  thf('32', plain, ((v1_relat_1 @ sk_D)),
% 3.45/3.65      inference('demod', [status(thm)], ['30', '31'])).
% 3.45/3.65  thf('33', plain,
% 3.45/3.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.65  thf('34', plain,
% 3.45/3.65      (![X15 : $i, X16 : $i]:
% 3.45/3.65         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 3.45/3.65          | (v1_relat_1 @ X15)
% 3.45/3.65          | ~ (v1_relat_1 @ X16))),
% 3.45/3.65      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.45/3.65  thf('35', plain,
% 3.45/3.65      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 3.45/3.65      inference('sup-', [status(thm)], ['33', '34'])).
% 3.45/3.65  thf('36', plain,
% 3.45/3.65      (![X19 : $i, X20 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X19 @ X20))),
% 3.45/3.65      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.45/3.65  thf('37', plain, ((v1_relat_1 @ sk_C)),
% 3.45/3.65      inference('demod', [status(thm)], ['35', '36'])).
% 3.45/3.65  thf('38', plain,
% 3.45/3.65      ((v5_relat_1 @ (k5_relat_1 @ sk_C @ sk_D) @ (k2_relat_1 @ sk_D))),
% 3.45/3.65      inference('demod', [status(thm)], ['27', '32', '37'])).
% 3.45/3.65  thf('39', plain,
% 3.45/3.65      (![X17 : $i, X18 : $i]:
% 3.45/3.65         (~ (v5_relat_1 @ X17 @ X18)
% 3.45/3.65          | (r1_tarski @ (k2_relat_1 @ X17) @ X18)
% 3.45/3.65          | ~ (v1_relat_1 @ X17))),
% 3.45/3.65      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.45/3.65  thf('40', plain,
% 3.45/3.65      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 3.45/3.65        | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ 
% 3.45/3.65           (k2_relat_1 @ sk_D)))),
% 3.45/3.65      inference('sup-', [status(thm)], ['38', '39'])).
% 3.45/3.65  thf('41', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))),
% 3.45/3.65      inference('demod', [status(thm)], ['21', '22'])).
% 3.45/3.65  thf('42', plain,
% 3.45/3.65      ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ 
% 3.45/3.65        (k2_relat_1 @ sk_D))),
% 3.45/3.65      inference('demod', [status(thm)], ['40', '41'])).
% 3.45/3.65  thf(d10_xboole_0, axiom,
% 3.45/3.65    (![A:$i,B:$i]:
% 3.45/3.65     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.45/3.65  thf('43', plain,
% 3.45/3.65      (![X0 : $i, X2 : $i]:
% 3.45/3.65         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.45/3.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.45/3.65  thf('44', plain,
% 3.45/3.65      ((~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 3.45/3.65           (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 3.45/3.65        | ((k2_relat_1 @ sk_D) = (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))))),
% 3.45/3.65      inference('sup-', [status(thm)], ['42', '43'])).
% 3.45/3.65  thf('45', plain,
% 3.45/3.65      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.45/3.65        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.45/3.65        (k6_partfun1 @ sk_A))),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.65  thf('46', plain,
% 3.45/3.65      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.45/3.65         = (k5_relat_1 @ sk_C @ sk_D))),
% 3.45/3.65      inference('demod', [status(thm)], ['16', '17'])).
% 3.45/3.65  thf('47', plain,
% 3.45/3.65      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 3.45/3.65        (k6_partfun1 @ sk_A))),
% 3.45/3.65      inference('demod', [status(thm)], ['45', '46'])).
% 3.45/3.65  thf('48', plain,
% 3.45/3.65      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 3.45/3.65        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.45/3.65      inference('demod', [status(thm)], ['8', '9', '18'])).
% 3.45/3.65  thf(redefinition_r2_relset_1, axiom,
% 3.45/3.65    (![A:$i,B:$i,C:$i,D:$i]:
% 3.45/3.65     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.45/3.65         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.45/3.65       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.45/3.65  thf('49', plain,
% 3.45/3.65      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 3.45/3.65         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 3.45/3.65          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 3.45/3.65          | ((X30) = (X33))
% 3.45/3.65          | ~ (r2_relset_1 @ X31 @ X32 @ X30 @ X33))),
% 3.45/3.65      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.45/3.65  thf('50', plain,
% 3.45/3.65      (![X0 : $i]:
% 3.45/3.65         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 3.45/3.65          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 3.45/3.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.45/3.65      inference('sup-', [status(thm)], ['48', '49'])).
% 3.45/3.65  thf('51', plain,
% 3.45/3.65      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 3.45/3.65           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.45/3.65        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 3.45/3.65      inference('sup-', [status(thm)], ['47', '50'])).
% 3.45/3.65  thf(dt_k6_partfun1, axiom,
% 3.45/3.65    (![A:$i]:
% 3.45/3.65     ( ( m1_subset_1 @
% 3.45/3.65         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 3.45/3.65       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 3.45/3.65  thf('52', plain,
% 3.45/3.65      (![X43 : $i]:
% 3.45/3.65         (m1_subset_1 @ (k6_partfun1 @ X43) @ 
% 3.45/3.65          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X43)))),
% 3.45/3.65      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 3.45/3.65  thf('53', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 3.45/3.65      inference('demod', [status(thm)], ['51', '52'])).
% 3.45/3.65  thf(t71_relat_1, axiom,
% 3.45/3.65    (![A:$i]:
% 3.45/3.65     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 3.45/3.65       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 3.45/3.65  thf('54', plain, (![X25 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 3.45/3.65      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.45/3.65  thf(redefinition_k6_partfun1, axiom,
% 3.45/3.65    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 3.45/3.65  thf('55', plain, (![X50 : $i]: ((k6_partfun1 @ X50) = (k6_relat_1 @ X50))),
% 3.45/3.65      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.45/3.65  thf('56', plain, (![X25 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X25)) = (X25))),
% 3.45/3.65      inference('demod', [status(thm)], ['54', '55'])).
% 3.45/3.65  thf('57', plain,
% 3.45/3.65      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.65  thf(cc2_relset_1, axiom,
% 3.45/3.65    (![A:$i,B:$i,C:$i]:
% 3.45/3.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.45/3.65       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.45/3.65  thf('58', plain,
% 3.45/3.65      (![X27 : $i, X28 : $i, X29 : $i]:
% 3.45/3.65         ((v5_relat_1 @ X27 @ X29)
% 3.45/3.65          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 3.45/3.65      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.45/3.65  thf('59', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 3.45/3.65      inference('sup-', [status(thm)], ['57', '58'])).
% 3.45/3.65  thf('60', plain,
% 3.45/3.65      (![X17 : $i, X18 : $i]:
% 3.45/3.65         (~ (v5_relat_1 @ X17 @ X18)
% 3.45/3.65          | (r1_tarski @ (k2_relat_1 @ X17) @ X18)
% 3.45/3.65          | ~ (v1_relat_1 @ X17))),
% 3.45/3.65      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.45/3.65  thf('61', plain,
% 3.45/3.65      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 3.45/3.65      inference('sup-', [status(thm)], ['59', '60'])).
% 3.45/3.65  thf('62', plain, ((v1_relat_1 @ sk_D)),
% 3.45/3.65      inference('demod', [status(thm)], ['30', '31'])).
% 3.45/3.65  thf('63', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 3.45/3.65      inference('demod', [status(thm)], ['61', '62'])).
% 3.45/3.65  thf('64', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 3.45/3.65      inference('demod', [status(thm)], ['51', '52'])).
% 3.45/3.65  thf('65', plain, (![X25 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X25)) = (X25))),
% 3.45/3.65      inference('demod', [status(thm)], ['54', '55'])).
% 3.45/3.65  thf('66', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.45/3.65      inference('demod', [status(thm)], ['44', '53', '56', '63', '64', '65'])).
% 3.45/3.65  thf(d3_funct_2, axiom,
% 3.45/3.65    (![A:$i,B:$i]:
% 3.45/3.65     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 3.45/3.65       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 3.45/3.65  thf('67', plain,
% 3.45/3.65      (![X34 : $i, X35 : $i]:
% 3.45/3.65         (((k2_relat_1 @ X35) != (X34))
% 3.45/3.65          | (v2_funct_2 @ X35 @ X34)
% 3.45/3.65          | ~ (v5_relat_1 @ X35 @ X34)
% 3.45/3.65          | ~ (v1_relat_1 @ X35))),
% 3.45/3.65      inference('cnf', [status(esa)], [d3_funct_2])).
% 3.45/3.65  thf('68', plain,
% 3.45/3.65      (![X35 : $i]:
% 3.45/3.65         (~ (v1_relat_1 @ X35)
% 3.45/3.65          | ~ (v5_relat_1 @ X35 @ (k2_relat_1 @ X35))
% 3.45/3.65          | (v2_funct_2 @ X35 @ (k2_relat_1 @ X35)))),
% 3.45/3.65      inference('simplify', [status(thm)], ['67'])).
% 3.45/3.65  thf('69', plain,
% 3.45/3.65      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 3.45/3.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.45/3.65  thf('70', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.45/3.65      inference('simplify', [status(thm)], ['69'])).
% 3.45/3.65  thf('71', plain,
% 3.45/3.65      (![X17 : $i, X18 : $i]:
% 3.45/3.65         (~ (r1_tarski @ (k2_relat_1 @ X17) @ X18)
% 3.45/3.65          | (v5_relat_1 @ X17 @ X18)
% 3.45/3.65          | ~ (v1_relat_1 @ X17))),
% 3.45/3.65      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.45/3.65  thf('72', plain,
% 3.45/3.65      (![X0 : $i]:
% 3.45/3.65         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 3.45/3.65      inference('sup-', [status(thm)], ['70', '71'])).
% 3.45/3.65  thf('73', plain,
% 3.45/3.65      (![X35 : $i]:
% 3.45/3.65         ((v2_funct_2 @ X35 @ (k2_relat_1 @ X35)) | ~ (v1_relat_1 @ X35))),
% 3.45/3.65      inference('clc', [status(thm)], ['68', '72'])).
% 3.45/3.65  thf('74', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 3.45/3.65      inference('sup+', [status(thm)], ['66', '73'])).
% 3.45/3.65  thf('75', plain, ((v1_relat_1 @ sk_D)),
% 3.45/3.65      inference('demod', [status(thm)], ['30', '31'])).
% 3.45/3.65  thf('76', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 3.45/3.65      inference('demod', [status(thm)], ['74', '75'])).
% 3.45/3.65  thf('77', plain, (($false) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 3.45/3.65      inference('demod', [status(thm)], ['1', '76'])).
% 3.45/3.65  thf(fc3_zfmisc_1, axiom,
% 3.45/3.65    (![A:$i,B:$i]:
% 3.45/3.65     ( ( v1_xboole_0 @ B ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 3.45/3.65  thf('78', plain,
% 3.45/3.65      (![X9 : $i, X10 : $i]:
% 3.45/3.65         ((v1_xboole_0 @ (k2_zfmisc_1 @ X9 @ X10)) | ~ (v1_xboole_0 @ X10))),
% 3.45/3.65      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 3.45/3.65  thf('79', plain,
% 3.45/3.65      (![X43 : $i]:
% 3.45/3.65         (m1_subset_1 @ (k6_partfun1 @ X43) @ 
% 3.45/3.65          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X43)))),
% 3.45/3.65      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 3.45/3.65  thf(cc1_subset_1, axiom,
% 3.45/3.65    (![A:$i]:
% 3.45/3.65     ( ( v1_xboole_0 @ A ) =>
% 3.45/3.65       ( ![B:$i]:
% 3.45/3.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 3.45/3.65  thf('80', plain,
% 3.45/3.65      (![X13 : $i, X14 : $i]:
% 3.45/3.65         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 3.45/3.65          | (v1_xboole_0 @ X13)
% 3.45/3.65          | ~ (v1_xboole_0 @ X14))),
% 3.45/3.65      inference('cnf', [status(esa)], [cc1_subset_1])).
% 3.45/3.65  thf('81', plain,
% 3.45/3.65      (![X0 : $i]:
% 3.45/3.65         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X0))
% 3.45/3.65          | (v1_xboole_0 @ (k6_partfun1 @ X0)))),
% 3.45/3.65      inference('sup-', [status(thm)], ['79', '80'])).
% 3.45/3.65  thf('82', plain,
% 3.45/3.65      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k6_partfun1 @ X0)))),
% 3.45/3.65      inference('sup-', [status(thm)], ['78', '81'])).
% 3.45/3.65  thf(t8_boole, axiom,
% 3.45/3.65    (![A:$i,B:$i]:
% 3.45/3.65     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 3.45/3.65  thf('83', plain,
% 3.45/3.65      (![X7 : $i, X8 : $i]:
% 3.45/3.65         (~ (v1_xboole_0 @ X7) | ~ (v1_xboole_0 @ X8) | ((X7) = (X8)))),
% 3.45/3.65      inference('cnf', [status(esa)], [t8_boole])).
% 3.45/3.65  thf('84', plain,
% 3.45/3.65      (![X0 : $i, X1 : $i]:
% 3.45/3.65         (~ (v1_xboole_0 @ X0)
% 3.45/3.65          | ((k6_partfun1 @ X0) = (X1))
% 3.45/3.65          | ~ (v1_xboole_0 @ X1))),
% 3.45/3.65      inference('sup-', [status(thm)], ['82', '83'])).
% 3.45/3.65  thf('85', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.45/3.65      inference('split', [status(esa)], ['0'])).
% 3.45/3.65  thf('86', plain,
% 3.45/3.65      ((![X0 : $i]:
% 3.45/3.65          (~ (v2_funct_1 @ (k6_partfun1 @ X0))
% 3.45/3.65           | ~ (v1_xboole_0 @ sk_C)
% 3.45/3.65           | ~ (v1_xboole_0 @ X0)))
% 3.45/3.65         <= (~ ((v2_funct_1 @ sk_C)))),
% 3.45/3.65      inference('sup-', [status(thm)], ['84', '85'])).
% 3.45/3.65  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 3.45/3.65  thf('87', plain, (![X26 : $i]: (v2_funct_1 @ (k6_relat_1 @ X26))),
% 3.45/3.65      inference('cnf', [status(esa)], [t52_funct_1])).
% 3.45/3.65  thf('88', plain, (![X50 : $i]: ((k6_partfun1 @ X50) = (k6_relat_1 @ X50))),
% 3.45/3.65      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.45/3.65  thf('89', plain, (![X26 : $i]: (v2_funct_1 @ (k6_partfun1 @ X26))),
% 3.45/3.65      inference('demod', [status(thm)], ['87', '88'])).
% 3.45/3.65  thf('90', plain,
% 3.45/3.65      ((![X0 : $i]: (~ (v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ X0)))
% 3.45/3.65         <= (~ ((v2_funct_1 @ sk_C)))),
% 3.45/3.65      inference('demod', [status(thm)], ['86', '89'])).
% 3.45/3.65  thf('91', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.45/3.65      inference('condensation', [status(thm)], ['90'])).
% 3.45/3.65  thf('92', plain,
% 3.45/3.65      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.45/3.65         = (k5_relat_1 @ sk_C @ sk_D))),
% 3.45/3.65      inference('demod', [status(thm)], ['16', '17'])).
% 3.45/3.65  thf('93', plain,
% 3.45/3.65      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.65  thf(t26_funct_2, axiom,
% 3.45/3.65    (![A:$i,B:$i,C:$i,D:$i]:
% 3.45/3.65     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.45/3.65         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.45/3.65       ( ![E:$i]:
% 3.45/3.65         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.45/3.65             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.45/3.65           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 3.45/3.65             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 3.45/3.65               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 3.45/3.65  thf('94', plain,
% 3.45/3.65      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 3.45/3.65         (~ (v1_funct_1 @ X51)
% 3.45/3.65          | ~ (v1_funct_2 @ X51 @ X52 @ X53)
% 3.45/3.65          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53)))
% 3.45/3.65          | ~ (v2_funct_1 @ (k1_partfun1 @ X54 @ X52 @ X52 @ X53 @ X55 @ X51))
% 3.45/3.65          | (v2_funct_1 @ X55)
% 3.45/3.65          | ((X53) = (k1_xboole_0))
% 3.45/3.65          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X52)))
% 3.45/3.65          | ~ (v1_funct_2 @ X55 @ X54 @ X52)
% 3.45/3.65          | ~ (v1_funct_1 @ X55))),
% 3.45/3.65      inference('cnf', [status(esa)], [t26_funct_2])).
% 3.45/3.65  thf('95', plain,
% 3.45/3.65      (![X0 : $i, X1 : $i]:
% 3.45/3.65         (~ (v1_funct_1 @ X0)
% 3.45/3.65          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.45/3.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.45/3.65          | ((sk_A) = (k1_xboole_0))
% 3.45/3.65          | (v2_funct_1 @ X0)
% 3.45/3.65          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 3.45/3.65          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.45/3.65          | ~ (v1_funct_1 @ sk_D))),
% 3.45/3.65      inference('sup-', [status(thm)], ['93', '94'])).
% 3.45/3.65  thf('96', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.65  thf('97', plain, ((v1_funct_1 @ sk_D)),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.65  thf('98', plain,
% 3.45/3.65      (![X0 : $i, X1 : $i]:
% 3.45/3.65         (~ (v1_funct_1 @ X0)
% 3.45/3.65          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.45/3.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.45/3.65          | ((sk_A) = (k1_xboole_0))
% 3.45/3.65          | (v2_funct_1 @ X0)
% 3.45/3.65          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 3.45/3.65      inference('demod', [status(thm)], ['95', '96', '97'])).
% 3.45/3.65  thf('99', plain,
% 3.45/3.65      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 3.45/3.65        | (v2_funct_1 @ sk_C)
% 3.45/3.65        | ((sk_A) = (k1_xboole_0))
% 3.45/3.65        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 3.45/3.65        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.45/3.65        | ~ (v1_funct_1 @ sk_C))),
% 3.45/3.65      inference('sup-', [status(thm)], ['92', '98'])).
% 3.45/3.65  thf('100', plain,
% 3.45/3.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.65  thf('101', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.65  thf('102', plain, ((v1_funct_1 @ sk_C)),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.65  thf('103', plain,
% 3.45/3.65      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 3.45/3.65        | (v2_funct_1 @ sk_C)
% 3.45/3.65        | ((sk_A) = (k1_xboole_0)))),
% 3.45/3.65      inference('demod', [status(thm)], ['99', '100', '101', '102'])).
% 3.45/3.65  thf('104', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 3.45/3.65      inference('demod', [status(thm)], ['51', '52'])).
% 3.45/3.65  thf('105', plain, (![X26 : $i]: (v2_funct_1 @ (k6_partfun1 @ X26))),
% 3.45/3.65      inference('demod', [status(thm)], ['87', '88'])).
% 3.45/3.65  thf('106', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 3.45/3.65      inference('demod', [status(thm)], ['103', '104', '105'])).
% 3.45/3.65  thf('107', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.45/3.65      inference('split', [status(esa)], ['0'])).
% 3.45/3.65  thf('108', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.45/3.65      inference('sup-', [status(thm)], ['106', '107'])).
% 3.45/3.65  thf(fc4_zfmisc_1, axiom,
% 3.45/3.65    (![A:$i,B:$i]:
% 3.45/3.65     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 3.45/3.65  thf('109', plain,
% 3.45/3.65      (![X11 : $i, X12 : $i]:
% 3.45/3.65         (~ (v1_xboole_0 @ X11) | (v1_xboole_0 @ (k2_zfmisc_1 @ X11 @ X12)))),
% 3.45/3.65      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 3.45/3.65  thf('110', plain,
% 3.45/3.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.45/3.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.45/3.65  thf('111', plain,
% 3.45/3.65      (![X13 : $i, X14 : $i]:
% 3.45/3.65         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 3.45/3.65          | (v1_xboole_0 @ X13)
% 3.45/3.65          | ~ (v1_xboole_0 @ X14))),
% 3.45/3.65      inference('cnf', [status(esa)], [cc1_subset_1])).
% 3.45/3.65  thf('112', plain,
% 3.45/3.65      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 3.45/3.65      inference('sup-', [status(thm)], ['110', '111'])).
% 3.45/3.65  thf('113', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C))),
% 3.45/3.65      inference('sup-', [status(thm)], ['109', '112'])).
% 3.45/3.65  thf('114', plain,
% 3.45/3.65      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_C)))
% 3.45/3.65         <= (~ ((v2_funct_1 @ sk_C)))),
% 3.45/3.65      inference('sup-', [status(thm)], ['108', '113'])).
% 3.45/3.65  thf('115', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.45/3.65      inference('simplify', [status(thm)], ['69'])).
% 3.45/3.65  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 3.45/3.65  thf('116', plain, (![X4 : $i]: (r1_xboole_0 @ X4 @ k1_xboole_0)),
% 3.45/3.65      inference('cnf', [status(esa)], [t65_xboole_1])).
% 3.45/3.65  thf(t69_xboole_1, axiom,
% 3.45/3.65    (![A:$i,B:$i]:
% 3.45/3.65     ( ( ~( v1_xboole_0 @ B ) ) =>
% 3.45/3.65       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 3.45/3.65  thf('117', plain,
% 3.45/3.65      (![X5 : $i, X6 : $i]:
% 3.45/3.65         (~ (r1_xboole_0 @ X5 @ X6)
% 3.45/3.65          | ~ (r1_tarski @ X5 @ X6)
% 3.45/3.65          | (v1_xboole_0 @ X5))),
% 3.45/3.65      inference('cnf', [status(esa)], [t69_xboole_1])).
% 3.45/3.65  thf('118', plain,
% 3.45/3.65      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 3.45/3.65      inference('sup-', [status(thm)], ['116', '117'])).
% 3.45/3.65  thf('119', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.45/3.65      inference('sup-', [status(thm)], ['115', '118'])).
% 3.45/3.65  thf('120', plain, (((v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.45/3.65      inference('demod', [status(thm)], ['114', '119'])).
% 3.45/3.65  thf('121', plain, (((v2_funct_1 @ sk_C))),
% 3.45/3.65      inference('demod', [status(thm)], ['91', '120'])).
% 3.45/3.65  thf('122', plain, (~ ((v2_funct_2 @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_C))),
% 3.45/3.65      inference('split', [status(esa)], ['0'])).
% 3.45/3.65  thf('123', plain, (~ ((v2_funct_2 @ sk_D @ sk_A))),
% 3.45/3.65      inference('sat_resolution*', [status(thm)], ['121', '122'])).
% 3.45/3.65  thf('124', plain, ($false),
% 3.45/3.65      inference('simpl_trail', [status(thm)], ['77', '123'])).
% 3.45/3.65  
% 3.45/3.65  % SZS output end Refutation
% 3.45/3.65  
% 3.49/3.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tWLLMeLj8T

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:18 EST 2020

% Result     : Theorem 4.24s
% Output     : Refutation 4.24s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 503 expanded)
%              Number of leaves         :   48 ( 163 expanded)
%              Depth                    :   19
%              Number of atoms          : 1340 (9533 expanded)
%              Number of equality atoms :   43 ( 107 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( ( k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46 )
        = ( k5_relat_1 @ X43 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_1 @ X0 )
        = ( k5_relat_1 @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_1 @ X0 )
        = ( k5_relat_1 @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
      = ( k5_relat_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
    = ( k5_relat_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9','18'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('20',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('22',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('23',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('24',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X21 @ X20 ) ) @ ( k2_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('25',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X16 ) @ X17 )
      | ( v5_relat_1 @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( v5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( v5_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('32',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('37',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    v5_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['27','32','37'])).

thf('39',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v5_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k2_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('42',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) ) @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('43',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('44',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) ) )
    | ( ( k2_relat_1 @ sk_D )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
    = ( k5_relat_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('47',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9','18'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('49',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( X29 = X32 )
      | ~ ( r2_relset_1 @ X30 @ X31 @ X29 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C_1 @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C_1 @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('52',plain,(
    ! [X42: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('53',plain,
    ( ( k5_relat_1 @ sk_C_1 @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('54',plain,(
    ! [X23: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('55',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('56',plain,(
    ! [X23: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X23 ) )
      = X23 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('58',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v5_relat_1 @ X26 @ X28 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('59',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v5_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k2_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
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
    ( ( k5_relat_1 @ sk_C_1 @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('65',plain,(
    ! [X23: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X23 ) )
      = X23 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('66',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['44','53','56','63','64','65'])).

thf('67',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('68',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X16 ) @ X17 )
      | ( v5_relat_1 @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('71',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k2_relat_1 @ X34 )
       != X33 )
      | ( v2_funct_2 @ X34 @ X33 )
      | ~ ( v5_relat_1 @ X34 @ X33 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('72',plain,(
    ! [X34: $i] :
      ( ~ ( v1_relat_1 @ X34 )
      | ~ ( v5_relat_1 @ X34 @ ( k2_relat_1 @ X34 ) )
      | ( v2_funct_2 @ X34 @ ( k2_relat_1 @ X34 ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['66','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['30','31'])).

thf('77',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( $false
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['1','77'])).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('79',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_xboole_0 @ X10 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('80',plain,(
    ! [X42: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('81',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v1_xboole_0 @ X12 )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ( v1_xboole_0 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('84',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('88',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k6_partfun1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['83','90'])).

thf('92',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('93',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_funct_1 @ ( k6_partfun1 @ X0 ) )
        | ~ ( v1_xboole_0 @ sk_C_1 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('94',plain,(
    ! [X25: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('95',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('96',plain,(
    ! [X25: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X25 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ sk_C_1 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['93','96'])).

thf('98',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(condensation,[status(thm)],['97'])).

thf('99',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
    = ( k5_relat_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('100',plain,(
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

thf('101',plain,(
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

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['99','105'])).

thf('107',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['106','107','108','109'])).

thf('111',plain,
    ( ( k5_relat_1 @ sk_C_1 @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('112',plain,(
    ! [X25: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X25 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('113',plain,
    ( ( v2_funct_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('115',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_xboole_0 @ X10 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('117',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v1_xboole_0 @ X12 )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('119',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['116','119'])).

thf('121',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['115','120'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('122',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('123',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['98','123'])).

thf('125',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('126',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['124','125'])).

thf('127',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['78','126'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tWLLMeLj8T
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:38:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.20/0.34  % Running in FO mode
% 4.24/4.42  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.24/4.42  % Solved by: fo/fo7.sh
% 4.24/4.42  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.24/4.42  % done 3765 iterations in 3.997s
% 4.24/4.42  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.24/4.42  % SZS output start Refutation
% 4.24/4.42  thf(sk_A_type, type, sk_A: $i).
% 4.24/4.42  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 4.24/4.42  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.24/4.42  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.24/4.42  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.24/4.42  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 4.24/4.42  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.24/4.42  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.24/4.42  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 4.24/4.42  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.24/4.42  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.24/4.42  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.24/4.42  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 4.24/4.42  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 4.24/4.42  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 4.24/4.42  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 4.24/4.42  thf(sk_C_1_type, type, sk_C_1: $i).
% 4.24/4.42  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.24/4.42  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.24/4.42  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.24/4.42  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 4.24/4.42  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 4.24/4.42  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 4.24/4.42  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.24/4.42  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.24/4.42  thf(sk_D_type, type, sk_D: $i).
% 4.24/4.42  thf(sk_B_1_type, type, sk_B_1: $i).
% 4.24/4.42  thf(t29_funct_2, conjecture,
% 4.24/4.42    (![A:$i,B:$i,C:$i]:
% 4.24/4.42     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.24/4.42         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.24/4.42       ( ![D:$i]:
% 4.24/4.42         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.24/4.42             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.24/4.42           ( ( r2_relset_1 @
% 4.24/4.42               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 4.24/4.42               ( k6_partfun1 @ A ) ) =>
% 4.24/4.42             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 4.24/4.42  thf(zf_stmt_0, negated_conjecture,
% 4.24/4.42    (~( ![A:$i,B:$i,C:$i]:
% 4.24/4.42        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.24/4.42            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.24/4.42          ( ![D:$i]:
% 4.24/4.42            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.24/4.42                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.24/4.42              ( ( r2_relset_1 @
% 4.24/4.42                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 4.24/4.42                  ( k6_partfun1 @ A ) ) =>
% 4.24/4.42                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 4.24/4.42    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 4.24/4.42  thf('0', plain, ((~ (v2_funct_1 @ sk_C_1) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 4.24/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.24/4.42  thf('1', plain,
% 4.24/4.42      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 4.24/4.42      inference('split', [status(esa)], ['0'])).
% 4.24/4.42  thf('2', plain,
% 4.24/4.42      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 4.24/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.24/4.42  thf('3', plain,
% 4.24/4.42      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.24/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.24/4.42  thf(dt_k1_partfun1, axiom,
% 4.24/4.42    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.24/4.42     ( ( ( v1_funct_1 @ E ) & 
% 4.24/4.42         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.24/4.42         ( v1_funct_1 @ F ) & 
% 4.24/4.42         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 4.24/4.42       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 4.24/4.42         ( m1_subset_1 @
% 4.24/4.42           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 4.24/4.42           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 4.24/4.42  thf('4', plain,
% 4.24/4.42      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 4.24/4.42         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 4.24/4.42          | ~ (v1_funct_1 @ X35)
% 4.24/4.42          | ~ (v1_funct_1 @ X38)
% 4.24/4.42          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 4.24/4.42          | (m1_subset_1 @ (k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38) @ 
% 4.24/4.42             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X40))))),
% 4.24/4.42      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 4.24/4.42  thf('5', plain,
% 4.24/4.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.24/4.42         ((m1_subset_1 @ 
% 4.24/4.42           (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 4.24/4.42           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 4.24/4.42          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 4.24/4.42          | ~ (v1_funct_1 @ X1)
% 4.24/4.42          | ~ (v1_funct_1 @ sk_C_1))),
% 4.24/4.42      inference('sup-', [status(thm)], ['3', '4'])).
% 4.24/4.42  thf('6', plain, ((v1_funct_1 @ sk_C_1)),
% 4.24/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.24/4.42  thf('7', plain,
% 4.24/4.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.24/4.42         ((m1_subset_1 @ 
% 4.24/4.42           (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 4.24/4.42           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 4.24/4.42          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 4.24/4.42          | ~ (v1_funct_1 @ X1))),
% 4.24/4.42      inference('demod', [status(thm)], ['5', '6'])).
% 4.24/4.42  thf('8', plain,
% 4.24/4.42      ((~ (v1_funct_1 @ sk_D)
% 4.24/4.42        | (m1_subset_1 @ 
% 4.24/4.42           (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ 
% 4.24/4.42           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 4.24/4.42      inference('sup-', [status(thm)], ['2', '7'])).
% 4.24/4.42  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 4.24/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.24/4.42  thf('10', plain,
% 4.24/4.42      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 4.24/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.24/4.42  thf('11', plain,
% 4.24/4.42      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.24/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.24/4.42  thf(redefinition_k1_partfun1, axiom,
% 4.24/4.42    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.24/4.42     ( ( ( v1_funct_1 @ E ) & 
% 4.24/4.42         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.24/4.42         ( v1_funct_1 @ F ) & 
% 4.24/4.42         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 4.24/4.42       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 4.24/4.42  thf('12', plain,
% 4.24/4.42      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 4.24/4.42         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 4.24/4.42          | ~ (v1_funct_1 @ X43)
% 4.24/4.42          | ~ (v1_funct_1 @ X46)
% 4.24/4.42          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 4.24/4.42          | ((k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46)
% 4.24/4.42              = (k5_relat_1 @ X43 @ X46)))),
% 4.24/4.42      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 4.24/4.42  thf('13', plain,
% 4.24/4.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.24/4.42         (((k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_1 @ X0)
% 4.24/4.42            = (k5_relat_1 @ sk_C_1 @ X0))
% 4.24/4.42          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 4.24/4.42          | ~ (v1_funct_1 @ X0)
% 4.24/4.42          | ~ (v1_funct_1 @ sk_C_1))),
% 4.24/4.42      inference('sup-', [status(thm)], ['11', '12'])).
% 4.24/4.42  thf('14', plain, ((v1_funct_1 @ sk_C_1)),
% 4.24/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.24/4.42  thf('15', plain,
% 4.24/4.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.24/4.42         (((k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_1 @ X0)
% 4.24/4.42            = (k5_relat_1 @ sk_C_1 @ X0))
% 4.24/4.42          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 4.24/4.42          | ~ (v1_funct_1 @ X0))),
% 4.24/4.42      inference('demod', [status(thm)], ['13', '14'])).
% 4.24/4.42  thf('16', plain,
% 4.24/4.42      ((~ (v1_funct_1 @ sk_D)
% 4.24/4.42        | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 4.24/4.42            = (k5_relat_1 @ sk_C_1 @ sk_D)))),
% 4.24/4.42      inference('sup-', [status(thm)], ['10', '15'])).
% 4.24/4.42  thf('17', plain, ((v1_funct_1 @ sk_D)),
% 4.24/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.24/4.42  thf('18', plain,
% 4.24/4.42      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 4.24/4.42         = (k5_relat_1 @ sk_C_1 @ sk_D))),
% 4.24/4.42      inference('demod', [status(thm)], ['16', '17'])).
% 4.24/4.42  thf('19', plain,
% 4.24/4.42      ((m1_subset_1 @ (k5_relat_1 @ sk_C_1 @ sk_D) @ 
% 4.24/4.42        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.24/4.42      inference('demod', [status(thm)], ['8', '9', '18'])).
% 4.24/4.42  thf(cc2_relat_1, axiom,
% 4.24/4.42    (![A:$i]:
% 4.24/4.42     ( ( v1_relat_1 @ A ) =>
% 4.24/4.42       ( ![B:$i]:
% 4.24/4.42         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 4.24/4.42  thf('20', plain,
% 4.24/4.42      (![X14 : $i, X15 : $i]:
% 4.24/4.42         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 4.24/4.42          | (v1_relat_1 @ X14)
% 4.24/4.42          | ~ (v1_relat_1 @ X15))),
% 4.24/4.42      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.24/4.42  thf('21', plain,
% 4.24/4.42      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 4.24/4.42        | (v1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D)))),
% 4.24/4.42      inference('sup-', [status(thm)], ['19', '20'])).
% 4.24/4.42  thf(fc6_relat_1, axiom,
% 4.24/4.42    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 4.24/4.42  thf('22', plain,
% 4.24/4.42      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 4.24/4.42      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.24/4.42  thf('23', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D))),
% 4.24/4.42      inference('demod', [status(thm)], ['21', '22'])).
% 4.24/4.42  thf(t45_relat_1, axiom,
% 4.24/4.42    (![A:$i]:
% 4.24/4.42     ( ( v1_relat_1 @ A ) =>
% 4.24/4.42       ( ![B:$i]:
% 4.24/4.42         ( ( v1_relat_1 @ B ) =>
% 4.24/4.42           ( r1_tarski @
% 4.24/4.42             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 4.24/4.42  thf('24', plain,
% 4.24/4.42      (![X20 : $i, X21 : $i]:
% 4.24/4.42         (~ (v1_relat_1 @ X20)
% 4.24/4.42          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X21 @ X20)) @ 
% 4.24/4.42             (k2_relat_1 @ X20))
% 4.24/4.42          | ~ (v1_relat_1 @ X21))),
% 4.24/4.42      inference('cnf', [status(esa)], [t45_relat_1])).
% 4.24/4.42  thf(d19_relat_1, axiom,
% 4.24/4.42    (![A:$i,B:$i]:
% 4.24/4.42     ( ( v1_relat_1 @ B ) =>
% 4.24/4.42       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 4.24/4.42  thf('25', plain,
% 4.24/4.42      (![X16 : $i, X17 : $i]:
% 4.24/4.42         (~ (r1_tarski @ (k2_relat_1 @ X16) @ X17)
% 4.24/4.42          | (v5_relat_1 @ X16 @ X17)
% 4.24/4.42          | ~ (v1_relat_1 @ X16))),
% 4.24/4.42      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.24/4.42  thf('26', plain,
% 4.24/4.42      (![X0 : $i, X1 : $i]:
% 4.24/4.42         (~ (v1_relat_1 @ X1)
% 4.24/4.42          | ~ (v1_relat_1 @ X0)
% 4.24/4.42          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 4.24/4.42          | (v5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 4.24/4.42      inference('sup-', [status(thm)], ['24', '25'])).
% 4.24/4.42  thf('27', plain,
% 4.24/4.42      (((v5_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D) @ (k2_relat_1 @ sk_D))
% 4.24/4.42        | ~ (v1_relat_1 @ sk_D)
% 4.24/4.42        | ~ (v1_relat_1 @ sk_C_1))),
% 4.24/4.42      inference('sup-', [status(thm)], ['23', '26'])).
% 4.24/4.42  thf('28', plain,
% 4.24/4.42      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 4.24/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.24/4.42  thf('29', plain,
% 4.24/4.42      (![X14 : $i, X15 : $i]:
% 4.24/4.42         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 4.24/4.42          | (v1_relat_1 @ X14)
% 4.24/4.42          | ~ (v1_relat_1 @ X15))),
% 4.24/4.42      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.24/4.42  thf('30', plain,
% 4.24/4.42      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)) | (v1_relat_1 @ sk_D))),
% 4.24/4.42      inference('sup-', [status(thm)], ['28', '29'])).
% 4.24/4.42  thf('31', plain,
% 4.24/4.42      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 4.24/4.42      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.24/4.42  thf('32', plain, ((v1_relat_1 @ sk_D)),
% 4.24/4.42      inference('demod', [status(thm)], ['30', '31'])).
% 4.24/4.42  thf('33', plain,
% 4.24/4.42      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.24/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.24/4.42  thf('34', plain,
% 4.24/4.42      (![X14 : $i, X15 : $i]:
% 4.24/4.42         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 4.24/4.42          | (v1_relat_1 @ X14)
% 4.24/4.42          | ~ (v1_relat_1 @ X15))),
% 4.24/4.42      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.24/4.42  thf('35', plain,
% 4.24/4.42      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_C_1))),
% 4.24/4.42      inference('sup-', [status(thm)], ['33', '34'])).
% 4.24/4.42  thf('36', plain,
% 4.24/4.42      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 4.24/4.42      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.24/4.42  thf('37', plain, ((v1_relat_1 @ sk_C_1)),
% 4.24/4.42      inference('demod', [status(thm)], ['35', '36'])).
% 4.24/4.42  thf('38', plain,
% 4.24/4.42      ((v5_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D) @ (k2_relat_1 @ sk_D))),
% 4.24/4.42      inference('demod', [status(thm)], ['27', '32', '37'])).
% 4.24/4.42  thf('39', plain,
% 4.24/4.42      (![X16 : $i, X17 : $i]:
% 4.24/4.42         (~ (v5_relat_1 @ X16 @ X17)
% 4.24/4.42          | (r1_tarski @ (k2_relat_1 @ X16) @ X17)
% 4.24/4.42          | ~ (v1_relat_1 @ X16))),
% 4.24/4.42      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.24/4.42  thf('40', plain,
% 4.24/4.42      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D))
% 4.24/4.42        | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D)) @ 
% 4.24/4.42           (k2_relat_1 @ sk_D)))),
% 4.24/4.42      inference('sup-', [status(thm)], ['38', '39'])).
% 4.24/4.42  thf('41', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D))),
% 4.24/4.42      inference('demod', [status(thm)], ['21', '22'])).
% 4.24/4.42  thf('42', plain,
% 4.24/4.42      ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D)) @ 
% 4.24/4.42        (k2_relat_1 @ sk_D))),
% 4.24/4.42      inference('demod', [status(thm)], ['40', '41'])).
% 4.24/4.42  thf(d10_xboole_0, axiom,
% 4.24/4.42    (![A:$i,B:$i]:
% 4.24/4.42     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.24/4.42  thf('43', plain,
% 4.24/4.42      (![X7 : $i, X9 : $i]:
% 4.24/4.42         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 4.24/4.42      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.24/4.42  thf('44', plain,
% 4.24/4.42      ((~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 4.24/4.42           (k2_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D)))
% 4.24/4.42        | ((k2_relat_1 @ sk_D) = (k2_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D))))),
% 4.24/4.42      inference('sup-', [status(thm)], ['42', '43'])).
% 4.24/4.42  thf('45', plain,
% 4.24/4.42      ((r2_relset_1 @ sk_A @ sk_A @ 
% 4.24/4.42        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ 
% 4.24/4.42        (k6_partfun1 @ sk_A))),
% 4.24/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.24/4.42  thf('46', plain,
% 4.24/4.42      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 4.24/4.42         = (k5_relat_1 @ sk_C_1 @ sk_D))),
% 4.24/4.42      inference('demod', [status(thm)], ['16', '17'])).
% 4.24/4.42  thf('47', plain,
% 4.24/4.42      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C_1 @ sk_D) @ 
% 4.24/4.42        (k6_partfun1 @ sk_A))),
% 4.24/4.42      inference('demod', [status(thm)], ['45', '46'])).
% 4.24/4.42  thf('48', plain,
% 4.24/4.42      ((m1_subset_1 @ (k5_relat_1 @ sk_C_1 @ sk_D) @ 
% 4.24/4.42        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.24/4.42      inference('demod', [status(thm)], ['8', '9', '18'])).
% 4.24/4.42  thf(redefinition_r2_relset_1, axiom,
% 4.24/4.42    (![A:$i,B:$i,C:$i,D:$i]:
% 4.24/4.42     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.24/4.42         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.24/4.42       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 4.24/4.42  thf('49', plain,
% 4.24/4.42      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 4.24/4.42         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 4.24/4.42          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 4.24/4.42          | ((X29) = (X32))
% 4.24/4.42          | ~ (r2_relset_1 @ X30 @ X31 @ X29 @ X32))),
% 4.24/4.42      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 4.24/4.42  thf('50', plain,
% 4.24/4.42      (![X0 : $i]:
% 4.24/4.42         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C_1 @ sk_D) @ X0)
% 4.24/4.42          | ((k5_relat_1 @ sk_C_1 @ sk_D) = (X0))
% 4.24/4.42          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 4.24/4.42      inference('sup-', [status(thm)], ['48', '49'])).
% 4.24/4.42  thf('51', plain,
% 4.24/4.42      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 4.24/4.42           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 4.24/4.42        | ((k5_relat_1 @ sk_C_1 @ sk_D) = (k6_partfun1 @ sk_A)))),
% 4.24/4.42      inference('sup-', [status(thm)], ['47', '50'])).
% 4.24/4.42  thf(dt_k6_partfun1, axiom,
% 4.24/4.42    (![A:$i]:
% 4.24/4.42     ( ( m1_subset_1 @
% 4.24/4.42         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 4.24/4.42       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 4.24/4.42  thf('52', plain,
% 4.24/4.42      (![X42 : $i]:
% 4.24/4.42         (m1_subset_1 @ (k6_partfun1 @ X42) @ 
% 4.24/4.42          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X42)))),
% 4.24/4.42      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 4.24/4.42  thf('53', plain, (((k5_relat_1 @ sk_C_1 @ sk_D) = (k6_partfun1 @ sk_A))),
% 4.24/4.42      inference('demod', [status(thm)], ['51', '52'])).
% 4.24/4.42  thf(t71_relat_1, axiom,
% 4.24/4.42    (![A:$i]:
% 4.24/4.42     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 4.24/4.42       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 4.24/4.42  thf('54', plain, (![X23 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 4.24/4.42      inference('cnf', [status(esa)], [t71_relat_1])).
% 4.24/4.42  thf(redefinition_k6_partfun1, axiom,
% 4.24/4.42    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 4.24/4.42  thf('55', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 4.24/4.42      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.24/4.42  thf('56', plain, (![X23 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X23)) = (X23))),
% 4.24/4.42      inference('demod', [status(thm)], ['54', '55'])).
% 4.24/4.42  thf('57', plain,
% 4.24/4.42      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 4.24/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.24/4.42  thf(cc2_relset_1, axiom,
% 4.24/4.42    (![A:$i,B:$i,C:$i]:
% 4.24/4.42     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.24/4.42       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 4.24/4.42  thf('58', plain,
% 4.24/4.42      (![X26 : $i, X27 : $i, X28 : $i]:
% 4.24/4.42         ((v5_relat_1 @ X26 @ X28)
% 4.24/4.42          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 4.24/4.42      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.24/4.42  thf('59', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 4.24/4.42      inference('sup-', [status(thm)], ['57', '58'])).
% 4.24/4.42  thf('60', plain,
% 4.24/4.42      (![X16 : $i, X17 : $i]:
% 4.24/4.42         (~ (v5_relat_1 @ X16 @ X17)
% 4.24/4.42          | (r1_tarski @ (k2_relat_1 @ X16) @ X17)
% 4.24/4.42          | ~ (v1_relat_1 @ X16))),
% 4.24/4.42      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.24/4.42  thf('61', plain,
% 4.24/4.42      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 4.24/4.42      inference('sup-', [status(thm)], ['59', '60'])).
% 4.24/4.42  thf('62', plain, ((v1_relat_1 @ sk_D)),
% 4.24/4.42      inference('demod', [status(thm)], ['30', '31'])).
% 4.24/4.42  thf('63', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 4.24/4.42      inference('demod', [status(thm)], ['61', '62'])).
% 4.24/4.42  thf('64', plain, (((k5_relat_1 @ sk_C_1 @ sk_D) = (k6_partfun1 @ sk_A))),
% 4.24/4.42      inference('demod', [status(thm)], ['51', '52'])).
% 4.24/4.42  thf('65', plain, (![X23 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X23)) = (X23))),
% 4.24/4.42      inference('demod', [status(thm)], ['54', '55'])).
% 4.24/4.42  thf('66', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 4.24/4.42      inference('demod', [status(thm)], ['44', '53', '56', '63', '64', '65'])).
% 4.24/4.42  thf('67', plain,
% 4.24/4.42      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 4.24/4.42      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.24/4.42  thf('68', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 4.24/4.42      inference('simplify', [status(thm)], ['67'])).
% 4.24/4.42  thf('69', plain,
% 4.24/4.42      (![X16 : $i, X17 : $i]:
% 4.24/4.42         (~ (r1_tarski @ (k2_relat_1 @ X16) @ X17)
% 4.24/4.42          | (v5_relat_1 @ X16 @ X17)
% 4.24/4.42          | ~ (v1_relat_1 @ X16))),
% 4.24/4.42      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.24/4.42  thf('70', plain,
% 4.24/4.42      (![X0 : $i]:
% 4.24/4.42         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 4.24/4.42      inference('sup-', [status(thm)], ['68', '69'])).
% 4.24/4.42  thf(d3_funct_2, axiom,
% 4.24/4.42    (![A:$i,B:$i]:
% 4.24/4.42     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 4.24/4.42       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 4.24/4.42  thf('71', plain,
% 4.24/4.42      (![X33 : $i, X34 : $i]:
% 4.24/4.42         (((k2_relat_1 @ X34) != (X33))
% 4.24/4.42          | (v2_funct_2 @ X34 @ X33)
% 4.24/4.42          | ~ (v5_relat_1 @ X34 @ X33)
% 4.24/4.42          | ~ (v1_relat_1 @ X34))),
% 4.24/4.42      inference('cnf', [status(esa)], [d3_funct_2])).
% 4.24/4.42  thf('72', plain,
% 4.24/4.42      (![X34 : $i]:
% 4.24/4.42         (~ (v1_relat_1 @ X34)
% 4.24/4.42          | ~ (v5_relat_1 @ X34 @ (k2_relat_1 @ X34))
% 4.24/4.42          | (v2_funct_2 @ X34 @ (k2_relat_1 @ X34)))),
% 4.24/4.42      inference('simplify', [status(thm)], ['71'])).
% 4.24/4.42  thf('73', plain,
% 4.24/4.42      (![X0 : $i]:
% 4.24/4.42         (~ (v1_relat_1 @ X0)
% 4.24/4.42          | (v2_funct_2 @ X0 @ (k2_relat_1 @ X0))
% 4.24/4.42          | ~ (v1_relat_1 @ X0))),
% 4.24/4.42      inference('sup-', [status(thm)], ['70', '72'])).
% 4.24/4.42  thf('74', plain,
% 4.24/4.42      (![X0 : $i]:
% 4.24/4.42         ((v2_funct_2 @ X0 @ (k2_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 4.24/4.42      inference('simplify', [status(thm)], ['73'])).
% 4.24/4.42  thf('75', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 4.24/4.42      inference('sup+', [status(thm)], ['66', '74'])).
% 4.24/4.42  thf('76', plain, ((v1_relat_1 @ sk_D)),
% 4.24/4.42      inference('demod', [status(thm)], ['30', '31'])).
% 4.24/4.42  thf('77', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 4.24/4.42      inference('demod', [status(thm)], ['75', '76'])).
% 4.24/4.42  thf('78', plain, (($false) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 4.24/4.42      inference('demod', [status(thm)], ['1', '77'])).
% 4.24/4.42  thf(fc4_zfmisc_1, axiom,
% 4.24/4.42    (![A:$i,B:$i]:
% 4.24/4.42     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 4.24/4.42  thf('79', plain,
% 4.24/4.42      (![X10 : $i, X11 : $i]:
% 4.24/4.42         (~ (v1_xboole_0 @ X10) | (v1_xboole_0 @ (k2_zfmisc_1 @ X10 @ X11)))),
% 4.24/4.42      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 4.24/4.42  thf('80', plain,
% 4.24/4.42      (![X42 : $i]:
% 4.24/4.42         (m1_subset_1 @ (k6_partfun1 @ X42) @ 
% 4.24/4.42          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X42)))),
% 4.24/4.42      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 4.24/4.42  thf(cc1_subset_1, axiom,
% 4.24/4.42    (![A:$i]:
% 4.24/4.42     ( ( v1_xboole_0 @ A ) =>
% 4.24/4.42       ( ![B:$i]:
% 4.24/4.42         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 4.24/4.42  thf('81', plain,
% 4.24/4.42      (![X12 : $i, X13 : $i]:
% 4.24/4.42         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 4.24/4.42          | (v1_xboole_0 @ X12)
% 4.24/4.42          | ~ (v1_xboole_0 @ X13))),
% 4.24/4.42      inference('cnf', [status(esa)], [cc1_subset_1])).
% 4.24/4.42  thf('82', plain,
% 4.24/4.42      (![X0 : $i]:
% 4.24/4.42         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X0))
% 4.24/4.42          | (v1_xboole_0 @ (k6_partfun1 @ X0)))),
% 4.24/4.42      inference('sup-', [status(thm)], ['80', '81'])).
% 4.24/4.42  thf('83', plain,
% 4.24/4.42      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k6_partfun1 @ X0)))),
% 4.24/4.42      inference('sup-', [status(thm)], ['79', '82'])).
% 4.24/4.42  thf(d3_tarski, axiom,
% 4.24/4.42    (![A:$i,B:$i]:
% 4.24/4.42     ( ( r1_tarski @ A @ B ) <=>
% 4.24/4.42       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 4.24/4.42  thf('84', plain,
% 4.24/4.42      (![X4 : $i, X6 : $i]:
% 4.24/4.42         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 4.24/4.42      inference('cnf', [status(esa)], [d3_tarski])).
% 4.24/4.42  thf(d1_xboole_0, axiom,
% 4.24/4.42    (![A:$i]:
% 4.24/4.42     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 4.24/4.42  thf('85', plain,
% 4.24/4.42      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 4.24/4.42      inference('cnf', [status(esa)], [d1_xboole_0])).
% 4.24/4.42  thf('86', plain,
% 4.24/4.42      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 4.24/4.42      inference('sup-', [status(thm)], ['84', '85'])).
% 4.24/4.42  thf('87', plain,
% 4.24/4.42      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 4.24/4.42      inference('sup-', [status(thm)], ['84', '85'])).
% 4.24/4.42  thf('88', plain,
% 4.24/4.42      (![X7 : $i, X9 : $i]:
% 4.24/4.42         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 4.24/4.42      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.24/4.42  thf('89', plain,
% 4.24/4.42      (![X0 : $i, X1 : $i]:
% 4.24/4.42         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 4.24/4.42      inference('sup-', [status(thm)], ['87', '88'])).
% 4.24/4.42  thf('90', plain,
% 4.24/4.42      (![X0 : $i, X1 : $i]:
% 4.24/4.42         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 4.24/4.42      inference('sup-', [status(thm)], ['86', '89'])).
% 4.24/4.42  thf('91', plain,
% 4.24/4.42      (![X0 : $i, X1 : $i]:
% 4.24/4.42         (~ (v1_xboole_0 @ X0)
% 4.24/4.42          | ~ (v1_xboole_0 @ X1)
% 4.24/4.42          | ((k6_partfun1 @ X0) = (X1)))),
% 4.24/4.42      inference('sup-', [status(thm)], ['83', '90'])).
% 4.24/4.42  thf('92', plain, ((~ (v2_funct_1 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 4.24/4.42      inference('split', [status(esa)], ['0'])).
% 4.24/4.42  thf('93', plain,
% 4.24/4.42      ((![X0 : $i]:
% 4.24/4.42          (~ (v2_funct_1 @ (k6_partfun1 @ X0))
% 4.24/4.42           | ~ (v1_xboole_0 @ sk_C_1)
% 4.24/4.42           | ~ (v1_xboole_0 @ X0)))
% 4.24/4.42         <= (~ ((v2_funct_1 @ sk_C_1)))),
% 4.24/4.42      inference('sup-', [status(thm)], ['91', '92'])).
% 4.24/4.42  thf(fc4_funct_1, axiom,
% 4.24/4.42    (![A:$i]:
% 4.24/4.42     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 4.24/4.42       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 4.24/4.42  thf('94', plain, (![X25 : $i]: (v2_funct_1 @ (k6_relat_1 @ X25))),
% 4.24/4.42      inference('cnf', [status(esa)], [fc4_funct_1])).
% 4.24/4.42  thf('95', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 4.24/4.42      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.24/4.42  thf('96', plain, (![X25 : $i]: (v2_funct_1 @ (k6_partfun1 @ X25))),
% 4.24/4.42      inference('demod', [status(thm)], ['94', '95'])).
% 4.24/4.42  thf('97', plain,
% 4.24/4.42      ((![X0 : $i]: (~ (v1_xboole_0 @ sk_C_1) | ~ (v1_xboole_0 @ X0)))
% 4.24/4.42         <= (~ ((v2_funct_1 @ sk_C_1)))),
% 4.24/4.42      inference('demod', [status(thm)], ['93', '96'])).
% 4.24/4.42  thf('98', plain, ((~ (v1_xboole_0 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 4.24/4.42      inference('condensation', [status(thm)], ['97'])).
% 4.24/4.42  thf('99', plain,
% 4.24/4.42      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 4.24/4.42         = (k5_relat_1 @ sk_C_1 @ sk_D))),
% 4.24/4.42      inference('demod', [status(thm)], ['16', '17'])).
% 4.24/4.42  thf('100', plain,
% 4.24/4.42      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 4.24/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.24/4.42  thf(t26_funct_2, axiom,
% 4.24/4.42    (![A:$i,B:$i,C:$i,D:$i]:
% 4.24/4.42     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 4.24/4.42         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.24/4.42       ( ![E:$i]:
% 4.24/4.42         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 4.24/4.42             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 4.24/4.42           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 4.24/4.42             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 4.24/4.42               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 4.24/4.42  thf('101', plain,
% 4.24/4.42      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 4.24/4.42         (~ (v1_funct_1 @ X50)
% 4.24/4.42          | ~ (v1_funct_2 @ X50 @ X51 @ X52)
% 4.24/4.42          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 4.24/4.42          | ~ (v2_funct_1 @ (k1_partfun1 @ X53 @ X51 @ X51 @ X52 @ X54 @ X50))
% 4.24/4.42          | (v2_funct_1 @ X54)
% 4.24/4.42          | ((X52) = (k1_xboole_0))
% 4.24/4.42          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X51)))
% 4.24/4.42          | ~ (v1_funct_2 @ X54 @ X53 @ X51)
% 4.24/4.42          | ~ (v1_funct_1 @ X54))),
% 4.24/4.42      inference('cnf', [status(esa)], [t26_funct_2])).
% 4.24/4.42  thf('102', plain,
% 4.24/4.42      (![X0 : $i, X1 : $i]:
% 4.24/4.42         (~ (v1_funct_1 @ X0)
% 4.24/4.42          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 4.24/4.42          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 4.24/4.42          | ((sk_A) = (k1_xboole_0))
% 4.24/4.42          | (v2_funct_1 @ X0)
% 4.24/4.42          | ~ (v2_funct_1 @ 
% 4.24/4.42               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D))
% 4.24/4.42          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 4.24/4.42          | ~ (v1_funct_1 @ sk_D))),
% 4.24/4.42      inference('sup-', [status(thm)], ['100', '101'])).
% 4.24/4.42  thf('103', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 4.24/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.24/4.42  thf('104', plain, ((v1_funct_1 @ sk_D)),
% 4.24/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.24/4.42  thf('105', plain,
% 4.24/4.42      (![X0 : $i, X1 : $i]:
% 4.24/4.42         (~ (v1_funct_1 @ X0)
% 4.24/4.42          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 4.24/4.42          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 4.24/4.42          | ((sk_A) = (k1_xboole_0))
% 4.24/4.42          | (v2_funct_1 @ X0)
% 4.24/4.42          | ~ (v2_funct_1 @ 
% 4.24/4.42               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D)))),
% 4.24/4.42      inference('demod', [status(thm)], ['102', '103', '104'])).
% 4.24/4.42  thf('106', plain,
% 4.24/4.42      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C_1 @ sk_D))
% 4.24/4.42        | (v2_funct_1 @ sk_C_1)
% 4.24/4.42        | ((sk_A) = (k1_xboole_0))
% 4.24/4.42        | ~ (m1_subset_1 @ sk_C_1 @ 
% 4.24/4.42             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 4.24/4.42        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 4.24/4.42        | ~ (v1_funct_1 @ sk_C_1))),
% 4.24/4.42      inference('sup-', [status(thm)], ['99', '105'])).
% 4.24/4.42  thf('107', plain,
% 4.24/4.42      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.24/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.24/4.42  thf('108', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 4.24/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.24/4.42  thf('109', plain, ((v1_funct_1 @ sk_C_1)),
% 4.24/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.24/4.42  thf('110', plain,
% 4.24/4.42      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C_1 @ sk_D))
% 4.24/4.42        | (v2_funct_1 @ sk_C_1)
% 4.24/4.42        | ((sk_A) = (k1_xboole_0)))),
% 4.24/4.42      inference('demod', [status(thm)], ['106', '107', '108', '109'])).
% 4.24/4.42  thf('111', plain, (((k5_relat_1 @ sk_C_1 @ sk_D) = (k6_partfun1 @ sk_A))),
% 4.24/4.42      inference('demod', [status(thm)], ['51', '52'])).
% 4.24/4.42  thf('112', plain, (![X25 : $i]: (v2_funct_1 @ (k6_partfun1 @ X25))),
% 4.24/4.42      inference('demod', [status(thm)], ['94', '95'])).
% 4.24/4.42  thf('113', plain, (((v2_funct_1 @ sk_C_1) | ((sk_A) = (k1_xboole_0)))),
% 4.24/4.42      inference('demod', [status(thm)], ['110', '111', '112'])).
% 4.24/4.42  thf('114', plain, ((~ (v2_funct_1 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 4.24/4.42      inference('split', [status(esa)], ['0'])).
% 4.24/4.42  thf('115', plain,
% 4.24/4.42      ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 4.24/4.42      inference('sup-', [status(thm)], ['113', '114'])).
% 4.24/4.42  thf('116', plain,
% 4.24/4.42      (![X10 : $i, X11 : $i]:
% 4.24/4.42         (~ (v1_xboole_0 @ X10) | (v1_xboole_0 @ (k2_zfmisc_1 @ X10 @ X11)))),
% 4.24/4.42      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 4.24/4.42  thf('117', plain,
% 4.24/4.42      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.24/4.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.24/4.42  thf('118', plain,
% 4.24/4.42      (![X12 : $i, X13 : $i]:
% 4.24/4.42         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 4.24/4.42          | (v1_xboole_0 @ X12)
% 4.24/4.42          | ~ (v1_xboole_0 @ X13))),
% 4.24/4.42      inference('cnf', [status(esa)], [cc1_subset_1])).
% 4.24/4.42  thf('119', plain,
% 4.24/4.42      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 4.24/4.42        | (v1_xboole_0 @ sk_C_1))),
% 4.24/4.42      inference('sup-', [status(thm)], ['117', '118'])).
% 4.24/4.42  thf('120', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C_1))),
% 4.24/4.42      inference('sup-', [status(thm)], ['116', '119'])).
% 4.24/4.42  thf('121', plain,
% 4.24/4.42      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_C_1)))
% 4.24/4.42         <= (~ ((v2_funct_1 @ sk_C_1)))),
% 4.24/4.42      inference('sup-', [status(thm)], ['115', '120'])).
% 4.24/4.42  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 4.24/4.42  thf('122', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.24/4.42      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.24/4.42  thf('123', plain, (((v1_xboole_0 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 4.24/4.42      inference('demod', [status(thm)], ['121', '122'])).
% 4.24/4.42  thf('124', plain, (((v2_funct_1 @ sk_C_1))),
% 4.24/4.42      inference('demod', [status(thm)], ['98', '123'])).
% 4.24/4.42  thf('125', plain,
% 4.24/4.42      (~ ((v2_funct_2 @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_C_1))),
% 4.24/4.42      inference('split', [status(esa)], ['0'])).
% 4.24/4.42  thf('126', plain, (~ ((v2_funct_2 @ sk_D @ sk_A))),
% 4.24/4.42      inference('sat_resolution*', [status(thm)], ['124', '125'])).
% 4.24/4.42  thf('127', plain, ($false),
% 4.24/4.42      inference('simpl_trail', [status(thm)], ['78', '126'])).
% 4.24/4.42  
% 4.24/4.42  % SZS output end Refutation
% 4.24/4.42  
% 4.24/4.43  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

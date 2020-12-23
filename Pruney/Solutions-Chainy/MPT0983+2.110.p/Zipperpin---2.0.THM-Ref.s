%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iGrDFmgVS6

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:18 EST 2020

% Result     : Theorem 3.66s
% Output     : Refutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 511 expanded)
%              Number of leaves         :   50 ( 166 expanded)
%              Depth                    :   19
%              Number of atoms          : 1368 (9576 expanded)
%              Number of equality atoms :   43 ( 109 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X43 ) ) ) ) ),
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
    ! [X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ( ( k1_partfun1 @ X47 @ X48 @ X50 @ X51 @ X46 @ X49 )
        = ( k5_relat_1 @ X46 @ X49 ) ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('22',plain,(
    ! [X21: $i,X22: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X24 @ X23 ) ) @ ( k2_relat_1 @ X23 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('25',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ( v5_relat_1 @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X21: $i,X22: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('32',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X21: $i,X22: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('37',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    v5_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['27','32','37'])).

thf('39',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v5_relat_1 @ X19 @ X20 )
      | ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( X32 = X35 )
      | ~ ( r2_relset_1 @ X33 @ X34 @ X32 @ X35 ) ) ),
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
    ! [X45: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X45 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X45 ) ) ) ),
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
    ! [X26: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('55',plain,(
    ! [X52: $i] :
      ( ( k6_partfun1 @ X52 )
      = ( k6_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('56',plain,(
    ! [X26: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X26 ) )
      = X26 ) ),
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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v5_relat_1 @ X29 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('59',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v5_relat_1 @ X19 @ X20 )
      | ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
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
    ! [X26: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X26 ) )
      = X26 ) ),
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
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ( v5_relat_1 @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
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
    ! [X36: $i,X37: $i] :
      ( ( ( k2_relat_1 @ X37 )
       != X36 )
      | ( v2_funct_2 @ X37 @ X36 )
      | ~ ( v5_relat_1 @ X37 @ X36 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('72',plain,(
    ! [X37: $i] :
      ( ~ ( v1_relat_1 @ X37 )
      | ~ ( v5_relat_1 @ X37 @ ( k2_relat_1 @ X37 ) )
      | ( v2_funct_2 @ X37 @ ( k2_relat_1 @ X37 ) ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_xboole_0 @ X13 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('80',plain,(
    ! [X45: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X45 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('81',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( v1_xboole_0 @ X15 )
      | ~ ( v1_xboole_0 @ X16 ) ) ),
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
    ! [X28: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('95',plain,(
    ! [X52: $i] :
      ( ( k6_partfun1 @ X52 )
      = ( k6_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('96',plain,(
    ! [X28: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X28 ) ) ),
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
    ! [X53: $i,X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_funct_2 @ X53 @ X54 @ X55 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X55 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X56 @ X54 @ X54 @ X55 @ X57 @ X53 ) )
      | ( v2_funct_1 @ X57 )
      | ( X55 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X54 ) ) )
      | ~ ( v1_funct_2 @ X57 @ X56 @ X54 )
      | ~ ( v1_funct_1 @ X57 ) ) ),
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
    ! [X28: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X28 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_xboole_0 @ X13 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('117',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( v1_xboole_0 @ X15 )
      | ~ ( v1_xboole_0 @ X16 ) ) ),
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

thf('122',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['67'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('123',plain,(
    ! [X10: $i] :
      ( r1_xboole_0 @ X10 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('124',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['122','125'])).

thf('127',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['121','126'])).

thf('128',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['98','127'])).

thf('129',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('130',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['128','129'])).

thf('131',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['78','130'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iGrDFmgVS6
% 0.14/0.37  % Computer   : n006.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 17:55:23 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 3.66/3.85  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.66/3.85  % Solved by: fo/fo7.sh
% 3.66/3.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.66/3.85  % done 3384 iterations in 3.363s
% 3.66/3.85  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.66/3.85  % SZS output start Refutation
% 3.66/3.85  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.66/3.85  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.66/3.85  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.66/3.85  thf(sk_A_type, type, sk_A: $i).
% 3.66/3.85  thf(sk_D_type, type, sk_D: $i).
% 3.66/3.85  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.66/3.85  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 3.66/3.85  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.66/3.85  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.66/3.85  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.66/3.85  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.66/3.85  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.66/3.85  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.66/3.85  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.66/3.85  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.66/3.85  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.66/3.85  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.66/3.85  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.66/3.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.66/3.85  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 3.66/3.85  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.66/3.85  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 3.66/3.85  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.66/3.85  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.66/3.85  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.66/3.85  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.66/3.85  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.66/3.85  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.66/3.85  thf(t29_funct_2, conjecture,
% 3.66/3.85    (![A:$i,B:$i,C:$i]:
% 3.66/3.85     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.66/3.85         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.66/3.85       ( ![D:$i]:
% 3.66/3.85         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.66/3.85             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.66/3.85           ( ( r2_relset_1 @
% 3.66/3.85               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.66/3.85               ( k6_partfun1 @ A ) ) =>
% 3.66/3.85             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 3.66/3.85  thf(zf_stmt_0, negated_conjecture,
% 3.66/3.85    (~( ![A:$i,B:$i,C:$i]:
% 3.66/3.85        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.66/3.85            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.66/3.85          ( ![D:$i]:
% 3.66/3.85            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.66/3.85                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.66/3.85              ( ( r2_relset_1 @
% 3.66/3.85                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.66/3.85                  ( k6_partfun1 @ A ) ) =>
% 3.66/3.85                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 3.66/3.85    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 3.66/3.85  thf('0', plain, ((~ (v2_funct_1 @ sk_C_1) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 3.66/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.66/3.85  thf('1', plain,
% 3.66/3.85      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 3.66/3.85      inference('split', [status(esa)], ['0'])).
% 3.66/3.85  thf('2', plain,
% 3.66/3.85      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.66/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.66/3.85  thf('3', plain,
% 3.66/3.85      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.66/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.66/3.85  thf(dt_k1_partfun1, axiom,
% 3.66/3.85    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.66/3.85     ( ( ( v1_funct_1 @ E ) & 
% 3.66/3.85         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.66/3.85         ( v1_funct_1 @ F ) & 
% 3.66/3.85         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.66/3.85       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 3.66/3.85         ( m1_subset_1 @
% 3.66/3.85           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.66/3.85           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 3.66/3.85  thf('4', plain,
% 3.66/3.85      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 3.66/3.85         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 3.66/3.85          | ~ (v1_funct_1 @ X38)
% 3.66/3.85          | ~ (v1_funct_1 @ X41)
% 3.66/3.85          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 3.66/3.85          | (m1_subset_1 @ (k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41) @ 
% 3.66/3.85             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X43))))),
% 3.66/3.85      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.66/3.85  thf('5', plain,
% 3.66/3.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.66/3.85         ((m1_subset_1 @ 
% 3.66/3.85           (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 3.66/3.85           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.66/3.85          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.66/3.85          | ~ (v1_funct_1 @ X1)
% 3.66/3.85          | ~ (v1_funct_1 @ sk_C_1))),
% 3.66/3.85      inference('sup-', [status(thm)], ['3', '4'])).
% 3.66/3.85  thf('6', plain, ((v1_funct_1 @ sk_C_1)),
% 3.66/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.66/3.85  thf('7', plain,
% 3.66/3.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.66/3.85         ((m1_subset_1 @ 
% 3.66/3.85           (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 3.66/3.85           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.66/3.85          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.66/3.85          | ~ (v1_funct_1 @ X1))),
% 3.66/3.85      inference('demod', [status(thm)], ['5', '6'])).
% 3.66/3.85  thf('8', plain,
% 3.66/3.85      ((~ (v1_funct_1 @ sk_D)
% 3.66/3.85        | (m1_subset_1 @ 
% 3.66/3.85           (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ 
% 3.66/3.85           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.66/3.85      inference('sup-', [status(thm)], ['2', '7'])).
% 3.66/3.85  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 3.66/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.66/3.85  thf('10', plain,
% 3.66/3.85      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.66/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.66/3.85  thf('11', plain,
% 3.66/3.85      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.66/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.66/3.85  thf(redefinition_k1_partfun1, axiom,
% 3.66/3.85    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.66/3.85     ( ( ( v1_funct_1 @ E ) & 
% 3.66/3.85         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.66/3.85         ( v1_funct_1 @ F ) & 
% 3.66/3.85         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.66/3.85       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 3.66/3.85  thf('12', plain,
% 3.66/3.85      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 3.66/3.85         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 3.66/3.85          | ~ (v1_funct_1 @ X46)
% 3.66/3.85          | ~ (v1_funct_1 @ X49)
% 3.66/3.85          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 3.66/3.85          | ((k1_partfun1 @ X47 @ X48 @ X50 @ X51 @ X46 @ X49)
% 3.66/3.85              = (k5_relat_1 @ X46 @ X49)))),
% 3.66/3.85      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 3.66/3.85  thf('13', plain,
% 3.66/3.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.66/3.85         (((k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_1 @ X0)
% 3.66/3.85            = (k5_relat_1 @ sk_C_1 @ X0))
% 3.66/3.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.66/3.85          | ~ (v1_funct_1 @ X0)
% 3.66/3.85          | ~ (v1_funct_1 @ sk_C_1))),
% 3.66/3.85      inference('sup-', [status(thm)], ['11', '12'])).
% 3.66/3.85  thf('14', plain, ((v1_funct_1 @ sk_C_1)),
% 3.66/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.66/3.85  thf('15', plain,
% 3.66/3.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.66/3.85         (((k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_1 @ X0)
% 3.66/3.85            = (k5_relat_1 @ sk_C_1 @ X0))
% 3.66/3.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.66/3.85          | ~ (v1_funct_1 @ X0))),
% 3.66/3.85      inference('demod', [status(thm)], ['13', '14'])).
% 3.66/3.85  thf('16', plain,
% 3.66/3.85      ((~ (v1_funct_1 @ sk_D)
% 3.66/3.85        | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 3.66/3.85            = (k5_relat_1 @ sk_C_1 @ sk_D)))),
% 3.66/3.85      inference('sup-', [status(thm)], ['10', '15'])).
% 3.66/3.85  thf('17', plain, ((v1_funct_1 @ sk_D)),
% 3.66/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.66/3.85  thf('18', plain,
% 3.66/3.85      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 3.66/3.85         = (k5_relat_1 @ sk_C_1 @ sk_D))),
% 3.66/3.85      inference('demod', [status(thm)], ['16', '17'])).
% 3.66/3.85  thf('19', plain,
% 3.66/3.85      ((m1_subset_1 @ (k5_relat_1 @ sk_C_1 @ sk_D) @ 
% 3.66/3.85        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.66/3.85      inference('demod', [status(thm)], ['8', '9', '18'])).
% 3.66/3.85  thf(cc2_relat_1, axiom,
% 3.66/3.85    (![A:$i]:
% 3.66/3.85     ( ( v1_relat_1 @ A ) =>
% 3.66/3.85       ( ![B:$i]:
% 3.66/3.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 3.66/3.85  thf('20', plain,
% 3.66/3.85      (![X17 : $i, X18 : $i]:
% 3.66/3.85         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 3.66/3.85          | (v1_relat_1 @ X17)
% 3.66/3.85          | ~ (v1_relat_1 @ X18))),
% 3.66/3.85      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.66/3.85  thf('21', plain,
% 3.66/3.85      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 3.66/3.85        | (v1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D)))),
% 3.66/3.85      inference('sup-', [status(thm)], ['19', '20'])).
% 3.66/3.85  thf(fc6_relat_1, axiom,
% 3.66/3.85    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 3.66/3.85  thf('22', plain,
% 3.66/3.85      (![X21 : $i, X22 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X21 @ X22))),
% 3.66/3.85      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.66/3.85  thf('23', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D))),
% 3.66/3.85      inference('demod', [status(thm)], ['21', '22'])).
% 3.66/3.85  thf(t45_relat_1, axiom,
% 3.66/3.85    (![A:$i]:
% 3.66/3.85     ( ( v1_relat_1 @ A ) =>
% 3.66/3.85       ( ![B:$i]:
% 3.66/3.85         ( ( v1_relat_1 @ B ) =>
% 3.66/3.85           ( r1_tarski @
% 3.66/3.85             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 3.66/3.85  thf('24', plain,
% 3.66/3.85      (![X23 : $i, X24 : $i]:
% 3.66/3.85         (~ (v1_relat_1 @ X23)
% 3.66/3.85          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X24 @ X23)) @ 
% 3.66/3.85             (k2_relat_1 @ X23))
% 3.66/3.85          | ~ (v1_relat_1 @ X24))),
% 3.66/3.85      inference('cnf', [status(esa)], [t45_relat_1])).
% 3.66/3.85  thf(d19_relat_1, axiom,
% 3.66/3.85    (![A:$i,B:$i]:
% 3.66/3.85     ( ( v1_relat_1 @ B ) =>
% 3.66/3.85       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 3.66/3.85  thf('25', plain,
% 3.66/3.85      (![X19 : $i, X20 : $i]:
% 3.66/3.85         (~ (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 3.66/3.85          | (v5_relat_1 @ X19 @ X20)
% 3.66/3.85          | ~ (v1_relat_1 @ X19))),
% 3.66/3.85      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.66/3.85  thf('26', plain,
% 3.66/3.85      (![X0 : $i, X1 : $i]:
% 3.66/3.85         (~ (v1_relat_1 @ X1)
% 3.66/3.85          | ~ (v1_relat_1 @ X0)
% 3.66/3.85          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 3.66/3.85          | (v5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 3.66/3.85      inference('sup-', [status(thm)], ['24', '25'])).
% 3.66/3.85  thf('27', plain,
% 3.66/3.85      (((v5_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D) @ (k2_relat_1 @ sk_D))
% 3.66/3.85        | ~ (v1_relat_1 @ sk_D)
% 3.66/3.85        | ~ (v1_relat_1 @ sk_C_1))),
% 3.66/3.85      inference('sup-', [status(thm)], ['23', '26'])).
% 3.66/3.85  thf('28', plain,
% 3.66/3.85      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.66/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.66/3.85  thf('29', plain,
% 3.66/3.85      (![X17 : $i, X18 : $i]:
% 3.66/3.85         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 3.66/3.85          | (v1_relat_1 @ X17)
% 3.66/3.85          | ~ (v1_relat_1 @ X18))),
% 3.66/3.85      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.66/3.85  thf('30', plain,
% 3.66/3.85      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)) | (v1_relat_1 @ sk_D))),
% 3.66/3.85      inference('sup-', [status(thm)], ['28', '29'])).
% 3.66/3.85  thf('31', plain,
% 3.66/3.85      (![X21 : $i, X22 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X21 @ X22))),
% 3.66/3.85      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.66/3.85  thf('32', plain, ((v1_relat_1 @ sk_D)),
% 3.66/3.85      inference('demod', [status(thm)], ['30', '31'])).
% 3.66/3.85  thf('33', plain,
% 3.66/3.85      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.66/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.66/3.85  thf('34', plain,
% 3.66/3.85      (![X17 : $i, X18 : $i]:
% 3.66/3.85         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 3.66/3.85          | (v1_relat_1 @ X17)
% 3.66/3.85          | ~ (v1_relat_1 @ X18))),
% 3.66/3.85      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.66/3.85  thf('35', plain,
% 3.66/3.85      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_C_1))),
% 3.66/3.85      inference('sup-', [status(thm)], ['33', '34'])).
% 3.66/3.85  thf('36', plain,
% 3.66/3.85      (![X21 : $i, X22 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X21 @ X22))),
% 3.66/3.85      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.66/3.85  thf('37', plain, ((v1_relat_1 @ sk_C_1)),
% 3.66/3.85      inference('demod', [status(thm)], ['35', '36'])).
% 3.66/3.85  thf('38', plain,
% 3.66/3.85      ((v5_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D) @ (k2_relat_1 @ sk_D))),
% 3.66/3.85      inference('demod', [status(thm)], ['27', '32', '37'])).
% 3.66/3.85  thf('39', plain,
% 3.66/3.85      (![X19 : $i, X20 : $i]:
% 3.66/3.85         (~ (v5_relat_1 @ X19 @ X20)
% 3.66/3.85          | (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 3.66/3.85          | ~ (v1_relat_1 @ X19))),
% 3.66/3.85      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.66/3.85  thf('40', plain,
% 3.66/3.85      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D))
% 3.66/3.85        | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D)) @ 
% 3.66/3.85           (k2_relat_1 @ sk_D)))),
% 3.66/3.85      inference('sup-', [status(thm)], ['38', '39'])).
% 3.66/3.85  thf('41', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D))),
% 3.66/3.85      inference('demod', [status(thm)], ['21', '22'])).
% 3.66/3.85  thf('42', plain,
% 3.66/3.85      ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D)) @ 
% 3.66/3.85        (k2_relat_1 @ sk_D))),
% 3.66/3.85      inference('demod', [status(thm)], ['40', '41'])).
% 3.66/3.85  thf(d10_xboole_0, axiom,
% 3.66/3.85    (![A:$i,B:$i]:
% 3.66/3.85     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.66/3.85  thf('43', plain,
% 3.66/3.85      (![X7 : $i, X9 : $i]:
% 3.66/3.85         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 3.66/3.85      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.66/3.85  thf('44', plain,
% 3.66/3.85      ((~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 3.66/3.85           (k2_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D)))
% 3.66/3.85        | ((k2_relat_1 @ sk_D) = (k2_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D))))),
% 3.66/3.85      inference('sup-', [status(thm)], ['42', '43'])).
% 3.66/3.85  thf('45', plain,
% 3.66/3.85      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.66/3.85        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ 
% 3.66/3.85        (k6_partfun1 @ sk_A))),
% 3.66/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.66/3.85  thf('46', plain,
% 3.66/3.85      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 3.66/3.85         = (k5_relat_1 @ sk_C_1 @ sk_D))),
% 3.66/3.85      inference('demod', [status(thm)], ['16', '17'])).
% 3.66/3.85  thf('47', plain,
% 3.66/3.85      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C_1 @ sk_D) @ 
% 3.66/3.85        (k6_partfun1 @ sk_A))),
% 3.66/3.85      inference('demod', [status(thm)], ['45', '46'])).
% 3.66/3.85  thf('48', plain,
% 3.66/3.85      ((m1_subset_1 @ (k5_relat_1 @ sk_C_1 @ sk_D) @ 
% 3.66/3.85        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.66/3.85      inference('demod', [status(thm)], ['8', '9', '18'])).
% 3.66/3.85  thf(redefinition_r2_relset_1, axiom,
% 3.66/3.85    (![A:$i,B:$i,C:$i,D:$i]:
% 3.66/3.85     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.66/3.85         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.66/3.85       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.66/3.85  thf('49', plain,
% 3.66/3.85      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 3.66/3.85         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 3.66/3.85          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 3.66/3.85          | ((X32) = (X35))
% 3.66/3.85          | ~ (r2_relset_1 @ X33 @ X34 @ X32 @ X35))),
% 3.66/3.85      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.66/3.85  thf('50', plain,
% 3.66/3.85      (![X0 : $i]:
% 3.66/3.85         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C_1 @ sk_D) @ X0)
% 3.66/3.85          | ((k5_relat_1 @ sk_C_1 @ sk_D) = (X0))
% 3.66/3.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.66/3.85      inference('sup-', [status(thm)], ['48', '49'])).
% 3.66/3.85  thf('51', plain,
% 3.66/3.85      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 3.66/3.85           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.66/3.85        | ((k5_relat_1 @ sk_C_1 @ sk_D) = (k6_partfun1 @ sk_A)))),
% 3.66/3.85      inference('sup-', [status(thm)], ['47', '50'])).
% 3.66/3.85  thf(dt_k6_partfun1, axiom,
% 3.66/3.85    (![A:$i]:
% 3.66/3.85     ( ( m1_subset_1 @
% 3.66/3.85         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 3.66/3.85       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 3.66/3.85  thf('52', plain,
% 3.66/3.85      (![X45 : $i]:
% 3.66/3.85         (m1_subset_1 @ (k6_partfun1 @ X45) @ 
% 3.66/3.85          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X45)))),
% 3.66/3.85      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 3.66/3.85  thf('53', plain, (((k5_relat_1 @ sk_C_1 @ sk_D) = (k6_partfun1 @ sk_A))),
% 3.66/3.85      inference('demod', [status(thm)], ['51', '52'])).
% 3.66/3.85  thf(t71_relat_1, axiom,
% 3.66/3.85    (![A:$i]:
% 3.66/3.85     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 3.66/3.85       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 3.66/3.85  thf('54', plain, (![X26 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 3.66/3.85      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.66/3.85  thf(redefinition_k6_partfun1, axiom,
% 3.66/3.85    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 3.66/3.85  thf('55', plain, (![X52 : $i]: ((k6_partfun1 @ X52) = (k6_relat_1 @ X52))),
% 3.66/3.85      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.66/3.85  thf('56', plain, (![X26 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X26)) = (X26))),
% 3.66/3.85      inference('demod', [status(thm)], ['54', '55'])).
% 3.66/3.85  thf('57', plain,
% 3.66/3.85      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.66/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.66/3.85  thf(cc2_relset_1, axiom,
% 3.66/3.85    (![A:$i,B:$i,C:$i]:
% 3.66/3.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.66/3.85       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.66/3.85  thf('58', plain,
% 3.66/3.85      (![X29 : $i, X30 : $i, X31 : $i]:
% 3.66/3.85         ((v5_relat_1 @ X29 @ X31)
% 3.66/3.85          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 3.66/3.85      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.66/3.85  thf('59', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 3.66/3.85      inference('sup-', [status(thm)], ['57', '58'])).
% 3.66/3.85  thf('60', plain,
% 3.66/3.85      (![X19 : $i, X20 : $i]:
% 3.66/3.85         (~ (v5_relat_1 @ X19 @ X20)
% 3.66/3.85          | (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 3.66/3.85          | ~ (v1_relat_1 @ X19))),
% 3.66/3.85      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.66/3.85  thf('61', plain,
% 3.66/3.85      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 3.66/3.85      inference('sup-', [status(thm)], ['59', '60'])).
% 3.66/3.85  thf('62', plain, ((v1_relat_1 @ sk_D)),
% 3.66/3.85      inference('demod', [status(thm)], ['30', '31'])).
% 3.66/3.85  thf('63', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 3.66/3.85      inference('demod', [status(thm)], ['61', '62'])).
% 3.66/3.85  thf('64', plain, (((k5_relat_1 @ sk_C_1 @ sk_D) = (k6_partfun1 @ sk_A))),
% 3.66/3.85      inference('demod', [status(thm)], ['51', '52'])).
% 3.66/3.85  thf('65', plain, (![X26 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X26)) = (X26))),
% 3.66/3.85      inference('demod', [status(thm)], ['54', '55'])).
% 3.66/3.85  thf('66', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.66/3.85      inference('demod', [status(thm)], ['44', '53', '56', '63', '64', '65'])).
% 3.66/3.85  thf('67', plain,
% 3.66/3.85      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 3.66/3.85      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.66/3.85  thf('68', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 3.66/3.85      inference('simplify', [status(thm)], ['67'])).
% 3.66/3.85  thf('69', plain,
% 3.66/3.85      (![X19 : $i, X20 : $i]:
% 3.66/3.85         (~ (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 3.66/3.85          | (v5_relat_1 @ X19 @ X20)
% 3.66/3.85          | ~ (v1_relat_1 @ X19))),
% 3.66/3.85      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.66/3.85  thf('70', plain,
% 3.66/3.85      (![X0 : $i]:
% 3.66/3.85         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 3.66/3.85      inference('sup-', [status(thm)], ['68', '69'])).
% 3.66/3.85  thf(d3_funct_2, axiom,
% 3.66/3.85    (![A:$i,B:$i]:
% 3.66/3.85     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 3.66/3.85       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 3.66/3.85  thf('71', plain,
% 3.66/3.85      (![X36 : $i, X37 : $i]:
% 3.66/3.85         (((k2_relat_1 @ X37) != (X36))
% 3.66/3.85          | (v2_funct_2 @ X37 @ X36)
% 3.66/3.85          | ~ (v5_relat_1 @ X37 @ X36)
% 3.66/3.85          | ~ (v1_relat_1 @ X37))),
% 3.66/3.85      inference('cnf', [status(esa)], [d3_funct_2])).
% 3.66/3.85  thf('72', plain,
% 3.66/3.85      (![X37 : $i]:
% 3.66/3.85         (~ (v1_relat_1 @ X37)
% 3.66/3.85          | ~ (v5_relat_1 @ X37 @ (k2_relat_1 @ X37))
% 3.66/3.85          | (v2_funct_2 @ X37 @ (k2_relat_1 @ X37)))),
% 3.66/3.85      inference('simplify', [status(thm)], ['71'])).
% 3.66/3.85  thf('73', plain,
% 3.66/3.85      (![X0 : $i]:
% 3.66/3.85         (~ (v1_relat_1 @ X0)
% 3.66/3.85          | (v2_funct_2 @ X0 @ (k2_relat_1 @ X0))
% 3.66/3.85          | ~ (v1_relat_1 @ X0))),
% 3.66/3.85      inference('sup-', [status(thm)], ['70', '72'])).
% 3.66/3.85  thf('74', plain,
% 3.66/3.85      (![X0 : $i]:
% 3.66/3.85         ((v2_funct_2 @ X0 @ (k2_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 3.66/3.85      inference('simplify', [status(thm)], ['73'])).
% 3.66/3.85  thf('75', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 3.66/3.85      inference('sup+', [status(thm)], ['66', '74'])).
% 3.66/3.85  thf('76', plain, ((v1_relat_1 @ sk_D)),
% 3.66/3.85      inference('demod', [status(thm)], ['30', '31'])).
% 3.66/3.85  thf('77', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 3.66/3.85      inference('demod', [status(thm)], ['75', '76'])).
% 3.66/3.85  thf('78', plain, (($false) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 3.66/3.85      inference('demod', [status(thm)], ['1', '77'])).
% 3.66/3.85  thf(fc4_zfmisc_1, axiom,
% 3.66/3.85    (![A:$i,B:$i]:
% 3.66/3.85     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 3.66/3.85  thf('79', plain,
% 3.66/3.85      (![X13 : $i, X14 : $i]:
% 3.66/3.85         (~ (v1_xboole_0 @ X13) | (v1_xboole_0 @ (k2_zfmisc_1 @ X13 @ X14)))),
% 3.66/3.85      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 3.66/3.85  thf('80', plain,
% 3.66/3.85      (![X45 : $i]:
% 3.66/3.85         (m1_subset_1 @ (k6_partfun1 @ X45) @ 
% 3.66/3.85          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X45)))),
% 3.66/3.85      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 3.66/3.85  thf(cc1_subset_1, axiom,
% 3.66/3.85    (![A:$i]:
% 3.66/3.85     ( ( v1_xboole_0 @ A ) =>
% 3.66/3.85       ( ![B:$i]:
% 3.66/3.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 3.66/3.85  thf('81', plain,
% 3.66/3.85      (![X15 : $i, X16 : $i]:
% 3.66/3.85         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 3.66/3.85          | (v1_xboole_0 @ X15)
% 3.66/3.85          | ~ (v1_xboole_0 @ X16))),
% 3.66/3.85      inference('cnf', [status(esa)], [cc1_subset_1])).
% 3.66/3.85  thf('82', plain,
% 3.66/3.85      (![X0 : $i]:
% 3.66/3.85         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X0))
% 3.66/3.85          | (v1_xboole_0 @ (k6_partfun1 @ X0)))),
% 3.66/3.85      inference('sup-', [status(thm)], ['80', '81'])).
% 3.66/3.85  thf('83', plain,
% 3.66/3.85      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k6_partfun1 @ X0)))),
% 3.66/3.85      inference('sup-', [status(thm)], ['79', '82'])).
% 3.66/3.85  thf(d3_tarski, axiom,
% 3.66/3.85    (![A:$i,B:$i]:
% 3.66/3.85     ( ( r1_tarski @ A @ B ) <=>
% 3.66/3.85       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 3.66/3.85  thf('84', plain,
% 3.66/3.85      (![X4 : $i, X6 : $i]:
% 3.66/3.85         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 3.66/3.85      inference('cnf', [status(esa)], [d3_tarski])).
% 3.66/3.85  thf(d1_xboole_0, axiom,
% 3.66/3.85    (![A:$i]:
% 3.66/3.85     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 3.66/3.85  thf('85', plain,
% 3.66/3.85      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.66/3.85      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.66/3.85  thf('86', plain,
% 3.66/3.85      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 3.66/3.85      inference('sup-', [status(thm)], ['84', '85'])).
% 3.66/3.85  thf('87', plain,
% 3.66/3.85      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 3.66/3.85      inference('sup-', [status(thm)], ['84', '85'])).
% 3.66/3.85  thf('88', plain,
% 3.66/3.85      (![X7 : $i, X9 : $i]:
% 3.66/3.85         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 3.66/3.85      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.66/3.85  thf('89', plain,
% 3.66/3.85      (![X0 : $i, X1 : $i]:
% 3.66/3.85         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 3.66/3.85      inference('sup-', [status(thm)], ['87', '88'])).
% 3.66/3.85  thf('90', plain,
% 3.66/3.85      (![X0 : $i, X1 : $i]:
% 3.66/3.85         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.66/3.85      inference('sup-', [status(thm)], ['86', '89'])).
% 3.66/3.85  thf('91', plain,
% 3.66/3.85      (![X0 : $i, X1 : $i]:
% 3.66/3.85         (~ (v1_xboole_0 @ X0)
% 3.66/3.85          | ~ (v1_xboole_0 @ X1)
% 3.66/3.85          | ((k6_partfun1 @ X0) = (X1)))),
% 3.66/3.85      inference('sup-', [status(thm)], ['83', '90'])).
% 3.66/3.85  thf('92', plain, ((~ (v2_funct_1 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 3.66/3.85      inference('split', [status(esa)], ['0'])).
% 3.66/3.85  thf('93', plain,
% 3.66/3.85      ((![X0 : $i]:
% 3.66/3.85          (~ (v2_funct_1 @ (k6_partfun1 @ X0))
% 3.66/3.85           | ~ (v1_xboole_0 @ sk_C_1)
% 3.66/3.85           | ~ (v1_xboole_0 @ X0)))
% 3.66/3.85         <= (~ ((v2_funct_1 @ sk_C_1)))),
% 3.66/3.85      inference('sup-', [status(thm)], ['91', '92'])).
% 3.66/3.85  thf(fc4_funct_1, axiom,
% 3.66/3.85    (![A:$i]:
% 3.66/3.85     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 3.66/3.85       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 3.66/3.85  thf('94', plain, (![X28 : $i]: (v2_funct_1 @ (k6_relat_1 @ X28))),
% 3.66/3.85      inference('cnf', [status(esa)], [fc4_funct_1])).
% 3.66/3.85  thf('95', plain, (![X52 : $i]: ((k6_partfun1 @ X52) = (k6_relat_1 @ X52))),
% 3.66/3.85      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.66/3.85  thf('96', plain, (![X28 : $i]: (v2_funct_1 @ (k6_partfun1 @ X28))),
% 3.66/3.85      inference('demod', [status(thm)], ['94', '95'])).
% 3.66/3.85  thf('97', plain,
% 3.66/3.85      ((![X0 : $i]: (~ (v1_xboole_0 @ sk_C_1) | ~ (v1_xboole_0 @ X0)))
% 3.66/3.85         <= (~ ((v2_funct_1 @ sk_C_1)))),
% 3.66/3.85      inference('demod', [status(thm)], ['93', '96'])).
% 3.66/3.85  thf('98', plain, ((~ (v1_xboole_0 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 3.66/3.85      inference('condensation', [status(thm)], ['97'])).
% 3.66/3.85  thf('99', plain,
% 3.66/3.85      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 3.66/3.85         = (k5_relat_1 @ sk_C_1 @ sk_D))),
% 3.66/3.85      inference('demod', [status(thm)], ['16', '17'])).
% 3.66/3.85  thf('100', plain,
% 3.66/3.85      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.66/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.66/3.85  thf(t26_funct_2, axiom,
% 3.66/3.85    (![A:$i,B:$i,C:$i,D:$i]:
% 3.66/3.85     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.66/3.85         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.66/3.85       ( ![E:$i]:
% 3.66/3.85         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.66/3.85             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.66/3.85           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 3.66/3.85             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 3.66/3.85               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 3.66/3.85  thf('101', plain,
% 3.66/3.85      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 3.66/3.85         (~ (v1_funct_1 @ X53)
% 3.66/3.85          | ~ (v1_funct_2 @ X53 @ X54 @ X55)
% 3.66/3.85          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X55)))
% 3.66/3.85          | ~ (v2_funct_1 @ (k1_partfun1 @ X56 @ X54 @ X54 @ X55 @ X57 @ X53))
% 3.66/3.85          | (v2_funct_1 @ X57)
% 3.66/3.85          | ((X55) = (k1_xboole_0))
% 3.66/3.85          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X54)))
% 3.66/3.85          | ~ (v1_funct_2 @ X57 @ X56 @ X54)
% 3.66/3.85          | ~ (v1_funct_1 @ X57))),
% 3.66/3.85      inference('cnf', [status(esa)], [t26_funct_2])).
% 3.66/3.85  thf('102', plain,
% 3.66/3.85      (![X0 : $i, X1 : $i]:
% 3.66/3.85         (~ (v1_funct_1 @ X0)
% 3.66/3.85          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 3.66/3.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 3.66/3.85          | ((sk_A) = (k1_xboole_0))
% 3.66/3.85          | (v2_funct_1 @ X0)
% 3.66/3.85          | ~ (v2_funct_1 @ 
% 3.66/3.85               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D))
% 3.66/3.85          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 3.66/3.85          | ~ (v1_funct_1 @ sk_D))),
% 3.66/3.85      inference('sup-', [status(thm)], ['100', '101'])).
% 3.66/3.85  thf('103', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 3.66/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.66/3.85  thf('104', plain, ((v1_funct_1 @ sk_D)),
% 3.66/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.66/3.85  thf('105', plain,
% 3.66/3.85      (![X0 : $i, X1 : $i]:
% 3.66/3.85         (~ (v1_funct_1 @ X0)
% 3.66/3.85          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 3.66/3.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 3.66/3.85          | ((sk_A) = (k1_xboole_0))
% 3.66/3.85          | (v2_funct_1 @ X0)
% 3.66/3.85          | ~ (v2_funct_1 @ 
% 3.66/3.85               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D)))),
% 3.66/3.85      inference('demod', [status(thm)], ['102', '103', '104'])).
% 3.66/3.85  thf('106', plain,
% 3.66/3.85      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C_1 @ sk_D))
% 3.66/3.85        | (v2_funct_1 @ sk_C_1)
% 3.66/3.85        | ((sk_A) = (k1_xboole_0))
% 3.66/3.85        | ~ (m1_subset_1 @ sk_C_1 @ 
% 3.66/3.85             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 3.66/3.85        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 3.66/3.85        | ~ (v1_funct_1 @ sk_C_1))),
% 3.66/3.85      inference('sup-', [status(thm)], ['99', '105'])).
% 3.66/3.85  thf('107', plain,
% 3.66/3.85      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.66/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.66/3.85  thf('108', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 3.66/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.66/3.85  thf('109', plain, ((v1_funct_1 @ sk_C_1)),
% 3.66/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.66/3.85  thf('110', plain,
% 3.66/3.85      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C_1 @ sk_D))
% 3.66/3.85        | (v2_funct_1 @ sk_C_1)
% 3.66/3.85        | ((sk_A) = (k1_xboole_0)))),
% 3.66/3.85      inference('demod', [status(thm)], ['106', '107', '108', '109'])).
% 3.66/3.85  thf('111', plain, (((k5_relat_1 @ sk_C_1 @ sk_D) = (k6_partfun1 @ sk_A))),
% 3.66/3.85      inference('demod', [status(thm)], ['51', '52'])).
% 3.66/3.85  thf('112', plain, (![X28 : $i]: (v2_funct_1 @ (k6_partfun1 @ X28))),
% 3.66/3.85      inference('demod', [status(thm)], ['94', '95'])).
% 3.66/3.85  thf('113', plain, (((v2_funct_1 @ sk_C_1) | ((sk_A) = (k1_xboole_0)))),
% 3.66/3.85      inference('demod', [status(thm)], ['110', '111', '112'])).
% 3.66/3.85  thf('114', plain, ((~ (v2_funct_1 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 3.66/3.85      inference('split', [status(esa)], ['0'])).
% 3.66/3.85  thf('115', plain,
% 3.66/3.85      ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 3.66/3.85      inference('sup-', [status(thm)], ['113', '114'])).
% 3.66/3.85  thf('116', plain,
% 3.66/3.85      (![X13 : $i, X14 : $i]:
% 3.66/3.85         (~ (v1_xboole_0 @ X13) | (v1_xboole_0 @ (k2_zfmisc_1 @ X13 @ X14)))),
% 3.66/3.85      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 3.66/3.85  thf('117', plain,
% 3.66/3.85      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.66/3.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.66/3.85  thf('118', plain,
% 3.66/3.85      (![X15 : $i, X16 : $i]:
% 3.66/3.85         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 3.66/3.85          | (v1_xboole_0 @ X15)
% 3.66/3.85          | ~ (v1_xboole_0 @ X16))),
% 3.66/3.85      inference('cnf', [status(esa)], [cc1_subset_1])).
% 3.66/3.85  thf('119', plain,
% 3.66/3.85      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 3.66/3.85        | (v1_xboole_0 @ sk_C_1))),
% 3.66/3.85      inference('sup-', [status(thm)], ['117', '118'])).
% 3.66/3.85  thf('120', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C_1))),
% 3.66/3.85      inference('sup-', [status(thm)], ['116', '119'])).
% 3.66/3.85  thf('121', plain,
% 3.66/3.85      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_C_1)))
% 3.66/3.85         <= (~ ((v2_funct_1 @ sk_C_1)))),
% 3.66/3.85      inference('sup-', [status(thm)], ['115', '120'])).
% 3.66/3.85  thf('122', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 3.66/3.85      inference('simplify', [status(thm)], ['67'])).
% 3.66/3.85  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 3.66/3.85  thf('123', plain, (![X10 : $i]: (r1_xboole_0 @ X10 @ k1_xboole_0)),
% 3.66/3.85      inference('cnf', [status(esa)], [t65_xboole_1])).
% 3.66/3.85  thf(t69_xboole_1, axiom,
% 3.66/3.85    (![A:$i,B:$i]:
% 3.66/3.85     ( ( ~( v1_xboole_0 @ B ) ) =>
% 3.66/3.85       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 3.66/3.85  thf('124', plain,
% 3.66/3.85      (![X11 : $i, X12 : $i]:
% 3.66/3.85         (~ (r1_xboole_0 @ X11 @ X12)
% 3.66/3.85          | ~ (r1_tarski @ X11 @ X12)
% 3.66/3.85          | (v1_xboole_0 @ X11))),
% 3.66/3.85      inference('cnf', [status(esa)], [t69_xboole_1])).
% 3.66/3.85  thf('125', plain,
% 3.66/3.85      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 3.66/3.85      inference('sup-', [status(thm)], ['123', '124'])).
% 3.66/3.85  thf('126', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.66/3.85      inference('sup-', [status(thm)], ['122', '125'])).
% 3.66/3.85  thf('127', plain, (((v1_xboole_0 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 3.66/3.85      inference('demod', [status(thm)], ['121', '126'])).
% 3.66/3.85  thf('128', plain, (((v2_funct_1 @ sk_C_1))),
% 3.66/3.85      inference('demod', [status(thm)], ['98', '127'])).
% 3.66/3.85  thf('129', plain,
% 3.66/3.85      (~ ((v2_funct_2 @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_C_1))),
% 3.66/3.85      inference('split', [status(esa)], ['0'])).
% 3.66/3.85  thf('130', plain, (~ ((v2_funct_2 @ sk_D @ sk_A))),
% 3.66/3.85      inference('sat_resolution*', [status(thm)], ['128', '129'])).
% 3.66/3.85  thf('131', plain, ($false),
% 3.66/3.85      inference('simpl_trail', [status(thm)], ['78', '130'])).
% 3.66/3.85  
% 3.66/3.85  % SZS output end Refutation
% 3.66/3.85  
% 3.66/3.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

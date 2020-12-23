%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GlmNO2PTaB

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:25 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  188 (1065 expanded)
%              Number of leaves         :   44 ( 322 expanded)
%              Depth                    :   25
%              Number of atoms          : 1427 (21447 expanded)
%              Number of equality atoms :   64 ( 247 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

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

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('4',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X34 ) ) ) ) ),
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
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( ( k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40 )
        = ( k5_relat_1 @ X37 @ X40 ) ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('22',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) ) @ ( k2_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ( v5_relat_1 @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('32',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('37',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    v5_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['27','32','37'])).

thf('39',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v5_relat_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( X23 = X26 )
      | ~ ( r2_relset_1 @ X24 @ X25 @ X23 @ X26 ) ) ),
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
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
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
    ! [X17: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('55',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('56',plain,(
    ! [X17: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X17 ) )
      = X17 ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v5_relat_1 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('59',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v5_relat_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
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
    ! [X17: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X17 ) )
      = X17 ) ),
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
    ! [X27: $i,X28: $i] :
      ( ( ( k2_relat_1 @ X28 )
       != X27 )
      | ( v2_funct_2 @ X28 @ X27 )
      | ~ ( v5_relat_1 @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('68',plain,(
    ! [X28: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ~ ( v5_relat_1 @ X28 @ ( k2_relat_1 @ X28 ) )
      | ( v2_funct_2 @ X28 @ ( k2_relat_1 @ X28 ) ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ( v5_relat_1 @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X28: $i] :
      ( ( v2_funct_2 @ X28 @ ( k2_relat_1 @ X28 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
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
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('78',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('80',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','80'])).

thf('82',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('83',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) ) @ ( k1_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('84',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ( v4_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) )
      | ( v4_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( v4_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['30','31'])).

thf('88',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['35','36'])).

thf('89',plain,(
    v4_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('91',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('93',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('95',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('97',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('98',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('99',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X16 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('102',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('104',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['35','36'])).

thf('106',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('108',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X16 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('109',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['95','96','99','106','107','108'])).

thf('110',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('111',plain,(
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

thf('112',plain,(
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

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['110','116'])).

thf('118',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['117','118','119','120'])).

thf('122',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('123',plain,(
    ! [X19: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('124',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('125',plain,(
    ! [X19: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['121','122','125'])).

thf('127',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('128',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['78','79'])).

thf('130',plain,(
    sk_A = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['109','130'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('132',plain,(
    ! [X15: $i] :
      ( ( ( k1_relat_1 @ X15 )
       != k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('133',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['35','36'])).

thf('135',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['135'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('137',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('138',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('139',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X19: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('141',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['139','140'])).

thf('142',plain,(
    $false ),
    inference(demod,[status(thm)],['81','136','141'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GlmNO2PTaB
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:12:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.39/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.57  % Solved by: fo/fo7.sh
% 0.39/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.57  % done 310 iterations in 0.118s
% 0.39/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.57  % SZS output start Refutation
% 0.39/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.57  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.39/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.57  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.39/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.57  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.39/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.57  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.39/0.57  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.39/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.57  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.39/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.57  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.39/0.57  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.39/0.57  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.39/0.57  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.39/0.57  thf(sk_D_type, type, sk_D: $i).
% 0.39/0.57  thf(t29_funct_2, conjecture,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.57       ( ![D:$i]:
% 0.39/0.57         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.39/0.57             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.39/0.57           ( ( r2_relset_1 @
% 0.39/0.57               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.39/0.57               ( k6_partfun1 @ A ) ) =>
% 0.39/0.57             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 0.39/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.39/0.57        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.57            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.57          ( ![D:$i]:
% 0.39/0.57            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.39/0.57                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.39/0.57              ( ( r2_relset_1 @
% 0.39/0.57                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.39/0.57                  ( k6_partfun1 @ A ) ) =>
% 0.39/0.57                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 0.39/0.57    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 0.39/0.57  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('1', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.39/0.57      inference('split', [status(esa)], ['0'])).
% 0.39/0.57  thf('2', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('3', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(dt_k1_partfun1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.39/0.57     ( ( ( v1_funct_1 @ E ) & 
% 0.39/0.57         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.39/0.57         ( v1_funct_1 @ F ) & 
% 0.39/0.57         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.39/0.57       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.39/0.57         ( m1_subset_1 @
% 0.39/0.57           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.39/0.57           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.39/0.57  thf('4', plain,
% 0.39/0.57      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.39/0.57          | ~ (v1_funct_1 @ X29)
% 0.39/0.57          | ~ (v1_funct_1 @ X32)
% 0.39/0.57          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.39/0.57          | (m1_subset_1 @ (k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32) @ 
% 0.39/0.57             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X34))))),
% 0.39/0.57      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.39/0.57  thf('5', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.39/0.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.39/0.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.39/0.57          | ~ (v1_funct_1 @ X1)
% 0.39/0.57          | ~ (v1_funct_1 @ sk_C))),
% 0.39/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.39/0.57  thf('6', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('7', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.39/0.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.39/0.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.39/0.57          | ~ (v1_funct_1 @ X1))),
% 0.39/0.57      inference('demod', [status(thm)], ['5', '6'])).
% 0.39/0.57  thf('8', plain,
% 0.39/0.57      ((~ (v1_funct_1 @ sk_D)
% 0.39/0.57        | (m1_subset_1 @ 
% 0.39/0.57           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.39/0.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['2', '7'])).
% 0.39/0.57  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('10', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('11', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(redefinition_k1_partfun1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.39/0.57     ( ( ( v1_funct_1 @ E ) & 
% 0.39/0.57         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.39/0.57         ( v1_funct_1 @ F ) & 
% 0.39/0.57         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.39/0.57       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.39/0.57  thf('12', plain,
% 0.39/0.57      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.39/0.57          | ~ (v1_funct_1 @ X37)
% 0.39/0.57          | ~ (v1_funct_1 @ X40)
% 0.39/0.57          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.39/0.57          | ((k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40)
% 0.39/0.57              = (k5_relat_1 @ X37 @ X40)))),
% 0.39/0.57      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.39/0.57  thf('13', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.39/0.57            = (k5_relat_1 @ sk_C @ X0))
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.39/0.57          | ~ (v1_funct_1 @ X0)
% 0.39/0.57          | ~ (v1_funct_1 @ sk_C))),
% 0.39/0.57      inference('sup-', [status(thm)], ['11', '12'])).
% 0.39/0.57  thf('14', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('15', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.39/0.57            = (k5_relat_1 @ sk_C @ X0))
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.39/0.57          | ~ (v1_funct_1 @ X0))),
% 0.39/0.57      inference('demod', [status(thm)], ['13', '14'])).
% 0.39/0.57  thf('16', plain,
% 0.39/0.57      ((~ (v1_funct_1 @ sk_D)
% 0.39/0.57        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.39/0.57            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['10', '15'])).
% 0.39/0.57  thf('17', plain, ((v1_funct_1 @ sk_D)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('18', plain,
% 0.39/0.57      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.39/0.57         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.39/0.57      inference('demod', [status(thm)], ['16', '17'])).
% 0.39/0.57  thf('19', plain,
% 0.39/0.57      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.39/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.39/0.57      inference('demod', [status(thm)], ['8', '9', '18'])).
% 0.39/0.57  thf(cc2_relat_1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ A ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.39/0.57  thf('20', plain,
% 0.39/0.57      (![X3 : $i, X4 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.39/0.57          | (v1_relat_1 @ X3)
% 0.39/0.57          | ~ (v1_relat_1 @ X4))),
% 0.39/0.57      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.39/0.57  thf('21', plain,
% 0.39/0.57      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 0.39/0.57        | (v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['19', '20'])).
% 0.39/0.57  thf(fc6_relat_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.39/0.57  thf('22', plain,
% 0.39/0.57      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.39/0.57      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.39/0.57  thf('23', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))),
% 0.39/0.57      inference('demod', [status(thm)], ['21', '22'])).
% 0.39/0.57  thf(t45_relat_1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ A ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( v1_relat_1 @ B ) =>
% 0.39/0.57           ( r1_tarski @
% 0.39/0.57             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.39/0.57  thf('24', plain,
% 0.39/0.57      (![X13 : $i, X14 : $i]:
% 0.39/0.57         (~ (v1_relat_1 @ X13)
% 0.39/0.57          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X14 @ X13)) @ 
% 0.39/0.57             (k2_relat_1 @ X13))
% 0.39/0.57          | ~ (v1_relat_1 @ X14))),
% 0.39/0.57      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.39/0.57  thf(d19_relat_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ B ) =>
% 0.39/0.57       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.39/0.57  thf('25', plain,
% 0.39/0.57      (![X7 : $i, X8 : $i]:
% 0.39/0.57         (~ (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 0.39/0.57          | (v5_relat_1 @ X7 @ X8)
% 0.39/0.57          | ~ (v1_relat_1 @ X7))),
% 0.39/0.57      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.39/0.57  thf('26', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (~ (v1_relat_1 @ X1)
% 0.39/0.57          | ~ (v1_relat_1 @ X0)
% 0.39/0.57          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.39/0.57          | (v5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['24', '25'])).
% 0.39/0.57  thf('27', plain,
% 0.39/0.57      (((v5_relat_1 @ (k5_relat_1 @ sk_C @ sk_D) @ (k2_relat_1 @ sk_D))
% 0.39/0.57        | ~ (v1_relat_1 @ sk_D)
% 0.39/0.57        | ~ (v1_relat_1 @ sk_C))),
% 0.39/0.57      inference('sup-', [status(thm)], ['23', '26'])).
% 0.39/0.57  thf('28', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('29', plain,
% 0.39/0.57      (![X3 : $i, X4 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.39/0.57          | (v1_relat_1 @ X3)
% 0.39/0.57          | ~ (v1_relat_1 @ X4))),
% 0.39/0.57      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.39/0.57  thf('30', plain,
% 0.39/0.57      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.39/0.57      inference('sup-', [status(thm)], ['28', '29'])).
% 0.39/0.57  thf('31', plain,
% 0.39/0.57      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.39/0.57      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.39/0.57  thf('32', plain, ((v1_relat_1 @ sk_D)),
% 0.39/0.57      inference('demod', [status(thm)], ['30', '31'])).
% 0.39/0.57  thf('33', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('34', plain,
% 0.39/0.57      (![X3 : $i, X4 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.39/0.57          | (v1_relat_1 @ X3)
% 0.39/0.57          | ~ (v1_relat_1 @ X4))),
% 0.39/0.57      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.39/0.57  thf('35', plain,
% 0.39/0.57      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.39/0.57      inference('sup-', [status(thm)], ['33', '34'])).
% 0.39/0.57  thf('36', plain,
% 0.39/0.57      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.39/0.57      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.39/0.57  thf('37', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.57      inference('demod', [status(thm)], ['35', '36'])).
% 0.39/0.57  thf('38', plain,
% 0.39/0.57      ((v5_relat_1 @ (k5_relat_1 @ sk_C @ sk_D) @ (k2_relat_1 @ sk_D))),
% 0.39/0.57      inference('demod', [status(thm)], ['27', '32', '37'])).
% 0.39/0.57  thf('39', plain,
% 0.39/0.57      (![X7 : $i, X8 : $i]:
% 0.39/0.57         (~ (v5_relat_1 @ X7 @ X8)
% 0.39/0.57          | (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 0.39/0.57          | ~ (v1_relat_1 @ X7))),
% 0.39/0.57      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.39/0.57  thf('40', plain,
% 0.39/0.57      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 0.39/0.57        | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ 
% 0.39/0.57           (k2_relat_1 @ sk_D)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['38', '39'])).
% 0.39/0.57  thf('41', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))),
% 0.39/0.57      inference('demod', [status(thm)], ['21', '22'])).
% 0.39/0.57  thf('42', plain,
% 0.39/0.57      ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ 
% 0.39/0.57        (k2_relat_1 @ sk_D))),
% 0.39/0.57      inference('demod', [status(thm)], ['40', '41'])).
% 0.39/0.57  thf(d10_xboole_0, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.39/0.57  thf('43', plain,
% 0.39/0.57      (![X0 : $i, X2 : $i]:
% 0.39/0.57         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.39/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.57  thf('44', plain,
% 0.39/0.57      ((~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 0.39/0.57           (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 0.39/0.57        | ((k2_relat_1 @ sk_D) = (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['42', '43'])).
% 0.39/0.57  thf('45', plain,
% 0.39/0.57      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.39/0.57        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.39/0.57        (k6_partfun1 @ sk_A))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('46', plain,
% 0.39/0.57      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.39/0.57         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.39/0.57      inference('demod', [status(thm)], ['16', '17'])).
% 0.39/0.57  thf('47', plain,
% 0.39/0.57      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.39/0.57        (k6_partfun1 @ sk_A))),
% 0.39/0.57      inference('demod', [status(thm)], ['45', '46'])).
% 0.39/0.57  thf('48', plain,
% 0.39/0.57      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.39/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.39/0.57      inference('demod', [status(thm)], ['8', '9', '18'])).
% 0.39/0.57  thf(redefinition_r2_relset_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.57     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.39/0.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.57       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.39/0.57  thf('49', plain,
% 0.39/0.57      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.39/0.57          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.39/0.57          | ((X23) = (X26))
% 0.39/0.57          | ~ (r2_relset_1 @ X24 @ X25 @ X23 @ X26))),
% 0.39/0.57      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.39/0.57  thf('50', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 0.39/0.57          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['48', '49'])).
% 0.39/0.57  thf('51', plain,
% 0.39/0.57      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.39/0.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.39/0.57        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['47', '50'])).
% 0.39/0.57  thf(dt_k6_partfun1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( m1_subset_1 @
% 0.39/0.57         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.39/0.57       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.39/0.57  thf('52', plain,
% 0.39/0.57      (![X36 : $i]:
% 0.39/0.57         (m1_subset_1 @ (k6_partfun1 @ X36) @ 
% 0.39/0.57          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 0.39/0.57      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.39/0.57  thf('53', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.39/0.57      inference('demod', [status(thm)], ['51', '52'])).
% 0.39/0.57  thf(t71_relat_1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.39/0.57       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.39/0.57  thf('54', plain, (![X17 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X17)) = (X17))),
% 0.39/0.57      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.39/0.57  thf(redefinition_k6_partfun1, axiom,
% 0.39/0.57    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.39/0.57  thf('55', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 0.39/0.57      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.39/0.57  thf('56', plain, (![X17 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X17)) = (X17))),
% 0.39/0.57      inference('demod', [status(thm)], ['54', '55'])).
% 0.39/0.57  thf('57', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(cc2_relset_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.57       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.39/0.57  thf('58', plain,
% 0.39/0.57      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.39/0.57         ((v5_relat_1 @ X20 @ X22)
% 0.39/0.57          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.39/0.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.39/0.57  thf('59', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 0.39/0.57      inference('sup-', [status(thm)], ['57', '58'])).
% 0.39/0.57  thf('60', plain,
% 0.39/0.57      (![X7 : $i, X8 : $i]:
% 0.39/0.57         (~ (v5_relat_1 @ X7 @ X8)
% 0.39/0.57          | (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 0.39/0.57          | ~ (v1_relat_1 @ X7))),
% 0.39/0.57      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.39/0.57  thf('61', plain,
% 0.39/0.57      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['59', '60'])).
% 0.39/0.57  thf('62', plain, ((v1_relat_1 @ sk_D)),
% 0.39/0.57      inference('demod', [status(thm)], ['30', '31'])).
% 0.39/0.57  thf('63', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 0.39/0.57      inference('demod', [status(thm)], ['61', '62'])).
% 0.39/0.57  thf('64', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.39/0.57      inference('demod', [status(thm)], ['51', '52'])).
% 0.39/0.57  thf('65', plain, (![X17 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X17)) = (X17))),
% 0.39/0.57      inference('demod', [status(thm)], ['54', '55'])).
% 0.39/0.57  thf('66', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.39/0.57      inference('demod', [status(thm)], ['44', '53', '56', '63', '64', '65'])).
% 0.39/0.57  thf(d3_funct_2, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.39/0.57       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.39/0.57  thf('67', plain,
% 0.39/0.57      (![X27 : $i, X28 : $i]:
% 0.39/0.57         (((k2_relat_1 @ X28) != (X27))
% 0.39/0.57          | (v2_funct_2 @ X28 @ X27)
% 0.39/0.57          | ~ (v5_relat_1 @ X28 @ X27)
% 0.39/0.57          | ~ (v1_relat_1 @ X28))),
% 0.39/0.57      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.39/0.57  thf('68', plain,
% 0.39/0.57      (![X28 : $i]:
% 0.39/0.57         (~ (v1_relat_1 @ X28)
% 0.39/0.57          | ~ (v5_relat_1 @ X28 @ (k2_relat_1 @ X28))
% 0.39/0.57          | (v2_funct_2 @ X28 @ (k2_relat_1 @ X28)))),
% 0.39/0.57      inference('simplify', [status(thm)], ['67'])).
% 0.39/0.57  thf('69', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.57  thf('70', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.39/0.57      inference('simplify', [status(thm)], ['69'])).
% 0.39/0.57  thf('71', plain,
% 0.39/0.57      (![X7 : $i, X8 : $i]:
% 0.39/0.57         (~ (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 0.39/0.58          | (v5_relat_1 @ X7 @ X8)
% 0.39/0.58          | ~ (v1_relat_1 @ X7))),
% 0.39/0.58      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.39/0.58  thf('72', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['70', '71'])).
% 0.39/0.58  thf('73', plain,
% 0.39/0.58      (![X28 : $i]:
% 0.39/0.58         ((v2_funct_2 @ X28 @ (k2_relat_1 @ X28)) | ~ (v1_relat_1 @ X28))),
% 0.39/0.58      inference('clc', [status(thm)], ['68', '72'])).
% 0.39/0.58  thf('74', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 0.39/0.58      inference('sup+', [status(thm)], ['66', '73'])).
% 0.39/0.58  thf('75', plain, ((v1_relat_1 @ sk_D)),
% 0.39/0.58      inference('demod', [status(thm)], ['30', '31'])).
% 0.39/0.58  thf('76', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 0.39/0.58      inference('demod', [status(thm)], ['74', '75'])).
% 0.39/0.58  thf('77', plain,
% 0.39/0.58      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 0.39/0.58      inference('split', [status(esa)], ['0'])).
% 0.39/0.58  thf('78', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['76', '77'])).
% 0.39/0.58  thf('79', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 0.39/0.58      inference('split', [status(esa)], ['0'])).
% 0.39/0.58  thf('80', plain, (~ ((v2_funct_1 @ sk_C))),
% 0.39/0.58      inference('sat_resolution*', [status(thm)], ['78', '79'])).
% 0.39/0.58  thf('81', plain, (~ (v2_funct_1 @ sk_C)),
% 0.39/0.58      inference('simpl_trail', [status(thm)], ['1', '80'])).
% 0.39/0.58  thf('82', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))),
% 0.39/0.58      inference('demod', [status(thm)], ['21', '22'])).
% 0.39/0.58  thf(t44_relat_1, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( v1_relat_1 @ A ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( v1_relat_1 @ B ) =>
% 0.39/0.58           ( r1_tarski @
% 0.39/0.58             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.39/0.58  thf('83', plain,
% 0.39/0.58      (![X11 : $i, X12 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X11)
% 0.39/0.58          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X12 @ X11)) @ 
% 0.39/0.58             (k1_relat_1 @ X12))
% 0.39/0.58          | ~ (v1_relat_1 @ X12))),
% 0.39/0.58      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.39/0.58  thf(d18_relat_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( v1_relat_1 @ B ) =>
% 0.39/0.58       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.39/0.58  thf('84', plain,
% 0.39/0.58      (![X5 : $i, X6 : $i]:
% 0.39/0.58         (~ (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 0.39/0.58          | (v4_relat_1 @ X5 @ X6)
% 0.39/0.58          | ~ (v1_relat_1 @ X5))),
% 0.39/0.58      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.39/0.58  thf('85', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ X1)
% 0.39/0.58          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ X1))
% 0.39/0.58          | (v4_relat_1 @ (k5_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['83', '84'])).
% 0.39/0.58  thf('86', plain,
% 0.39/0.58      (((v4_relat_1 @ (k5_relat_1 @ sk_C @ sk_D) @ (k1_relat_1 @ sk_C))
% 0.39/0.58        | ~ (v1_relat_1 @ sk_D)
% 0.39/0.58        | ~ (v1_relat_1 @ sk_C))),
% 0.39/0.58      inference('sup-', [status(thm)], ['82', '85'])).
% 0.39/0.58  thf('87', plain, ((v1_relat_1 @ sk_D)),
% 0.39/0.58      inference('demod', [status(thm)], ['30', '31'])).
% 0.39/0.58  thf('88', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.58      inference('demod', [status(thm)], ['35', '36'])).
% 0.39/0.58  thf('89', plain,
% 0.39/0.58      ((v4_relat_1 @ (k5_relat_1 @ sk_C @ sk_D) @ (k1_relat_1 @ sk_C))),
% 0.39/0.58      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.39/0.58  thf('90', plain,
% 0.39/0.58      (![X5 : $i, X6 : $i]:
% 0.39/0.58         (~ (v4_relat_1 @ X5 @ X6)
% 0.39/0.58          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 0.39/0.58          | ~ (v1_relat_1 @ X5))),
% 0.39/0.58      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.39/0.58  thf('91', plain,
% 0.39/0.58      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 0.39/0.58        | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ 
% 0.39/0.58           (k1_relat_1 @ sk_C)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['89', '90'])).
% 0.39/0.58  thf('92', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))),
% 0.39/0.58      inference('demod', [status(thm)], ['21', '22'])).
% 0.39/0.58  thf('93', plain,
% 0.39/0.58      ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ 
% 0.39/0.58        (k1_relat_1 @ sk_C))),
% 0.39/0.58      inference('demod', [status(thm)], ['91', '92'])).
% 0.39/0.58  thf('94', plain,
% 0.39/0.58      (![X0 : $i, X2 : $i]:
% 0.39/0.58         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.39/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.58  thf('95', plain,
% 0.39/0.58      ((~ (r1_tarski @ (k1_relat_1 @ sk_C) @ 
% 0.39/0.58           (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 0.39/0.58        | ((k1_relat_1 @ sk_C) = (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['93', '94'])).
% 0.39/0.58  thf('96', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['51', '52'])).
% 0.39/0.58  thf('97', plain, (![X16 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 0.39/0.58      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.39/0.58  thf('98', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 0.39/0.58      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.39/0.58  thf('99', plain, (![X16 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X16)) = (X16))),
% 0.39/0.58      inference('demod', [status(thm)], ['97', '98'])).
% 0.39/0.58  thf('100', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('101', plain,
% 0.39/0.58      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.39/0.58         ((v4_relat_1 @ X20 @ X21)
% 0.39/0.58          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.39/0.58      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.39/0.58  thf('102', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.39/0.58      inference('sup-', [status(thm)], ['100', '101'])).
% 0.39/0.58  thf('103', plain,
% 0.39/0.58      (![X5 : $i, X6 : $i]:
% 0.39/0.58         (~ (v4_relat_1 @ X5 @ X6)
% 0.39/0.58          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 0.39/0.58          | ~ (v1_relat_1 @ X5))),
% 0.39/0.58      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.39/0.58  thf('104', plain,
% 0.39/0.58      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['102', '103'])).
% 0.39/0.58  thf('105', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.58      inference('demod', [status(thm)], ['35', '36'])).
% 0.39/0.58  thf('106', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.39/0.58      inference('demod', [status(thm)], ['104', '105'])).
% 0.39/0.58  thf('107', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['51', '52'])).
% 0.39/0.58  thf('108', plain,
% 0.39/0.58      (![X16 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X16)) = (X16))),
% 0.39/0.58      inference('demod', [status(thm)], ['97', '98'])).
% 0.39/0.58  thf('109', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['95', '96', '99', '106', '107', '108'])).
% 0.39/0.58  thf('110', plain,
% 0.39/0.58      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.39/0.58         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.39/0.58      inference('demod', [status(thm)], ['16', '17'])).
% 0.39/0.58  thf('111', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(t26_funct_2, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.58     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.39/0.58         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.58       ( ![E:$i]:
% 0.39/0.58         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.39/0.58             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.39/0.58           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 0.39/0.58             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 0.39/0.58               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 0.39/0.58  thf('112', plain,
% 0.39/0.58      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.39/0.58         (~ (v1_funct_1 @ X44)
% 0.39/0.58          | ~ (v1_funct_2 @ X44 @ X45 @ X46)
% 0.39/0.58          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 0.39/0.58          | ~ (v2_funct_1 @ (k1_partfun1 @ X47 @ X45 @ X45 @ X46 @ X48 @ X44))
% 0.39/0.58          | (v2_funct_1 @ X48)
% 0.39/0.58          | ((X46) = (k1_xboole_0))
% 0.39/0.58          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X45)))
% 0.39/0.58          | ~ (v1_funct_2 @ X48 @ X47 @ X45)
% 0.39/0.58          | ~ (v1_funct_1 @ X48))),
% 0.39/0.58      inference('cnf', [status(esa)], [t26_funct_2])).
% 0.39/0.58  thf('113', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.39/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.39/0.58          | ((sk_A) = (k1_xboole_0))
% 0.39/0.58          | (v2_funct_1 @ X0)
% 0.39/0.58          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.39/0.58          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.39/0.58          | ~ (v1_funct_1 @ sk_D))),
% 0.39/0.58      inference('sup-', [status(thm)], ['111', '112'])).
% 0.39/0.58  thf('114', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('115', plain, ((v1_funct_1 @ sk_D)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('116', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.39/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.39/0.58          | ((sk_A) = (k1_xboole_0))
% 0.39/0.58          | (v2_funct_1 @ X0)
% 0.39/0.58          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 0.39/0.58      inference('demod', [status(thm)], ['113', '114', '115'])).
% 0.39/0.58  thf('117', plain,
% 0.39/0.58      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 0.39/0.58        | (v2_funct_1 @ sk_C)
% 0.39/0.58        | ((sk_A) = (k1_xboole_0))
% 0.39/0.58        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.39/0.58        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.39/0.58        | ~ (v1_funct_1 @ sk_C))),
% 0.39/0.58      inference('sup-', [status(thm)], ['110', '116'])).
% 0.39/0.58  thf('118', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('119', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('120', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('121', plain,
% 0.39/0.58      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 0.39/0.58        | (v2_funct_1 @ sk_C)
% 0.39/0.58        | ((sk_A) = (k1_xboole_0)))),
% 0.39/0.58      inference('demod', [status(thm)], ['117', '118', '119', '120'])).
% 0.39/0.58  thf('122', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['51', '52'])).
% 0.39/0.58  thf(fc4_funct_1, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.39/0.58       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.39/0.58  thf('123', plain, (![X19 : $i]: (v2_funct_1 @ (k6_relat_1 @ X19))),
% 0.39/0.58      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.39/0.58  thf('124', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 0.39/0.58      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.39/0.58  thf('125', plain, (![X19 : $i]: (v2_funct_1 @ (k6_partfun1 @ X19))),
% 0.39/0.58      inference('demod', [status(thm)], ['123', '124'])).
% 0.39/0.58  thf('126', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.39/0.58      inference('demod', [status(thm)], ['121', '122', '125'])).
% 0.39/0.58  thf('127', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.39/0.58      inference('split', [status(esa)], ['0'])).
% 0.39/0.58  thf('128', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['126', '127'])).
% 0.39/0.58  thf('129', plain, (~ ((v2_funct_1 @ sk_C))),
% 0.39/0.58      inference('sat_resolution*', [status(thm)], ['78', '79'])).
% 0.39/0.58  thf('130', plain, (((sk_A) = (k1_xboole_0))),
% 0.39/0.58      inference('simpl_trail', [status(thm)], ['128', '129'])).
% 0.39/0.58  thf('131', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.39/0.58      inference('demod', [status(thm)], ['109', '130'])).
% 0.39/0.58  thf(t64_relat_1, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( v1_relat_1 @ A ) =>
% 0.39/0.58       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.39/0.58           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.58         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.39/0.58  thf('132', plain,
% 0.39/0.58      (![X15 : $i]:
% 0.39/0.58         (((k1_relat_1 @ X15) != (k1_xboole_0))
% 0.39/0.58          | ((X15) = (k1_xboole_0))
% 0.39/0.58          | ~ (v1_relat_1 @ X15))),
% 0.39/0.58      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.39/0.58  thf('133', plain,
% 0.39/0.58      ((((k1_xboole_0) != (k1_xboole_0))
% 0.39/0.58        | ~ (v1_relat_1 @ sk_C)
% 0.39/0.58        | ((sk_C) = (k1_xboole_0)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['131', '132'])).
% 0.39/0.58  thf('134', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.58      inference('demod', [status(thm)], ['35', '36'])).
% 0.39/0.58  thf('135', plain,
% 0.39/0.58      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.39/0.58      inference('demod', [status(thm)], ['133', '134'])).
% 0.39/0.58  thf('136', plain, (((sk_C) = (k1_xboole_0))),
% 0.39/0.58      inference('simplify', [status(thm)], ['135'])).
% 0.39/0.58  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.39/0.58  thf('137', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.58      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.39/0.58  thf('138', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 0.39/0.58      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.39/0.58  thf('139', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.58      inference('demod', [status(thm)], ['137', '138'])).
% 0.39/0.58  thf('140', plain, (![X19 : $i]: (v2_funct_1 @ (k6_partfun1 @ X19))),
% 0.39/0.58      inference('demod', [status(thm)], ['123', '124'])).
% 0.39/0.58  thf('141', plain, ((v2_funct_1 @ k1_xboole_0)),
% 0.39/0.58      inference('sup+', [status(thm)], ['139', '140'])).
% 0.39/0.58  thf('142', plain, ($false),
% 0.39/0.58      inference('demod', [status(thm)], ['81', '136', '141'])).
% 0.39/0.58  
% 0.39/0.58  % SZS output end Refutation
% 0.39/0.58  
% 0.39/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

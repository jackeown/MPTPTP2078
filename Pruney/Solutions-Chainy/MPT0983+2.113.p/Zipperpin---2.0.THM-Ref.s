%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yqGoUucQB3

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:19 EST 2020

% Result     : Theorem 3.70s
% Output     : Refutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 813 expanded)
%              Number of leaves         :   46 ( 251 expanded)
%              Depth                    :   24
%              Number of atoms          : 1291 (15721 expanded)
%              Number of equality atoms :   48 ( 185 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

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
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X39 ) ) ) ) ),
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
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ( ( k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45 )
        = ( k5_relat_1 @ X42 @ X45 ) ) ) ),
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

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('52',plain,(
    ! [X41: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) ) ),
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
    ! [X22: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('55',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('56',plain,(
    ! [X22: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X22 ) )
      = X22 ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v5_relat_1 @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('59',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v5_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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
    ! [X22: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X22 ) )
      = X22 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('66',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['44','53','56','63','64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('68',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ( v5_relat_1 @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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
    ! [X32: $i,X33: $i] :
      ( ( ( k2_relat_1 @ X33 )
       != X32 )
      | ( v2_funct_2 @ X33 @ X32 )
      | ~ ( v5_relat_1 @ X33 @ X32 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('72',plain,(
    ! [X33: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ~ ( v5_relat_1 @ X33 @ ( k2_relat_1 @ X33 ) )
      | ( v2_funct_2 @ X33 @ ( k2_relat_1 @ X33 ) ) ) ),
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
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('79',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('81',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','81'])).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('83',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('84',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('85',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_xboole_0 @ X10 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('86',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('89',plain,(
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

thf('90',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X51 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X52 @ X50 @ X50 @ X51 @ X53 @ X49 ) )
      | ( v2_funct_1 @ X53 )
      | ( X51 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X50 ) ) )
      | ~ ( v1_funct_2 @ X53 @ X52 @ X50 )
      | ~ ( v1_funct_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['88','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['95','96','97','98'])).

thf('100',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('101',plain,(
    ! [X24: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('102',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('103',plain,(
    ! [X24: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X24 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['99','100','103'])).

thf('105',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','81'])).

thf('106',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['104','105'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('107',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('108',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['87','106','107'])).

thf('109',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('110',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 )
      | ( X4 = X5 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    k1_xboole_0 = sk_C ),
    inference('sup-',[status(thm)],['108','111'])).

thf('113',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('114',plain,(
    ! [X22: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X22 ) )
      = X22 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('115',plain,(
    ! [X18: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('118',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('119',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X23 ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['116','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( k1_xboole_0
    = ( k6_partfun1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['113','122'])).

thf('124',plain,(
    ! [X24: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X24 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('125',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    $false ),
    inference(demod,[status(thm)],['82','112','125'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yqGoUucQB3
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:11:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 3.70/3.91  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.70/3.91  % Solved by: fo/fo7.sh
% 3.70/3.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.70/3.91  % done 3315 iterations in 3.452s
% 3.70/3.91  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.70/3.91  % SZS output start Refutation
% 3.70/3.91  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.70/3.91  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.70/3.91  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.70/3.91  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 3.70/3.91  thf(sk_D_type, type, sk_D: $i).
% 3.70/3.91  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.70/3.91  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.70/3.91  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.70/3.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.70/3.91  thf(sk_A_type, type, sk_A: $i).
% 3.70/3.91  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.70/3.91  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.70/3.91  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.70/3.91  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.70/3.91  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 3.70/3.91  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.70/3.91  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.70/3.91  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.70/3.91  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.70/3.91  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.70/3.91  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.70/3.91  thf(sk_C_type, type, sk_C: $i).
% 3.70/3.91  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.70/3.91  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.70/3.91  thf(sk_B_type, type, sk_B: $i).
% 3.70/3.91  thf(t29_funct_2, conjecture,
% 3.70/3.91    (![A:$i,B:$i,C:$i]:
% 3.70/3.91     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.70/3.91         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.70/3.91       ( ![D:$i]:
% 3.70/3.91         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.70/3.91             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.70/3.91           ( ( r2_relset_1 @
% 3.70/3.91               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.70/3.91               ( k6_partfun1 @ A ) ) =>
% 3.70/3.91             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 3.70/3.91  thf(zf_stmt_0, negated_conjecture,
% 3.70/3.91    (~( ![A:$i,B:$i,C:$i]:
% 3.70/3.91        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.70/3.91            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.70/3.91          ( ![D:$i]:
% 3.70/3.91            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.70/3.91                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.70/3.91              ( ( r2_relset_1 @
% 3.70/3.91                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.70/3.91                  ( k6_partfun1 @ A ) ) =>
% 3.70/3.91                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 3.70/3.91    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 3.70/3.91  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 3.70/3.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.91  thf('1', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.70/3.91      inference('split', [status(esa)], ['0'])).
% 3.70/3.91  thf('2', plain,
% 3.70/3.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.70/3.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.91  thf('3', plain,
% 3.70/3.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.70/3.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.91  thf(dt_k1_partfun1, axiom,
% 3.70/3.91    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.70/3.91     ( ( ( v1_funct_1 @ E ) & 
% 3.70/3.91         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.70/3.91         ( v1_funct_1 @ F ) & 
% 3.70/3.91         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.70/3.91       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 3.70/3.91         ( m1_subset_1 @
% 3.70/3.91           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.70/3.91           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 3.70/3.91  thf('4', plain,
% 3.70/3.91      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 3.70/3.91         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 3.70/3.91          | ~ (v1_funct_1 @ X34)
% 3.70/3.91          | ~ (v1_funct_1 @ X37)
% 3.70/3.91          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 3.70/3.91          | (m1_subset_1 @ (k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37) @ 
% 3.70/3.91             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X39))))),
% 3.70/3.91      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.70/3.91  thf('5', plain,
% 3.70/3.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.70/3.91         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.70/3.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.70/3.91          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.70/3.91          | ~ (v1_funct_1 @ X1)
% 3.70/3.91          | ~ (v1_funct_1 @ sk_C))),
% 3.70/3.91      inference('sup-', [status(thm)], ['3', '4'])).
% 3.70/3.91  thf('6', plain, ((v1_funct_1 @ sk_C)),
% 3.70/3.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.91  thf('7', plain,
% 3.70/3.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.70/3.91         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.70/3.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.70/3.91          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.70/3.91          | ~ (v1_funct_1 @ X1))),
% 3.70/3.91      inference('demod', [status(thm)], ['5', '6'])).
% 3.70/3.91  thf('8', plain,
% 3.70/3.91      ((~ (v1_funct_1 @ sk_D)
% 3.70/3.91        | (m1_subset_1 @ 
% 3.70/3.91           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.70/3.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.70/3.91      inference('sup-', [status(thm)], ['2', '7'])).
% 3.70/3.91  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 3.70/3.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.91  thf('10', plain,
% 3.70/3.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.70/3.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.91  thf('11', plain,
% 3.70/3.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.70/3.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.91  thf(redefinition_k1_partfun1, axiom,
% 3.70/3.91    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.70/3.91     ( ( ( v1_funct_1 @ E ) & 
% 3.70/3.91         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.70/3.91         ( v1_funct_1 @ F ) & 
% 3.70/3.91         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.70/3.91       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 3.70/3.91  thf('12', plain,
% 3.70/3.91      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 3.70/3.91         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 3.70/3.91          | ~ (v1_funct_1 @ X42)
% 3.70/3.91          | ~ (v1_funct_1 @ X45)
% 3.70/3.91          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 3.70/3.91          | ((k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45)
% 3.70/3.91              = (k5_relat_1 @ X42 @ X45)))),
% 3.70/3.91      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 3.70/3.91  thf('13', plain,
% 3.70/3.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.70/3.91         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 3.70/3.91            = (k5_relat_1 @ sk_C @ X0))
% 3.70/3.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.70/3.91          | ~ (v1_funct_1 @ X0)
% 3.70/3.91          | ~ (v1_funct_1 @ sk_C))),
% 3.70/3.91      inference('sup-', [status(thm)], ['11', '12'])).
% 3.70/3.91  thf('14', plain, ((v1_funct_1 @ sk_C)),
% 3.70/3.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.91  thf('15', plain,
% 3.70/3.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.70/3.91         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 3.70/3.91            = (k5_relat_1 @ sk_C @ X0))
% 3.70/3.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.70/3.91          | ~ (v1_funct_1 @ X0))),
% 3.70/3.91      inference('demod', [status(thm)], ['13', '14'])).
% 3.70/3.91  thf('16', plain,
% 3.70/3.91      ((~ (v1_funct_1 @ sk_D)
% 3.70/3.91        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.70/3.91            = (k5_relat_1 @ sk_C @ sk_D)))),
% 3.70/3.91      inference('sup-', [status(thm)], ['10', '15'])).
% 3.70/3.91  thf('17', plain, ((v1_funct_1 @ sk_D)),
% 3.70/3.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.91  thf('18', plain,
% 3.70/3.91      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.70/3.91         = (k5_relat_1 @ sk_C @ sk_D))),
% 3.70/3.91      inference('demod', [status(thm)], ['16', '17'])).
% 3.70/3.91  thf('19', plain,
% 3.70/3.91      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 3.70/3.91        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.70/3.91      inference('demod', [status(thm)], ['8', '9', '18'])).
% 3.70/3.91  thf(cc2_relat_1, axiom,
% 3.70/3.91    (![A:$i]:
% 3.70/3.91     ( ( v1_relat_1 @ A ) =>
% 3.70/3.91       ( ![B:$i]:
% 3.70/3.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 3.70/3.91  thf('20', plain,
% 3.70/3.91      (![X12 : $i, X13 : $i]:
% 3.70/3.91         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 3.70/3.91          | (v1_relat_1 @ X12)
% 3.70/3.91          | ~ (v1_relat_1 @ X13))),
% 3.70/3.91      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.70/3.91  thf('21', plain,
% 3.70/3.91      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 3.70/3.91        | (v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))),
% 3.70/3.91      inference('sup-', [status(thm)], ['19', '20'])).
% 3.70/3.91  thf(fc6_relat_1, axiom,
% 3.70/3.91    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 3.70/3.91  thf('22', plain,
% 3.70/3.91      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 3.70/3.91      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.70/3.91  thf('23', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))),
% 3.70/3.91      inference('demod', [status(thm)], ['21', '22'])).
% 3.70/3.91  thf(t45_relat_1, axiom,
% 3.70/3.91    (![A:$i]:
% 3.70/3.91     ( ( v1_relat_1 @ A ) =>
% 3.70/3.91       ( ![B:$i]:
% 3.70/3.91         ( ( v1_relat_1 @ B ) =>
% 3.70/3.91           ( r1_tarski @
% 3.70/3.91             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 3.70/3.91  thf('24', plain,
% 3.70/3.91      (![X19 : $i, X20 : $i]:
% 3.70/3.91         (~ (v1_relat_1 @ X19)
% 3.70/3.91          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X20 @ X19)) @ 
% 3.70/3.91             (k2_relat_1 @ X19))
% 3.70/3.91          | ~ (v1_relat_1 @ X20))),
% 3.70/3.91      inference('cnf', [status(esa)], [t45_relat_1])).
% 3.70/3.91  thf(d19_relat_1, axiom,
% 3.70/3.91    (![A:$i,B:$i]:
% 3.70/3.91     ( ( v1_relat_1 @ B ) =>
% 3.70/3.91       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 3.70/3.91  thf('25', plain,
% 3.70/3.91      (![X14 : $i, X15 : $i]:
% 3.70/3.91         (~ (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 3.70/3.91          | (v5_relat_1 @ X14 @ X15)
% 3.70/3.91          | ~ (v1_relat_1 @ X14))),
% 3.70/3.91      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.70/3.91  thf('26', plain,
% 3.70/3.91      (![X0 : $i, X1 : $i]:
% 3.70/3.91         (~ (v1_relat_1 @ X1)
% 3.70/3.91          | ~ (v1_relat_1 @ X0)
% 3.70/3.91          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 3.70/3.91          | (v5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 3.70/3.91      inference('sup-', [status(thm)], ['24', '25'])).
% 3.70/3.91  thf('27', plain,
% 3.70/3.91      (((v5_relat_1 @ (k5_relat_1 @ sk_C @ sk_D) @ (k2_relat_1 @ sk_D))
% 3.70/3.91        | ~ (v1_relat_1 @ sk_D)
% 3.70/3.91        | ~ (v1_relat_1 @ sk_C))),
% 3.70/3.91      inference('sup-', [status(thm)], ['23', '26'])).
% 3.70/3.91  thf('28', plain,
% 3.70/3.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.70/3.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.91  thf('29', plain,
% 3.70/3.91      (![X12 : $i, X13 : $i]:
% 3.70/3.91         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 3.70/3.91          | (v1_relat_1 @ X12)
% 3.70/3.91          | ~ (v1_relat_1 @ X13))),
% 3.70/3.91      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.70/3.91  thf('30', plain,
% 3.70/3.91      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 3.70/3.91      inference('sup-', [status(thm)], ['28', '29'])).
% 3.70/3.91  thf('31', plain,
% 3.70/3.91      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 3.70/3.91      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.70/3.91  thf('32', plain, ((v1_relat_1 @ sk_D)),
% 3.70/3.91      inference('demod', [status(thm)], ['30', '31'])).
% 3.70/3.91  thf('33', plain,
% 3.70/3.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.70/3.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.91  thf('34', plain,
% 3.70/3.91      (![X12 : $i, X13 : $i]:
% 3.70/3.91         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 3.70/3.91          | (v1_relat_1 @ X12)
% 3.70/3.91          | ~ (v1_relat_1 @ X13))),
% 3.70/3.91      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.70/3.91  thf('35', plain,
% 3.70/3.91      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 3.70/3.91      inference('sup-', [status(thm)], ['33', '34'])).
% 3.70/3.91  thf('36', plain,
% 3.70/3.91      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 3.70/3.91      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.70/3.91  thf('37', plain, ((v1_relat_1 @ sk_C)),
% 3.70/3.91      inference('demod', [status(thm)], ['35', '36'])).
% 3.70/3.91  thf('38', plain,
% 3.70/3.91      ((v5_relat_1 @ (k5_relat_1 @ sk_C @ sk_D) @ (k2_relat_1 @ sk_D))),
% 3.70/3.91      inference('demod', [status(thm)], ['27', '32', '37'])).
% 3.70/3.91  thf('39', plain,
% 3.70/3.91      (![X14 : $i, X15 : $i]:
% 3.70/3.91         (~ (v5_relat_1 @ X14 @ X15)
% 3.70/3.91          | (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 3.70/3.91          | ~ (v1_relat_1 @ X14))),
% 3.70/3.91      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.70/3.91  thf('40', plain,
% 3.70/3.91      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 3.70/3.91        | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ 
% 3.70/3.91           (k2_relat_1 @ sk_D)))),
% 3.70/3.91      inference('sup-', [status(thm)], ['38', '39'])).
% 3.70/3.91  thf('41', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))),
% 3.70/3.91      inference('demod', [status(thm)], ['21', '22'])).
% 3.70/3.91  thf('42', plain,
% 3.70/3.91      ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ 
% 3.70/3.91        (k2_relat_1 @ sk_D))),
% 3.70/3.91      inference('demod', [status(thm)], ['40', '41'])).
% 3.70/3.91  thf(d10_xboole_0, axiom,
% 3.70/3.91    (![A:$i,B:$i]:
% 3.70/3.91     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.70/3.91  thf('43', plain,
% 3.70/3.91      (![X0 : $i, X2 : $i]:
% 3.70/3.91         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.70/3.91      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.70/3.91  thf('44', plain,
% 3.70/3.91      ((~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 3.70/3.91           (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 3.70/3.91        | ((k2_relat_1 @ sk_D) = (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))))),
% 3.70/3.91      inference('sup-', [status(thm)], ['42', '43'])).
% 3.70/3.91  thf('45', plain,
% 3.70/3.91      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.70/3.91        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.70/3.91        (k6_partfun1 @ sk_A))),
% 3.70/3.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.91  thf('46', plain,
% 3.70/3.91      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.70/3.91         = (k5_relat_1 @ sk_C @ sk_D))),
% 3.70/3.91      inference('demod', [status(thm)], ['16', '17'])).
% 3.70/3.91  thf('47', plain,
% 3.70/3.91      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 3.70/3.91        (k6_partfun1 @ sk_A))),
% 3.70/3.91      inference('demod', [status(thm)], ['45', '46'])).
% 3.70/3.91  thf('48', plain,
% 3.70/3.91      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 3.70/3.91        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.70/3.91      inference('demod', [status(thm)], ['8', '9', '18'])).
% 3.70/3.91  thf(redefinition_r2_relset_1, axiom,
% 3.70/3.91    (![A:$i,B:$i,C:$i,D:$i]:
% 3.70/3.91     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.70/3.91         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.70/3.91       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.70/3.91  thf('49', plain,
% 3.70/3.91      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 3.70/3.91         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 3.70/3.91          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 3.70/3.91          | ((X28) = (X31))
% 3.70/3.91          | ~ (r2_relset_1 @ X29 @ X30 @ X28 @ X31))),
% 3.70/3.91      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.70/3.91  thf('50', plain,
% 3.70/3.91      (![X0 : $i]:
% 3.70/3.91         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 3.70/3.91          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 3.70/3.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.70/3.91      inference('sup-', [status(thm)], ['48', '49'])).
% 3.70/3.91  thf('51', plain,
% 3.70/3.91      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 3.70/3.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.70/3.91        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 3.70/3.91      inference('sup-', [status(thm)], ['47', '50'])).
% 3.70/3.91  thf(dt_k6_partfun1, axiom,
% 3.70/3.91    (![A:$i]:
% 3.70/3.91     ( ( m1_subset_1 @
% 3.70/3.91         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 3.70/3.91       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 3.70/3.91  thf('52', plain,
% 3.70/3.91      (![X41 : $i]:
% 3.70/3.91         (m1_subset_1 @ (k6_partfun1 @ X41) @ 
% 3.70/3.91          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))),
% 3.70/3.91      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 3.70/3.91  thf('53', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 3.70/3.91      inference('demod', [status(thm)], ['51', '52'])).
% 3.70/3.91  thf(t71_relat_1, axiom,
% 3.70/3.91    (![A:$i]:
% 3.70/3.91     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 3.70/3.91       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 3.70/3.91  thf('54', plain, (![X22 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 3.70/3.91      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.70/3.91  thf(redefinition_k6_partfun1, axiom,
% 3.70/3.91    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 3.70/3.91  thf('55', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 3.70/3.91      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.70/3.91  thf('56', plain, (![X22 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X22)) = (X22))),
% 3.70/3.91      inference('demod', [status(thm)], ['54', '55'])).
% 3.70/3.91  thf('57', plain,
% 3.70/3.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.70/3.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.91  thf(cc2_relset_1, axiom,
% 3.70/3.91    (![A:$i,B:$i,C:$i]:
% 3.70/3.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.70/3.91       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.70/3.91  thf('58', plain,
% 3.70/3.91      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.70/3.91         ((v5_relat_1 @ X25 @ X27)
% 3.70/3.91          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 3.70/3.91      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.70/3.91  thf('59', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 3.70/3.91      inference('sup-', [status(thm)], ['57', '58'])).
% 3.70/3.91  thf('60', plain,
% 3.70/3.91      (![X14 : $i, X15 : $i]:
% 3.70/3.91         (~ (v5_relat_1 @ X14 @ X15)
% 3.70/3.91          | (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 3.70/3.91          | ~ (v1_relat_1 @ X14))),
% 3.70/3.91      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.70/3.91  thf('61', plain,
% 3.70/3.91      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 3.70/3.91      inference('sup-', [status(thm)], ['59', '60'])).
% 3.70/3.91  thf('62', plain, ((v1_relat_1 @ sk_D)),
% 3.70/3.91      inference('demod', [status(thm)], ['30', '31'])).
% 3.70/3.91  thf('63', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 3.70/3.91      inference('demod', [status(thm)], ['61', '62'])).
% 3.70/3.91  thf('64', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 3.70/3.91      inference('demod', [status(thm)], ['51', '52'])).
% 3.70/3.91  thf('65', plain, (![X22 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X22)) = (X22))),
% 3.70/3.91      inference('demod', [status(thm)], ['54', '55'])).
% 3.70/3.91  thf('66', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.70/3.91      inference('demod', [status(thm)], ['44', '53', '56', '63', '64', '65'])).
% 3.70/3.91  thf('67', plain,
% 3.70/3.91      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 3.70/3.91      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.70/3.91  thf('68', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.70/3.91      inference('simplify', [status(thm)], ['67'])).
% 3.70/3.91  thf('69', plain,
% 3.70/3.91      (![X14 : $i, X15 : $i]:
% 3.70/3.91         (~ (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 3.70/3.91          | (v5_relat_1 @ X14 @ X15)
% 3.70/3.91          | ~ (v1_relat_1 @ X14))),
% 3.70/3.91      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.70/3.91  thf('70', plain,
% 3.70/3.91      (![X0 : $i]:
% 3.70/3.91         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 3.70/3.91      inference('sup-', [status(thm)], ['68', '69'])).
% 3.70/3.91  thf(d3_funct_2, axiom,
% 3.70/3.91    (![A:$i,B:$i]:
% 3.70/3.91     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 3.70/3.91       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 3.70/3.91  thf('71', plain,
% 3.70/3.91      (![X32 : $i, X33 : $i]:
% 3.70/3.91         (((k2_relat_1 @ X33) != (X32))
% 3.70/3.91          | (v2_funct_2 @ X33 @ X32)
% 3.70/3.91          | ~ (v5_relat_1 @ X33 @ X32)
% 3.70/3.91          | ~ (v1_relat_1 @ X33))),
% 3.70/3.91      inference('cnf', [status(esa)], [d3_funct_2])).
% 3.70/3.91  thf('72', plain,
% 3.70/3.91      (![X33 : $i]:
% 3.70/3.91         (~ (v1_relat_1 @ X33)
% 3.70/3.91          | ~ (v5_relat_1 @ X33 @ (k2_relat_1 @ X33))
% 3.70/3.91          | (v2_funct_2 @ X33 @ (k2_relat_1 @ X33)))),
% 3.70/3.91      inference('simplify', [status(thm)], ['71'])).
% 3.70/3.91  thf('73', plain,
% 3.70/3.91      (![X0 : $i]:
% 3.70/3.91         (~ (v1_relat_1 @ X0)
% 3.70/3.91          | (v2_funct_2 @ X0 @ (k2_relat_1 @ X0))
% 3.70/3.91          | ~ (v1_relat_1 @ X0))),
% 3.70/3.91      inference('sup-', [status(thm)], ['70', '72'])).
% 3.70/3.91  thf('74', plain,
% 3.70/3.91      (![X0 : $i]:
% 3.70/3.91         ((v2_funct_2 @ X0 @ (k2_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 3.70/3.91      inference('simplify', [status(thm)], ['73'])).
% 3.70/3.91  thf('75', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 3.70/3.91      inference('sup+', [status(thm)], ['66', '74'])).
% 3.70/3.91  thf('76', plain, ((v1_relat_1 @ sk_D)),
% 3.70/3.91      inference('demod', [status(thm)], ['30', '31'])).
% 3.70/3.91  thf('77', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 3.70/3.91      inference('demod', [status(thm)], ['75', '76'])).
% 3.70/3.91  thf('78', plain,
% 3.70/3.91      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 3.70/3.91      inference('split', [status(esa)], ['0'])).
% 3.70/3.91  thf('79', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 3.70/3.91      inference('sup-', [status(thm)], ['77', '78'])).
% 3.70/3.91  thf('80', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 3.70/3.91      inference('split', [status(esa)], ['0'])).
% 3.70/3.91  thf('81', plain, (~ ((v2_funct_1 @ sk_C))),
% 3.70/3.91      inference('sat_resolution*', [status(thm)], ['79', '80'])).
% 3.70/3.91  thf('82', plain, (~ (v2_funct_1 @ sk_C)),
% 3.70/3.91      inference('simpl_trail', [status(thm)], ['1', '81'])).
% 3.70/3.91  thf(fc4_zfmisc_1, axiom,
% 3.70/3.91    (![A:$i,B:$i]:
% 3.70/3.91     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 3.70/3.91  thf('83', plain,
% 3.70/3.91      (![X8 : $i, X9 : $i]:
% 3.70/3.91         (~ (v1_xboole_0 @ X8) | (v1_xboole_0 @ (k2_zfmisc_1 @ X8 @ X9)))),
% 3.70/3.91      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 3.70/3.91  thf('84', plain,
% 3.70/3.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.70/3.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.91  thf(cc1_subset_1, axiom,
% 3.70/3.91    (![A:$i]:
% 3.70/3.91     ( ( v1_xboole_0 @ A ) =>
% 3.70/3.91       ( ![B:$i]:
% 3.70/3.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 3.70/3.91  thf('85', plain,
% 3.70/3.91      (![X10 : $i, X11 : $i]:
% 3.70/3.91         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 3.70/3.91          | (v1_xboole_0 @ X10)
% 3.70/3.91          | ~ (v1_xboole_0 @ X11))),
% 3.70/3.91      inference('cnf', [status(esa)], [cc1_subset_1])).
% 3.70/3.91  thf('86', plain,
% 3.70/3.91      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 3.70/3.91      inference('sup-', [status(thm)], ['84', '85'])).
% 3.70/3.91  thf('87', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C))),
% 3.70/3.91      inference('sup-', [status(thm)], ['83', '86'])).
% 3.70/3.91  thf('88', plain,
% 3.70/3.91      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.70/3.91         = (k5_relat_1 @ sk_C @ sk_D))),
% 3.70/3.91      inference('demod', [status(thm)], ['16', '17'])).
% 3.70/3.91  thf('89', plain,
% 3.70/3.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.70/3.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.91  thf(t26_funct_2, axiom,
% 3.70/3.91    (![A:$i,B:$i,C:$i,D:$i]:
% 3.70/3.91     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.70/3.91         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.70/3.91       ( ![E:$i]:
% 3.70/3.91         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.70/3.91             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.70/3.91           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 3.70/3.91             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 3.70/3.91               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 3.70/3.91  thf('90', plain,
% 3.70/3.91      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 3.70/3.91         (~ (v1_funct_1 @ X49)
% 3.70/3.91          | ~ (v1_funct_2 @ X49 @ X50 @ X51)
% 3.70/3.91          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 3.70/3.91          | ~ (v2_funct_1 @ (k1_partfun1 @ X52 @ X50 @ X50 @ X51 @ X53 @ X49))
% 3.70/3.91          | (v2_funct_1 @ X53)
% 3.70/3.91          | ((X51) = (k1_xboole_0))
% 3.70/3.91          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 3.70/3.91          | ~ (v1_funct_2 @ X53 @ X52 @ X50)
% 3.70/3.91          | ~ (v1_funct_1 @ X53))),
% 3.70/3.91      inference('cnf', [status(esa)], [t26_funct_2])).
% 3.70/3.91  thf('91', plain,
% 3.70/3.91      (![X0 : $i, X1 : $i]:
% 3.70/3.91         (~ (v1_funct_1 @ X0)
% 3.70/3.91          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.70/3.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.70/3.91          | ((sk_A) = (k1_xboole_0))
% 3.70/3.91          | (v2_funct_1 @ X0)
% 3.70/3.91          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 3.70/3.91          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.70/3.91          | ~ (v1_funct_1 @ sk_D))),
% 3.70/3.91      inference('sup-', [status(thm)], ['89', '90'])).
% 3.70/3.91  thf('92', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.70/3.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.91  thf('93', plain, ((v1_funct_1 @ sk_D)),
% 3.70/3.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.91  thf('94', plain,
% 3.70/3.91      (![X0 : $i, X1 : $i]:
% 3.70/3.91         (~ (v1_funct_1 @ X0)
% 3.70/3.91          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.70/3.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.70/3.91          | ((sk_A) = (k1_xboole_0))
% 3.70/3.91          | (v2_funct_1 @ X0)
% 3.70/3.91          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 3.70/3.91      inference('demod', [status(thm)], ['91', '92', '93'])).
% 3.70/3.91  thf('95', plain,
% 3.70/3.91      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 3.70/3.91        | (v2_funct_1 @ sk_C)
% 3.70/3.91        | ((sk_A) = (k1_xboole_0))
% 3.70/3.91        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 3.70/3.91        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.70/3.91        | ~ (v1_funct_1 @ sk_C))),
% 3.70/3.91      inference('sup-', [status(thm)], ['88', '94'])).
% 3.70/3.91  thf('96', plain,
% 3.70/3.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.70/3.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.91  thf('97', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.70/3.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.91  thf('98', plain, ((v1_funct_1 @ sk_C)),
% 3.70/3.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.70/3.91  thf('99', plain,
% 3.70/3.91      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 3.70/3.91        | (v2_funct_1 @ sk_C)
% 3.70/3.91        | ((sk_A) = (k1_xboole_0)))),
% 3.70/3.91      inference('demod', [status(thm)], ['95', '96', '97', '98'])).
% 3.70/3.91  thf('100', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 3.70/3.91      inference('demod', [status(thm)], ['51', '52'])).
% 3.70/3.91  thf(fc4_funct_1, axiom,
% 3.70/3.91    (![A:$i]:
% 3.70/3.91     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 3.70/3.91       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 3.70/3.91  thf('101', plain, (![X24 : $i]: (v2_funct_1 @ (k6_relat_1 @ X24))),
% 3.70/3.91      inference('cnf', [status(esa)], [fc4_funct_1])).
% 3.70/3.91  thf('102', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 3.70/3.91      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.70/3.91  thf('103', plain, (![X24 : $i]: (v2_funct_1 @ (k6_partfun1 @ X24))),
% 3.70/3.91      inference('demod', [status(thm)], ['101', '102'])).
% 3.70/3.91  thf('104', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 3.70/3.91      inference('demod', [status(thm)], ['99', '100', '103'])).
% 3.70/3.91  thf('105', plain, (~ (v2_funct_1 @ sk_C)),
% 3.70/3.91      inference('simpl_trail', [status(thm)], ['1', '81'])).
% 3.70/3.91  thf('106', plain, (((sk_A) = (k1_xboole_0))),
% 3.70/3.91      inference('sup-', [status(thm)], ['104', '105'])).
% 3.70/3.91  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.70/3.91  thf('107', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.70/3.91      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.70/3.91  thf('108', plain, ((v1_xboole_0 @ sk_C)),
% 3.70/3.91      inference('demod', [status(thm)], ['87', '106', '107'])).
% 3.70/3.91  thf('109', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.70/3.91      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.70/3.91  thf(t8_boole, axiom,
% 3.70/3.91    (![A:$i,B:$i]:
% 3.70/3.91     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 3.70/3.91  thf('110', plain,
% 3.70/3.91      (![X4 : $i, X5 : $i]:
% 3.70/3.91         (~ (v1_xboole_0 @ X4) | ~ (v1_xboole_0 @ X5) | ((X4) = (X5)))),
% 3.70/3.91      inference('cnf', [status(esa)], [t8_boole])).
% 3.70/3.91  thf('111', plain,
% 3.70/3.91      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.70/3.91      inference('sup-', [status(thm)], ['109', '110'])).
% 3.70/3.91  thf('112', plain, (((k1_xboole_0) = (sk_C))),
% 3.70/3.91      inference('sup-', [status(thm)], ['108', '111'])).
% 3.70/3.91  thf('113', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.70/3.91      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.70/3.91  thf('114', plain,
% 3.70/3.91      (![X22 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X22)) = (X22))),
% 3.70/3.91      inference('demod', [status(thm)], ['54', '55'])).
% 3.70/3.91  thf(fc9_relat_1, axiom,
% 3.70/3.91    (![A:$i]:
% 3.70/3.91     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 3.70/3.91       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 3.70/3.91  thf('115', plain,
% 3.70/3.91      (![X18 : $i]:
% 3.70/3.91         (~ (v1_xboole_0 @ (k2_relat_1 @ X18))
% 3.70/3.91          | ~ (v1_relat_1 @ X18)
% 3.70/3.91          | (v1_xboole_0 @ X18))),
% 3.70/3.91      inference('cnf', [status(esa)], [fc9_relat_1])).
% 3.70/3.91  thf('116', plain,
% 3.70/3.91      (![X0 : $i]:
% 3.70/3.91         (~ (v1_xboole_0 @ X0)
% 3.70/3.91          | (v1_xboole_0 @ (k6_partfun1 @ X0))
% 3.70/3.91          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 3.70/3.91      inference('sup-', [status(thm)], ['114', '115'])).
% 3.70/3.91  thf('117', plain, (![X23 : $i]: (v1_relat_1 @ (k6_relat_1 @ X23))),
% 3.70/3.91      inference('cnf', [status(esa)], [fc4_funct_1])).
% 3.70/3.91  thf('118', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 3.70/3.91      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.70/3.91  thf('119', plain, (![X23 : $i]: (v1_relat_1 @ (k6_partfun1 @ X23))),
% 3.70/3.91      inference('demod', [status(thm)], ['117', '118'])).
% 3.70/3.91  thf('120', plain,
% 3.70/3.91      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k6_partfun1 @ X0)))),
% 3.70/3.91      inference('demod', [status(thm)], ['116', '119'])).
% 3.70/3.91  thf('121', plain,
% 3.70/3.91      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.70/3.91      inference('sup-', [status(thm)], ['109', '110'])).
% 3.70/3.91  thf('122', plain,
% 3.70/3.91      (![X0 : $i]:
% 3.70/3.91         (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (k6_partfun1 @ X0)))),
% 3.70/3.91      inference('sup-', [status(thm)], ['120', '121'])).
% 3.70/3.91  thf('123', plain, (((k1_xboole_0) = (k6_partfun1 @ k1_xboole_0))),
% 3.70/3.91      inference('sup-', [status(thm)], ['113', '122'])).
% 3.70/3.91  thf('124', plain, (![X24 : $i]: (v2_funct_1 @ (k6_partfun1 @ X24))),
% 3.70/3.91      inference('demod', [status(thm)], ['101', '102'])).
% 3.70/3.91  thf('125', plain, ((v2_funct_1 @ k1_xboole_0)),
% 3.70/3.91      inference('sup+', [status(thm)], ['123', '124'])).
% 3.70/3.91  thf('126', plain, ($false),
% 3.70/3.91      inference('demod', [status(thm)], ['82', '112', '125'])).
% 3.70/3.91  
% 3.70/3.91  % SZS output end Refutation
% 3.70/3.91  
% 3.70/3.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.l9mPm7B0b6

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:25 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 758 expanded)
%              Number of leaves         :   43 ( 234 expanded)
%              Depth                    :   21
%              Number of atoms          : 1267 (14848 expanded)
%              Number of equality atoms :   67 ( 214 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( ( k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39 )
        = ( k5_relat_1 @ X36 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('22',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('23',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( X22 = X25 )
      | ~ ( r2_relset_1 @ X23 @ X24 @ X22 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','24'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('26',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('27',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('28',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) ) @ ( k2_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k2_relat_1 @ ( k6_partfun1 @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_D )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('32',plain,(
    ! [X16: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('33',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('34',plain,(
    ! [X16: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X16 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('36',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v5_relat_1 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('37',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('38',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v5_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('41',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('43',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('44',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['39','44'])).

thf('46',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('47',plain,(
    ! [X16: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X16 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('48',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['42','43'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('53',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['31','34','45','46','47','48','53'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('55',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k2_relat_1 @ X27 )
       != X26 )
      | ( v2_funct_2 @ X27 @ X26 )
      | ~ ( v5_relat_1 @ X27 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('56',plain,(
    ! [X27: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ~ ( v5_relat_1 @ X27 @ ( k2_relat_1 @ X27 ) )
      | ( v2_funct_2 @ X27 @ ( k2_relat_1 @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('58',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ( v5_relat_1 @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X27: $i] :
      ( ( v2_funct_2 @ X27 @ ( k2_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(clc,[status(thm)],['56','60'])).

thf('62',plain,
    ( ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['54','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['42','43'])).

thf('64',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('66',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('68',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','68'])).

thf('70',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('71',plain,(
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

thf('72',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X46 @ X44 @ X44 @ X45 @ X47 @ X43 ) )
      | ( v2_funct_1 @ X47 )
      | ( X45 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X47 @ X46 @ X44 )
      | ~ ( v1_funct_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['70','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','78','79','80'])).

thf('82',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('83',plain,(
    ! [X18: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('84',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('85',plain,(
    ! [X18: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X18 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['81','82','85'])).

thf('87',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('88',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v4_relat_1 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('91',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['89','90'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('92',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v4_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('93',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('95',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('97',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['88','97'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('99',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('100',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('101',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['66','67'])).

thf('103',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['101','102'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('104',plain,(
    ! [X14: $i] :
      ( ( ( k1_relat_1 @ X14 )
       != k1_xboole_0 )
      | ( X14 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('105',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('107',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    ! [X15: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('110',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('111',plain,(
    ! [X15: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X15 ) )
      = X15 ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X14: $i] :
      ( ( ( k1_relat_1 @ X14 )
       != k1_xboole_0 )
      | ( X14 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k6_partfun1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('115',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('116',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X17 ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k6_partfun1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['113','116'])).

thf('118',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ! [X18: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X18 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('120',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['118','119'])).

thf('121',plain,(
    $false ),
    inference(demod,[status(thm)],['69','108','120'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.l9mPm7B0b6
% 0.14/0.36  % Computer   : n011.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 20:55:12 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.47/0.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.64  % Solved by: fo/fo7.sh
% 0.47/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.64  % done 322 iterations in 0.165s
% 0.47/0.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.64  % SZS output start Refutation
% 0.47/0.64  thf(sk_D_type, type, sk_D: $i).
% 0.47/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.64  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.47/0.64  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.47/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.64  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.47/0.64  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.47/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.64  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.64  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.47/0.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.64  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.47/0.64  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.64  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.64  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.47/0.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.64  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.47/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.64  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.47/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.64  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.47/0.64  thf(t29_funct_2, conjecture,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.47/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.64       ( ![D:$i]:
% 0.47/0.64         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.47/0.64             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.47/0.64           ( ( r2_relset_1 @
% 0.47/0.64               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.47/0.64               ( k6_partfun1 @ A ) ) =>
% 0.47/0.64             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 0.47/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.64    (~( ![A:$i,B:$i,C:$i]:
% 0.47/0.64        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.47/0.64            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.64          ( ![D:$i]:
% 0.47/0.64            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.47/0.64                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.47/0.64              ( ( r2_relset_1 @
% 0.47/0.64                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.47/0.64                  ( k6_partfun1 @ A ) ) =>
% 0.47/0.64                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 0.47/0.64    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 0.47/0.64  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('1', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.47/0.64      inference('split', [status(esa)], ['0'])).
% 0.47/0.64  thf('2', plain,
% 0.47/0.64      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.47/0.64        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.47/0.64        (k6_partfun1 @ sk_A))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('3', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('4', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf(redefinition_k1_partfun1, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.47/0.64     ( ( ( v1_funct_1 @ E ) & 
% 0.47/0.64         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.47/0.64         ( v1_funct_1 @ F ) & 
% 0.47/0.64         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.47/0.64       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.47/0.64  thf('5', plain,
% 0.47/0.64      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.47/0.64         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.47/0.64          | ~ (v1_funct_1 @ X36)
% 0.47/0.64          | ~ (v1_funct_1 @ X39)
% 0.47/0.64          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.47/0.64          | ((k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39)
% 0.47/0.64              = (k5_relat_1 @ X36 @ X39)))),
% 0.47/0.64      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.47/0.64  thf('6', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.64         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.47/0.64            = (k5_relat_1 @ sk_C @ X0))
% 0.47/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.47/0.64          | ~ (v1_funct_1 @ X0)
% 0.47/0.64          | ~ (v1_funct_1 @ sk_C))),
% 0.47/0.64      inference('sup-', [status(thm)], ['4', '5'])).
% 0.47/0.64  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('8', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.64         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.47/0.64            = (k5_relat_1 @ sk_C @ X0))
% 0.47/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.47/0.64          | ~ (v1_funct_1 @ X0))),
% 0.47/0.64      inference('demod', [status(thm)], ['6', '7'])).
% 0.47/0.64  thf('9', plain,
% 0.47/0.64      ((~ (v1_funct_1 @ sk_D)
% 0.47/0.64        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.47/0.64            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['3', '8'])).
% 0.47/0.64  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('11', plain,
% 0.47/0.64      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.47/0.64         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.47/0.64      inference('demod', [status(thm)], ['9', '10'])).
% 0.47/0.64  thf('12', plain,
% 0.47/0.64      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.47/0.64        (k6_partfun1 @ sk_A))),
% 0.47/0.64      inference('demod', [status(thm)], ['2', '11'])).
% 0.47/0.64  thf('13', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('14', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf(dt_k1_partfun1, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.47/0.64     ( ( ( v1_funct_1 @ E ) & 
% 0.47/0.64         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.47/0.64         ( v1_funct_1 @ F ) & 
% 0.47/0.64         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.47/0.64       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.47/0.64         ( m1_subset_1 @
% 0.47/0.64           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.47/0.64           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.47/0.64  thf('15', plain,
% 0.47/0.64      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.47/0.64         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.47/0.64          | ~ (v1_funct_1 @ X28)
% 0.47/0.64          | ~ (v1_funct_1 @ X31)
% 0.47/0.64          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.47/0.64          | (m1_subset_1 @ (k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31) @ 
% 0.47/0.64             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X33))))),
% 0.47/0.64      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.47/0.64  thf('16', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.64         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.47/0.64           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.47/0.64          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.47/0.64          | ~ (v1_funct_1 @ X1)
% 0.47/0.64          | ~ (v1_funct_1 @ sk_C))),
% 0.47/0.64      inference('sup-', [status(thm)], ['14', '15'])).
% 0.47/0.64  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('18', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.64         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.47/0.64           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.47/0.64          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.47/0.64          | ~ (v1_funct_1 @ X1))),
% 0.47/0.64      inference('demod', [status(thm)], ['16', '17'])).
% 0.47/0.64  thf('19', plain,
% 0.47/0.64      ((~ (v1_funct_1 @ sk_D)
% 0.47/0.64        | (m1_subset_1 @ 
% 0.47/0.64           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.47/0.64           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['13', '18'])).
% 0.47/0.64  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('21', plain,
% 0.47/0.64      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.47/0.64         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.47/0.64      inference('demod', [status(thm)], ['9', '10'])).
% 0.47/0.64  thf('22', plain,
% 0.47/0.64      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.47/0.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.47/0.64      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.47/0.64  thf(redefinition_r2_relset_1, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.64     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.47/0.64         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.64       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.47/0.64  thf('23', plain,
% 0.47/0.64      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.47/0.64         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.47/0.64          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.47/0.64          | ((X22) = (X25))
% 0.47/0.64          | ~ (r2_relset_1 @ X23 @ X24 @ X22 @ X25))),
% 0.47/0.64      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.47/0.64  thf('24', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 0.47/0.64          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 0.47/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['22', '23'])).
% 0.47/0.64  thf('25', plain,
% 0.47/0.64      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.47/0.64           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.47/0.64        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['12', '24'])).
% 0.47/0.64  thf(dt_k6_partfun1, axiom,
% 0.47/0.64    (![A:$i]:
% 0.47/0.64     ( ( m1_subset_1 @
% 0.47/0.64         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.47/0.64       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.47/0.64  thf('26', plain,
% 0.47/0.64      (![X35 : $i]:
% 0.47/0.64         (m1_subset_1 @ (k6_partfun1 @ X35) @ 
% 0.47/0.64          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 0.47/0.64      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.47/0.64  thf('27', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.47/0.64      inference('demod', [status(thm)], ['25', '26'])).
% 0.47/0.64  thf(t45_relat_1, axiom,
% 0.47/0.64    (![A:$i]:
% 0.47/0.64     ( ( v1_relat_1 @ A ) =>
% 0.47/0.64       ( ![B:$i]:
% 0.47/0.64         ( ( v1_relat_1 @ B ) =>
% 0.47/0.64           ( r1_tarski @
% 0.47/0.64             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.47/0.64  thf('28', plain,
% 0.47/0.64      (![X12 : $i, X13 : $i]:
% 0.47/0.64         (~ (v1_relat_1 @ X12)
% 0.47/0.64          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X13 @ X12)) @ 
% 0.47/0.64             (k2_relat_1 @ X12))
% 0.47/0.64          | ~ (v1_relat_1 @ X13))),
% 0.47/0.64      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.47/0.64  thf(d10_xboole_0, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.64  thf('29', plain,
% 0.47/0.64      (![X0 : $i, X2 : $i]:
% 0.47/0.64         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.47/0.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.64  thf('30', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         (~ (v1_relat_1 @ X1)
% 0.47/0.64          | ~ (v1_relat_1 @ X0)
% 0.47/0.64          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 0.47/0.64               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.47/0.64          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 0.47/0.64      inference('sup-', [status(thm)], ['28', '29'])).
% 0.47/0.64  thf('31', plain,
% 0.47/0.64      ((~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 0.47/0.64           (k2_relat_1 @ (k6_partfun1 @ sk_A)))
% 0.47/0.64        | ((k2_relat_1 @ sk_D) = (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 0.47/0.64        | ~ (v1_relat_1 @ sk_D)
% 0.47/0.64        | ~ (v1_relat_1 @ sk_C))),
% 0.47/0.64      inference('sup-', [status(thm)], ['27', '30'])).
% 0.47/0.64  thf(t71_relat_1, axiom,
% 0.47/0.64    (![A:$i]:
% 0.47/0.64     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.47/0.64       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.47/0.64  thf('32', plain, (![X16 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 0.47/0.64      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.47/0.64  thf(redefinition_k6_partfun1, axiom,
% 0.47/0.64    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.47/0.64  thf('33', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 0.47/0.64      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.47/0.64  thf('34', plain, (![X16 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X16)) = (X16))),
% 0.47/0.64      inference('demod', [status(thm)], ['32', '33'])).
% 0.47/0.64  thf('35', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf(cc2_relset_1, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.64       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.47/0.64  thf('36', plain,
% 0.47/0.64      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.47/0.64         ((v5_relat_1 @ X19 @ X21)
% 0.47/0.64          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.47/0.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.64  thf('37', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 0.47/0.64      inference('sup-', [status(thm)], ['35', '36'])).
% 0.47/0.64  thf(d19_relat_1, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( v1_relat_1 @ B ) =>
% 0.47/0.64       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.47/0.64  thf('38', plain,
% 0.47/0.64      (![X8 : $i, X9 : $i]:
% 0.47/0.64         (~ (v5_relat_1 @ X8 @ X9)
% 0.47/0.64          | (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 0.47/0.64          | ~ (v1_relat_1 @ X8))),
% 0.47/0.64      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.47/0.64  thf('39', plain,
% 0.47/0.64      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 0.47/0.64      inference('sup-', [status(thm)], ['37', '38'])).
% 0.47/0.64  thf('40', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf(cc2_relat_1, axiom,
% 0.47/0.64    (![A:$i]:
% 0.47/0.64     ( ( v1_relat_1 @ A ) =>
% 0.47/0.64       ( ![B:$i]:
% 0.47/0.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.47/0.64  thf('41', plain,
% 0.47/0.64      (![X4 : $i, X5 : $i]:
% 0.47/0.64         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.47/0.64          | (v1_relat_1 @ X4)
% 0.47/0.64          | ~ (v1_relat_1 @ X5))),
% 0.47/0.64      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.47/0.64  thf('42', plain,
% 0.47/0.64      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.47/0.64      inference('sup-', [status(thm)], ['40', '41'])).
% 0.47/0.64  thf(fc6_relat_1, axiom,
% 0.47/0.64    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.47/0.64  thf('43', plain,
% 0.47/0.64      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.47/0.64      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.47/0.64  thf('44', plain, ((v1_relat_1 @ sk_D)),
% 0.47/0.64      inference('demod', [status(thm)], ['42', '43'])).
% 0.47/0.64  thf('45', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 0.47/0.64      inference('demod', [status(thm)], ['39', '44'])).
% 0.47/0.64  thf('46', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.47/0.64      inference('demod', [status(thm)], ['25', '26'])).
% 0.47/0.64  thf('47', plain, (![X16 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X16)) = (X16))),
% 0.47/0.64      inference('demod', [status(thm)], ['32', '33'])).
% 0.47/0.64  thf('48', plain, ((v1_relat_1 @ sk_D)),
% 0.47/0.64      inference('demod', [status(thm)], ['42', '43'])).
% 0.47/0.64  thf('49', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('50', plain,
% 0.47/0.64      (![X4 : $i, X5 : $i]:
% 0.47/0.64         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.47/0.64          | (v1_relat_1 @ X4)
% 0.47/0.64          | ~ (v1_relat_1 @ X5))),
% 0.47/0.64      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.47/0.64  thf('51', plain,
% 0.47/0.64      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.47/0.64      inference('sup-', [status(thm)], ['49', '50'])).
% 0.47/0.64  thf('52', plain,
% 0.47/0.64      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.47/0.64      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.47/0.64  thf('53', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.64      inference('demod', [status(thm)], ['51', '52'])).
% 0.47/0.64  thf('54', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.47/0.64      inference('demod', [status(thm)],
% 0.47/0.64                ['31', '34', '45', '46', '47', '48', '53'])).
% 0.47/0.64  thf(d3_funct_2, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.47/0.64       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.47/0.64  thf('55', plain,
% 0.47/0.64      (![X26 : $i, X27 : $i]:
% 0.47/0.64         (((k2_relat_1 @ X27) != (X26))
% 0.47/0.64          | (v2_funct_2 @ X27 @ X26)
% 0.47/0.64          | ~ (v5_relat_1 @ X27 @ X26)
% 0.47/0.64          | ~ (v1_relat_1 @ X27))),
% 0.47/0.64      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.47/0.64  thf('56', plain,
% 0.47/0.64      (![X27 : $i]:
% 0.47/0.64         (~ (v1_relat_1 @ X27)
% 0.47/0.64          | ~ (v5_relat_1 @ X27 @ (k2_relat_1 @ X27))
% 0.47/0.64          | (v2_funct_2 @ X27 @ (k2_relat_1 @ X27)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['55'])).
% 0.47/0.64  thf('57', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.47/0.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.64  thf('58', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.47/0.64      inference('simplify', [status(thm)], ['57'])).
% 0.47/0.64  thf('59', plain,
% 0.47/0.64      (![X8 : $i, X9 : $i]:
% 0.47/0.64         (~ (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 0.47/0.64          | (v5_relat_1 @ X8 @ X9)
% 0.47/0.64          | ~ (v1_relat_1 @ X8))),
% 0.47/0.64      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.47/0.64  thf('60', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['58', '59'])).
% 0.47/0.64  thf('61', plain,
% 0.47/0.64      (![X27 : $i]:
% 0.47/0.64         ((v2_funct_2 @ X27 @ (k2_relat_1 @ X27)) | ~ (v1_relat_1 @ X27))),
% 0.47/0.64      inference('clc', [status(thm)], ['56', '60'])).
% 0.47/0.64  thf('62', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 0.47/0.64      inference('sup+', [status(thm)], ['54', '61'])).
% 0.47/0.64  thf('63', plain, ((v1_relat_1 @ sk_D)),
% 0.47/0.64      inference('demod', [status(thm)], ['42', '43'])).
% 0.47/0.64  thf('64', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 0.47/0.64      inference('demod', [status(thm)], ['62', '63'])).
% 0.47/0.64  thf('65', plain,
% 0.47/0.64      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 0.47/0.64      inference('split', [status(esa)], ['0'])).
% 0.47/0.64  thf('66', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 0.47/0.64      inference('sup-', [status(thm)], ['64', '65'])).
% 0.47/0.64  thf('67', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 0.47/0.64      inference('split', [status(esa)], ['0'])).
% 0.47/0.64  thf('68', plain, (~ ((v2_funct_1 @ sk_C))),
% 0.47/0.64      inference('sat_resolution*', [status(thm)], ['66', '67'])).
% 0.47/0.64  thf('69', plain, (~ (v2_funct_1 @ sk_C)),
% 0.47/0.64      inference('simpl_trail', [status(thm)], ['1', '68'])).
% 0.47/0.64  thf('70', plain,
% 0.47/0.64      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.47/0.64         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.47/0.64      inference('demod', [status(thm)], ['9', '10'])).
% 0.47/0.64  thf('71', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf(t26_funct_2, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.64     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.47/0.64         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.64       ( ![E:$i]:
% 0.47/0.64         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.47/0.64             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.47/0.64           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 0.47/0.64             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 0.47/0.64               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 0.47/0.64  thf('72', plain,
% 0.47/0.64      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.47/0.64         (~ (v1_funct_1 @ X43)
% 0.47/0.64          | ~ (v1_funct_2 @ X43 @ X44 @ X45)
% 0.47/0.64          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 0.47/0.64          | ~ (v2_funct_1 @ (k1_partfun1 @ X46 @ X44 @ X44 @ X45 @ X47 @ X43))
% 0.47/0.64          | (v2_funct_1 @ X47)
% 0.47/0.64          | ((X45) = (k1_xboole_0))
% 0.47/0.64          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X44)))
% 0.47/0.64          | ~ (v1_funct_2 @ X47 @ X46 @ X44)
% 0.47/0.64          | ~ (v1_funct_1 @ X47))),
% 0.47/0.64      inference('cnf', [status(esa)], [t26_funct_2])).
% 0.47/0.64  thf('73', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         (~ (v1_funct_1 @ X0)
% 0.47/0.64          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.47/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.47/0.64          | ((sk_A) = (k1_xboole_0))
% 0.47/0.64          | (v2_funct_1 @ X0)
% 0.47/0.64          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.47/0.64          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.47/0.64          | ~ (v1_funct_1 @ sk_D))),
% 0.47/0.64      inference('sup-', [status(thm)], ['71', '72'])).
% 0.47/0.64  thf('74', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('75', plain, ((v1_funct_1 @ sk_D)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('76', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         (~ (v1_funct_1 @ X0)
% 0.47/0.64          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.47/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.47/0.64          | ((sk_A) = (k1_xboole_0))
% 0.47/0.64          | (v2_funct_1 @ X0)
% 0.47/0.64          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 0.47/0.64      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.47/0.64  thf('77', plain,
% 0.47/0.64      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 0.47/0.64        | (v2_funct_1 @ sk_C)
% 0.47/0.64        | ((sk_A) = (k1_xboole_0))
% 0.47/0.64        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.47/0.64        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.47/0.64        | ~ (v1_funct_1 @ sk_C))),
% 0.47/0.64      inference('sup-', [status(thm)], ['70', '76'])).
% 0.47/0.64  thf('78', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('79', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('80', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('81', plain,
% 0.47/0.64      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 0.47/0.64        | (v2_funct_1 @ sk_C)
% 0.47/0.64        | ((sk_A) = (k1_xboole_0)))),
% 0.47/0.64      inference('demod', [status(thm)], ['77', '78', '79', '80'])).
% 0.47/0.64  thf('82', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.47/0.64      inference('demod', [status(thm)], ['25', '26'])).
% 0.47/0.64  thf(fc4_funct_1, axiom,
% 0.47/0.64    (![A:$i]:
% 0.47/0.64     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.47/0.64       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.47/0.64  thf('83', plain, (![X18 : $i]: (v2_funct_1 @ (k6_relat_1 @ X18))),
% 0.47/0.64      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.47/0.64  thf('84', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 0.47/0.64      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.47/0.64  thf('85', plain, (![X18 : $i]: (v2_funct_1 @ (k6_partfun1 @ X18))),
% 0.47/0.64      inference('demod', [status(thm)], ['83', '84'])).
% 0.47/0.64  thf('86', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.47/0.64      inference('demod', [status(thm)], ['81', '82', '85'])).
% 0.47/0.64  thf('87', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.47/0.64      inference('split', [status(esa)], ['0'])).
% 0.47/0.64  thf('88', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['86', '87'])).
% 0.47/0.64  thf('89', plain,
% 0.47/0.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('90', plain,
% 0.47/0.64      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.47/0.64         ((v4_relat_1 @ X19 @ X20)
% 0.47/0.64          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.47/0.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.64  thf('91', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.47/0.64      inference('sup-', [status(thm)], ['89', '90'])).
% 0.47/0.64  thf(d18_relat_1, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( v1_relat_1 @ B ) =>
% 0.47/0.64       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.47/0.64  thf('92', plain,
% 0.47/0.64      (![X6 : $i, X7 : $i]:
% 0.47/0.64         (~ (v4_relat_1 @ X6 @ X7)
% 0.47/0.64          | (r1_tarski @ (k1_relat_1 @ X6) @ X7)
% 0.47/0.64          | ~ (v1_relat_1 @ X6))),
% 0.47/0.64      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.47/0.64  thf('93', plain,
% 0.47/0.64      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 0.47/0.64      inference('sup-', [status(thm)], ['91', '92'])).
% 0.47/0.64  thf('94', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.64      inference('demod', [status(thm)], ['51', '52'])).
% 0.47/0.64  thf('95', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.47/0.64      inference('demod', [status(thm)], ['93', '94'])).
% 0.47/0.64  thf('96', plain,
% 0.47/0.64      (![X0 : $i, X2 : $i]:
% 0.47/0.64         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.47/0.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.64  thf('97', plain,
% 0.47/0.64      ((~ (r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))
% 0.47/0.64        | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['95', '96'])).
% 0.47/0.64  thf('98', plain,
% 0.47/0.64      (((~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.47/0.64         | ((sk_A) = (k1_relat_1 @ sk_C)))) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['88', '97'])).
% 0.47/0.64  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.47/0.64  thf('99', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.47/0.64      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.47/0.64  thf('100', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['86', '87'])).
% 0.47/0.64  thf('101', plain,
% 0.47/0.64      ((((k1_xboole_0) = (k1_relat_1 @ sk_C))) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.47/0.64      inference('demod', [status(thm)], ['98', '99', '100'])).
% 0.47/0.64  thf('102', plain, (~ ((v2_funct_1 @ sk_C))),
% 0.47/0.64      inference('sat_resolution*', [status(thm)], ['66', '67'])).
% 0.47/0.64  thf('103', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_C))),
% 0.47/0.64      inference('simpl_trail', [status(thm)], ['101', '102'])).
% 0.47/0.64  thf(t64_relat_1, axiom,
% 0.47/0.64    (![A:$i]:
% 0.47/0.64     ( ( v1_relat_1 @ A ) =>
% 0.47/0.64       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.47/0.64           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.64         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.47/0.64  thf('104', plain,
% 0.47/0.64      (![X14 : $i]:
% 0.47/0.64         (((k1_relat_1 @ X14) != (k1_xboole_0))
% 0.47/0.64          | ((X14) = (k1_xboole_0))
% 0.47/0.64          | ~ (v1_relat_1 @ X14))),
% 0.47/0.64      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.47/0.64  thf('105', plain,
% 0.47/0.64      ((((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.64        | ~ (v1_relat_1 @ sk_C)
% 0.47/0.64        | ((sk_C) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['103', '104'])).
% 0.47/0.64  thf('106', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.64      inference('demod', [status(thm)], ['51', '52'])).
% 0.47/0.64  thf('107', plain,
% 0.47/0.64      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.47/0.64      inference('demod', [status(thm)], ['105', '106'])).
% 0.47/0.64  thf('108', plain, (((sk_C) = (k1_xboole_0))),
% 0.47/0.64      inference('simplify', [status(thm)], ['107'])).
% 0.47/0.64  thf('109', plain, (![X15 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X15)) = (X15))),
% 0.47/0.64      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.47/0.64  thf('110', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 0.47/0.64      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.47/0.64  thf('111', plain,
% 0.47/0.64      (![X15 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X15)) = (X15))),
% 0.47/0.64      inference('demod', [status(thm)], ['109', '110'])).
% 0.47/0.64  thf('112', plain,
% 0.47/0.64      (![X14 : $i]:
% 0.47/0.64         (((k1_relat_1 @ X14) != (k1_xboole_0))
% 0.47/0.64          | ((X14) = (k1_xboole_0))
% 0.47/0.64          | ~ (v1_relat_1 @ X14))),
% 0.47/0.64      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.47/0.64  thf('113', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((X0) != (k1_xboole_0))
% 0.47/0.64          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 0.47/0.64          | ((k6_partfun1 @ X0) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['111', '112'])).
% 0.47/0.64  thf('114', plain, (![X17 : $i]: (v1_relat_1 @ (k6_relat_1 @ X17))),
% 0.47/0.64      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.47/0.64  thf('115', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 0.47/0.64      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.47/0.64  thf('116', plain, (![X17 : $i]: (v1_relat_1 @ (k6_partfun1 @ X17))),
% 0.47/0.64      inference('demod', [status(thm)], ['114', '115'])).
% 0.47/0.64  thf('117', plain,
% 0.47/0.64      (![X0 : $i]:
% 0.47/0.64         (((X0) != (k1_xboole_0)) | ((k6_partfun1 @ X0) = (k1_xboole_0)))),
% 0.47/0.64      inference('demod', [status(thm)], ['113', '116'])).
% 0.47/0.64  thf('118', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.64      inference('simplify', [status(thm)], ['117'])).
% 0.47/0.64  thf('119', plain, (![X18 : $i]: (v2_funct_1 @ (k6_partfun1 @ X18))),
% 0.47/0.64      inference('demod', [status(thm)], ['83', '84'])).
% 0.47/0.64  thf('120', plain, ((v2_funct_1 @ k1_xboole_0)),
% 0.47/0.64      inference('sup+', [status(thm)], ['118', '119'])).
% 0.47/0.64  thf('121', plain, ($false),
% 0.47/0.64      inference('demod', [status(thm)], ['69', '108', '120'])).
% 0.47/0.64  
% 0.47/0.64  % SZS output end Refutation
% 0.47/0.64  
% 0.47/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

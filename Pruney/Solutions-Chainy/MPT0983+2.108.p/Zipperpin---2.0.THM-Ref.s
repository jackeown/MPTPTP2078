%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5k3bmeR2zN

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:18 EST 2020

% Result     : Theorem 3.06s
% Output     : Refutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :  213 (1495 expanded)
%              Number of leaves         :   48 ( 451 expanded)
%              Depth                    :   23
%              Number of atoms          : 1562 (26527 expanded)
%              Number of equality atoms :   74 ( 473 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ( ~ ( v2_funct_1 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
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
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X46 ) ) ) ) ),
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
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('13',plain,(
    ! [X21: $i,X22: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('14',plain,(
    v1_relat_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
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

thf('17',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) )
      | ( ( k1_partfun1 @ X48 @ X49 @ X51 @ X52 @ X47 @ X50 )
        = ( k5_relat_1 @ X47 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_1 @ X0 )
        = ( k5_relat_1 @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_1 @ X0 )
        = ( k5_relat_1 @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
      = ( k5_relat_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
    = ( k5_relat_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['14','23'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('25',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X25 @ X24 ) ) @ ( k2_relat_1 @ X24 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('26',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ( v5_relat_1 @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( v5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( v5_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X21: $i,X22: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('33',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X21: $i,X22: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('38',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    v5_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['28','33','38'])).

thf('40',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v5_relat_1 @ X19 @ X20 )
      | ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['14','23'])).

thf('43',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) ) @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('44',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('45',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) ) )
    | ( ( k2_relat_1 @ sk_D )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
    = ( k5_relat_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('48',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('50',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
    = ( k5_relat_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('51',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('52',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( X34 = X37 )
      | ~ ( r2_relset_1 @ X35 @ X36 @ X34 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C_1 @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C_1 @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('55',plain,(
    ! [X38: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('56',plain,(
    ! [X53: $i] :
      ( ( k6_partfun1 @ X53 )
      = ( k6_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('57',plain,(
    ! [X38: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k5_relat_1 @ sk_C_1 @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['54','57'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('59',plain,(
    ! [X28: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('60',plain,(
    ! [X53: $i] :
      ( ( k6_partfun1 @ X53 )
      = ( k6_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('61',plain,(
    ! [X28: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X28 ) )
      = X28 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('63',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v5_relat_1 @ X31 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('64',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v5_relat_1 @ X19 @ X20 )
      | ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('66',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['31','32'])).

thf('68',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k5_relat_1 @ sk_C_1 @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['54','57'])).

thf('70',plain,(
    ! [X28: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X28 ) )
      = X28 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('71',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['45','58','61','68','69','70'])).

thf('72',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('73',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ( v5_relat_1 @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('76',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k2_relat_1 @ X40 )
       != X39 )
      | ( v2_funct_2 @ X40 @ X39 )
      | ~ ( v5_relat_1 @ X40 @ X39 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('77',plain,(
    ! [X40: $i] :
      ( ~ ( v1_relat_1 @ X40 )
      | ~ ( v5_relat_1 @ X40 @ ( k2_relat_1 @ X40 ) )
      | ( v2_funct_2 @ X40 @ ( k2_relat_1 @ X40 ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['71','79'])).

thf('81',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['31','32'])).

thf('82',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('84',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('86',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('89',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('90',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('92',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C_1 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
    = ( k5_relat_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('94',plain,(
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

thf('95',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i,X58: $i] :
      ( ~ ( v1_funct_1 @ X54 )
      | ~ ( v1_funct_2 @ X54 @ X55 @ X56 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X56 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X57 @ X55 @ X55 @ X56 @ X58 @ X54 ) )
      | ( v2_funct_1 @ X58 )
      | ( X56 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X55 ) ) )
      | ~ ( v1_funct_2 @ X58 @ X57 @ X55 )
      | ~ ( v1_funct_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['93','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['100','101','102','103'])).

thf('105',plain,
    ( ( k5_relat_1 @ sk_C_1 @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['54','57'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('106',plain,(
    ! [X30: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('107',plain,(
    ! [X53: $i] :
      ( ( k6_partfun1 @ X53 )
      = ( k6_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('108',plain,(
    ! [X30: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X30 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( v2_funct_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['104','105','108'])).

thf('110',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','86'])).

thf('111',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('113',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('114',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v4_relat_1 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( v4_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('117',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v4_relat_1 @ X17 @ X18 )
      | ( r1_tarski @ ( k1_relat_1 @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X21: $i,X22: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['118','119'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('121',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('122',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v4_relat_1 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('128',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( v4_relat_1 @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['121','128'])).

thf('130',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v4_relat_1 @ X17 @ X18 )
      | ( r1_tarski @ ( k1_relat_1 @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X27: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('133',plain,(
    ! [X53: $i] :
      ( ( k6_partfun1 @ X53 )
      = ( k6_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('134',plain,(
    ! [X27: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X27 ) )
      = X27 ) ),
    inference(demod,[status(thm)],['132','133'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('135',plain,(
    ! [X26: $i] :
      ( ( ( k1_relat_1 @ X26 )
       != k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k6_partfun1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('138',plain,(
    ! [X53: $i] :
      ( ( k6_partfun1 @ X53 )
      = ( k6_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('139',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X29 ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k6_partfun1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['136','139'])).

thf('141',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X29 ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('143',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['141','142'])).

thf('144',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['140'])).

thf('145',plain,(
    ! [X27: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X27 ) )
      = X27 ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('146',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['131','143','146'])).

thf('148',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['120','149'])).

thf('151',plain,(
    ! [X26: $i] :
      ( ( ( k1_relat_1 @ X26 )
       != k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X21: $i,X22: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['131','143','146'])).

thf('157',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['109','110'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['154'])).

thf('159',plain,(
    k1_xboole_0 = sk_C_1 ),
    inference(demod,[status(thm)],['92','111','155','156','157','158'])).

thf('160',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['140'])).

thf('161',plain,(
    ! [X30: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X30 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('162',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['160','161'])).

thf('163',plain,(
    $false ),
    inference(demod,[status(thm)],['87','159','162'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5k3bmeR2zN
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:57:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 3.06/3.27  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.06/3.27  % Solved by: fo/fo7.sh
% 3.06/3.27  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.06/3.27  % done 4208 iterations in 2.819s
% 3.06/3.27  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.06/3.27  % SZS output start Refutation
% 3.06/3.27  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.06/3.27  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.06/3.27  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.06/3.27  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.06/3.27  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.06/3.27  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.06/3.27  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.06/3.27  thf(sk_A_type, type, sk_A: $i).
% 3.06/3.27  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.06/3.27  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.06/3.27  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.06/3.27  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.06/3.27  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.06/3.27  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.06/3.27  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.06/3.27  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.06/3.27  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.06/3.27  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 3.06/3.27  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.06/3.27  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.06/3.27  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.06/3.27  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.06/3.27  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.06/3.27  thf(sk_D_type, type, sk_D: $i).
% 3.06/3.27  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.06/3.27  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.06/3.27  thf(t29_funct_2, conjecture,
% 3.06/3.27    (![A:$i,B:$i,C:$i]:
% 3.06/3.27     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.06/3.27         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.06/3.27       ( ![D:$i]:
% 3.06/3.27         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.06/3.27             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.06/3.27           ( ( r2_relset_1 @
% 3.06/3.27               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.06/3.27               ( k6_partfun1 @ A ) ) =>
% 3.06/3.27             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 3.06/3.27  thf(zf_stmt_0, negated_conjecture,
% 3.06/3.27    (~( ![A:$i,B:$i,C:$i]:
% 3.06/3.27        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.06/3.27            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.06/3.27          ( ![D:$i]:
% 3.06/3.27            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.06/3.27                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.06/3.27              ( ( r2_relset_1 @
% 3.06/3.27                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.06/3.27                  ( k6_partfun1 @ A ) ) =>
% 3.06/3.27                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 3.06/3.27    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 3.06/3.27  thf('0', plain, ((~ (v2_funct_1 @ sk_C_1) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 3.06/3.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.27  thf('1', plain, ((~ (v2_funct_1 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 3.06/3.27      inference('split', [status(esa)], ['0'])).
% 3.06/3.27  thf('2', plain,
% 3.06/3.27      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.06/3.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.27  thf('3', plain,
% 3.06/3.27      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.06/3.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.27  thf(dt_k1_partfun1, axiom,
% 3.06/3.27    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.06/3.27     ( ( ( v1_funct_1 @ E ) & 
% 3.06/3.27         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.06/3.27         ( v1_funct_1 @ F ) & 
% 3.06/3.27         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.06/3.27       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 3.06/3.27         ( m1_subset_1 @
% 3.06/3.27           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.06/3.27           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 3.06/3.27  thf('4', plain,
% 3.06/3.27      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 3.06/3.27         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 3.06/3.27          | ~ (v1_funct_1 @ X41)
% 3.06/3.27          | ~ (v1_funct_1 @ X44)
% 3.06/3.27          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 3.06/3.27          | (m1_subset_1 @ (k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44) @ 
% 3.06/3.27             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X46))))),
% 3.06/3.27      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.06/3.27  thf('5', plain,
% 3.06/3.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.06/3.27         ((m1_subset_1 @ 
% 3.06/3.27           (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 3.06/3.27           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.06/3.27          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.06/3.27          | ~ (v1_funct_1 @ X1)
% 3.06/3.27          | ~ (v1_funct_1 @ sk_C_1))),
% 3.06/3.27      inference('sup-', [status(thm)], ['3', '4'])).
% 3.06/3.27  thf('6', plain, ((v1_funct_1 @ sk_C_1)),
% 3.06/3.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.27  thf('7', plain,
% 3.06/3.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.06/3.27         ((m1_subset_1 @ 
% 3.06/3.27           (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 3.06/3.27           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.06/3.27          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.06/3.27          | ~ (v1_funct_1 @ X1))),
% 3.06/3.27      inference('demod', [status(thm)], ['5', '6'])).
% 3.06/3.27  thf('8', plain,
% 3.06/3.27      ((~ (v1_funct_1 @ sk_D)
% 3.06/3.27        | (m1_subset_1 @ 
% 3.06/3.27           (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ 
% 3.06/3.27           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.06/3.27      inference('sup-', [status(thm)], ['2', '7'])).
% 3.06/3.27  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 3.06/3.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.27  thf('10', plain,
% 3.06/3.27      ((m1_subset_1 @ 
% 3.06/3.27        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ 
% 3.06/3.27        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.06/3.27      inference('demod', [status(thm)], ['8', '9'])).
% 3.06/3.27  thf(cc2_relat_1, axiom,
% 3.06/3.27    (![A:$i]:
% 3.06/3.27     ( ( v1_relat_1 @ A ) =>
% 3.06/3.27       ( ![B:$i]:
% 3.06/3.27         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 3.06/3.27  thf('11', plain,
% 3.06/3.27      (![X15 : $i, X16 : $i]:
% 3.06/3.27         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 3.06/3.27          | (v1_relat_1 @ X15)
% 3.06/3.27          | ~ (v1_relat_1 @ X16))),
% 3.06/3.27      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.06/3.27  thf('12', plain,
% 3.06/3.27      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 3.06/3.27        | (v1_relat_1 @ 
% 3.06/3.27           (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)))),
% 3.06/3.27      inference('sup-', [status(thm)], ['10', '11'])).
% 3.06/3.27  thf(fc6_relat_1, axiom,
% 3.06/3.27    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 3.06/3.27  thf('13', plain,
% 3.06/3.27      (![X21 : $i, X22 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X21 @ X22))),
% 3.06/3.27      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.06/3.27  thf('14', plain,
% 3.06/3.27      ((v1_relat_1 @ 
% 3.06/3.27        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D))),
% 3.06/3.27      inference('demod', [status(thm)], ['12', '13'])).
% 3.06/3.27  thf('15', plain,
% 3.06/3.27      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.06/3.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.27  thf('16', plain,
% 3.06/3.27      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.06/3.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.27  thf(redefinition_k1_partfun1, axiom,
% 3.06/3.27    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.06/3.27     ( ( ( v1_funct_1 @ E ) & 
% 3.06/3.27         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.06/3.27         ( v1_funct_1 @ F ) & 
% 3.06/3.27         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.06/3.27       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 3.06/3.27  thf('17', plain,
% 3.06/3.27      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 3.06/3.27         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 3.06/3.27          | ~ (v1_funct_1 @ X47)
% 3.06/3.27          | ~ (v1_funct_1 @ X50)
% 3.06/3.27          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 3.06/3.27          | ((k1_partfun1 @ X48 @ X49 @ X51 @ X52 @ X47 @ X50)
% 3.06/3.27              = (k5_relat_1 @ X47 @ X50)))),
% 3.06/3.27      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 3.06/3.27  thf('18', plain,
% 3.06/3.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.06/3.27         (((k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_1 @ X0)
% 3.06/3.27            = (k5_relat_1 @ sk_C_1 @ X0))
% 3.06/3.27          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.06/3.27          | ~ (v1_funct_1 @ X0)
% 3.06/3.27          | ~ (v1_funct_1 @ sk_C_1))),
% 3.06/3.27      inference('sup-', [status(thm)], ['16', '17'])).
% 3.06/3.27  thf('19', plain, ((v1_funct_1 @ sk_C_1)),
% 3.06/3.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.27  thf('20', plain,
% 3.06/3.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.06/3.27         (((k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_1 @ X0)
% 3.06/3.27            = (k5_relat_1 @ sk_C_1 @ X0))
% 3.06/3.27          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.06/3.27          | ~ (v1_funct_1 @ X0))),
% 3.06/3.27      inference('demod', [status(thm)], ['18', '19'])).
% 3.06/3.27  thf('21', plain,
% 3.06/3.27      ((~ (v1_funct_1 @ sk_D)
% 3.06/3.27        | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 3.06/3.27            = (k5_relat_1 @ sk_C_1 @ sk_D)))),
% 3.06/3.27      inference('sup-', [status(thm)], ['15', '20'])).
% 3.06/3.27  thf('22', plain, ((v1_funct_1 @ sk_D)),
% 3.06/3.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.27  thf('23', plain,
% 3.06/3.27      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 3.06/3.27         = (k5_relat_1 @ sk_C_1 @ sk_D))),
% 3.06/3.27      inference('demod', [status(thm)], ['21', '22'])).
% 3.06/3.27  thf('24', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D))),
% 3.06/3.27      inference('demod', [status(thm)], ['14', '23'])).
% 3.06/3.27  thf(t45_relat_1, axiom,
% 3.06/3.27    (![A:$i]:
% 3.06/3.27     ( ( v1_relat_1 @ A ) =>
% 3.06/3.27       ( ![B:$i]:
% 3.06/3.27         ( ( v1_relat_1 @ B ) =>
% 3.06/3.27           ( r1_tarski @
% 3.06/3.27             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 3.06/3.27  thf('25', plain,
% 3.06/3.27      (![X24 : $i, X25 : $i]:
% 3.06/3.27         (~ (v1_relat_1 @ X24)
% 3.06/3.27          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X25 @ X24)) @ 
% 3.06/3.27             (k2_relat_1 @ X24))
% 3.06/3.27          | ~ (v1_relat_1 @ X25))),
% 3.06/3.27      inference('cnf', [status(esa)], [t45_relat_1])).
% 3.06/3.27  thf(d19_relat_1, axiom,
% 3.06/3.27    (![A:$i,B:$i]:
% 3.06/3.27     ( ( v1_relat_1 @ B ) =>
% 3.06/3.27       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 3.06/3.27  thf('26', plain,
% 3.06/3.27      (![X19 : $i, X20 : $i]:
% 3.06/3.27         (~ (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 3.06/3.27          | (v5_relat_1 @ X19 @ X20)
% 3.06/3.27          | ~ (v1_relat_1 @ X19))),
% 3.06/3.27      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.06/3.27  thf('27', plain,
% 3.06/3.27      (![X0 : $i, X1 : $i]:
% 3.06/3.27         (~ (v1_relat_1 @ X1)
% 3.06/3.27          | ~ (v1_relat_1 @ X0)
% 3.06/3.27          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 3.06/3.27          | (v5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 3.06/3.27      inference('sup-', [status(thm)], ['25', '26'])).
% 3.06/3.27  thf('28', plain,
% 3.06/3.27      (((v5_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D) @ (k2_relat_1 @ sk_D))
% 3.06/3.27        | ~ (v1_relat_1 @ sk_D)
% 3.06/3.27        | ~ (v1_relat_1 @ sk_C_1))),
% 3.06/3.27      inference('sup-', [status(thm)], ['24', '27'])).
% 3.06/3.27  thf('29', plain,
% 3.06/3.27      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.06/3.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.27  thf('30', plain,
% 3.06/3.27      (![X15 : $i, X16 : $i]:
% 3.06/3.27         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 3.06/3.27          | (v1_relat_1 @ X15)
% 3.06/3.27          | ~ (v1_relat_1 @ X16))),
% 3.06/3.27      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.06/3.27  thf('31', plain,
% 3.06/3.27      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)) | (v1_relat_1 @ sk_D))),
% 3.06/3.27      inference('sup-', [status(thm)], ['29', '30'])).
% 3.06/3.27  thf('32', plain,
% 3.06/3.27      (![X21 : $i, X22 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X21 @ X22))),
% 3.06/3.27      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.06/3.27  thf('33', plain, ((v1_relat_1 @ sk_D)),
% 3.06/3.27      inference('demod', [status(thm)], ['31', '32'])).
% 3.06/3.27  thf('34', plain,
% 3.06/3.27      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.06/3.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.27  thf('35', plain,
% 3.06/3.27      (![X15 : $i, X16 : $i]:
% 3.06/3.27         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 3.06/3.27          | (v1_relat_1 @ X15)
% 3.06/3.27          | ~ (v1_relat_1 @ X16))),
% 3.06/3.27      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.06/3.27  thf('36', plain,
% 3.06/3.27      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_C_1))),
% 3.06/3.27      inference('sup-', [status(thm)], ['34', '35'])).
% 3.06/3.27  thf('37', plain,
% 3.06/3.27      (![X21 : $i, X22 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X21 @ X22))),
% 3.06/3.27      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.06/3.27  thf('38', plain, ((v1_relat_1 @ sk_C_1)),
% 3.06/3.27      inference('demod', [status(thm)], ['36', '37'])).
% 3.06/3.27  thf('39', plain,
% 3.06/3.27      ((v5_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D) @ (k2_relat_1 @ sk_D))),
% 3.06/3.27      inference('demod', [status(thm)], ['28', '33', '38'])).
% 3.06/3.27  thf('40', plain,
% 3.06/3.27      (![X19 : $i, X20 : $i]:
% 3.06/3.27         (~ (v5_relat_1 @ X19 @ X20)
% 3.06/3.27          | (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 3.06/3.27          | ~ (v1_relat_1 @ X19))),
% 3.06/3.27      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.06/3.27  thf('41', plain,
% 3.06/3.27      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D))
% 3.06/3.27        | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D)) @ 
% 3.06/3.27           (k2_relat_1 @ sk_D)))),
% 3.06/3.27      inference('sup-', [status(thm)], ['39', '40'])).
% 3.06/3.27  thf('42', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D))),
% 3.06/3.27      inference('demod', [status(thm)], ['14', '23'])).
% 3.06/3.27  thf('43', plain,
% 3.06/3.27      ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D)) @ 
% 3.06/3.27        (k2_relat_1 @ sk_D))),
% 3.06/3.27      inference('demod', [status(thm)], ['41', '42'])).
% 3.06/3.27  thf(d10_xboole_0, axiom,
% 3.06/3.27    (![A:$i,B:$i]:
% 3.06/3.27     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.06/3.27  thf('44', plain,
% 3.06/3.27      (![X7 : $i, X9 : $i]:
% 3.06/3.27         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 3.06/3.27      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.06/3.27  thf('45', plain,
% 3.06/3.27      ((~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 3.06/3.27           (k2_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D)))
% 3.06/3.27        | ((k2_relat_1 @ sk_D) = (k2_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D))))),
% 3.06/3.27      inference('sup-', [status(thm)], ['43', '44'])).
% 3.06/3.27  thf('46', plain,
% 3.06/3.27      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.06/3.27        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ 
% 3.06/3.27        (k6_partfun1 @ sk_A))),
% 3.06/3.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.27  thf('47', plain,
% 3.06/3.27      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 3.06/3.27         = (k5_relat_1 @ sk_C_1 @ sk_D))),
% 3.06/3.27      inference('demod', [status(thm)], ['21', '22'])).
% 3.06/3.27  thf('48', plain,
% 3.06/3.27      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C_1 @ sk_D) @ 
% 3.06/3.27        (k6_partfun1 @ sk_A))),
% 3.06/3.27      inference('demod', [status(thm)], ['46', '47'])).
% 3.06/3.27  thf('49', plain,
% 3.06/3.27      ((m1_subset_1 @ 
% 3.06/3.27        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ 
% 3.06/3.27        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.06/3.27      inference('demod', [status(thm)], ['8', '9'])).
% 3.06/3.27  thf('50', plain,
% 3.06/3.27      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 3.06/3.27         = (k5_relat_1 @ sk_C_1 @ sk_D))),
% 3.06/3.27      inference('demod', [status(thm)], ['21', '22'])).
% 3.06/3.27  thf('51', plain,
% 3.06/3.27      ((m1_subset_1 @ (k5_relat_1 @ sk_C_1 @ sk_D) @ 
% 3.06/3.27        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.06/3.27      inference('demod', [status(thm)], ['49', '50'])).
% 3.06/3.27  thf(redefinition_r2_relset_1, axiom,
% 3.06/3.27    (![A:$i,B:$i,C:$i,D:$i]:
% 3.06/3.27     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.06/3.27         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.06/3.27       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.06/3.27  thf('52', plain,
% 3.06/3.27      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 3.06/3.27         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 3.06/3.27          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 3.06/3.27          | ((X34) = (X37))
% 3.06/3.27          | ~ (r2_relset_1 @ X35 @ X36 @ X34 @ X37))),
% 3.06/3.27      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.06/3.27  thf('53', plain,
% 3.06/3.27      (![X0 : $i]:
% 3.06/3.27         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C_1 @ sk_D) @ X0)
% 3.06/3.27          | ((k5_relat_1 @ sk_C_1 @ sk_D) = (X0))
% 3.06/3.27          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.06/3.27      inference('sup-', [status(thm)], ['51', '52'])).
% 3.06/3.27  thf('54', plain,
% 3.06/3.27      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 3.06/3.27           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.06/3.27        | ((k5_relat_1 @ sk_C_1 @ sk_D) = (k6_partfun1 @ sk_A)))),
% 3.06/3.27      inference('sup-', [status(thm)], ['48', '53'])).
% 3.06/3.27  thf(t29_relset_1, axiom,
% 3.06/3.27    (![A:$i]:
% 3.06/3.27     ( m1_subset_1 @
% 3.06/3.27       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 3.06/3.27  thf('55', plain,
% 3.06/3.27      (![X38 : $i]:
% 3.06/3.27         (m1_subset_1 @ (k6_relat_1 @ X38) @ 
% 3.06/3.27          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X38)))),
% 3.06/3.27      inference('cnf', [status(esa)], [t29_relset_1])).
% 3.06/3.27  thf(redefinition_k6_partfun1, axiom,
% 3.06/3.27    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 3.06/3.27  thf('56', plain, (![X53 : $i]: ((k6_partfun1 @ X53) = (k6_relat_1 @ X53))),
% 3.06/3.27      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.06/3.27  thf('57', plain,
% 3.06/3.27      (![X38 : $i]:
% 3.06/3.27         (m1_subset_1 @ (k6_partfun1 @ X38) @ 
% 3.06/3.27          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X38)))),
% 3.06/3.27      inference('demod', [status(thm)], ['55', '56'])).
% 3.06/3.27  thf('58', plain, (((k5_relat_1 @ sk_C_1 @ sk_D) = (k6_partfun1 @ sk_A))),
% 3.06/3.27      inference('demod', [status(thm)], ['54', '57'])).
% 3.06/3.27  thf(t71_relat_1, axiom,
% 3.06/3.27    (![A:$i]:
% 3.06/3.27     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 3.06/3.27       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 3.06/3.27  thf('59', plain, (![X28 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X28)) = (X28))),
% 3.06/3.27      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.06/3.27  thf('60', plain, (![X53 : $i]: ((k6_partfun1 @ X53) = (k6_relat_1 @ X53))),
% 3.06/3.27      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.06/3.27  thf('61', plain, (![X28 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X28)) = (X28))),
% 3.06/3.27      inference('demod', [status(thm)], ['59', '60'])).
% 3.06/3.27  thf('62', plain,
% 3.06/3.27      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.06/3.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.27  thf(cc2_relset_1, axiom,
% 3.06/3.27    (![A:$i,B:$i,C:$i]:
% 3.06/3.27     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.06/3.27       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.06/3.27  thf('63', plain,
% 3.06/3.27      (![X31 : $i, X32 : $i, X33 : $i]:
% 3.06/3.27         ((v5_relat_1 @ X31 @ X33)
% 3.06/3.27          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 3.06/3.27      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.06/3.27  thf('64', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 3.06/3.27      inference('sup-', [status(thm)], ['62', '63'])).
% 3.06/3.27  thf('65', plain,
% 3.06/3.27      (![X19 : $i, X20 : $i]:
% 3.06/3.27         (~ (v5_relat_1 @ X19 @ X20)
% 3.06/3.27          | (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 3.06/3.27          | ~ (v1_relat_1 @ X19))),
% 3.06/3.27      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.06/3.27  thf('66', plain,
% 3.06/3.27      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 3.06/3.27      inference('sup-', [status(thm)], ['64', '65'])).
% 3.06/3.27  thf('67', plain, ((v1_relat_1 @ sk_D)),
% 3.06/3.27      inference('demod', [status(thm)], ['31', '32'])).
% 3.06/3.27  thf('68', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 3.06/3.27      inference('demod', [status(thm)], ['66', '67'])).
% 3.06/3.27  thf('69', plain, (((k5_relat_1 @ sk_C_1 @ sk_D) = (k6_partfun1 @ sk_A))),
% 3.06/3.27      inference('demod', [status(thm)], ['54', '57'])).
% 3.06/3.27  thf('70', plain, (![X28 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X28)) = (X28))),
% 3.06/3.27      inference('demod', [status(thm)], ['59', '60'])).
% 3.06/3.27  thf('71', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.06/3.27      inference('demod', [status(thm)], ['45', '58', '61', '68', '69', '70'])).
% 3.06/3.27  thf('72', plain,
% 3.06/3.27      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 3.06/3.27      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.06/3.27  thf('73', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 3.06/3.27      inference('simplify', [status(thm)], ['72'])).
% 3.06/3.27  thf('74', plain,
% 3.06/3.27      (![X19 : $i, X20 : $i]:
% 3.06/3.27         (~ (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 3.06/3.27          | (v5_relat_1 @ X19 @ X20)
% 3.06/3.27          | ~ (v1_relat_1 @ X19))),
% 3.06/3.27      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.06/3.27  thf('75', plain,
% 3.06/3.27      (![X0 : $i]:
% 3.06/3.27         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 3.06/3.27      inference('sup-', [status(thm)], ['73', '74'])).
% 3.06/3.27  thf(d3_funct_2, axiom,
% 3.06/3.27    (![A:$i,B:$i]:
% 3.06/3.27     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 3.06/3.27       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 3.06/3.27  thf('76', plain,
% 3.06/3.27      (![X39 : $i, X40 : $i]:
% 3.06/3.27         (((k2_relat_1 @ X40) != (X39))
% 3.06/3.27          | (v2_funct_2 @ X40 @ X39)
% 3.06/3.27          | ~ (v5_relat_1 @ X40 @ X39)
% 3.06/3.27          | ~ (v1_relat_1 @ X40))),
% 3.06/3.27      inference('cnf', [status(esa)], [d3_funct_2])).
% 3.06/3.27  thf('77', plain,
% 3.06/3.27      (![X40 : $i]:
% 3.06/3.27         (~ (v1_relat_1 @ X40)
% 3.06/3.27          | ~ (v5_relat_1 @ X40 @ (k2_relat_1 @ X40))
% 3.06/3.27          | (v2_funct_2 @ X40 @ (k2_relat_1 @ X40)))),
% 3.06/3.27      inference('simplify', [status(thm)], ['76'])).
% 3.06/3.27  thf('78', plain,
% 3.06/3.27      (![X0 : $i]:
% 3.06/3.27         (~ (v1_relat_1 @ X0)
% 3.06/3.27          | (v2_funct_2 @ X0 @ (k2_relat_1 @ X0))
% 3.06/3.27          | ~ (v1_relat_1 @ X0))),
% 3.06/3.27      inference('sup-', [status(thm)], ['75', '77'])).
% 3.06/3.27  thf('79', plain,
% 3.06/3.27      (![X0 : $i]:
% 3.06/3.27         ((v2_funct_2 @ X0 @ (k2_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 3.06/3.27      inference('simplify', [status(thm)], ['78'])).
% 3.06/3.27  thf('80', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 3.06/3.27      inference('sup+', [status(thm)], ['71', '79'])).
% 3.06/3.27  thf('81', plain, ((v1_relat_1 @ sk_D)),
% 3.06/3.27      inference('demod', [status(thm)], ['31', '32'])).
% 3.06/3.27  thf('82', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 3.06/3.27      inference('demod', [status(thm)], ['80', '81'])).
% 3.06/3.27  thf('83', plain,
% 3.06/3.27      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 3.06/3.27      inference('split', [status(esa)], ['0'])).
% 3.06/3.27  thf('84', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 3.06/3.27      inference('sup-', [status(thm)], ['82', '83'])).
% 3.06/3.27  thf('85', plain,
% 3.06/3.27      (~ ((v2_funct_1 @ sk_C_1)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 3.06/3.27      inference('split', [status(esa)], ['0'])).
% 3.06/3.27  thf('86', plain, (~ ((v2_funct_1 @ sk_C_1))),
% 3.06/3.27      inference('sat_resolution*', [status(thm)], ['84', '85'])).
% 3.06/3.27  thf('87', plain, (~ (v2_funct_1 @ sk_C_1)),
% 3.06/3.27      inference('simpl_trail', [status(thm)], ['1', '86'])).
% 3.06/3.27  thf('88', plain,
% 3.06/3.27      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.06/3.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.27  thf(t3_subset, axiom,
% 3.06/3.27    (![A:$i,B:$i]:
% 3.06/3.27     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.06/3.27  thf('89', plain,
% 3.06/3.27      (![X12 : $i, X13 : $i]:
% 3.06/3.27         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 3.06/3.27      inference('cnf', [status(esa)], [t3_subset])).
% 3.06/3.27  thf('90', plain, ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 3.06/3.27      inference('sup-', [status(thm)], ['88', '89'])).
% 3.06/3.27  thf('91', plain,
% 3.06/3.27      (![X7 : $i, X9 : $i]:
% 3.06/3.27         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 3.06/3.27      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.06/3.27  thf('92', plain,
% 3.06/3.27      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C_1)
% 3.06/3.27        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_C_1)))),
% 3.06/3.27      inference('sup-', [status(thm)], ['90', '91'])).
% 3.06/3.27  thf('93', plain,
% 3.06/3.27      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 3.06/3.27         = (k5_relat_1 @ sk_C_1 @ sk_D))),
% 3.06/3.27      inference('demod', [status(thm)], ['21', '22'])).
% 3.06/3.27  thf('94', plain,
% 3.06/3.27      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.06/3.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.27  thf(t26_funct_2, axiom,
% 3.06/3.27    (![A:$i,B:$i,C:$i,D:$i]:
% 3.06/3.27     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.06/3.27         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.06/3.27       ( ![E:$i]:
% 3.06/3.27         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.06/3.27             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.06/3.27           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 3.06/3.27             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 3.06/3.27               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 3.06/3.27  thf('95', plain,
% 3.06/3.27      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i, X58 : $i]:
% 3.06/3.27         (~ (v1_funct_1 @ X54)
% 3.06/3.27          | ~ (v1_funct_2 @ X54 @ X55 @ X56)
% 3.06/3.27          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X56)))
% 3.06/3.27          | ~ (v2_funct_1 @ (k1_partfun1 @ X57 @ X55 @ X55 @ X56 @ X58 @ X54))
% 3.06/3.27          | (v2_funct_1 @ X58)
% 3.06/3.27          | ((X56) = (k1_xboole_0))
% 3.06/3.27          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X55)))
% 3.06/3.27          | ~ (v1_funct_2 @ X58 @ X57 @ X55)
% 3.06/3.27          | ~ (v1_funct_1 @ X58))),
% 3.06/3.27      inference('cnf', [status(esa)], [t26_funct_2])).
% 3.06/3.27  thf('96', plain,
% 3.06/3.27      (![X0 : $i, X1 : $i]:
% 3.06/3.27         (~ (v1_funct_1 @ X0)
% 3.06/3.27          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 3.06/3.27          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 3.06/3.27          | ((sk_A) = (k1_xboole_0))
% 3.06/3.27          | (v2_funct_1 @ X0)
% 3.06/3.27          | ~ (v2_funct_1 @ 
% 3.06/3.27               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D))
% 3.06/3.27          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 3.06/3.27          | ~ (v1_funct_1 @ sk_D))),
% 3.06/3.27      inference('sup-', [status(thm)], ['94', '95'])).
% 3.06/3.27  thf('97', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 3.06/3.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.27  thf('98', plain, ((v1_funct_1 @ sk_D)),
% 3.06/3.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.27  thf('99', plain,
% 3.06/3.27      (![X0 : $i, X1 : $i]:
% 3.06/3.27         (~ (v1_funct_1 @ X0)
% 3.06/3.27          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 3.06/3.27          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 3.06/3.27          | ((sk_A) = (k1_xboole_0))
% 3.06/3.27          | (v2_funct_1 @ X0)
% 3.06/3.27          | ~ (v2_funct_1 @ 
% 3.06/3.27               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D)))),
% 3.06/3.27      inference('demod', [status(thm)], ['96', '97', '98'])).
% 3.06/3.27  thf('100', plain,
% 3.06/3.27      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C_1 @ sk_D))
% 3.06/3.27        | (v2_funct_1 @ sk_C_1)
% 3.06/3.27        | ((sk_A) = (k1_xboole_0))
% 3.06/3.27        | ~ (m1_subset_1 @ sk_C_1 @ 
% 3.06/3.27             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 3.06/3.27        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 3.06/3.27        | ~ (v1_funct_1 @ sk_C_1))),
% 3.06/3.27      inference('sup-', [status(thm)], ['93', '99'])).
% 3.06/3.27  thf('101', plain,
% 3.06/3.27      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.06/3.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.27  thf('102', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 3.06/3.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.27  thf('103', plain, ((v1_funct_1 @ sk_C_1)),
% 3.06/3.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.06/3.27  thf('104', plain,
% 3.06/3.27      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C_1 @ sk_D))
% 3.06/3.27        | (v2_funct_1 @ sk_C_1)
% 3.06/3.27        | ((sk_A) = (k1_xboole_0)))),
% 3.06/3.27      inference('demod', [status(thm)], ['100', '101', '102', '103'])).
% 3.06/3.27  thf('105', plain, (((k5_relat_1 @ sk_C_1 @ sk_D) = (k6_partfun1 @ sk_A))),
% 3.06/3.27      inference('demod', [status(thm)], ['54', '57'])).
% 3.06/3.27  thf(fc4_funct_1, axiom,
% 3.06/3.27    (![A:$i]:
% 3.06/3.27     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 3.06/3.27       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 3.06/3.27  thf('106', plain, (![X30 : $i]: (v2_funct_1 @ (k6_relat_1 @ X30))),
% 3.06/3.27      inference('cnf', [status(esa)], [fc4_funct_1])).
% 3.06/3.27  thf('107', plain, (![X53 : $i]: ((k6_partfun1 @ X53) = (k6_relat_1 @ X53))),
% 3.06/3.27      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.06/3.27  thf('108', plain, (![X30 : $i]: (v2_funct_1 @ (k6_partfun1 @ X30))),
% 3.06/3.27      inference('demod', [status(thm)], ['106', '107'])).
% 3.06/3.27  thf('109', plain, (((v2_funct_1 @ sk_C_1) | ((sk_A) = (k1_xboole_0)))),
% 3.06/3.27      inference('demod', [status(thm)], ['104', '105', '108'])).
% 3.06/3.27  thf('110', plain, (~ (v2_funct_1 @ sk_C_1)),
% 3.06/3.27      inference('simpl_trail', [status(thm)], ['1', '86'])).
% 3.06/3.27  thf('111', plain, (((sk_A) = (k1_xboole_0))),
% 3.06/3.27      inference('clc', [status(thm)], ['109', '110'])).
% 3.06/3.27  thf('112', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 3.06/3.27      inference('simplify', [status(thm)], ['72'])).
% 3.06/3.27  thf('113', plain,
% 3.06/3.27      (![X12 : $i, X14 : $i]:
% 3.06/3.27         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 3.06/3.27      inference('cnf', [status(esa)], [t3_subset])).
% 3.06/3.27  thf('114', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 3.06/3.27      inference('sup-', [status(thm)], ['112', '113'])).
% 3.06/3.27  thf('115', plain,
% 3.06/3.27      (![X31 : $i, X32 : $i, X33 : $i]:
% 3.06/3.27         ((v4_relat_1 @ X31 @ X32)
% 3.06/3.27          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 3.06/3.27      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.06/3.27  thf('116', plain,
% 3.06/3.27      (![X0 : $i, X1 : $i]: (v4_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X1)),
% 3.06/3.27      inference('sup-', [status(thm)], ['114', '115'])).
% 3.06/3.27  thf(d18_relat_1, axiom,
% 3.06/3.27    (![A:$i,B:$i]:
% 3.06/3.27     ( ( v1_relat_1 @ B ) =>
% 3.06/3.27       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 3.06/3.27  thf('117', plain,
% 3.06/3.27      (![X17 : $i, X18 : $i]:
% 3.06/3.27         (~ (v4_relat_1 @ X17 @ X18)
% 3.06/3.27          | (r1_tarski @ (k1_relat_1 @ X17) @ X18)
% 3.06/3.27          | ~ (v1_relat_1 @ X17))),
% 3.06/3.27      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.06/3.27  thf('118', plain,
% 3.06/3.27      (![X0 : $i, X1 : $i]:
% 3.06/3.27         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))
% 3.06/3.27          | (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0))),
% 3.06/3.27      inference('sup-', [status(thm)], ['116', '117'])).
% 3.06/3.27  thf('119', plain,
% 3.06/3.27      (![X21 : $i, X22 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X21 @ X22))),
% 3.06/3.27      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.06/3.27  thf('120', plain,
% 3.06/3.27      (![X0 : $i, X1 : $i]:
% 3.06/3.27         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0)),
% 3.06/3.27      inference('demod', [status(thm)], ['118', '119'])).
% 3.06/3.27  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.06/3.27  thf('121', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.06/3.27      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.06/3.27  thf(d3_tarski, axiom,
% 3.06/3.27    (![A:$i,B:$i]:
% 3.06/3.27     ( ( r1_tarski @ A @ B ) <=>
% 3.06/3.27       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 3.06/3.27  thf('122', plain,
% 3.06/3.27      (![X4 : $i, X6 : $i]:
% 3.06/3.27         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 3.06/3.27      inference('cnf', [status(esa)], [d3_tarski])).
% 3.06/3.27  thf(d1_xboole_0, axiom,
% 3.06/3.27    (![A:$i]:
% 3.06/3.27     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 3.06/3.27  thf('123', plain,
% 3.06/3.27      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.06/3.27      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.06/3.27  thf('124', plain,
% 3.06/3.27      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 3.06/3.27      inference('sup-', [status(thm)], ['122', '123'])).
% 3.06/3.27  thf('125', plain,
% 3.06/3.27      (![X12 : $i, X14 : $i]:
% 3.06/3.27         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 3.06/3.27      inference('cnf', [status(esa)], [t3_subset])).
% 3.06/3.27  thf('126', plain,
% 3.06/3.27      (![X0 : $i, X1 : $i]:
% 3.06/3.27         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 3.06/3.27      inference('sup-', [status(thm)], ['124', '125'])).
% 3.06/3.27  thf('127', plain,
% 3.06/3.27      (![X31 : $i, X32 : $i, X33 : $i]:
% 3.06/3.27         ((v4_relat_1 @ X31 @ X32)
% 3.06/3.27          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 3.06/3.27      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.06/3.27  thf('128', plain,
% 3.06/3.27      (![X1 : $i, X2 : $i]: (~ (v1_xboole_0 @ X2) | (v4_relat_1 @ X2 @ X1))),
% 3.06/3.27      inference('sup-', [status(thm)], ['126', '127'])).
% 3.06/3.27  thf('129', plain, (![X0 : $i]: (v4_relat_1 @ k1_xboole_0 @ X0)),
% 3.06/3.27      inference('sup-', [status(thm)], ['121', '128'])).
% 3.06/3.27  thf('130', plain,
% 3.06/3.27      (![X17 : $i, X18 : $i]:
% 3.06/3.27         (~ (v4_relat_1 @ X17 @ X18)
% 3.06/3.27          | (r1_tarski @ (k1_relat_1 @ X17) @ X18)
% 3.06/3.27          | ~ (v1_relat_1 @ X17))),
% 3.06/3.27      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.06/3.27  thf('131', plain,
% 3.06/3.27      (![X0 : $i]:
% 3.06/3.27         (~ (v1_relat_1 @ k1_xboole_0)
% 3.06/3.27          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 3.06/3.27      inference('sup-', [status(thm)], ['129', '130'])).
% 3.06/3.27  thf('132', plain, (![X27 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 3.06/3.27      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.06/3.27  thf('133', plain, (![X53 : $i]: ((k6_partfun1 @ X53) = (k6_relat_1 @ X53))),
% 3.06/3.27      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.06/3.27  thf('134', plain,
% 3.06/3.27      (![X27 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X27)) = (X27))),
% 3.06/3.27      inference('demod', [status(thm)], ['132', '133'])).
% 3.06/3.27  thf(t64_relat_1, axiom,
% 3.06/3.27    (![A:$i]:
% 3.06/3.27     ( ( v1_relat_1 @ A ) =>
% 3.06/3.27       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 3.06/3.27           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 3.06/3.27         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 3.06/3.27  thf('135', plain,
% 3.06/3.27      (![X26 : $i]:
% 3.06/3.27         (((k1_relat_1 @ X26) != (k1_xboole_0))
% 3.06/3.27          | ((X26) = (k1_xboole_0))
% 3.06/3.27          | ~ (v1_relat_1 @ X26))),
% 3.06/3.27      inference('cnf', [status(esa)], [t64_relat_1])).
% 3.06/3.27  thf('136', plain,
% 3.06/3.27      (![X0 : $i]:
% 3.06/3.27         (((X0) != (k1_xboole_0))
% 3.06/3.27          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 3.06/3.27          | ((k6_partfun1 @ X0) = (k1_xboole_0)))),
% 3.06/3.27      inference('sup-', [status(thm)], ['134', '135'])).
% 3.06/3.27  thf('137', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 3.06/3.27      inference('cnf', [status(esa)], [fc4_funct_1])).
% 3.06/3.27  thf('138', plain, (![X53 : $i]: ((k6_partfun1 @ X53) = (k6_relat_1 @ X53))),
% 3.06/3.27      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.06/3.27  thf('139', plain, (![X29 : $i]: (v1_relat_1 @ (k6_partfun1 @ X29))),
% 3.06/3.27      inference('demod', [status(thm)], ['137', '138'])).
% 3.06/3.27  thf('140', plain,
% 3.06/3.27      (![X0 : $i]:
% 3.06/3.27         (((X0) != (k1_xboole_0)) | ((k6_partfun1 @ X0) = (k1_xboole_0)))),
% 3.06/3.27      inference('demod', [status(thm)], ['136', '139'])).
% 3.06/3.27  thf('141', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.06/3.27      inference('simplify', [status(thm)], ['140'])).
% 3.06/3.27  thf('142', plain, (![X29 : $i]: (v1_relat_1 @ (k6_partfun1 @ X29))),
% 3.06/3.27      inference('demod', [status(thm)], ['137', '138'])).
% 3.06/3.27  thf('143', plain, ((v1_relat_1 @ k1_xboole_0)),
% 3.06/3.27      inference('sup+', [status(thm)], ['141', '142'])).
% 3.06/3.27  thf('144', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.06/3.27      inference('simplify', [status(thm)], ['140'])).
% 3.06/3.27  thf('145', plain,
% 3.06/3.27      (![X27 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X27)) = (X27))),
% 3.06/3.27      inference('demod', [status(thm)], ['132', '133'])).
% 3.06/3.27  thf('146', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.06/3.27      inference('sup+', [status(thm)], ['144', '145'])).
% 3.06/3.27  thf('147', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 3.06/3.27      inference('demod', [status(thm)], ['131', '143', '146'])).
% 3.06/3.27  thf('148', plain,
% 3.06/3.27      (![X7 : $i, X9 : $i]:
% 3.06/3.27         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 3.06/3.27      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.06/3.27  thf('149', plain,
% 3.06/3.27      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 3.06/3.27      inference('sup-', [status(thm)], ['147', '148'])).
% 3.06/3.27  thf('150', plain,
% 3.06/3.27      (![X0 : $i]:
% 3.06/3.27         ((k1_relat_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))),
% 3.06/3.27      inference('sup-', [status(thm)], ['120', '149'])).
% 3.06/3.27  thf('151', plain,
% 3.06/3.27      (![X26 : $i]:
% 3.06/3.27         (((k1_relat_1 @ X26) != (k1_xboole_0))
% 3.06/3.27          | ((X26) = (k1_xboole_0))
% 3.06/3.27          | ~ (v1_relat_1 @ X26))),
% 3.06/3.27      inference('cnf', [status(esa)], [t64_relat_1])).
% 3.06/3.27  thf('152', plain,
% 3.06/3.27      (![X0 : $i]:
% 3.06/3.27         (((k1_xboole_0) != (k1_xboole_0))
% 3.06/3.27          | ~ (v1_relat_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 3.06/3.27          | ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 3.06/3.27      inference('sup-', [status(thm)], ['150', '151'])).
% 3.06/3.27  thf('153', plain,
% 3.06/3.27      (![X21 : $i, X22 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X21 @ X22))),
% 3.06/3.27      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.06/3.27  thf('154', plain,
% 3.06/3.27      (![X0 : $i]:
% 3.06/3.27         (((k1_xboole_0) != (k1_xboole_0))
% 3.06/3.27          | ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 3.06/3.27      inference('demod', [status(thm)], ['152', '153'])).
% 3.06/3.27  thf('155', plain,
% 3.06/3.27      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.06/3.27      inference('simplify', [status(thm)], ['154'])).
% 3.06/3.27  thf('156', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 3.06/3.27      inference('demod', [status(thm)], ['131', '143', '146'])).
% 3.06/3.27  thf('157', plain, (((sk_A) = (k1_xboole_0))),
% 3.06/3.27      inference('clc', [status(thm)], ['109', '110'])).
% 3.06/3.27  thf('158', plain,
% 3.06/3.27      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.06/3.27      inference('simplify', [status(thm)], ['154'])).
% 3.06/3.27  thf('159', plain, (((k1_xboole_0) = (sk_C_1))),
% 3.06/3.27      inference('demod', [status(thm)],
% 3.06/3.27                ['92', '111', '155', '156', '157', '158'])).
% 3.06/3.27  thf('160', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.06/3.27      inference('simplify', [status(thm)], ['140'])).
% 3.06/3.27  thf('161', plain, (![X30 : $i]: (v2_funct_1 @ (k6_partfun1 @ X30))),
% 3.06/3.27      inference('demod', [status(thm)], ['106', '107'])).
% 3.06/3.27  thf('162', plain, ((v2_funct_1 @ k1_xboole_0)),
% 3.06/3.27      inference('sup+', [status(thm)], ['160', '161'])).
% 3.06/3.27  thf('163', plain, ($false),
% 3.06/3.27      inference('demod', [status(thm)], ['87', '159', '162'])).
% 3.06/3.27  
% 3.06/3.27  % SZS output end Refutation
% 3.06/3.27  
% 3.06/3.28  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

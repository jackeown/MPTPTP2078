%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RqoJiaviy8

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:23 EST 2020

% Result     : Theorem 10.02s
% Output     : Refutation 10.02s
% Verified   : 
% Statistics : Number of formulae       :  205 (1313 expanded)
%              Number of leaves         :   48 ( 389 expanded)
%              Depth                    :   23
%              Number of atoms          : 1563 (25532 expanded)
%              Number of equality atoms :   69 ( 334 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ( ~ ( v2_funct_1 @ sk_C_2 )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v2_funct_1 @ sk_C_2 )
   <= ~ ( v2_funct_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X54 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X50 @ X51 @ X53 @ X54 @ X49 @ X52 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X54 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_2 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_2 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_2 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_2 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_2 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('13',plain,(
    ! [X22: $i,X23: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('14',plain,(
    v1_relat_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
    ! [X55: $i,X56: $i,X57: $i,X58: $i,X59: $i,X60: $i] :
      ( ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X57 ) ) )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_funct_1 @ X58 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X60 ) ) )
      | ( ( k1_partfun1 @ X56 @ X57 @ X59 @ X60 @ X55 @ X58 )
        = ( k5_relat_1 @ X55 @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_2 @ X0 )
        = ( k5_relat_1 @ sk_C_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_2 @ X0 )
        = ( k5_relat_1 @ sk_C_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_2 @ sk_D )
      = ( k5_relat_1 @ sk_C_2 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_2 @ sk_D )
    = ( k5_relat_1 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_C_2 @ sk_D ) ),
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
    ( ( v5_relat_1 @ ( k5_relat_1 @ sk_C_2 @ sk_D ) @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X22: $i,X23: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('33',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X22: $i,X23: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('38',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    v5_relat_1 @ ( k5_relat_1 @ sk_C_2 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['28','33','38'])).

thf('40',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v5_relat_1 @ X19 @ X20 )
      | ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C_2 @ sk_D ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C_2 @ sk_D ) ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['14','23'])).

thf('43',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C_2 @ sk_D ) ) @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('44',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('45',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C_2 @ sk_D ) ) )
    | ( ( k2_relat_1 @ sk_D )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_C_2 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_2 @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_2 @ sk_D )
    = ( k5_relat_1 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('48',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C_2 @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_2 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('50',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_2 @ sk_D )
    = ( k5_relat_1 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('51',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C_2 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('52',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( X42 = X45 )
      | ~ ( r2_relset_1 @ X43 @ X44 @ X42 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C_2 @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C_2 @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C_2 @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('55',plain,(
    ! [X46: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X46 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('56',plain,(
    ! [X61: $i] :
      ( ( k6_partfun1 @ X61 )
      = ( k6_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('57',plain,(
    ! [X46: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X46 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X46 ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k5_relat_1 @ sk_C_2 @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['54','57'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('59',plain,(
    ! [X27: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('60',plain,(
    ! [X61: $i] :
      ( ( k6_partfun1 @ X61 )
      = ( k6_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('61',plain,(
    ! [X27: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X27 ) )
      = X27 ) ),
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v5_relat_1 @ X33 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
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
    ( ( k5_relat_1 @ sk_C_2 @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['54','57'])).

thf('70',plain,(
    ! [X27: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X27 ) )
      = X27 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('71',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['45','58','61','68','69','70'])).

thf('72',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('73',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
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
    ! [X47: $i,X48: $i] :
      ( ( ( k2_relat_1 @ X48 )
       != X47 )
      | ( v2_funct_2 @ X48 @ X47 )
      | ~ ( v5_relat_1 @ X48 @ X47 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('77',plain,(
    ! [X48: $i] :
      ( ~ ( v1_relat_1 @ X48 )
      | ~ ( v5_relat_1 @ X48 @ ( k2_relat_1 @ X48 ) )
      | ( v2_funct_2 @ X48 @ ( k2_relat_1 @ X48 ) ) ) ),
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
    ( ~ ( v2_funct_1 @ sk_C_2 )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('86',plain,(
    ~ ( v2_funct_1 @ sk_C_2 ) ),
    inference('sat_resolution*',[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v2_funct_1 @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['1','86'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('88',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('89',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('90',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ( X7
       != ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('91',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','91'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('93',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ X15 @ X16 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('94',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( r2_relset_1 @ X43 @ X44 @ X42 @ X45 )
      | ( X42 != X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('96',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( r2_relset_1 @ X43 @ X44 @ X45 @ X45 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['94','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['88','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('100',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X11 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('101',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['99','101'])).

thf('103',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('104',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('105',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ X15 @ X16 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('107',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( X42 = X45 )
      | ~ ( r2_relset_1 @ X43 @ X44 @ X42 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ X0 )
      | ( sk_C_2 = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( sk_C_2
      = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['107','110'])).

thf('112',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_A )
    | ( sk_C_2
      = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['102','111'])).

thf('113',plain,
    ( ~ ( v1_xboole_0 @ sk_C_2 )
    | ( sk_C_2
      = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['98','112'])).

thf('114',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('115',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X38 ) ) )
      | ( v1_xboole_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('116',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( sk_C_2
      = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['113','116'])).

thf('118',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_2 @ sk_D )
    = ( k5_relat_1 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('119',plain,(
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

thf('120',plain,(
    ! [X62: $i,X63: $i,X64: $i,X65: $i,X66: $i] :
      ( ~ ( v1_funct_1 @ X62 )
      | ~ ( v1_funct_2 @ X62 @ X63 @ X64 )
      | ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X63 @ X64 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X65 @ X63 @ X63 @ X64 @ X66 @ X62 ) )
      | ( v2_funct_1 @ X66 )
      | ( X64 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X65 @ X63 ) ) )
      | ~ ( v1_funct_2 @ X66 @ X65 @ X63 )
      | ~ ( v1_funct_1 @ X66 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['121','122','123'])).

thf('125',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C_2 @ sk_D ) )
    | ( v2_funct_1 @ sk_C_2 )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['118','124'])).

thf('126',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C_2 @ sk_D ) )
    | ( v2_funct_1 @ sk_C_2 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['125','126','127','128'])).

thf('130',plain,
    ( ( k5_relat_1 @ sk_C_2 @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['54','57'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('131',plain,(
    ! [X32: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('132',plain,(
    ! [X61: $i] :
      ( ( k6_partfun1 @ X61 )
      = ( k6_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('133',plain,(
    ! [X32: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X32 ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( v2_funct_1 @ sk_C_2 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['129','130','133'])).

thf('135',plain,(
    ~ ( v2_funct_1 @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['1','86'])).

thf('136',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['134','135'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('137',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('138',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['134','135'])).

thf('139',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['100'])).

thf('140',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference(demod,[status(thm)],['117','136','137','138','139'])).

thf('141',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('142',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,(
    ! [X46: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X46 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X46 ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('144',plain,(
    m1_subset_1 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['100'])).

thf('146',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X38 ) ) )
      | ( v1_xboole_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('147',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('149',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,(
    v1_xboole_0 @ ( k6_partfun1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['144','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('152',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X32: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X32 ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('154',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['152','153'])).

thf('155',plain,(
    $false ),
    inference(demod,[status(thm)],['87','140','154'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RqoJiaviy8
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:47:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 10.02/10.21  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 10.02/10.21  % Solved by: fo/fo7.sh
% 10.02/10.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 10.02/10.21  % done 10877 iterations in 9.753s
% 10.02/10.21  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 10.02/10.21  % SZS output start Refutation
% 10.02/10.21  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 10.02/10.21  thf(sk_C_2_type, type, sk_C_2: $i).
% 10.02/10.21  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 10.02/10.21  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 10.02/10.21  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 10.02/10.21  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 10.02/10.21  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 10.02/10.21  thf(sk_D_type, type, sk_D: $i).
% 10.02/10.21  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 10.02/10.21  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 10.02/10.21  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 10.02/10.21  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 10.02/10.21  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 10.02/10.21  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 10.02/10.21  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 10.02/10.21  thf(sk_B_1_type, type, sk_B_1: $i).
% 10.02/10.21  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 10.02/10.21  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 10.02/10.21  thf(sk_A_type, type, sk_A: $i).
% 10.02/10.21  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 10.02/10.21  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 10.02/10.21  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 10.02/10.21  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 10.02/10.21  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 10.02/10.21  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 10.02/10.21  thf(t29_funct_2, conjecture,
% 10.02/10.21    (![A:$i,B:$i,C:$i]:
% 10.02/10.21     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 10.02/10.21         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.02/10.21       ( ![D:$i]:
% 10.02/10.21         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 10.02/10.21             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 10.02/10.21           ( ( r2_relset_1 @
% 10.02/10.21               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 10.02/10.21               ( k6_partfun1 @ A ) ) =>
% 10.02/10.21             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 10.02/10.21  thf(zf_stmt_0, negated_conjecture,
% 10.02/10.21    (~( ![A:$i,B:$i,C:$i]:
% 10.02/10.21        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 10.02/10.21            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.02/10.21          ( ![D:$i]:
% 10.02/10.21            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 10.02/10.21                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 10.02/10.21              ( ( r2_relset_1 @
% 10.02/10.21                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 10.02/10.21                  ( k6_partfun1 @ A ) ) =>
% 10.02/10.21                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 10.02/10.21    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 10.02/10.21  thf('0', plain, ((~ (v2_funct_1 @ sk_C_2) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 10.02/10.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.02/10.21  thf('1', plain, ((~ (v2_funct_1 @ sk_C_2)) <= (~ ((v2_funct_1 @ sk_C_2)))),
% 10.02/10.21      inference('split', [status(esa)], ['0'])).
% 10.02/10.21  thf('2', plain,
% 10.02/10.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 10.02/10.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.02/10.21  thf('3', plain,
% 10.02/10.21      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 10.02/10.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.02/10.21  thf(dt_k1_partfun1, axiom,
% 10.02/10.21    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 10.02/10.21     ( ( ( v1_funct_1 @ E ) & 
% 10.02/10.21         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 10.02/10.21         ( v1_funct_1 @ F ) & 
% 10.02/10.21         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 10.02/10.21       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 10.02/10.21         ( m1_subset_1 @
% 10.02/10.21           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 10.02/10.21           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 10.02/10.21  thf('4', plain,
% 10.02/10.21      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 10.02/10.21         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 10.02/10.21          | ~ (v1_funct_1 @ X49)
% 10.02/10.21          | ~ (v1_funct_1 @ X52)
% 10.02/10.21          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X54)))
% 10.02/10.21          | (m1_subset_1 @ (k1_partfun1 @ X50 @ X51 @ X53 @ X54 @ X49 @ X52) @ 
% 10.02/10.21             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X54))))),
% 10.02/10.21      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 10.02/10.21  thf('5', plain,
% 10.02/10.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.02/10.21         ((m1_subset_1 @ 
% 10.02/10.21           (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_2 @ X1) @ 
% 10.02/10.21           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 10.02/10.21          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 10.02/10.21          | ~ (v1_funct_1 @ X1)
% 10.02/10.21          | ~ (v1_funct_1 @ sk_C_2))),
% 10.02/10.21      inference('sup-', [status(thm)], ['3', '4'])).
% 10.02/10.21  thf('6', plain, ((v1_funct_1 @ sk_C_2)),
% 10.02/10.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.02/10.21  thf('7', plain,
% 10.02/10.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.02/10.21         ((m1_subset_1 @ 
% 10.02/10.21           (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_2 @ X1) @ 
% 10.02/10.21           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 10.02/10.21          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 10.02/10.21          | ~ (v1_funct_1 @ X1))),
% 10.02/10.21      inference('demod', [status(thm)], ['5', '6'])).
% 10.02/10.21  thf('8', plain,
% 10.02/10.21      ((~ (v1_funct_1 @ sk_D)
% 10.02/10.21        | (m1_subset_1 @ 
% 10.02/10.21           (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_2 @ sk_D) @ 
% 10.02/10.21           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 10.02/10.21      inference('sup-', [status(thm)], ['2', '7'])).
% 10.02/10.21  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 10.02/10.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.02/10.21  thf('10', plain,
% 10.02/10.21      ((m1_subset_1 @ 
% 10.02/10.21        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_2 @ sk_D) @ 
% 10.02/10.21        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.02/10.21      inference('demod', [status(thm)], ['8', '9'])).
% 10.02/10.21  thf(cc2_relat_1, axiom,
% 10.02/10.21    (![A:$i]:
% 10.02/10.21     ( ( v1_relat_1 @ A ) =>
% 10.02/10.21       ( ![B:$i]:
% 10.02/10.21         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 10.02/10.21  thf('11', plain,
% 10.02/10.21      (![X17 : $i, X18 : $i]:
% 10.02/10.21         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 10.02/10.21          | (v1_relat_1 @ X17)
% 10.02/10.21          | ~ (v1_relat_1 @ X18))),
% 10.02/10.21      inference('cnf', [status(esa)], [cc2_relat_1])).
% 10.02/10.21  thf('12', plain,
% 10.02/10.21      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 10.02/10.21        | (v1_relat_1 @ 
% 10.02/10.21           (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_2 @ sk_D)))),
% 10.02/10.21      inference('sup-', [status(thm)], ['10', '11'])).
% 10.02/10.21  thf(fc6_relat_1, axiom,
% 10.02/10.21    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 10.02/10.21  thf('13', plain,
% 10.02/10.21      (![X22 : $i, X23 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X22 @ X23))),
% 10.02/10.21      inference('cnf', [status(esa)], [fc6_relat_1])).
% 10.02/10.21  thf('14', plain,
% 10.02/10.21      ((v1_relat_1 @ 
% 10.02/10.21        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_2 @ sk_D))),
% 10.02/10.21      inference('demod', [status(thm)], ['12', '13'])).
% 10.02/10.21  thf('15', plain,
% 10.02/10.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 10.02/10.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.02/10.21  thf('16', plain,
% 10.02/10.21      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 10.02/10.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.02/10.21  thf(redefinition_k1_partfun1, axiom,
% 10.02/10.21    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 10.02/10.21     ( ( ( v1_funct_1 @ E ) & 
% 10.02/10.21         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 10.02/10.21         ( v1_funct_1 @ F ) & 
% 10.02/10.21         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 10.02/10.21       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 10.02/10.21  thf('17', plain,
% 10.02/10.21      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i, X59 : $i, X60 : $i]:
% 10.02/10.21         (~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X57)))
% 10.02/10.21          | ~ (v1_funct_1 @ X55)
% 10.02/10.21          | ~ (v1_funct_1 @ X58)
% 10.02/10.21          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X60)))
% 10.02/10.21          | ((k1_partfun1 @ X56 @ X57 @ X59 @ X60 @ X55 @ X58)
% 10.02/10.21              = (k5_relat_1 @ X55 @ X58)))),
% 10.02/10.21      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 10.02/10.21  thf('18', plain,
% 10.02/10.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.02/10.21         (((k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_2 @ X0)
% 10.02/10.21            = (k5_relat_1 @ sk_C_2 @ X0))
% 10.02/10.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 10.02/10.21          | ~ (v1_funct_1 @ X0)
% 10.02/10.21          | ~ (v1_funct_1 @ sk_C_2))),
% 10.02/10.21      inference('sup-', [status(thm)], ['16', '17'])).
% 10.02/10.21  thf('19', plain, ((v1_funct_1 @ sk_C_2)),
% 10.02/10.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.02/10.21  thf('20', plain,
% 10.02/10.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.02/10.21         (((k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_2 @ X0)
% 10.02/10.21            = (k5_relat_1 @ sk_C_2 @ X0))
% 10.02/10.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 10.02/10.21          | ~ (v1_funct_1 @ X0))),
% 10.02/10.21      inference('demod', [status(thm)], ['18', '19'])).
% 10.02/10.21  thf('21', plain,
% 10.02/10.21      ((~ (v1_funct_1 @ sk_D)
% 10.02/10.21        | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_2 @ sk_D)
% 10.02/10.21            = (k5_relat_1 @ sk_C_2 @ sk_D)))),
% 10.02/10.21      inference('sup-', [status(thm)], ['15', '20'])).
% 10.02/10.21  thf('22', plain, ((v1_funct_1 @ sk_D)),
% 10.02/10.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.02/10.21  thf('23', plain,
% 10.02/10.21      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_2 @ sk_D)
% 10.02/10.21         = (k5_relat_1 @ sk_C_2 @ sk_D))),
% 10.02/10.21      inference('demod', [status(thm)], ['21', '22'])).
% 10.02/10.21  thf('24', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C_2 @ sk_D))),
% 10.02/10.21      inference('demod', [status(thm)], ['14', '23'])).
% 10.02/10.21  thf(t45_relat_1, axiom,
% 10.02/10.21    (![A:$i]:
% 10.02/10.21     ( ( v1_relat_1 @ A ) =>
% 10.02/10.21       ( ![B:$i]:
% 10.02/10.21         ( ( v1_relat_1 @ B ) =>
% 10.02/10.21           ( r1_tarski @
% 10.02/10.21             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 10.02/10.21  thf('25', plain,
% 10.02/10.21      (![X24 : $i, X25 : $i]:
% 10.02/10.21         (~ (v1_relat_1 @ X24)
% 10.02/10.21          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X25 @ X24)) @ 
% 10.02/10.21             (k2_relat_1 @ X24))
% 10.02/10.21          | ~ (v1_relat_1 @ X25))),
% 10.02/10.21      inference('cnf', [status(esa)], [t45_relat_1])).
% 10.02/10.21  thf(d19_relat_1, axiom,
% 10.02/10.21    (![A:$i,B:$i]:
% 10.02/10.21     ( ( v1_relat_1 @ B ) =>
% 10.02/10.21       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 10.02/10.21  thf('26', plain,
% 10.02/10.21      (![X19 : $i, X20 : $i]:
% 10.02/10.21         (~ (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 10.02/10.21          | (v5_relat_1 @ X19 @ X20)
% 10.02/10.21          | ~ (v1_relat_1 @ X19))),
% 10.02/10.21      inference('cnf', [status(esa)], [d19_relat_1])).
% 10.02/10.21  thf('27', plain,
% 10.02/10.21      (![X0 : $i, X1 : $i]:
% 10.02/10.21         (~ (v1_relat_1 @ X1)
% 10.02/10.21          | ~ (v1_relat_1 @ X0)
% 10.02/10.21          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 10.02/10.21          | (v5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 10.02/10.21      inference('sup-', [status(thm)], ['25', '26'])).
% 10.02/10.21  thf('28', plain,
% 10.02/10.21      (((v5_relat_1 @ (k5_relat_1 @ sk_C_2 @ sk_D) @ (k2_relat_1 @ sk_D))
% 10.02/10.21        | ~ (v1_relat_1 @ sk_D)
% 10.02/10.21        | ~ (v1_relat_1 @ sk_C_2))),
% 10.02/10.21      inference('sup-', [status(thm)], ['24', '27'])).
% 10.02/10.21  thf('29', plain,
% 10.02/10.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 10.02/10.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.02/10.21  thf('30', plain,
% 10.02/10.21      (![X17 : $i, X18 : $i]:
% 10.02/10.21         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 10.02/10.21          | (v1_relat_1 @ X17)
% 10.02/10.21          | ~ (v1_relat_1 @ X18))),
% 10.02/10.21      inference('cnf', [status(esa)], [cc2_relat_1])).
% 10.02/10.21  thf('31', plain,
% 10.02/10.21      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)) | (v1_relat_1 @ sk_D))),
% 10.02/10.21      inference('sup-', [status(thm)], ['29', '30'])).
% 10.02/10.21  thf('32', plain,
% 10.02/10.21      (![X22 : $i, X23 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X22 @ X23))),
% 10.02/10.21      inference('cnf', [status(esa)], [fc6_relat_1])).
% 10.02/10.21  thf('33', plain, ((v1_relat_1 @ sk_D)),
% 10.02/10.21      inference('demod', [status(thm)], ['31', '32'])).
% 10.02/10.21  thf('34', plain,
% 10.02/10.21      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 10.02/10.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.02/10.21  thf('35', plain,
% 10.02/10.21      (![X17 : $i, X18 : $i]:
% 10.02/10.21         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 10.02/10.21          | (v1_relat_1 @ X17)
% 10.02/10.21          | ~ (v1_relat_1 @ X18))),
% 10.02/10.21      inference('cnf', [status(esa)], [cc2_relat_1])).
% 10.02/10.21  thf('36', plain,
% 10.02/10.21      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_C_2))),
% 10.02/10.21      inference('sup-', [status(thm)], ['34', '35'])).
% 10.02/10.21  thf('37', plain,
% 10.02/10.21      (![X22 : $i, X23 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X22 @ X23))),
% 10.02/10.21      inference('cnf', [status(esa)], [fc6_relat_1])).
% 10.02/10.21  thf('38', plain, ((v1_relat_1 @ sk_C_2)),
% 10.02/10.21      inference('demod', [status(thm)], ['36', '37'])).
% 10.02/10.21  thf('39', plain,
% 10.02/10.21      ((v5_relat_1 @ (k5_relat_1 @ sk_C_2 @ sk_D) @ (k2_relat_1 @ sk_D))),
% 10.02/10.21      inference('demod', [status(thm)], ['28', '33', '38'])).
% 10.02/10.21  thf('40', plain,
% 10.02/10.21      (![X19 : $i, X20 : $i]:
% 10.02/10.21         (~ (v5_relat_1 @ X19 @ X20)
% 10.02/10.21          | (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 10.02/10.21          | ~ (v1_relat_1 @ X19))),
% 10.02/10.21      inference('cnf', [status(esa)], [d19_relat_1])).
% 10.02/10.21  thf('41', plain,
% 10.02/10.21      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_C_2 @ sk_D))
% 10.02/10.21        | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C_2 @ sk_D)) @ 
% 10.02/10.21           (k2_relat_1 @ sk_D)))),
% 10.02/10.21      inference('sup-', [status(thm)], ['39', '40'])).
% 10.02/10.21  thf('42', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C_2 @ sk_D))),
% 10.02/10.21      inference('demod', [status(thm)], ['14', '23'])).
% 10.02/10.21  thf('43', plain,
% 10.02/10.21      ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C_2 @ sk_D)) @ 
% 10.02/10.21        (k2_relat_1 @ sk_D))),
% 10.02/10.21      inference('demod', [status(thm)], ['41', '42'])).
% 10.02/10.21  thf(d10_xboole_0, axiom,
% 10.02/10.21    (![A:$i,B:$i]:
% 10.02/10.21     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 10.02/10.21  thf('44', plain,
% 10.02/10.21      (![X1 : $i, X3 : $i]:
% 10.02/10.21         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 10.02/10.21      inference('cnf', [status(esa)], [d10_xboole_0])).
% 10.02/10.21  thf('45', plain,
% 10.02/10.21      ((~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 10.02/10.21           (k2_relat_1 @ (k5_relat_1 @ sk_C_2 @ sk_D)))
% 10.02/10.21        | ((k2_relat_1 @ sk_D) = (k2_relat_1 @ (k5_relat_1 @ sk_C_2 @ sk_D))))),
% 10.02/10.21      inference('sup-', [status(thm)], ['43', '44'])).
% 10.02/10.21  thf('46', plain,
% 10.02/10.21      ((r2_relset_1 @ sk_A @ sk_A @ 
% 10.02/10.21        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_2 @ sk_D) @ 
% 10.02/10.21        (k6_partfun1 @ sk_A))),
% 10.02/10.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.02/10.21  thf('47', plain,
% 10.02/10.21      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_2 @ sk_D)
% 10.02/10.21         = (k5_relat_1 @ sk_C_2 @ sk_D))),
% 10.02/10.21      inference('demod', [status(thm)], ['21', '22'])).
% 10.02/10.21  thf('48', plain,
% 10.02/10.21      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C_2 @ sk_D) @ 
% 10.02/10.21        (k6_partfun1 @ sk_A))),
% 10.02/10.21      inference('demod', [status(thm)], ['46', '47'])).
% 10.02/10.21  thf('49', plain,
% 10.02/10.21      ((m1_subset_1 @ 
% 10.02/10.21        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_2 @ sk_D) @ 
% 10.02/10.21        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.02/10.21      inference('demod', [status(thm)], ['8', '9'])).
% 10.02/10.21  thf('50', plain,
% 10.02/10.21      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_2 @ sk_D)
% 10.02/10.21         = (k5_relat_1 @ sk_C_2 @ sk_D))),
% 10.02/10.21      inference('demod', [status(thm)], ['21', '22'])).
% 10.02/10.21  thf('51', plain,
% 10.02/10.21      ((m1_subset_1 @ (k5_relat_1 @ sk_C_2 @ sk_D) @ 
% 10.02/10.21        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 10.02/10.21      inference('demod', [status(thm)], ['49', '50'])).
% 10.02/10.21  thf(redefinition_r2_relset_1, axiom,
% 10.02/10.21    (![A:$i,B:$i,C:$i,D:$i]:
% 10.02/10.21     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 10.02/10.21         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.02/10.21       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 10.02/10.21  thf('52', plain,
% 10.02/10.21      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 10.02/10.21         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 10.02/10.21          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 10.02/10.21          | ((X42) = (X45))
% 10.02/10.21          | ~ (r2_relset_1 @ X43 @ X44 @ X42 @ X45))),
% 10.02/10.21      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 10.02/10.21  thf('53', plain,
% 10.02/10.21      (![X0 : $i]:
% 10.02/10.21         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C_2 @ sk_D) @ X0)
% 10.02/10.21          | ((k5_relat_1 @ sk_C_2 @ sk_D) = (X0))
% 10.02/10.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 10.02/10.21      inference('sup-', [status(thm)], ['51', '52'])).
% 10.02/10.21  thf('54', plain,
% 10.02/10.21      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 10.02/10.21           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 10.02/10.21        | ((k5_relat_1 @ sk_C_2 @ sk_D) = (k6_partfun1 @ sk_A)))),
% 10.02/10.21      inference('sup-', [status(thm)], ['48', '53'])).
% 10.02/10.21  thf(t29_relset_1, axiom,
% 10.02/10.21    (![A:$i]:
% 10.02/10.21     ( m1_subset_1 @
% 10.02/10.21       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 10.02/10.21  thf('55', plain,
% 10.02/10.21      (![X46 : $i]:
% 10.02/10.21         (m1_subset_1 @ (k6_relat_1 @ X46) @ 
% 10.02/10.21          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X46)))),
% 10.02/10.21      inference('cnf', [status(esa)], [t29_relset_1])).
% 10.02/10.21  thf(redefinition_k6_partfun1, axiom,
% 10.02/10.21    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 10.02/10.21  thf('56', plain, (![X61 : $i]: ((k6_partfun1 @ X61) = (k6_relat_1 @ X61))),
% 10.02/10.21      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 10.02/10.21  thf('57', plain,
% 10.02/10.21      (![X46 : $i]:
% 10.02/10.21         (m1_subset_1 @ (k6_partfun1 @ X46) @ 
% 10.02/10.21          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X46)))),
% 10.02/10.21      inference('demod', [status(thm)], ['55', '56'])).
% 10.02/10.21  thf('58', plain, (((k5_relat_1 @ sk_C_2 @ sk_D) = (k6_partfun1 @ sk_A))),
% 10.02/10.21      inference('demod', [status(thm)], ['54', '57'])).
% 10.02/10.21  thf(t71_relat_1, axiom,
% 10.02/10.21    (![A:$i]:
% 10.02/10.21     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 10.02/10.21       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 10.02/10.21  thf('59', plain, (![X27 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 10.02/10.21      inference('cnf', [status(esa)], [t71_relat_1])).
% 10.02/10.21  thf('60', plain, (![X61 : $i]: ((k6_partfun1 @ X61) = (k6_relat_1 @ X61))),
% 10.02/10.21      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 10.02/10.21  thf('61', plain, (![X27 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X27)) = (X27))),
% 10.02/10.21      inference('demod', [status(thm)], ['59', '60'])).
% 10.02/10.21  thf('62', plain,
% 10.02/10.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 10.02/10.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.02/10.21  thf(cc2_relset_1, axiom,
% 10.02/10.21    (![A:$i,B:$i,C:$i]:
% 10.02/10.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.02/10.21       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 10.02/10.21  thf('63', plain,
% 10.02/10.21      (![X33 : $i, X34 : $i, X35 : $i]:
% 10.02/10.21         ((v5_relat_1 @ X33 @ X35)
% 10.02/10.21          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 10.02/10.21      inference('cnf', [status(esa)], [cc2_relset_1])).
% 10.02/10.21  thf('64', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 10.02/10.21      inference('sup-', [status(thm)], ['62', '63'])).
% 10.02/10.21  thf('65', plain,
% 10.02/10.21      (![X19 : $i, X20 : $i]:
% 10.02/10.21         (~ (v5_relat_1 @ X19 @ X20)
% 10.02/10.21          | (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 10.02/10.21          | ~ (v1_relat_1 @ X19))),
% 10.02/10.21      inference('cnf', [status(esa)], [d19_relat_1])).
% 10.02/10.21  thf('66', plain,
% 10.02/10.21      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 10.02/10.21      inference('sup-', [status(thm)], ['64', '65'])).
% 10.02/10.21  thf('67', plain, ((v1_relat_1 @ sk_D)),
% 10.02/10.21      inference('demod', [status(thm)], ['31', '32'])).
% 10.02/10.21  thf('68', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 10.02/10.21      inference('demod', [status(thm)], ['66', '67'])).
% 10.02/10.21  thf('69', plain, (((k5_relat_1 @ sk_C_2 @ sk_D) = (k6_partfun1 @ sk_A))),
% 10.02/10.21      inference('demod', [status(thm)], ['54', '57'])).
% 10.02/10.21  thf('70', plain, (![X27 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X27)) = (X27))),
% 10.02/10.21      inference('demod', [status(thm)], ['59', '60'])).
% 10.02/10.21  thf('71', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 10.02/10.21      inference('demod', [status(thm)], ['45', '58', '61', '68', '69', '70'])).
% 10.02/10.21  thf('72', plain,
% 10.02/10.21      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 10.02/10.21      inference('cnf', [status(esa)], [d10_xboole_0])).
% 10.02/10.21  thf('73', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 10.02/10.21      inference('simplify', [status(thm)], ['72'])).
% 10.02/10.21  thf('74', plain,
% 10.02/10.21      (![X19 : $i, X20 : $i]:
% 10.02/10.21         (~ (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 10.02/10.21          | (v5_relat_1 @ X19 @ X20)
% 10.02/10.21          | ~ (v1_relat_1 @ X19))),
% 10.02/10.21      inference('cnf', [status(esa)], [d19_relat_1])).
% 10.02/10.21  thf('75', plain,
% 10.02/10.21      (![X0 : $i]:
% 10.02/10.21         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 10.02/10.21      inference('sup-', [status(thm)], ['73', '74'])).
% 10.02/10.21  thf(d3_funct_2, axiom,
% 10.02/10.21    (![A:$i,B:$i]:
% 10.02/10.21     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 10.02/10.21       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 10.02/10.21  thf('76', plain,
% 10.02/10.21      (![X47 : $i, X48 : $i]:
% 10.02/10.21         (((k2_relat_1 @ X48) != (X47))
% 10.02/10.21          | (v2_funct_2 @ X48 @ X47)
% 10.02/10.21          | ~ (v5_relat_1 @ X48 @ X47)
% 10.02/10.21          | ~ (v1_relat_1 @ X48))),
% 10.02/10.21      inference('cnf', [status(esa)], [d3_funct_2])).
% 10.02/10.21  thf('77', plain,
% 10.02/10.21      (![X48 : $i]:
% 10.02/10.21         (~ (v1_relat_1 @ X48)
% 10.02/10.21          | ~ (v5_relat_1 @ X48 @ (k2_relat_1 @ X48))
% 10.02/10.21          | (v2_funct_2 @ X48 @ (k2_relat_1 @ X48)))),
% 10.02/10.21      inference('simplify', [status(thm)], ['76'])).
% 10.02/10.21  thf('78', plain,
% 10.02/10.21      (![X0 : $i]:
% 10.02/10.21         (~ (v1_relat_1 @ X0)
% 10.02/10.21          | (v2_funct_2 @ X0 @ (k2_relat_1 @ X0))
% 10.02/10.21          | ~ (v1_relat_1 @ X0))),
% 10.02/10.21      inference('sup-', [status(thm)], ['75', '77'])).
% 10.02/10.21  thf('79', plain,
% 10.02/10.21      (![X0 : $i]:
% 10.02/10.21         ((v2_funct_2 @ X0 @ (k2_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 10.02/10.21      inference('simplify', [status(thm)], ['78'])).
% 10.02/10.21  thf('80', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 10.02/10.21      inference('sup+', [status(thm)], ['71', '79'])).
% 10.02/10.21  thf('81', plain, ((v1_relat_1 @ sk_D)),
% 10.02/10.21      inference('demod', [status(thm)], ['31', '32'])).
% 10.02/10.21  thf('82', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 10.02/10.21      inference('demod', [status(thm)], ['80', '81'])).
% 10.02/10.21  thf('83', plain,
% 10.02/10.21      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 10.02/10.21      inference('split', [status(esa)], ['0'])).
% 10.02/10.21  thf('84', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 10.02/10.21      inference('sup-', [status(thm)], ['82', '83'])).
% 10.02/10.21  thf('85', plain,
% 10.02/10.21      (~ ((v2_funct_1 @ sk_C_2)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 10.02/10.21      inference('split', [status(esa)], ['0'])).
% 10.02/10.21  thf('86', plain, (~ ((v2_funct_1 @ sk_C_2))),
% 10.02/10.21      inference('sat_resolution*', [status(thm)], ['84', '85'])).
% 10.02/10.21  thf('87', plain, (~ (v2_funct_1 @ sk_C_2)),
% 10.02/10.21      inference('simpl_trail', [status(thm)], ['1', '86'])).
% 10.02/10.21  thf(l13_xboole_0, axiom,
% 10.02/10.21    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 10.02/10.21  thf('88', plain,
% 10.02/10.21      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 10.02/10.21      inference('cnf', [status(esa)], [l13_xboole_0])).
% 10.02/10.21  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 10.02/10.21  thf('89', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 10.02/10.21      inference('cnf', [status(esa)], [t2_xboole_1])).
% 10.02/10.21  thf(d1_zfmisc_1, axiom,
% 10.02/10.21    (![A:$i,B:$i]:
% 10.02/10.21     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 10.02/10.21       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 10.02/10.21  thf('90', plain,
% 10.02/10.21      (![X5 : $i, X6 : $i, X7 : $i]:
% 10.02/10.21         (~ (r1_tarski @ X5 @ X6)
% 10.02/10.21          | (r2_hidden @ X5 @ X7)
% 10.02/10.21          | ((X7) != (k1_zfmisc_1 @ X6)))),
% 10.02/10.21      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 10.02/10.21  thf('91', plain,
% 10.02/10.21      (![X5 : $i, X6 : $i]:
% 10.02/10.21         ((r2_hidden @ X5 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X5 @ X6))),
% 10.02/10.21      inference('simplify', [status(thm)], ['90'])).
% 10.02/10.21  thf('92', plain,
% 10.02/10.21      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 10.02/10.21      inference('sup-', [status(thm)], ['89', '91'])).
% 10.02/10.21  thf(t1_subset, axiom,
% 10.02/10.21    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 10.02/10.21  thf('93', plain,
% 10.02/10.21      (![X15 : $i, X16 : $i]:
% 10.02/10.21         ((m1_subset_1 @ X15 @ X16) | ~ (r2_hidden @ X15 @ X16))),
% 10.02/10.21      inference('cnf', [status(esa)], [t1_subset])).
% 10.02/10.21  thf('94', plain,
% 10.02/10.21      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 10.02/10.21      inference('sup-', [status(thm)], ['92', '93'])).
% 10.02/10.21  thf('95', plain,
% 10.02/10.21      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 10.02/10.21         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 10.02/10.21          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 10.02/10.21          | (r2_relset_1 @ X43 @ X44 @ X42 @ X45)
% 10.02/10.21          | ((X42) != (X45)))),
% 10.02/10.21      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 10.02/10.21  thf('96', plain,
% 10.02/10.21      (![X43 : $i, X44 : $i, X45 : $i]:
% 10.02/10.21         ((r2_relset_1 @ X43 @ X44 @ X45 @ X45)
% 10.02/10.21          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44))))),
% 10.02/10.21      inference('simplify', [status(thm)], ['95'])).
% 10.02/10.21  thf('97', plain,
% 10.02/10.21      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 10.02/10.21      inference('sup-', [status(thm)], ['94', '96'])).
% 10.02/10.21  thf('98', plain,
% 10.02/10.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.02/10.21         ((r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 10.02/10.21      inference('sup+', [status(thm)], ['88', '97'])).
% 10.02/10.21  thf('99', plain,
% 10.02/10.21      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 10.02/10.21      inference('cnf', [status(esa)], [l13_xboole_0])).
% 10.02/10.21  thf(t113_zfmisc_1, axiom,
% 10.02/10.21    (![A:$i,B:$i]:
% 10.02/10.21     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 10.02/10.21       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 10.02/10.21  thf('100', plain,
% 10.02/10.21      (![X11 : $i, X12 : $i]:
% 10.02/10.21         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 10.02/10.21          | ((X11) != (k1_xboole_0)))),
% 10.02/10.21      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 10.02/10.21  thf('101', plain,
% 10.02/10.21      (![X12 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 10.02/10.21      inference('simplify', [status(thm)], ['100'])).
% 10.02/10.21  thf('102', plain,
% 10.02/10.21      (![X0 : $i, X1 : $i]:
% 10.02/10.21         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 10.02/10.21      inference('sup+', [status(thm)], ['99', '101'])).
% 10.02/10.21  thf('103', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 10.02/10.21      inference('simplify', [status(thm)], ['72'])).
% 10.02/10.21  thf('104', plain,
% 10.02/10.21      (![X5 : $i, X6 : $i]:
% 10.02/10.21         ((r2_hidden @ X5 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X5 @ X6))),
% 10.02/10.21      inference('simplify', [status(thm)], ['90'])).
% 10.02/10.21  thf('105', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 10.02/10.21      inference('sup-', [status(thm)], ['103', '104'])).
% 10.02/10.21  thf('106', plain,
% 10.02/10.21      (![X15 : $i, X16 : $i]:
% 10.02/10.21         ((m1_subset_1 @ X15 @ X16) | ~ (r2_hidden @ X15 @ X16))),
% 10.02/10.21      inference('cnf', [status(esa)], [t1_subset])).
% 10.02/10.21  thf('107', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 10.02/10.21      inference('sup-', [status(thm)], ['105', '106'])).
% 10.02/10.21  thf('108', plain,
% 10.02/10.21      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 10.02/10.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.02/10.21  thf('109', plain,
% 10.02/10.21      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 10.02/10.21         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 10.02/10.21          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 10.02/10.21          | ((X42) = (X45))
% 10.02/10.21          | ~ (r2_relset_1 @ X43 @ X44 @ X42 @ X45))),
% 10.02/10.21      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 10.02/10.21  thf('110', plain,
% 10.02/10.21      (![X0 : $i]:
% 10.02/10.21         (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ X0)
% 10.02/10.21          | ((sk_C_2) = (X0))
% 10.02/10.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))),
% 10.02/10.21      inference('sup-', [status(thm)], ['108', '109'])).
% 10.02/10.21  thf('111', plain,
% 10.02/10.21      ((((sk_C_2) = (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 10.02/10.21        | ~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ 
% 10.02/10.21             (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 10.02/10.21      inference('sup-', [status(thm)], ['107', '110'])).
% 10.02/10.21  thf('112', plain,
% 10.02/10.21      ((~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ k1_xboole_0)
% 10.02/10.21        | ~ (v1_xboole_0 @ sk_A)
% 10.02/10.21        | ((sk_C_2) = (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 10.02/10.21      inference('sup-', [status(thm)], ['102', '111'])).
% 10.02/10.21  thf('113', plain,
% 10.02/10.21      ((~ (v1_xboole_0 @ sk_C_2)
% 10.02/10.21        | ((sk_C_2) = (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 10.02/10.21        | ~ (v1_xboole_0 @ sk_A))),
% 10.02/10.21      inference('sup-', [status(thm)], ['98', '112'])).
% 10.02/10.21  thf('114', plain,
% 10.02/10.21      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 10.02/10.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.02/10.21  thf(cc3_relset_1, axiom,
% 10.02/10.21    (![A:$i,B:$i]:
% 10.02/10.21     ( ( v1_xboole_0 @ A ) =>
% 10.02/10.21       ( ![C:$i]:
% 10.02/10.21         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.02/10.21           ( v1_xboole_0 @ C ) ) ) ))).
% 10.02/10.21  thf('115', plain,
% 10.02/10.21      (![X36 : $i, X37 : $i, X38 : $i]:
% 10.02/10.21         (~ (v1_xboole_0 @ X36)
% 10.02/10.21          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X38)))
% 10.02/10.21          | (v1_xboole_0 @ X37))),
% 10.02/10.21      inference('cnf', [status(esa)], [cc3_relset_1])).
% 10.02/10.21  thf('116', plain, (((v1_xboole_0 @ sk_C_2) | ~ (v1_xboole_0 @ sk_A))),
% 10.02/10.21      inference('sup-', [status(thm)], ['114', '115'])).
% 10.02/10.21  thf('117', plain,
% 10.02/10.21      ((~ (v1_xboole_0 @ sk_A) | ((sk_C_2) = (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 10.02/10.21      inference('clc', [status(thm)], ['113', '116'])).
% 10.02/10.21  thf('118', plain,
% 10.02/10.21      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_2 @ sk_D)
% 10.02/10.21         = (k5_relat_1 @ sk_C_2 @ sk_D))),
% 10.02/10.21      inference('demod', [status(thm)], ['21', '22'])).
% 10.02/10.21  thf('119', plain,
% 10.02/10.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 10.02/10.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.02/10.21  thf(t26_funct_2, axiom,
% 10.02/10.21    (![A:$i,B:$i,C:$i,D:$i]:
% 10.02/10.21     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 10.02/10.21         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.02/10.21       ( ![E:$i]:
% 10.02/10.21         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 10.02/10.21             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 10.02/10.21           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 10.02/10.21             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 10.02/10.21               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 10.02/10.21  thf('120', plain,
% 10.02/10.21      (![X62 : $i, X63 : $i, X64 : $i, X65 : $i, X66 : $i]:
% 10.02/10.21         (~ (v1_funct_1 @ X62)
% 10.02/10.21          | ~ (v1_funct_2 @ X62 @ X63 @ X64)
% 10.02/10.21          | ~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X63 @ X64)))
% 10.02/10.21          | ~ (v2_funct_1 @ (k1_partfun1 @ X65 @ X63 @ X63 @ X64 @ X66 @ X62))
% 10.02/10.21          | (v2_funct_1 @ X66)
% 10.02/10.21          | ((X64) = (k1_xboole_0))
% 10.02/10.21          | ~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X65 @ X63)))
% 10.02/10.21          | ~ (v1_funct_2 @ X66 @ X65 @ X63)
% 10.02/10.21          | ~ (v1_funct_1 @ X66))),
% 10.02/10.21      inference('cnf', [status(esa)], [t26_funct_2])).
% 10.02/10.21  thf('121', plain,
% 10.02/10.21      (![X0 : $i, X1 : $i]:
% 10.02/10.21         (~ (v1_funct_1 @ X0)
% 10.02/10.21          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 10.02/10.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 10.02/10.21          | ((sk_A) = (k1_xboole_0))
% 10.02/10.21          | (v2_funct_1 @ X0)
% 10.02/10.21          | ~ (v2_funct_1 @ 
% 10.02/10.21               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D))
% 10.02/10.21          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 10.02/10.21          | ~ (v1_funct_1 @ sk_D))),
% 10.02/10.21      inference('sup-', [status(thm)], ['119', '120'])).
% 10.02/10.21  thf('122', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 10.02/10.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.02/10.21  thf('123', plain, ((v1_funct_1 @ sk_D)),
% 10.02/10.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.02/10.21  thf('124', plain,
% 10.02/10.21      (![X0 : $i, X1 : $i]:
% 10.02/10.21         (~ (v1_funct_1 @ X0)
% 10.02/10.21          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 10.02/10.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 10.02/10.21          | ((sk_A) = (k1_xboole_0))
% 10.02/10.21          | (v2_funct_1 @ X0)
% 10.02/10.21          | ~ (v2_funct_1 @ 
% 10.02/10.21               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D)))),
% 10.02/10.21      inference('demod', [status(thm)], ['121', '122', '123'])).
% 10.02/10.21  thf('125', plain,
% 10.02/10.21      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C_2 @ sk_D))
% 10.02/10.21        | (v2_funct_1 @ sk_C_2)
% 10.02/10.21        | ((sk_A) = (k1_xboole_0))
% 10.02/10.21        | ~ (m1_subset_1 @ sk_C_2 @ 
% 10.02/10.21             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 10.02/10.21        | ~ (v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)
% 10.02/10.21        | ~ (v1_funct_1 @ sk_C_2))),
% 10.02/10.21      inference('sup-', [status(thm)], ['118', '124'])).
% 10.02/10.21  thf('126', plain,
% 10.02/10.21      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 10.02/10.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.02/10.21  thf('127', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)),
% 10.02/10.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.02/10.21  thf('128', plain, ((v1_funct_1 @ sk_C_2)),
% 10.02/10.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.02/10.21  thf('129', plain,
% 10.02/10.21      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C_2 @ sk_D))
% 10.02/10.21        | (v2_funct_1 @ sk_C_2)
% 10.02/10.21        | ((sk_A) = (k1_xboole_0)))),
% 10.02/10.21      inference('demod', [status(thm)], ['125', '126', '127', '128'])).
% 10.02/10.21  thf('130', plain, (((k5_relat_1 @ sk_C_2 @ sk_D) = (k6_partfun1 @ sk_A))),
% 10.02/10.21      inference('demod', [status(thm)], ['54', '57'])).
% 10.02/10.21  thf(fc4_funct_1, axiom,
% 10.02/10.21    (![A:$i]:
% 10.02/10.21     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 10.02/10.21       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 10.02/10.21  thf('131', plain, (![X32 : $i]: (v2_funct_1 @ (k6_relat_1 @ X32))),
% 10.02/10.21      inference('cnf', [status(esa)], [fc4_funct_1])).
% 10.02/10.21  thf('132', plain, (![X61 : $i]: ((k6_partfun1 @ X61) = (k6_relat_1 @ X61))),
% 10.02/10.21      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 10.02/10.21  thf('133', plain, (![X32 : $i]: (v2_funct_1 @ (k6_partfun1 @ X32))),
% 10.02/10.21      inference('demod', [status(thm)], ['131', '132'])).
% 10.02/10.21  thf('134', plain, (((v2_funct_1 @ sk_C_2) | ((sk_A) = (k1_xboole_0)))),
% 10.02/10.21      inference('demod', [status(thm)], ['129', '130', '133'])).
% 10.02/10.21  thf('135', plain, (~ (v2_funct_1 @ sk_C_2)),
% 10.02/10.21      inference('simpl_trail', [status(thm)], ['1', '86'])).
% 10.02/10.21  thf('136', plain, (((sk_A) = (k1_xboole_0))),
% 10.02/10.21      inference('clc', [status(thm)], ['134', '135'])).
% 10.02/10.21  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 10.02/10.21  thf('137', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 10.02/10.21      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 10.02/10.21  thf('138', plain, (((sk_A) = (k1_xboole_0))),
% 10.02/10.21      inference('clc', [status(thm)], ['134', '135'])).
% 10.02/10.21  thf('139', plain,
% 10.02/10.21      (![X12 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 10.02/10.21      inference('simplify', [status(thm)], ['100'])).
% 10.02/10.21  thf('140', plain, (((sk_C_2) = (k1_xboole_0))),
% 10.02/10.21      inference('demod', [status(thm)], ['117', '136', '137', '138', '139'])).
% 10.02/10.21  thf('141', plain,
% 10.02/10.21      (![X11 : $i, X12 : $i]:
% 10.02/10.21         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 10.02/10.21          | ((X12) != (k1_xboole_0)))),
% 10.02/10.21      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 10.02/10.21  thf('142', plain,
% 10.02/10.21      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 10.02/10.21      inference('simplify', [status(thm)], ['141'])).
% 10.02/10.21  thf('143', plain,
% 10.02/10.21      (![X46 : $i]:
% 10.02/10.21         (m1_subset_1 @ (k6_partfun1 @ X46) @ 
% 10.02/10.21          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X46)))),
% 10.02/10.21      inference('demod', [status(thm)], ['55', '56'])).
% 10.02/10.21  thf('144', plain,
% 10.02/10.21      ((m1_subset_1 @ (k6_partfun1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 10.02/10.21      inference('sup+', [status(thm)], ['142', '143'])).
% 10.02/10.21  thf('145', plain,
% 10.02/10.21      (![X12 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 10.02/10.21      inference('simplify', [status(thm)], ['100'])).
% 10.02/10.21  thf('146', plain,
% 10.02/10.21      (![X36 : $i, X37 : $i, X38 : $i]:
% 10.02/10.21         (~ (v1_xboole_0 @ X36)
% 10.02/10.21          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X38)))
% 10.02/10.21          | (v1_xboole_0 @ X37))),
% 10.02/10.21      inference('cnf', [status(esa)], [cc3_relset_1])).
% 10.02/10.21  thf('147', plain,
% 10.02/10.21      (![X1 : $i]:
% 10.02/10.21         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 10.02/10.21          | (v1_xboole_0 @ X1)
% 10.02/10.21          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 10.02/10.21      inference('sup-', [status(thm)], ['145', '146'])).
% 10.02/10.21  thf('148', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 10.02/10.21      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 10.02/10.21  thf('149', plain,
% 10.02/10.21      (![X1 : $i]:
% 10.02/10.21         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 10.02/10.21          | (v1_xboole_0 @ X1))),
% 10.02/10.21      inference('demod', [status(thm)], ['147', '148'])).
% 10.02/10.21  thf('150', plain, ((v1_xboole_0 @ (k6_partfun1 @ k1_xboole_0))),
% 10.02/10.21      inference('sup-', [status(thm)], ['144', '149'])).
% 10.02/10.21  thf('151', plain,
% 10.02/10.21      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 10.02/10.21      inference('cnf', [status(esa)], [l13_xboole_0])).
% 10.02/10.21  thf('152', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 10.02/10.21      inference('sup-', [status(thm)], ['150', '151'])).
% 10.02/10.21  thf('153', plain, (![X32 : $i]: (v2_funct_1 @ (k6_partfun1 @ X32))),
% 10.02/10.21      inference('demod', [status(thm)], ['131', '132'])).
% 10.02/10.21  thf('154', plain, ((v2_funct_1 @ k1_xboole_0)),
% 10.02/10.21      inference('sup+', [status(thm)], ['152', '153'])).
% 10.02/10.21  thf('155', plain, ($false),
% 10.02/10.21      inference('demod', [status(thm)], ['87', '140', '154'])).
% 10.02/10.21  
% 10.02/10.21  % SZS output end Refutation
% 10.02/10.21  
% 10.05/10.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

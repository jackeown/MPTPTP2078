%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rKTLAHxOpp

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:21 EST 2020

% Result     : Theorem 4.74s
% Output     : Refutation 4.74s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 526 expanded)
%              Number of leaves         :   46 ( 167 expanded)
%              Depth                    :   19
%              Number of atoms          : 1373 (9670 expanded)
%              Number of equality atoms :   54 ( 131 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('13',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('14',plain,(
    v1_relat_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
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

thf('17',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ( ( k1_partfun1 @ X41 @ X42 @ X44 @ X45 @ X40 @ X43 )
        = ( k5_relat_1 @ X40 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['14','23'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('25',plain,(
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

thf('26',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ( v5_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( v5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( v5_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('33',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('38',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    v5_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['28','33','38'])).

thf('40',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v5_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['14','23'])).

thf('43',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) @ ( k2_relat_1 @ sk_D ) ),
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
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
    | ( ( k2_relat_1 @ sk_D )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('48',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('50',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('51',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('52',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( X27 = X30 )
      | ~ ( r2_relset_1 @ X28 @ X29 @ X27 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('55',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('56',plain,(
    ! [X46: $i] :
      ( ( k6_partfun1 @ X46 )
      = ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('57',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['54','57'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('59',plain,(
    ! [X22: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('60',plain,(
    ! [X46: $i] :
      ( ( k6_partfun1 @ X46 )
      = ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('61',plain,(
    ! [X22: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X22 ) )
      = X22 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('63',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v5_relat_1 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('64',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v5_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
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
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['54','57'])).

thf('70',plain,(
    ! [X22: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X22 ) )
      = X22 ) ),
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
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ( v5_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
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
    ! [X32: $i,X33: $i] :
      ( ( ( k2_relat_1 @ X33 )
       != X32 )
      | ( v2_funct_2 @ X33 @ X32 )
      | ~ ( v5_relat_1 @ X33 @ X32 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('77',plain,(
    ! [X33: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ~ ( v5_relat_1 @ X33 @ ( k2_relat_1 @ X33 ) )
      | ( v2_funct_2 @ X33 @ ( k2_relat_1 @ X33 ) ) ) ),
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
    ( $false
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['1','82'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('84',plain,(
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

thf('85',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('86',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('88',plain,(
    m1_subset_1 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('89',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_xboole_0 @ X11 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('90',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k6_partfun1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['72'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('92',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('93',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['91','94'])).

thf('96',plain,(
    v1_xboole_0 @ ( k6_partfun1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['90','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('98',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['96','97'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('99',plain,(
    ! [X23: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('100',plain,(
    ! [X46: $i] :
      ( ( k6_partfun1 @ X46 )
      = ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('101',plain,(
    ! [X23: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X23 ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['98','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['84','102'])).

thf('104',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('105',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('107',plain,(
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

thf('108',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X50 @ X48 @ X48 @ X49 @ X51 @ X47 ) )
      | ( v2_funct_1 @ X51 )
      | ( X49 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X48 ) ) )
      | ~ ( v1_funct_2 @ X51 @ X50 @ X48 )
      | ~ ( v1_funct_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['106','112'])).

thf('114',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['113','114','115','116'])).

thf('118',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['54','57'])).

thf('119',plain,(
    ! [X23: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X23 ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('120',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('122',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_xboole_0 @ X11 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('125',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) )
      | ( v1_xboole_0 @ sk_C ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['122','125'])).

thf('127',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('128',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['91','94'])).

thf('130',plain,
    ( ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['126','128','129'])).

thf('131',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['105','130'])).

thf('132',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('133',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['131','132'])).

thf('134',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['83','133'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rKTLAHxOpp
% 0.16/0.37  % Computer   : n006.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 16:10:08 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 4.74/4.96  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.74/4.96  % Solved by: fo/fo7.sh
% 4.74/4.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.74/4.96  % done 5496 iterations in 4.470s
% 4.74/4.96  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.74/4.96  % SZS output start Refutation
% 4.74/4.96  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 4.74/4.96  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.74/4.96  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 4.74/4.96  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.74/4.96  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.74/4.96  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.74/4.96  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 4.74/4.96  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 4.74/4.96  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 4.74/4.96  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.74/4.96  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.74/4.96  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.74/4.96  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.74/4.96  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 4.74/4.96  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 4.74/4.96  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 4.74/4.96  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.74/4.96  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.74/4.96  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 4.74/4.96  thf(sk_C_type, type, sk_C: $i).
% 4.74/4.96  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 4.74/4.96  thf(sk_B_type, type, sk_B: $i).
% 4.74/4.96  thf(sk_D_type, type, sk_D: $i).
% 4.74/4.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.74/4.96  thf(sk_A_type, type, sk_A: $i).
% 4.74/4.96  thf(t29_funct_2, conjecture,
% 4.74/4.96    (![A:$i,B:$i,C:$i]:
% 4.74/4.96     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.74/4.96         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.74/4.96       ( ![D:$i]:
% 4.74/4.96         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.74/4.96             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.74/4.96           ( ( r2_relset_1 @
% 4.74/4.96               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 4.74/4.96               ( k6_partfun1 @ A ) ) =>
% 4.74/4.96             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 4.74/4.96  thf(zf_stmt_0, negated_conjecture,
% 4.74/4.96    (~( ![A:$i,B:$i,C:$i]:
% 4.74/4.96        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.74/4.96            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.74/4.96          ( ![D:$i]:
% 4.74/4.96            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.74/4.96                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.74/4.96              ( ( r2_relset_1 @
% 4.74/4.96                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 4.74/4.96                  ( k6_partfun1 @ A ) ) =>
% 4.74/4.96                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 4.74/4.96    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 4.74/4.96  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 4.74/4.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.74/4.96  thf('1', plain,
% 4.74/4.96      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 4.74/4.96      inference('split', [status(esa)], ['0'])).
% 4.74/4.96  thf('2', plain,
% 4.74/4.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.74/4.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.74/4.96  thf('3', plain,
% 4.74/4.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.74/4.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.74/4.96  thf(dt_k1_partfun1, axiom,
% 4.74/4.96    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.74/4.96     ( ( ( v1_funct_1 @ E ) & 
% 4.74/4.96         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.74/4.96         ( v1_funct_1 @ F ) & 
% 4.74/4.96         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 4.74/4.96       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 4.74/4.96         ( m1_subset_1 @
% 4.74/4.96           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 4.74/4.96           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 4.74/4.96  thf('4', plain,
% 4.74/4.96      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 4.74/4.96         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 4.74/4.96          | ~ (v1_funct_1 @ X34)
% 4.74/4.96          | ~ (v1_funct_1 @ X37)
% 4.74/4.96          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 4.74/4.96          | (m1_subset_1 @ (k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37) @ 
% 4.74/4.96             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X39))))),
% 4.74/4.96      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 4.74/4.96  thf('5', plain,
% 4.74/4.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.74/4.96         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 4.74/4.96           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 4.74/4.96          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 4.74/4.96          | ~ (v1_funct_1 @ X1)
% 4.74/4.96          | ~ (v1_funct_1 @ sk_C))),
% 4.74/4.96      inference('sup-', [status(thm)], ['3', '4'])).
% 4.74/4.96  thf('6', plain, ((v1_funct_1 @ sk_C)),
% 4.74/4.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.74/4.96  thf('7', plain,
% 4.74/4.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.74/4.96         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 4.74/4.96           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 4.74/4.96          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 4.74/4.96          | ~ (v1_funct_1 @ X1))),
% 4.74/4.96      inference('demod', [status(thm)], ['5', '6'])).
% 4.74/4.96  thf('8', plain,
% 4.74/4.96      ((~ (v1_funct_1 @ sk_D)
% 4.74/4.96        | (m1_subset_1 @ 
% 4.74/4.96           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 4.74/4.96           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 4.74/4.96      inference('sup-', [status(thm)], ['2', '7'])).
% 4.74/4.96  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 4.74/4.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.74/4.96  thf('10', plain,
% 4.74/4.96      ((m1_subset_1 @ 
% 4.74/4.96        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 4.74/4.96        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.74/4.96      inference('demod', [status(thm)], ['8', '9'])).
% 4.74/4.96  thf(cc2_relat_1, axiom,
% 4.74/4.96    (![A:$i]:
% 4.74/4.96     ( ( v1_relat_1 @ A ) =>
% 4.74/4.96       ( ![B:$i]:
% 4.74/4.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 4.74/4.96  thf('11', plain,
% 4.74/4.96      (![X13 : $i, X14 : $i]:
% 4.74/4.96         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 4.74/4.96          | (v1_relat_1 @ X13)
% 4.74/4.96          | ~ (v1_relat_1 @ X14))),
% 4.74/4.96      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.74/4.96  thf('12', plain,
% 4.74/4.96      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 4.74/4.96        | (v1_relat_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)))),
% 4.74/4.96      inference('sup-', [status(thm)], ['10', '11'])).
% 4.74/4.96  thf(fc6_relat_1, axiom,
% 4.74/4.96    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 4.74/4.96  thf('13', plain,
% 4.74/4.96      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 4.74/4.96      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.74/4.96  thf('14', plain,
% 4.74/4.96      ((v1_relat_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D))),
% 4.74/4.96      inference('demod', [status(thm)], ['12', '13'])).
% 4.74/4.96  thf('15', plain,
% 4.74/4.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.74/4.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.74/4.96  thf('16', plain,
% 4.74/4.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.74/4.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.74/4.96  thf(redefinition_k1_partfun1, axiom,
% 4.74/4.96    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.74/4.96     ( ( ( v1_funct_1 @ E ) & 
% 4.74/4.96         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.74/4.96         ( v1_funct_1 @ F ) & 
% 4.74/4.96         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 4.74/4.96       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 4.74/4.96  thf('17', plain,
% 4.74/4.96      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 4.74/4.96         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 4.74/4.96          | ~ (v1_funct_1 @ X40)
% 4.74/4.96          | ~ (v1_funct_1 @ X43)
% 4.74/4.96          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 4.74/4.96          | ((k1_partfun1 @ X41 @ X42 @ X44 @ X45 @ X40 @ X43)
% 4.74/4.96              = (k5_relat_1 @ X40 @ X43)))),
% 4.74/4.96      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 4.74/4.96  thf('18', plain,
% 4.74/4.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.74/4.96         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 4.74/4.96            = (k5_relat_1 @ sk_C @ X0))
% 4.74/4.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 4.74/4.96          | ~ (v1_funct_1 @ X0)
% 4.74/4.96          | ~ (v1_funct_1 @ sk_C))),
% 4.74/4.96      inference('sup-', [status(thm)], ['16', '17'])).
% 4.74/4.96  thf('19', plain, ((v1_funct_1 @ sk_C)),
% 4.74/4.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.74/4.96  thf('20', plain,
% 4.74/4.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.74/4.96         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 4.74/4.96            = (k5_relat_1 @ sk_C @ X0))
% 4.74/4.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 4.74/4.96          | ~ (v1_funct_1 @ X0))),
% 4.74/4.96      inference('demod', [status(thm)], ['18', '19'])).
% 4.74/4.96  thf('21', plain,
% 4.74/4.96      ((~ (v1_funct_1 @ sk_D)
% 4.74/4.96        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.74/4.96            = (k5_relat_1 @ sk_C @ sk_D)))),
% 4.74/4.96      inference('sup-', [status(thm)], ['15', '20'])).
% 4.74/4.96  thf('22', plain, ((v1_funct_1 @ sk_D)),
% 4.74/4.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.74/4.96  thf('23', plain,
% 4.74/4.96      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.74/4.96         = (k5_relat_1 @ sk_C @ sk_D))),
% 4.74/4.96      inference('demod', [status(thm)], ['21', '22'])).
% 4.74/4.96  thf('24', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))),
% 4.74/4.96      inference('demod', [status(thm)], ['14', '23'])).
% 4.74/4.96  thf(t45_relat_1, axiom,
% 4.74/4.96    (![A:$i]:
% 4.74/4.96     ( ( v1_relat_1 @ A ) =>
% 4.74/4.96       ( ![B:$i]:
% 4.74/4.96         ( ( v1_relat_1 @ B ) =>
% 4.74/4.96           ( r1_tarski @
% 4.74/4.96             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 4.74/4.96  thf('25', plain,
% 4.74/4.96      (![X19 : $i, X20 : $i]:
% 4.74/4.96         (~ (v1_relat_1 @ X19)
% 4.74/4.96          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X20 @ X19)) @ 
% 4.74/4.96             (k2_relat_1 @ X19))
% 4.74/4.96          | ~ (v1_relat_1 @ X20))),
% 4.74/4.96      inference('cnf', [status(esa)], [t45_relat_1])).
% 4.74/4.96  thf(d19_relat_1, axiom,
% 4.74/4.96    (![A:$i,B:$i]:
% 4.74/4.96     ( ( v1_relat_1 @ B ) =>
% 4.74/4.96       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 4.74/4.96  thf('26', plain,
% 4.74/4.96      (![X15 : $i, X16 : $i]:
% 4.74/4.96         (~ (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 4.74/4.96          | (v5_relat_1 @ X15 @ X16)
% 4.74/4.96          | ~ (v1_relat_1 @ X15))),
% 4.74/4.96      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.74/4.96  thf('27', plain,
% 4.74/4.96      (![X0 : $i, X1 : $i]:
% 4.74/4.96         (~ (v1_relat_1 @ X1)
% 4.74/4.96          | ~ (v1_relat_1 @ X0)
% 4.74/4.96          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 4.74/4.96          | (v5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 4.74/4.96      inference('sup-', [status(thm)], ['25', '26'])).
% 4.74/4.96  thf('28', plain,
% 4.74/4.96      (((v5_relat_1 @ (k5_relat_1 @ sk_C @ sk_D) @ (k2_relat_1 @ sk_D))
% 4.74/4.96        | ~ (v1_relat_1 @ sk_D)
% 4.74/4.96        | ~ (v1_relat_1 @ sk_C))),
% 4.74/4.96      inference('sup-', [status(thm)], ['24', '27'])).
% 4.74/4.96  thf('29', plain,
% 4.74/4.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.74/4.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.74/4.96  thf('30', plain,
% 4.74/4.96      (![X13 : $i, X14 : $i]:
% 4.74/4.96         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 4.74/4.96          | (v1_relat_1 @ X13)
% 4.74/4.96          | ~ (v1_relat_1 @ X14))),
% 4.74/4.96      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.74/4.96  thf('31', plain,
% 4.74/4.96      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 4.74/4.96      inference('sup-', [status(thm)], ['29', '30'])).
% 4.74/4.96  thf('32', plain,
% 4.74/4.96      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 4.74/4.96      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.74/4.96  thf('33', plain, ((v1_relat_1 @ sk_D)),
% 4.74/4.96      inference('demod', [status(thm)], ['31', '32'])).
% 4.74/4.96  thf('34', plain,
% 4.74/4.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.74/4.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.74/4.96  thf('35', plain,
% 4.74/4.96      (![X13 : $i, X14 : $i]:
% 4.74/4.96         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 4.74/4.96          | (v1_relat_1 @ X13)
% 4.74/4.96          | ~ (v1_relat_1 @ X14))),
% 4.74/4.96      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.74/4.96  thf('36', plain,
% 4.74/4.96      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 4.74/4.96      inference('sup-', [status(thm)], ['34', '35'])).
% 4.74/4.96  thf('37', plain,
% 4.74/4.96      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 4.74/4.96      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.74/4.96  thf('38', plain, ((v1_relat_1 @ sk_C)),
% 4.74/4.96      inference('demod', [status(thm)], ['36', '37'])).
% 4.74/4.96  thf('39', plain,
% 4.74/4.96      ((v5_relat_1 @ (k5_relat_1 @ sk_C @ sk_D) @ (k2_relat_1 @ sk_D))),
% 4.74/4.96      inference('demod', [status(thm)], ['28', '33', '38'])).
% 4.74/4.96  thf('40', plain,
% 4.74/4.96      (![X15 : $i, X16 : $i]:
% 4.74/4.96         (~ (v5_relat_1 @ X15 @ X16)
% 4.74/4.96          | (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 4.74/4.96          | ~ (v1_relat_1 @ X15))),
% 4.74/4.96      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.74/4.96  thf('41', plain,
% 4.74/4.96      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 4.74/4.96        | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ 
% 4.74/4.96           (k2_relat_1 @ sk_D)))),
% 4.74/4.96      inference('sup-', [status(thm)], ['39', '40'])).
% 4.74/4.96  thf('42', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))),
% 4.74/4.96      inference('demod', [status(thm)], ['14', '23'])).
% 4.74/4.96  thf('43', plain,
% 4.74/4.96      ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ 
% 4.74/4.96        (k2_relat_1 @ sk_D))),
% 4.74/4.96      inference('demod', [status(thm)], ['41', '42'])).
% 4.74/4.96  thf(d10_xboole_0, axiom,
% 4.74/4.96    (![A:$i,B:$i]:
% 4.74/4.96     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.74/4.96  thf('44', plain,
% 4.74/4.96      (![X1 : $i, X3 : $i]:
% 4.74/4.96         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 4.74/4.96      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.74/4.96  thf('45', plain,
% 4.74/4.96      ((~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 4.74/4.96           (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 4.74/4.96        | ((k2_relat_1 @ sk_D) = (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))))),
% 4.74/4.96      inference('sup-', [status(thm)], ['43', '44'])).
% 4.74/4.96  thf('46', plain,
% 4.74/4.96      ((r2_relset_1 @ sk_A @ sk_A @ 
% 4.74/4.96        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 4.74/4.96        (k6_partfun1 @ sk_A))),
% 4.74/4.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.74/4.96  thf('47', plain,
% 4.74/4.96      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.74/4.96         = (k5_relat_1 @ sk_C @ sk_D))),
% 4.74/4.96      inference('demod', [status(thm)], ['21', '22'])).
% 4.74/4.96  thf('48', plain,
% 4.74/4.96      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 4.74/4.96        (k6_partfun1 @ sk_A))),
% 4.74/4.96      inference('demod', [status(thm)], ['46', '47'])).
% 4.74/4.96  thf('49', plain,
% 4.74/4.96      ((m1_subset_1 @ 
% 4.74/4.96        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 4.74/4.96        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.74/4.96      inference('demod', [status(thm)], ['8', '9'])).
% 4.74/4.96  thf('50', plain,
% 4.74/4.96      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.74/4.96         = (k5_relat_1 @ sk_C @ sk_D))),
% 4.74/4.96      inference('demod', [status(thm)], ['21', '22'])).
% 4.74/4.96  thf('51', plain,
% 4.74/4.96      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 4.74/4.96        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.74/4.96      inference('demod', [status(thm)], ['49', '50'])).
% 4.74/4.96  thf(redefinition_r2_relset_1, axiom,
% 4.74/4.96    (![A:$i,B:$i,C:$i,D:$i]:
% 4.74/4.96     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.74/4.96         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.74/4.96       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 4.74/4.96  thf('52', plain,
% 4.74/4.96      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 4.74/4.96         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 4.74/4.96          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 4.74/4.96          | ((X27) = (X30))
% 4.74/4.96          | ~ (r2_relset_1 @ X28 @ X29 @ X27 @ X30))),
% 4.74/4.96      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 4.74/4.96  thf('53', plain,
% 4.74/4.96      (![X0 : $i]:
% 4.74/4.96         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 4.74/4.96          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 4.74/4.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 4.74/4.96      inference('sup-', [status(thm)], ['51', '52'])).
% 4.74/4.96  thf('54', plain,
% 4.74/4.96      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 4.74/4.96           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 4.74/4.96        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 4.74/4.96      inference('sup-', [status(thm)], ['48', '53'])).
% 4.74/4.96  thf(t29_relset_1, axiom,
% 4.74/4.96    (![A:$i]:
% 4.74/4.96     ( m1_subset_1 @
% 4.74/4.96       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 4.74/4.96  thf('55', plain,
% 4.74/4.96      (![X31 : $i]:
% 4.74/4.96         (m1_subset_1 @ (k6_relat_1 @ X31) @ 
% 4.74/4.96          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 4.74/4.96      inference('cnf', [status(esa)], [t29_relset_1])).
% 4.74/4.96  thf(redefinition_k6_partfun1, axiom,
% 4.74/4.96    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 4.74/4.96  thf('56', plain, (![X46 : $i]: ((k6_partfun1 @ X46) = (k6_relat_1 @ X46))),
% 4.74/4.96      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.74/4.96  thf('57', plain,
% 4.74/4.96      (![X31 : $i]:
% 4.74/4.96         (m1_subset_1 @ (k6_partfun1 @ X31) @ 
% 4.74/4.96          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 4.74/4.96      inference('demod', [status(thm)], ['55', '56'])).
% 4.74/4.96  thf('58', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 4.74/4.96      inference('demod', [status(thm)], ['54', '57'])).
% 4.74/4.96  thf(t71_relat_1, axiom,
% 4.74/4.96    (![A:$i]:
% 4.74/4.96     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 4.74/4.96       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 4.74/4.96  thf('59', plain, (![X22 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 4.74/4.96      inference('cnf', [status(esa)], [t71_relat_1])).
% 4.74/4.96  thf('60', plain, (![X46 : $i]: ((k6_partfun1 @ X46) = (k6_relat_1 @ X46))),
% 4.74/4.96      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.74/4.96  thf('61', plain, (![X22 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X22)) = (X22))),
% 4.74/4.96      inference('demod', [status(thm)], ['59', '60'])).
% 4.74/4.96  thf('62', plain,
% 4.74/4.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.74/4.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.74/4.96  thf(cc2_relset_1, axiom,
% 4.74/4.96    (![A:$i,B:$i,C:$i]:
% 4.74/4.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.74/4.96       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 4.74/4.96  thf('63', plain,
% 4.74/4.96      (![X24 : $i, X25 : $i, X26 : $i]:
% 4.74/4.96         ((v5_relat_1 @ X24 @ X26)
% 4.74/4.96          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 4.74/4.96      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.74/4.96  thf('64', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 4.74/4.96      inference('sup-', [status(thm)], ['62', '63'])).
% 4.74/4.96  thf('65', plain,
% 4.74/4.96      (![X15 : $i, X16 : $i]:
% 4.74/4.96         (~ (v5_relat_1 @ X15 @ X16)
% 4.74/4.96          | (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 4.74/4.96          | ~ (v1_relat_1 @ X15))),
% 4.74/4.96      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.74/4.96  thf('66', plain,
% 4.74/4.96      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 4.74/4.96      inference('sup-', [status(thm)], ['64', '65'])).
% 4.74/4.96  thf('67', plain, ((v1_relat_1 @ sk_D)),
% 4.74/4.96      inference('demod', [status(thm)], ['31', '32'])).
% 4.74/4.96  thf('68', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 4.74/4.96      inference('demod', [status(thm)], ['66', '67'])).
% 4.74/4.96  thf('69', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 4.74/4.96      inference('demod', [status(thm)], ['54', '57'])).
% 4.74/4.96  thf('70', plain, (![X22 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X22)) = (X22))),
% 4.74/4.96      inference('demod', [status(thm)], ['59', '60'])).
% 4.74/4.96  thf('71', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 4.74/4.96      inference('demod', [status(thm)], ['45', '58', '61', '68', '69', '70'])).
% 4.74/4.96  thf('72', plain,
% 4.74/4.96      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 4.74/4.96      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.74/4.96  thf('73', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 4.74/4.96      inference('simplify', [status(thm)], ['72'])).
% 4.74/4.96  thf('74', plain,
% 4.74/4.96      (![X15 : $i, X16 : $i]:
% 4.74/4.96         (~ (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 4.74/4.96          | (v5_relat_1 @ X15 @ X16)
% 4.74/4.96          | ~ (v1_relat_1 @ X15))),
% 4.74/4.96      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.74/4.96  thf('75', plain,
% 4.74/4.96      (![X0 : $i]:
% 4.74/4.96         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 4.74/4.96      inference('sup-', [status(thm)], ['73', '74'])).
% 4.74/4.96  thf(d3_funct_2, axiom,
% 4.74/4.96    (![A:$i,B:$i]:
% 4.74/4.96     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 4.74/4.96       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 4.74/4.96  thf('76', plain,
% 4.74/4.96      (![X32 : $i, X33 : $i]:
% 4.74/4.96         (((k2_relat_1 @ X33) != (X32))
% 4.74/4.96          | (v2_funct_2 @ X33 @ X32)
% 4.74/4.96          | ~ (v5_relat_1 @ X33 @ X32)
% 4.74/4.96          | ~ (v1_relat_1 @ X33))),
% 4.74/4.96      inference('cnf', [status(esa)], [d3_funct_2])).
% 4.74/4.96  thf('77', plain,
% 4.74/4.96      (![X33 : $i]:
% 4.74/4.96         (~ (v1_relat_1 @ X33)
% 4.74/4.96          | ~ (v5_relat_1 @ X33 @ (k2_relat_1 @ X33))
% 4.74/4.96          | (v2_funct_2 @ X33 @ (k2_relat_1 @ X33)))),
% 4.74/4.96      inference('simplify', [status(thm)], ['76'])).
% 4.74/4.96  thf('78', plain,
% 4.74/4.96      (![X0 : $i]:
% 4.74/4.96         (~ (v1_relat_1 @ X0)
% 4.74/4.96          | (v2_funct_2 @ X0 @ (k2_relat_1 @ X0))
% 4.74/4.96          | ~ (v1_relat_1 @ X0))),
% 4.74/4.96      inference('sup-', [status(thm)], ['75', '77'])).
% 4.74/4.96  thf('79', plain,
% 4.74/4.96      (![X0 : $i]:
% 4.74/4.96         ((v2_funct_2 @ X0 @ (k2_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 4.74/4.96      inference('simplify', [status(thm)], ['78'])).
% 4.74/4.96  thf('80', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 4.74/4.96      inference('sup+', [status(thm)], ['71', '79'])).
% 4.74/4.96  thf('81', plain, ((v1_relat_1 @ sk_D)),
% 4.74/4.96      inference('demod', [status(thm)], ['31', '32'])).
% 4.74/4.96  thf('82', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 4.74/4.96      inference('demod', [status(thm)], ['80', '81'])).
% 4.74/4.96  thf('83', plain, (($false) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 4.74/4.96      inference('demod', [status(thm)], ['1', '82'])).
% 4.74/4.96  thf(l13_xboole_0, axiom,
% 4.74/4.96    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 4.74/4.96  thf('84', plain,
% 4.74/4.96      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 4.74/4.96      inference('cnf', [status(esa)], [l13_xboole_0])).
% 4.74/4.96  thf(t113_zfmisc_1, axiom,
% 4.74/4.96    (![A:$i,B:$i]:
% 4.74/4.96     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 4.74/4.96       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 4.74/4.96  thf('85', plain,
% 4.74/4.96      (![X9 : $i, X10 : $i]:
% 4.74/4.96         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X10) != (k1_xboole_0)))),
% 4.74/4.96      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 4.74/4.96  thf('86', plain,
% 4.74/4.96      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 4.74/4.96      inference('simplify', [status(thm)], ['85'])).
% 4.74/4.96  thf('87', plain,
% 4.74/4.96      (![X31 : $i]:
% 4.74/4.96         (m1_subset_1 @ (k6_partfun1 @ X31) @ 
% 4.74/4.96          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 4.74/4.96      inference('demod', [status(thm)], ['55', '56'])).
% 4.74/4.96  thf('88', plain,
% 4.74/4.96      ((m1_subset_1 @ (k6_partfun1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 4.74/4.96      inference('sup+', [status(thm)], ['86', '87'])).
% 4.74/4.96  thf(cc1_subset_1, axiom,
% 4.74/4.96    (![A:$i]:
% 4.74/4.96     ( ( v1_xboole_0 @ A ) =>
% 4.74/4.96       ( ![B:$i]:
% 4.74/4.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 4.74/4.96  thf('89', plain,
% 4.74/4.96      (![X11 : $i, X12 : $i]:
% 4.74/4.96         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 4.74/4.96          | (v1_xboole_0 @ X11)
% 4.74/4.96          | ~ (v1_xboole_0 @ X12))),
% 4.74/4.96      inference('cnf', [status(esa)], [cc1_subset_1])).
% 4.74/4.96  thf('90', plain,
% 4.74/4.96      ((~ (v1_xboole_0 @ k1_xboole_0)
% 4.74/4.96        | (v1_xboole_0 @ (k6_partfun1 @ k1_xboole_0)))),
% 4.74/4.96      inference('sup-', [status(thm)], ['88', '89'])).
% 4.74/4.96  thf('91', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 4.74/4.96      inference('simplify', [status(thm)], ['72'])).
% 4.74/4.96  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 4.74/4.96  thf('92', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 4.74/4.96      inference('cnf', [status(esa)], [t65_xboole_1])).
% 4.74/4.96  thf(t69_xboole_1, axiom,
% 4.74/4.96    (![A:$i,B:$i]:
% 4.74/4.96     ( ( ~( v1_xboole_0 @ B ) ) =>
% 4.74/4.96       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 4.74/4.96  thf('93', plain,
% 4.74/4.96      (![X6 : $i, X7 : $i]:
% 4.74/4.96         (~ (r1_xboole_0 @ X6 @ X7)
% 4.74/4.96          | ~ (r1_tarski @ X6 @ X7)
% 4.74/4.96          | (v1_xboole_0 @ X6))),
% 4.74/4.96      inference('cnf', [status(esa)], [t69_xboole_1])).
% 4.74/4.96  thf('94', plain,
% 4.74/4.96      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 4.74/4.96      inference('sup-', [status(thm)], ['92', '93'])).
% 4.74/4.96  thf('95', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.74/4.96      inference('sup-', [status(thm)], ['91', '94'])).
% 4.74/4.96  thf('96', plain, ((v1_xboole_0 @ (k6_partfun1 @ k1_xboole_0))),
% 4.74/4.96      inference('demod', [status(thm)], ['90', '95'])).
% 4.74/4.96  thf('97', plain,
% 4.74/4.96      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 4.74/4.96      inference('cnf', [status(esa)], [l13_xboole_0])).
% 4.74/4.96  thf('98', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.74/4.96      inference('sup-', [status(thm)], ['96', '97'])).
% 4.74/4.96  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 4.74/4.96  thf('99', plain, (![X23 : $i]: (v2_funct_1 @ (k6_relat_1 @ X23))),
% 4.74/4.96      inference('cnf', [status(esa)], [t52_funct_1])).
% 4.74/4.96  thf('100', plain, (![X46 : $i]: ((k6_partfun1 @ X46) = (k6_relat_1 @ X46))),
% 4.74/4.96      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.74/4.96  thf('101', plain, (![X23 : $i]: (v2_funct_1 @ (k6_partfun1 @ X23))),
% 4.74/4.96      inference('demod', [status(thm)], ['99', '100'])).
% 4.74/4.96  thf('102', plain, ((v2_funct_1 @ k1_xboole_0)),
% 4.74/4.96      inference('sup+', [status(thm)], ['98', '101'])).
% 4.74/4.96  thf('103', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 4.74/4.96      inference('sup+', [status(thm)], ['84', '102'])).
% 4.74/4.96  thf('104', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 4.74/4.96      inference('split', [status(esa)], ['0'])).
% 4.74/4.96  thf('105', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 4.74/4.96      inference('sup-', [status(thm)], ['103', '104'])).
% 4.74/4.96  thf('106', plain,
% 4.74/4.96      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.74/4.96         = (k5_relat_1 @ sk_C @ sk_D))),
% 4.74/4.96      inference('demod', [status(thm)], ['21', '22'])).
% 4.74/4.96  thf('107', plain,
% 4.74/4.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.74/4.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.74/4.96  thf(t26_funct_2, axiom,
% 4.74/4.96    (![A:$i,B:$i,C:$i,D:$i]:
% 4.74/4.96     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 4.74/4.96         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.74/4.96       ( ![E:$i]:
% 4.74/4.96         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 4.74/4.96             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 4.74/4.96           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 4.74/4.96             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 4.74/4.96               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 4.74/4.96  thf('108', plain,
% 4.74/4.96      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 4.74/4.96         (~ (v1_funct_1 @ X47)
% 4.74/4.96          | ~ (v1_funct_2 @ X47 @ X48 @ X49)
% 4.74/4.96          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 4.74/4.96          | ~ (v2_funct_1 @ (k1_partfun1 @ X50 @ X48 @ X48 @ X49 @ X51 @ X47))
% 4.74/4.96          | (v2_funct_1 @ X51)
% 4.74/4.96          | ((X49) = (k1_xboole_0))
% 4.74/4.96          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X48)))
% 4.74/4.96          | ~ (v1_funct_2 @ X51 @ X50 @ X48)
% 4.74/4.96          | ~ (v1_funct_1 @ X51))),
% 4.74/4.96      inference('cnf', [status(esa)], [t26_funct_2])).
% 4.74/4.96  thf('109', plain,
% 4.74/4.96      (![X0 : $i, X1 : $i]:
% 4.74/4.96         (~ (v1_funct_1 @ X0)
% 4.74/4.96          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 4.74/4.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 4.74/4.96          | ((sk_A) = (k1_xboole_0))
% 4.74/4.96          | (v2_funct_1 @ X0)
% 4.74/4.96          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 4.74/4.96          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 4.74/4.96          | ~ (v1_funct_1 @ sk_D))),
% 4.74/4.96      inference('sup-', [status(thm)], ['107', '108'])).
% 4.74/4.96  thf('110', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 4.74/4.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.74/4.96  thf('111', plain, ((v1_funct_1 @ sk_D)),
% 4.74/4.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.74/4.96  thf('112', plain,
% 4.74/4.96      (![X0 : $i, X1 : $i]:
% 4.74/4.96         (~ (v1_funct_1 @ X0)
% 4.74/4.96          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 4.74/4.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 4.74/4.96          | ((sk_A) = (k1_xboole_0))
% 4.74/4.96          | (v2_funct_1 @ X0)
% 4.74/4.96          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 4.74/4.96      inference('demod', [status(thm)], ['109', '110', '111'])).
% 4.74/4.96  thf('113', plain,
% 4.74/4.96      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 4.74/4.96        | (v2_funct_1 @ sk_C)
% 4.74/4.96        | ((sk_A) = (k1_xboole_0))
% 4.74/4.96        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 4.74/4.96        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 4.74/4.96        | ~ (v1_funct_1 @ sk_C))),
% 4.74/4.96      inference('sup-', [status(thm)], ['106', '112'])).
% 4.74/4.96  thf('114', plain,
% 4.74/4.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.74/4.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.74/4.96  thf('115', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 4.74/4.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.74/4.96  thf('116', plain, ((v1_funct_1 @ sk_C)),
% 4.74/4.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.74/4.96  thf('117', plain,
% 4.74/4.96      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 4.74/4.96        | (v2_funct_1 @ sk_C)
% 4.74/4.96        | ((sk_A) = (k1_xboole_0)))),
% 4.74/4.96      inference('demod', [status(thm)], ['113', '114', '115', '116'])).
% 4.74/4.96  thf('118', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 4.74/4.96      inference('demod', [status(thm)], ['54', '57'])).
% 4.74/4.96  thf('119', plain, (![X23 : $i]: (v2_funct_1 @ (k6_partfun1 @ X23))),
% 4.74/4.96      inference('demod', [status(thm)], ['99', '100'])).
% 4.74/4.96  thf('120', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 4.74/4.96      inference('demod', [status(thm)], ['117', '118', '119'])).
% 4.74/4.96  thf('121', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 4.74/4.96      inference('split', [status(esa)], ['0'])).
% 4.74/4.96  thf('122', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 4.74/4.96      inference('sup-', [status(thm)], ['120', '121'])).
% 4.74/4.96  thf('123', plain,
% 4.74/4.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.74/4.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.74/4.96  thf('124', plain,
% 4.74/4.96      (![X11 : $i, X12 : $i]:
% 4.74/4.96         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 4.74/4.96          | (v1_xboole_0 @ X11)
% 4.74/4.96          | ~ (v1_xboole_0 @ X12))),
% 4.74/4.96      inference('cnf', [status(esa)], [cc1_subset_1])).
% 4.74/4.96  thf('125', plain,
% 4.74/4.96      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 4.74/4.96      inference('sup-', [status(thm)], ['123', '124'])).
% 4.74/4.96  thf('126', plain,
% 4.74/4.96      (((~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))
% 4.74/4.96         | (v1_xboole_0 @ sk_C))) <= (~ ((v2_funct_1 @ sk_C)))),
% 4.74/4.96      inference('sup-', [status(thm)], ['122', '125'])).
% 4.74/4.96  thf('127', plain,
% 4.74/4.96      (![X9 : $i, X10 : $i]:
% 4.74/4.96         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 4.74/4.96      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 4.74/4.96  thf('128', plain,
% 4.74/4.96      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 4.74/4.96      inference('simplify', [status(thm)], ['127'])).
% 4.74/4.96  thf('129', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.74/4.96      inference('sup-', [status(thm)], ['91', '94'])).
% 4.74/4.96  thf('130', plain, (((v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 4.74/4.96      inference('demod', [status(thm)], ['126', '128', '129'])).
% 4.74/4.96  thf('131', plain, (((v2_funct_1 @ sk_C))),
% 4.74/4.96      inference('demod', [status(thm)], ['105', '130'])).
% 4.74/4.96  thf('132', plain, (~ ((v2_funct_2 @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_C))),
% 4.74/4.96      inference('split', [status(esa)], ['0'])).
% 4.74/4.96  thf('133', plain, (~ ((v2_funct_2 @ sk_D @ sk_A))),
% 4.74/4.96      inference('sat_resolution*', [status(thm)], ['131', '132'])).
% 4.74/4.96  thf('134', plain, ($false),
% 4.74/4.96      inference('simpl_trail', [status(thm)], ['83', '133'])).
% 4.74/4.96  
% 4.74/4.96  % SZS output end Refutation
% 4.74/4.96  
% 4.74/4.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

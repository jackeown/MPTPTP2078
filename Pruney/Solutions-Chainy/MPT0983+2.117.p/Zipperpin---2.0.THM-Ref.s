%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.feucngMvjQ

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:19 EST 2020

% Result     : Theorem 5.47s
% Output     : Refutation 5.47s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 515 expanded)
%              Number of leaves         :   47 ( 164 expanded)
%              Depth                    :   19
%              Number of atoms          : 1368 (9624 expanded)
%              Number of equality atoms :   53 ( 123 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

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

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(sk_C_type,type,(
    sk_C: $i )).

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

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ( ( k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45 )
        = ( k5_relat_1 @ X42 @ X45 ) ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( X28 = X31 )
      | ~ ( r2_relset_1 @ X29 @ X30 @ X28 @ X31 ) ) ),
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

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('55',plain,(
    ! [X41: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('56',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('57',plain,(
    ! [X22: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('58',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('59',plain,(
    ! [X22: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X22 ) )
      = X22 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('61',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v5_relat_1 @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('62',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v5_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('64',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['31','32'])).

thf('66',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('68',plain,(
    ! [X22: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X22 ) )
      = X22 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('69',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['45','56','59','66','67','68'])).

thf('70',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('71',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ( v5_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('74',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k2_relat_1 @ X33 )
       != X32 )
      | ( v2_funct_2 @ X33 @ X32 )
      | ~ ( v5_relat_1 @ X33 @ X32 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('75',plain,(
    ! [X33: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ~ ( v5_relat_1 @ X33 @ ( k2_relat_1 @ X33 ) )
      | ( v2_funct_2 @ X33 @ ( k2_relat_1 @ X33 ) ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['69','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['31','32'])).

thf('80',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( $false
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['1','80'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('82',plain,(
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

thf('83',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('84',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X41: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('86',plain,(
    m1_subset_1 @ ( k6_partfun1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('87',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_xboole_0 @ X11 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('88',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k6_partfun1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['70'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('90',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('91',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['89','92'])).

thf('94',plain,(
    v1_xboole_0 @ ( k6_partfun1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['88','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('96',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['94','95'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('97',plain,(
    ! [X24: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('98',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('99',plain,(
    ! [X24: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X24 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['96','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['82','100'])).

thf('102',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('103',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('105',plain,(
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

thf('106',plain,(
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

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['104','110'])).

thf('112',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['111','112','113','114'])).

thf('116',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('117',plain,(
    ! [X24: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X24 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('118',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('119',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('120',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_xboole_0 @ X11 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('123',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) )
      | ( v1_xboole_0 @ sk_C ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['120','123'])).

thf('125',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('126',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['89','92'])).

thf('128',plain,
    ( ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['124','126','127'])).

thf('129',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['103','128'])).

thf('130',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('131',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['129','130'])).

thf('132',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['81','131'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.feucngMvjQ
% 0.14/0.33  % Computer   : n016.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 16:39:34 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  % Running portfolio for 600 s
% 0.14/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.33  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 5.47/5.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.47/5.65  % Solved by: fo/fo7.sh
% 5.47/5.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.47/5.65  % done 6047 iterations in 5.202s
% 5.47/5.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.47/5.65  % SZS output start Refutation
% 5.47/5.65  thf(sk_D_type, type, sk_D: $i).
% 5.47/5.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.47/5.65  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 5.47/5.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.47/5.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.47/5.65  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 5.47/5.65  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 5.47/5.65  thf(sk_B_type, type, sk_B: $i).
% 5.47/5.65  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 5.47/5.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 5.47/5.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 5.47/5.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 5.47/5.65  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 5.47/5.65  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 5.47/5.65  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 5.47/5.65  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 5.47/5.65  thf(sk_C_type, type, sk_C: $i).
% 5.47/5.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.47/5.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.47/5.65  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 5.47/5.65  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 5.47/5.65  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 5.47/5.65  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 5.47/5.65  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 5.47/5.65  thf(sk_A_type, type, sk_A: $i).
% 5.47/5.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.47/5.65  thf(t29_funct_2, conjecture,
% 5.47/5.65    (![A:$i,B:$i,C:$i]:
% 5.47/5.65     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.47/5.65         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.47/5.65       ( ![D:$i]:
% 5.47/5.65         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 5.47/5.65             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 5.47/5.65           ( ( r2_relset_1 @
% 5.47/5.65               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 5.47/5.65               ( k6_partfun1 @ A ) ) =>
% 5.47/5.65             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 5.47/5.65  thf(zf_stmt_0, negated_conjecture,
% 5.47/5.65    (~( ![A:$i,B:$i,C:$i]:
% 5.47/5.65        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.47/5.65            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.47/5.65          ( ![D:$i]:
% 5.47/5.65            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 5.47/5.65                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 5.47/5.65              ( ( r2_relset_1 @
% 5.47/5.65                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 5.47/5.65                  ( k6_partfun1 @ A ) ) =>
% 5.47/5.65                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 5.47/5.65    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 5.47/5.65  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 5.47/5.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.47/5.65  thf('1', plain,
% 5.47/5.65      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 5.47/5.65      inference('split', [status(esa)], ['0'])).
% 5.47/5.65  thf('2', plain,
% 5.47/5.65      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 5.47/5.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.47/5.65  thf('3', plain,
% 5.47/5.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.47/5.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.47/5.65  thf(dt_k1_partfun1, axiom,
% 5.47/5.65    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 5.47/5.65     ( ( ( v1_funct_1 @ E ) & 
% 5.47/5.65         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.47/5.65         ( v1_funct_1 @ F ) & 
% 5.47/5.65         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 5.47/5.65       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 5.47/5.65         ( m1_subset_1 @
% 5.47/5.65           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 5.47/5.65           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 5.47/5.65  thf('4', plain,
% 5.47/5.65      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 5.47/5.65         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 5.47/5.65          | ~ (v1_funct_1 @ X34)
% 5.47/5.65          | ~ (v1_funct_1 @ X37)
% 5.47/5.65          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 5.47/5.65          | (m1_subset_1 @ (k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37) @ 
% 5.47/5.65             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X39))))),
% 5.47/5.65      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 5.47/5.65  thf('5', plain,
% 5.47/5.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.47/5.65         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 5.47/5.65           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 5.47/5.65          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 5.47/5.65          | ~ (v1_funct_1 @ X1)
% 5.47/5.65          | ~ (v1_funct_1 @ sk_C))),
% 5.47/5.65      inference('sup-', [status(thm)], ['3', '4'])).
% 5.47/5.65  thf('6', plain, ((v1_funct_1 @ sk_C)),
% 5.47/5.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.47/5.65  thf('7', plain,
% 5.47/5.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.47/5.65         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 5.47/5.65           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 5.47/5.65          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 5.47/5.65          | ~ (v1_funct_1 @ X1))),
% 5.47/5.65      inference('demod', [status(thm)], ['5', '6'])).
% 5.47/5.65  thf('8', plain,
% 5.47/5.65      ((~ (v1_funct_1 @ sk_D)
% 5.47/5.65        | (m1_subset_1 @ 
% 5.47/5.65           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 5.47/5.65           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 5.47/5.65      inference('sup-', [status(thm)], ['2', '7'])).
% 5.47/5.65  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 5.47/5.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.47/5.65  thf('10', plain,
% 5.47/5.65      ((m1_subset_1 @ 
% 5.47/5.65        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 5.47/5.65        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.47/5.65      inference('demod', [status(thm)], ['8', '9'])).
% 5.47/5.65  thf(cc2_relat_1, axiom,
% 5.47/5.65    (![A:$i]:
% 5.47/5.65     ( ( v1_relat_1 @ A ) =>
% 5.47/5.65       ( ![B:$i]:
% 5.47/5.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 5.47/5.65  thf('11', plain,
% 5.47/5.65      (![X13 : $i, X14 : $i]:
% 5.47/5.65         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 5.47/5.65          | (v1_relat_1 @ X13)
% 5.47/5.65          | ~ (v1_relat_1 @ X14))),
% 5.47/5.65      inference('cnf', [status(esa)], [cc2_relat_1])).
% 5.47/5.65  thf('12', plain,
% 5.47/5.65      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 5.47/5.65        | (v1_relat_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)))),
% 5.47/5.65      inference('sup-', [status(thm)], ['10', '11'])).
% 5.47/5.65  thf(fc6_relat_1, axiom,
% 5.47/5.65    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 5.47/5.65  thf('13', plain,
% 5.47/5.65      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 5.47/5.65      inference('cnf', [status(esa)], [fc6_relat_1])).
% 5.47/5.65  thf('14', plain,
% 5.47/5.65      ((v1_relat_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D))),
% 5.47/5.65      inference('demod', [status(thm)], ['12', '13'])).
% 5.47/5.65  thf('15', plain,
% 5.47/5.65      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 5.47/5.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.47/5.65  thf('16', plain,
% 5.47/5.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.47/5.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.47/5.65  thf(redefinition_k1_partfun1, axiom,
% 5.47/5.65    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 5.47/5.65     ( ( ( v1_funct_1 @ E ) & 
% 5.47/5.65         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.47/5.65         ( v1_funct_1 @ F ) & 
% 5.47/5.65         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 5.47/5.65       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 5.47/5.65  thf('17', plain,
% 5.47/5.65      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 5.47/5.65         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 5.47/5.65          | ~ (v1_funct_1 @ X42)
% 5.47/5.65          | ~ (v1_funct_1 @ X45)
% 5.47/5.65          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 5.47/5.65          | ((k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45)
% 5.47/5.65              = (k5_relat_1 @ X42 @ X45)))),
% 5.47/5.65      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 5.47/5.65  thf('18', plain,
% 5.47/5.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.47/5.65         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 5.47/5.65            = (k5_relat_1 @ sk_C @ X0))
% 5.47/5.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 5.47/5.65          | ~ (v1_funct_1 @ X0)
% 5.47/5.65          | ~ (v1_funct_1 @ sk_C))),
% 5.47/5.65      inference('sup-', [status(thm)], ['16', '17'])).
% 5.47/5.65  thf('19', plain, ((v1_funct_1 @ sk_C)),
% 5.47/5.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.47/5.65  thf('20', plain,
% 5.47/5.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.47/5.65         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 5.47/5.65            = (k5_relat_1 @ sk_C @ X0))
% 5.47/5.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 5.47/5.65          | ~ (v1_funct_1 @ X0))),
% 5.47/5.65      inference('demod', [status(thm)], ['18', '19'])).
% 5.47/5.65  thf('21', plain,
% 5.47/5.65      ((~ (v1_funct_1 @ sk_D)
% 5.47/5.65        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 5.47/5.65            = (k5_relat_1 @ sk_C @ sk_D)))),
% 5.47/5.65      inference('sup-', [status(thm)], ['15', '20'])).
% 5.47/5.65  thf('22', plain, ((v1_funct_1 @ sk_D)),
% 5.47/5.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.47/5.65  thf('23', plain,
% 5.47/5.65      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 5.47/5.65         = (k5_relat_1 @ sk_C @ sk_D))),
% 5.47/5.65      inference('demod', [status(thm)], ['21', '22'])).
% 5.47/5.65  thf('24', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))),
% 5.47/5.65      inference('demod', [status(thm)], ['14', '23'])).
% 5.47/5.65  thf(t45_relat_1, axiom,
% 5.47/5.65    (![A:$i]:
% 5.47/5.65     ( ( v1_relat_1 @ A ) =>
% 5.47/5.65       ( ![B:$i]:
% 5.47/5.65         ( ( v1_relat_1 @ B ) =>
% 5.47/5.65           ( r1_tarski @
% 5.47/5.65             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 5.47/5.65  thf('25', plain,
% 5.47/5.65      (![X19 : $i, X20 : $i]:
% 5.47/5.65         (~ (v1_relat_1 @ X19)
% 5.47/5.65          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X20 @ X19)) @ 
% 5.47/5.65             (k2_relat_1 @ X19))
% 5.47/5.65          | ~ (v1_relat_1 @ X20))),
% 5.47/5.65      inference('cnf', [status(esa)], [t45_relat_1])).
% 5.47/5.65  thf(d19_relat_1, axiom,
% 5.47/5.65    (![A:$i,B:$i]:
% 5.47/5.65     ( ( v1_relat_1 @ B ) =>
% 5.47/5.65       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 5.47/5.65  thf('26', plain,
% 5.47/5.65      (![X15 : $i, X16 : $i]:
% 5.47/5.65         (~ (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 5.47/5.65          | (v5_relat_1 @ X15 @ X16)
% 5.47/5.65          | ~ (v1_relat_1 @ X15))),
% 5.47/5.65      inference('cnf', [status(esa)], [d19_relat_1])).
% 5.47/5.65  thf('27', plain,
% 5.47/5.65      (![X0 : $i, X1 : $i]:
% 5.47/5.65         (~ (v1_relat_1 @ X1)
% 5.47/5.65          | ~ (v1_relat_1 @ X0)
% 5.47/5.65          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 5.47/5.65          | (v5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 5.47/5.65      inference('sup-', [status(thm)], ['25', '26'])).
% 5.47/5.65  thf('28', plain,
% 5.47/5.65      (((v5_relat_1 @ (k5_relat_1 @ sk_C @ sk_D) @ (k2_relat_1 @ sk_D))
% 5.47/5.65        | ~ (v1_relat_1 @ sk_D)
% 5.47/5.65        | ~ (v1_relat_1 @ sk_C))),
% 5.47/5.65      inference('sup-', [status(thm)], ['24', '27'])).
% 5.47/5.65  thf('29', plain,
% 5.47/5.65      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 5.47/5.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.47/5.65  thf('30', plain,
% 5.47/5.65      (![X13 : $i, X14 : $i]:
% 5.47/5.65         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 5.47/5.65          | (v1_relat_1 @ X13)
% 5.47/5.65          | ~ (v1_relat_1 @ X14))),
% 5.47/5.65      inference('cnf', [status(esa)], [cc2_relat_1])).
% 5.47/5.65  thf('31', plain,
% 5.47/5.65      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 5.47/5.65      inference('sup-', [status(thm)], ['29', '30'])).
% 5.47/5.65  thf('32', plain,
% 5.47/5.65      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 5.47/5.65      inference('cnf', [status(esa)], [fc6_relat_1])).
% 5.47/5.65  thf('33', plain, ((v1_relat_1 @ sk_D)),
% 5.47/5.65      inference('demod', [status(thm)], ['31', '32'])).
% 5.47/5.65  thf('34', plain,
% 5.47/5.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.47/5.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.47/5.65  thf('35', plain,
% 5.47/5.65      (![X13 : $i, X14 : $i]:
% 5.47/5.65         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 5.47/5.65          | (v1_relat_1 @ X13)
% 5.47/5.65          | ~ (v1_relat_1 @ X14))),
% 5.47/5.65      inference('cnf', [status(esa)], [cc2_relat_1])).
% 5.47/5.65  thf('36', plain,
% 5.47/5.65      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 5.47/5.65      inference('sup-', [status(thm)], ['34', '35'])).
% 5.47/5.65  thf('37', plain,
% 5.47/5.65      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 5.47/5.65      inference('cnf', [status(esa)], [fc6_relat_1])).
% 5.47/5.65  thf('38', plain, ((v1_relat_1 @ sk_C)),
% 5.47/5.65      inference('demod', [status(thm)], ['36', '37'])).
% 5.47/5.65  thf('39', plain,
% 5.47/5.65      ((v5_relat_1 @ (k5_relat_1 @ sk_C @ sk_D) @ (k2_relat_1 @ sk_D))),
% 5.47/5.65      inference('demod', [status(thm)], ['28', '33', '38'])).
% 5.47/5.65  thf('40', plain,
% 5.47/5.65      (![X15 : $i, X16 : $i]:
% 5.47/5.65         (~ (v5_relat_1 @ X15 @ X16)
% 5.47/5.65          | (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 5.47/5.65          | ~ (v1_relat_1 @ X15))),
% 5.47/5.65      inference('cnf', [status(esa)], [d19_relat_1])).
% 5.47/5.65  thf('41', plain,
% 5.47/5.65      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 5.47/5.65        | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ 
% 5.47/5.65           (k2_relat_1 @ sk_D)))),
% 5.47/5.65      inference('sup-', [status(thm)], ['39', '40'])).
% 5.47/5.65  thf('42', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))),
% 5.47/5.65      inference('demod', [status(thm)], ['14', '23'])).
% 5.47/5.65  thf('43', plain,
% 5.47/5.65      ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ 
% 5.47/5.65        (k2_relat_1 @ sk_D))),
% 5.47/5.65      inference('demod', [status(thm)], ['41', '42'])).
% 5.47/5.65  thf(d10_xboole_0, axiom,
% 5.47/5.65    (![A:$i,B:$i]:
% 5.47/5.65     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.47/5.65  thf('44', plain,
% 5.47/5.65      (![X1 : $i, X3 : $i]:
% 5.47/5.65         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 5.47/5.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.47/5.65  thf('45', plain,
% 5.47/5.65      ((~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 5.47/5.65           (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 5.47/5.65        | ((k2_relat_1 @ sk_D) = (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))))),
% 5.47/5.65      inference('sup-', [status(thm)], ['43', '44'])).
% 5.47/5.65  thf('46', plain,
% 5.47/5.65      ((r2_relset_1 @ sk_A @ sk_A @ 
% 5.47/5.65        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 5.47/5.65        (k6_partfun1 @ sk_A))),
% 5.47/5.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.47/5.65  thf('47', plain,
% 5.47/5.65      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 5.47/5.65         = (k5_relat_1 @ sk_C @ sk_D))),
% 5.47/5.65      inference('demod', [status(thm)], ['21', '22'])).
% 5.47/5.65  thf('48', plain,
% 5.47/5.65      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 5.47/5.65        (k6_partfun1 @ sk_A))),
% 5.47/5.65      inference('demod', [status(thm)], ['46', '47'])).
% 5.47/5.65  thf('49', plain,
% 5.47/5.65      ((m1_subset_1 @ 
% 5.47/5.65        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 5.47/5.65        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.47/5.65      inference('demod', [status(thm)], ['8', '9'])).
% 5.47/5.65  thf('50', plain,
% 5.47/5.65      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 5.47/5.65         = (k5_relat_1 @ sk_C @ sk_D))),
% 5.47/5.65      inference('demod', [status(thm)], ['21', '22'])).
% 5.47/5.65  thf('51', plain,
% 5.47/5.65      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 5.47/5.65        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.47/5.65      inference('demod', [status(thm)], ['49', '50'])).
% 5.47/5.65  thf(redefinition_r2_relset_1, axiom,
% 5.47/5.65    (![A:$i,B:$i,C:$i,D:$i]:
% 5.47/5.65     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.47/5.65         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.47/5.65       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 5.47/5.65  thf('52', plain,
% 5.47/5.65      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 5.47/5.65         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 5.47/5.65          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 5.47/5.65          | ((X28) = (X31))
% 5.47/5.65          | ~ (r2_relset_1 @ X29 @ X30 @ X28 @ X31))),
% 5.47/5.65      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 5.47/5.65  thf('53', plain,
% 5.47/5.65      (![X0 : $i]:
% 5.47/5.65         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 5.47/5.65          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 5.47/5.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 5.47/5.65      inference('sup-', [status(thm)], ['51', '52'])).
% 5.47/5.65  thf('54', plain,
% 5.47/5.65      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 5.47/5.65           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 5.47/5.65        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 5.47/5.65      inference('sup-', [status(thm)], ['48', '53'])).
% 5.47/5.65  thf(dt_k6_partfun1, axiom,
% 5.47/5.65    (![A:$i]:
% 5.47/5.65     ( ( m1_subset_1 @
% 5.47/5.65         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 5.47/5.65       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 5.47/5.65  thf('55', plain,
% 5.47/5.65      (![X41 : $i]:
% 5.47/5.65         (m1_subset_1 @ (k6_partfun1 @ X41) @ 
% 5.47/5.65          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))),
% 5.47/5.65      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 5.47/5.65  thf('56', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 5.47/5.65      inference('demod', [status(thm)], ['54', '55'])).
% 5.47/5.65  thf(t71_relat_1, axiom,
% 5.47/5.65    (![A:$i]:
% 5.47/5.65     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 5.47/5.65       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 5.47/5.65  thf('57', plain, (![X22 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 5.47/5.65      inference('cnf', [status(esa)], [t71_relat_1])).
% 5.47/5.65  thf(redefinition_k6_partfun1, axiom,
% 5.47/5.65    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 5.47/5.65  thf('58', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 5.47/5.65      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.47/5.65  thf('59', plain, (![X22 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X22)) = (X22))),
% 5.47/5.65      inference('demod', [status(thm)], ['57', '58'])).
% 5.47/5.65  thf('60', plain,
% 5.47/5.65      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 5.47/5.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.47/5.65  thf(cc2_relset_1, axiom,
% 5.47/5.65    (![A:$i,B:$i,C:$i]:
% 5.47/5.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.47/5.65       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 5.47/5.65  thf('61', plain,
% 5.47/5.65      (![X25 : $i, X26 : $i, X27 : $i]:
% 5.47/5.65         ((v5_relat_1 @ X25 @ X27)
% 5.47/5.65          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 5.47/5.65      inference('cnf', [status(esa)], [cc2_relset_1])).
% 5.47/5.65  thf('62', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 5.47/5.65      inference('sup-', [status(thm)], ['60', '61'])).
% 5.47/5.65  thf('63', plain,
% 5.47/5.65      (![X15 : $i, X16 : $i]:
% 5.47/5.65         (~ (v5_relat_1 @ X15 @ X16)
% 5.47/5.65          | (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 5.47/5.65          | ~ (v1_relat_1 @ X15))),
% 5.47/5.65      inference('cnf', [status(esa)], [d19_relat_1])).
% 5.47/5.65  thf('64', plain,
% 5.47/5.65      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 5.47/5.65      inference('sup-', [status(thm)], ['62', '63'])).
% 5.47/5.65  thf('65', plain, ((v1_relat_1 @ sk_D)),
% 5.47/5.65      inference('demod', [status(thm)], ['31', '32'])).
% 5.47/5.65  thf('66', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 5.47/5.65      inference('demod', [status(thm)], ['64', '65'])).
% 5.47/5.65  thf('67', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 5.47/5.65      inference('demod', [status(thm)], ['54', '55'])).
% 5.47/5.65  thf('68', plain, (![X22 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X22)) = (X22))),
% 5.47/5.65      inference('demod', [status(thm)], ['57', '58'])).
% 5.47/5.65  thf('69', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 5.47/5.65      inference('demod', [status(thm)], ['45', '56', '59', '66', '67', '68'])).
% 5.47/5.65  thf('70', plain,
% 5.47/5.65      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 5.47/5.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.47/5.65  thf('71', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 5.47/5.65      inference('simplify', [status(thm)], ['70'])).
% 5.47/5.65  thf('72', plain,
% 5.47/5.65      (![X15 : $i, X16 : $i]:
% 5.47/5.65         (~ (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 5.47/5.65          | (v5_relat_1 @ X15 @ X16)
% 5.47/5.65          | ~ (v1_relat_1 @ X15))),
% 5.47/5.65      inference('cnf', [status(esa)], [d19_relat_1])).
% 5.47/5.65  thf('73', plain,
% 5.47/5.65      (![X0 : $i]:
% 5.47/5.65         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 5.47/5.65      inference('sup-', [status(thm)], ['71', '72'])).
% 5.47/5.65  thf(d3_funct_2, axiom,
% 5.47/5.65    (![A:$i,B:$i]:
% 5.47/5.65     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 5.47/5.65       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 5.47/5.65  thf('74', plain,
% 5.47/5.65      (![X32 : $i, X33 : $i]:
% 5.47/5.65         (((k2_relat_1 @ X33) != (X32))
% 5.47/5.65          | (v2_funct_2 @ X33 @ X32)
% 5.47/5.65          | ~ (v5_relat_1 @ X33 @ X32)
% 5.47/5.65          | ~ (v1_relat_1 @ X33))),
% 5.47/5.65      inference('cnf', [status(esa)], [d3_funct_2])).
% 5.47/5.65  thf('75', plain,
% 5.47/5.65      (![X33 : $i]:
% 5.47/5.65         (~ (v1_relat_1 @ X33)
% 5.47/5.65          | ~ (v5_relat_1 @ X33 @ (k2_relat_1 @ X33))
% 5.47/5.65          | (v2_funct_2 @ X33 @ (k2_relat_1 @ X33)))),
% 5.47/5.65      inference('simplify', [status(thm)], ['74'])).
% 5.47/5.65  thf('76', plain,
% 5.47/5.65      (![X0 : $i]:
% 5.47/5.65         (~ (v1_relat_1 @ X0)
% 5.47/5.65          | (v2_funct_2 @ X0 @ (k2_relat_1 @ X0))
% 5.47/5.65          | ~ (v1_relat_1 @ X0))),
% 5.47/5.65      inference('sup-', [status(thm)], ['73', '75'])).
% 5.47/5.65  thf('77', plain,
% 5.47/5.65      (![X0 : $i]:
% 5.47/5.65         ((v2_funct_2 @ X0 @ (k2_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 5.47/5.65      inference('simplify', [status(thm)], ['76'])).
% 5.47/5.65  thf('78', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 5.47/5.65      inference('sup+', [status(thm)], ['69', '77'])).
% 5.47/5.65  thf('79', plain, ((v1_relat_1 @ sk_D)),
% 5.47/5.65      inference('demod', [status(thm)], ['31', '32'])).
% 5.47/5.65  thf('80', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 5.47/5.65      inference('demod', [status(thm)], ['78', '79'])).
% 5.47/5.65  thf('81', plain, (($false) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 5.47/5.65      inference('demod', [status(thm)], ['1', '80'])).
% 5.47/5.65  thf(l13_xboole_0, axiom,
% 5.47/5.65    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 5.47/5.65  thf('82', plain,
% 5.47/5.65      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 5.47/5.65      inference('cnf', [status(esa)], [l13_xboole_0])).
% 5.47/5.65  thf(t113_zfmisc_1, axiom,
% 5.47/5.65    (![A:$i,B:$i]:
% 5.47/5.65     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 5.47/5.65       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 5.47/5.65  thf('83', plain,
% 5.47/5.65      (![X9 : $i, X10 : $i]:
% 5.47/5.65         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X10) != (k1_xboole_0)))),
% 5.47/5.65      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 5.47/5.65  thf('84', plain,
% 5.47/5.65      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 5.47/5.65      inference('simplify', [status(thm)], ['83'])).
% 5.47/5.65  thf('85', plain,
% 5.47/5.65      (![X41 : $i]:
% 5.47/5.65         (m1_subset_1 @ (k6_partfun1 @ X41) @ 
% 5.47/5.65          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))),
% 5.47/5.65      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 5.47/5.65  thf('86', plain,
% 5.47/5.65      ((m1_subset_1 @ (k6_partfun1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 5.47/5.65      inference('sup+', [status(thm)], ['84', '85'])).
% 5.47/5.65  thf(cc1_subset_1, axiom,
% 5.47/5.65    (![A:$i]:
% 5.47/5.65     ( ( v1_xboole_0 @ A ) =>
% 5.47/5.65       ( ![B:$i]:
% 5.47/5.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 5.47/5.65  thf('87', plain,
% 5.47/5.65      (![X11 : $i, X12 : $i]:
% 5.47/5.65         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 5.47/5.65          | (v1_xboole_0 @ X11)
% 5.47/5.65          | ~ (v1_xboole_0 @ X12))),
% 5.47/5.65      inference('cnf', [status(esa)], [cc1_subset_1])).
% 5.47/5.65  thf('88', plain,
% 5.47/5.65      ((~ (v1_xboole_0 @ k1_xboole_0)
% 5.47/5.65        | (v1_xboole_0 @ (k6_partfun1 @ k1_xboole_0)))),
% 5.47/5.65      inference('sup-', [status(thm)], ['86', '87'])).
% 5.47/5.65  thf('89', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 5.47/5.65      inference('simplify', [status(thm)], ['70'])).
% 5.47/5.65  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 5.47/5.65  thf('90', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 5.47/5.65      inference('cnf', [status(esa)], [t65_xboole_1])).
% 5.47/5.65  thf(t69_xboole_1, axiom,
% 5.47/5.65    (![A:$i,B:$i]:
% 5.47/5.65     ( ( ~( v1_xboole_0 @ B ) ) =>
% 5.47/5.65       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 5.47/5.65  thf('91', plain,
% 5.47/5.65      (![X6 : $i, X7 : $i]:
% 5.47/5.65         (~ (r1_xboole_0 @ X6 @ X7)
% 5.47/5.65          | ~ (r1_tarski @ X6 @ X7)
% 5.47/5.65          | (v1_xboole_0 @ X6))),
% 5.47/5.65      inference('cnf', [status(esa)], [t69_xboole_1])).
% 5.47/5.65  thf('92', plain,
% 5.47/5.65      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 5.47/5.65      inference('sup-', [status(thm)], ['90', '91'])).
% 5.47/5.65  thf('93', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.47/5.65      inference('sup-', [status(thm)], ['89', '92'])).
% 5.47/5.65  thf('94', plain, ((v1_xboole_0 @ (k6_partfun1 @ k1_xboole_0))),
% 5.47/5.65      inference('demod', [status(thm)], ['88', '93'])).
% 5.47/5.65  thf('95', plain,
% 5.47/5.65      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 5.47/5.65      inference('cnf', [status(esa)], [l13_xboole_0])).
% 5.47/5.65  thf('96', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 5.47/5.65      inference('sup-', [status(thm)], ['94', '95'])).
% 5.47/5.65  thf(fc4_funct_1, axiom,
% 5.47/5.65    (![A:$i]:
% 5.47/5.65     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 5.47/5.65       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 5.47/5.65  thf('97', plain, (![X24 : $i]: (v2_funct_1 @ (k6_relat_1 @ X24))),
% 5.47/5.65      inference('cnf', [status(esa)], [fc4_funct_1])).
% 5.47/5.65  thf('98', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 5.47/5.65      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.47/5.65  thf('99', plain, (![X24 : $i]: (v2_funct_1 @ (k6_partfun1 @ X24))),
% 5.47/5.65      inference('demod', [status(thm)], ['97', '98'])).
% 5.47/5.65  thf('100', plain, ((v2_funct_1 @ k1_xboole_0)),
% 5.47/5.65      inference('sup+', [status(thm)], ['96', '99'])).
% 5.47/5.65  thf('101', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 5.47/5.65      inference('sup+', [status(thm)], ['82', '100'])).
% 5.47/5.65  thf('102', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 5.47/5.65      inference('split', [status(esa)], ['0'])).
% 5.47/5.65  thf('103', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 5.47/5.65      inference('sup-', [status(thm)], ['101', '102'])).
% 5.47/5.65  thf('104', plain,
% 5.47/5.65      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 5.47/5.65         = (k5_relat_1 @ sk_C @ sk_D))),
% 5.47/5.65      inference('demod', [status(thm)], ['21', '22'])).
% 5.47/5.65  thf('105', plain,
% 5.47/5.65      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 5.47/5.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.47/5.65  thf(t26_funct_2, axiom,
% 5.47/5.65    (![A:$i,B:$i,C:$i,D:$i]:
% 5.47/5.65     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 5.47/5.65         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.47/5.65       ( ![E:$i]:
% 5.47/5.65         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 5.47/5.65             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 5.47/5.65           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 5.47/5.65             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 5.47/5.65               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 5.47/5.65  thf('106', plain,
% 5.47/5.65      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 5.47/5.65         (~ (v1_funct_1 @ X49)
% 5.47/5.65          | ~ (v1_funct_2 @ X49 @ X50 @ X51)
% 5.47/5.65          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 5.47/5.65          | ~ (v2_funct_1 @ (k1_partfun1 @ X52 @ X50 @ X50 @ X51 @ X53 @ X49))
% 5.47/5.65          | (v2_funct_1 @ X53)
% 5.47/5.65          | ((X51) = (k1_xboole_0))
% 5.47/5.65          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 5.47/5.65          | ~ (v1_funct_2 @ X53 @ X52 @ X50)
% 5.47/5.65          | ~ (v1_funct_1 @ X53))),
% 5.47/5.65      inference('cnf', [status(esa)], [t26_funct_2])).
% 5.47/5.65  thf('107', plain,
% 5.47/5.65      (![X0 : $i, X1 : $i]:
% 5.47/5.65         (~ (v1_funct_1 @ X0)
% 5.47/5.65          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 5.47/5.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 5.47/5.65          | ((sk_A) = (k1_xboole_0))
% 5.47/5.65          | (v2_funct_1 @ X0)
% 5.47/5.65          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 5.47/5.65          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 5.47/5.65          | ~ (v1_funct_1 @ sk_D))),
% 5.47/5.65      inference('sup-', [status(thm)], ['105', '106'])).
% 5.47/5.65  thf('108', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 5.47/5.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.47/5.65  thf('109', plain, ((v1_funct_1 @ sk_D)),
% 5.47/5.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.47/5.65  thf('110', plain,
% 5.47/5.65      (![X0 : $i, X1 : $i]:
% 5.47/5.65         (~ (v1_funct_1 @ X0)
% 5.47/5.65          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 5.47/5.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 5.47/5.65          | ((sk_A) = (k1_xboole_0))
% 5.47/5.65          | (v2_funct_1 @ X0)
% 5.47/5.65          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 5.47/5.65      inference('demod', [status(thm)], ['107', '108', '109'])).
% 5.47/5.65  thf('111', plain,
% 5.47/5.65      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 5.47/5.65        | (v2_funct_1 @ sk_C)
% 5.47/5.65        | ((sk_A) = (k1_xboole_0))
% 5.47/5.65        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 5.47/5.65        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 5.47/5.65        | ~ (v1_funct_1 @ sk_C))),
% 5.47/5.65      inference('sup-', [status(thm)], ['104', '110'])).
% 5.47/5.65  thf('112', plain,
% 5.47/5.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.47/5.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.47/5.65  thf('113', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 5.47/5.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.47/5.65  thf('114', plain, ((v1_funct_1 @ sk_C)),
% 5.47/5.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.47/5.65  thf('115', plain,
% 5.47/5.65      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 5.47/5.65        | (v2_funct_1 @ sk_C)
% 5.47/5.65        | ((sk_A) = (k1_xboole_0)))),
% 5.47/5.65      inference('demod', [status(thm)], ['111', '112', '113', '114'])).
% 5.47/5.65  thf('116', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 5.47/5.65      inference('demod', [status(thm)], ['54', '55'])).
% 5.47/5.65  thf('117', plain, (![X24 : $i]: (v2_funct_1 @ (k6_partfun1 @ X24))),
% 5.47/5.65      inference('demod', [status(thm)], ['97', '98'])).
% 5.47/5.65  thf('118', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 5.47/5.65      inference('demod', [status(thm)], ['115', '116', '117'])).
% 5.47/5.65  thf('119', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 5.47/5.65      inference('split', [status(esa)], ['0'])).
% 5.47/5.65  thf('120', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 5.47/5.65      inference('sup-', [status(thm)], ['118', '119'])).
% 5.47/5.65  thf('121', plain,
% 5.47/5.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.47/5.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.47/5.65  thf('122', plain,
% 5.47/5.65      (![X11 : $i, X12 : $i]:
% 5.47/5.65         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 5.47/5.65          | (v1_xboole_0 @ X11)
% 5.47/5.65          | ~ (v1_xboole_0 @ X12))),
% 5.47/5.65      inference('cnf', [status(esa)], [cc1_subset_1])).
% 5.47/5.65  thf('123', plain,
% 5.47/5.65      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 5.47/5.65      inference('sup-', [status(thm)], ['121', '122'])).
% 5.47/5.65  thf('124', plain,
% 5.47/5.65      (((~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))
% 5.47/5.65         | (v1_xboole_0 @ sk_C))) <= (~ ((v2_funct_1 @ sk_C)))),
% 5.47/5.65      inference('sup-', [status(thm)], ['120', '123'])).
% 5.47/5.65  thf('125', plain,
% 5.47/5.65      (![X9 : $i, X10 : $i]:
% 5.47/5.65         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 5.47/5.65      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 5.47/5.65  thf('126', plain,
% 5.47/5.65      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 5.47/5.65      inference('simplify', [status(thm)], ['125'])).
% 5.47/5.65  thf('127', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.47/5.65      inference('sup-', [status(thm)], ['89', '92'])).
% 5.47/5.65  thf('128', plain, (((v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 5.47/5.65      inference('demod', [status(thm)], ['124', '126', '127'])).
% 5.47/5.65  thf('129', plain, (((v2_funct_1 @ sk_C))),
% 5.47/5.65      inference('demod', [status(thm)], ['103', '128'])).
% 5.47/5.65  thf('130', plain, (~ ((v2_funct_2 @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_C))),
% 5.47/5.65      inference('split', [status(esa)], ['0'])).
% 5.47/5.65  thf('131', plain, (~ ((v2_funct_2 @ sk_D @ sk_A))),
% 5.47/5.65      inference('sat_resolution*', [status(thm)], ['129', '130'])).
% 5.47/5.65  thf('132', plain, ($false),
% 5.47/5.65      inference('simpl_trail', [status(thm)], ['81', '131'])).
% 5.47/5.65  
% 5.47/5.65  % SZS output end Refutation
% 5.47/5.65  
% 5.47/5.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rJHjJe0gta

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:25 EST 2020

% Result     : Theorem 6.86s
% Output     : Refutation 6.86s
% Verified   : 
% Statistics : Number of formulae       :  183 (1286 expanded)
%              Number of leaves         :   43 ( 381 expanded)
%              Depth                    :   23
%              Number of atoms          : 1383 (25218 expanded)
%              Number of equality atoms :   62 ( 323 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X38 ) ) ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
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
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( ( k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42 )
        = ( k5_relat_1 @ X39 @ X42 ) ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X18 @ X17 ) ) @ ( k2_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('26',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ( v5_relat_1 @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('33',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('38',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    v5_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['28','33','38'])).

thf('40',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v5_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
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
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( X26 = X29 )
      | ~ ( r2_relset_1 @ X27 @ X28 @ X26 @ X29 ) ) ),
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
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('56',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('57',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
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
    ! [X20: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('60',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('61',plain,(
    ! [X20: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X20 ) )
      = X20 ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v5_relat_1 @ X23 @ X25 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('64',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v5_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
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
    ! [X20: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X20 ) )
      = X20 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('71',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['45','58','61','68','69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('73',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ( v5_relat_1 @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
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
    ! [X31: $i,X32: $i] :
      ( ( ( k2_relat_1 @ X32 )
       != X31 )
      | ( v2_funct_2 @ X32 @ X31 )
      | ~ ( v5_relat_1 @ X32 @ X31 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('77',plain,(
    ! [X32: $i] :
      ( ~ ( v1_relat_1 @ X32 )
      | ~ ( v5_relat_1 @ X32 @ ( k2_relat_1 @ X32 ) )
      | ( v2_funct_2 @ X32 @ ( k2_relat_1 @ X32 ) ) ) ),
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
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('86',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('89',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('90',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('92',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('94',plain,(
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

thf('95',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X49 @ X47 @ X47 @ X48 @ X50 @ X46 ) )
      | ( v2_funct_1 @ X50 )
      | ( X48 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X47 ) ) )
      | ~ ( v1_funct_2 @ X50 @ X49 @ X47 )
      | ~ ( v1_funct_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['93','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['100','101','102','103'])).

thf('105',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['54','57'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('106',plain,(
    ! [X22: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('107',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('108',plain,(
    ! [X22: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X22 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['104','105','108'])).

thf('110',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','86'])).

thf('111',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['109','110'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('112',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('113',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['112'])).

thf('115',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('116',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('117',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v5_relat_1 @ X23 @ X25 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( v5_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['114','119'])).

thf('121',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v5_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('123',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('124',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('125',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('127',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('128',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X21 ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['125','128'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('130',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('131',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['122','129','130'])).

thf('132',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['109','110'])).

thf('133',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['112'])).

thf('134',plain,(
    k1_xboole_0 = sk_C ),
    inference(demod,[status(thm)],['92','111','113','131','132','133'])).

thf('135',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['123','124'])).

thf('136',plain,(
    ! [X22: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X22 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('137',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,(
    $false ),
    inference(demod,[status(thm)],['87','134','137'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rJHjJe0gta
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:07:35 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 6.86/7.07  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.86/7.07  % Solved by: fo/fo7.sh
% 6.86/7.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.86/7.07  % done 8806 iterations in 6.619s
% 6.86/7.07  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.86/7.07  % SZS output start Refutation
% 6.86/7.07  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 6.86/7.07  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 6.86/7.07  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 6.86/7.07  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.86/7.07  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 6.86/7.07  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.86/7.07  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 6.86/7.07  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.86/7.07  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 6.86/7.07  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 6.86/7.07  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 6.86/7.07  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 6.86/7.07  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.86/7.07  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.86/7.07  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 6.86/7.07  thf(sk_C_type, type, sk_C: $i).
% 6.86/7.07  thf(sk_D_type, type, sk_D: $i).
% 6.86/7.07  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.86/7.07  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 6.86/7.07  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 6.86/7.07  thf(sk_B_type, type, sk_B: $i).
% 6.86/7.07  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 6.86/7.07  thf(sk_A_type, type, sk_A: $i).
% 6.86/7.07  thf(t29_funct_2, conjecture,
% 6.86/7.07    (![A:$i,B:$i,C:$i]:
% 6.86/7.07     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.86/7.07         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.86/7.07       ( ![D:$i]:
% 6.86/7.07         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 6.86/7.07             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 6.86/7.07           ( ( r2_relset_1 @
% 6.86/7.07               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 6.86/7.07               ( k6_partfun1 @ A ) ) =>
% 6.86/7.07             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 6.86/7.07  thf(zf_stmt_0, negated_conjecture,
% 6.86/7.07    (~( ![A:$i,B:$i,C:$i]:
% 6.86/7.07        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.86/7.07            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.86/7.07          ( ![D:$i]:
% 6.86/7.07            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 6.86/7.07                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 6.86/7.07              ( ( r2_relset_1 @
% 6.86/7.07                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 6.86/7.07                  ( k6_partfun1 @ A ) ) =>
% 6.86/7.07                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 6.86/7.07    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 6.86/7.07  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 6.86/7.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.86/7.07  thf('1', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 6.86/7.07      inference('split', [status(esa)], ['0'])).
% 6.86/7.07  thf('2', plain,
% 6.86/7.07      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 6.86/7.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.86/7.07  thf('3', plain,
% 6.86/7.07      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.86/7.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.86/7.07  thf(dt_k1_partfun1, axiom,
% 6.86/7.07    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 6.86/7.07     ( ( ( v1_funct_1 @ E ) & 
% 6.86/7.07         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.86/7.07         ( v1_funct_1 @ F ) & 
% 6.86/7.07         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 6.86/7.07       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 6.86/7.07         ( m1_subset_1 @
% 6.86/7.07           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 6.86/7.07           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 6.86/7.07  thf('4', plain,
% 6.86/7.07      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 6.86/7.07         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 6.86/7.07          | ~ (v1_funct_1 @ X33)
% 6.86/7.07          | ~ (v1_funct_1 @ X36)
% 6.86/7.07          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 6.86/7.07          | (m1_subset_1 @ (k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36) @ 
% 6.86/7.07             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X38))))),
% 6.86/7.07      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 6.86/7.07  thf('5', plain,
% 6.86/7.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.86/7.07         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 6.86/7.07           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 6.86/7.07          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 6.86/7.07          | ~ (v1_funct_1 @ X1)
% 6.86/7.07          | ~ (v1_funct_1 @ sk_C))),
% 6.86/7.07      inference('sup-', [status(thm)], ['3', '4'])).
% 6.86/7.07  thf('6', plain, ((v1_funct_1 @ sk_C)),
% 6.86/7.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.86/7.07  thf('7', plain,
% 6.86/7.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.86/7.07         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 6.86/7.07           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 6.86/7.07          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 6.86/7.07          | ~ (v1_funct_1 @ X1))),
% 6.86/7.07      inference('demod', [status(thm)], ['5', '6'])).
% 6.86/7.07  thf('8', plain,
% 6.86/7.07      ((~ (v1_funct_1 @ sk_D)
% 6.86/7.07        | (m1_subset_1 @ 
% 6.86/7.07           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 6.86/7.07           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 6.86/7.07      inference('sup-', [status(thm)], ['2', '7'])).
% 6.86/7.07  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 6.86/7.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.86/7.07  thf('10', plain,
% 6.86/7.07      ((m1_subset_1 @ 
% 6.86/7.07        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 6.86/7.07        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.86/7.07      inference('demod', [status(thm)], ['8', '9'])).
% 6.86/7.07  thf(cc2_relat_1, axiom,
% 6.86/7.07    (![A:$i]:
% 6.86/7.07     ( ( v1_relat_1 @ A ) =>
% 6.86/7.07       ( ![B:$i]:
% 6.86/7.07         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 6.86/7.07  thf('11', plain,
% 6.86/7.07      (![X11 : $i, X12 : $i]:
% 6.86/7.07         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 6.86/7.07          | (v1_relat_1 @ X11)
% 6.86/7.07          | ~ (v1_relat_1 @ X12))),
% 6.86/7.07      inference('cnf', [status(esa)], [cc2_relat_1])).
% 6.86/7.07  thf('12', plain,
% 6.86/7.07      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 6.86/7.07        | (v1_relat_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)))),
% 6.86/7.07      inference('sup-', [status(thm)], ['10', '11'])).
% 6.86/7.07  thf(fc6_relat_1, axiom,
% 6.86/7.07    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 6.86/7.07  thf('13', plain,
% 6.86/7.07      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X15 @ X16))),
% 6.86/7.07      inference('cnf', [status(esa)], [fc6_relat_1])).
% 6.86/7.07  thf('14', plain,
% 6.86/7.07      ((v1_relat_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D))),
% 6.86/7.07      inference('demod', [status(thm)], ['12', '13'])).
% 6.86/7.07  thf('15', plain,
% 6.86/7.07      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 6.86/7.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.86/7.07  thf('16', plain,
% 6.86/7.07      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.86/7.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.86/7.07  thf(redefinition_k1_partfun1, axiom,
% 6.86/7.07    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 6.86/7.07     ( ( ( v1_funct_1 @ E ) & 
% 6.86/7.07         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.86/7.07         ( v1_funct_1 @ F ) & 
% 6.86/7.07         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 6.86/7.07       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 6.86/7.07  thf('17', plain,
% 6.86/7.07      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 6.86/7.07         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 6.86/7.07          | ~ (v1_funct_1 @ X39)
% 6.86/7.07          | ~ (v1_funct_1 @ X42)
% 6.86/7.07          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 6.86/7.07          | ((k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42)
% 6.86/7.07              = (k5_relat_1 @ X39 @ X42)))),
% 6.86/7.07      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 6.86/7.07  thf('18', plain,
% 6.86/7.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.86/7.07         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 6.86/7.07            = (k5_relat_1 @ sk_C @ X0))
% 6.86/7.07          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 6.86/7.07          | ~ (v1_funct_1 @ X0)
% 6.86/7.07          | ~ (v1_funct_1 @ sk_C))),
% 6.86/7.07      inference('sup-', [status(thm)], ['16', '17'])).
% 6.86/7.07  thf('19', plain, ((v1_funct_1 @ sk_C)),
% 6.86/7.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.86/7.07  thf('20', plain,
% 6.86/7.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.86/7.07         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 6.86/7.07            = (k5_relat_1 @ sk_C @ X0))
% 6.86/7.07          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 6.86/7.07          | ~ (v1_funct_1 @ X0))),
% 6.86/7.07      inference('demod', [status(thm)], ['18', '19'])).
% 6.86/7.07  thf('21', plain,
% 6.86/7.07      ((~ (v1_funct_1 @ sk_D)
% 6.86/7.07        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 6.86/7.07            = (k5_relat_1 @ sk_C @ sk_D)))),
% 6.86/7.07      inference('sup-', [status(thm)], ['15', '20'])).
% 6.86/7.07  thf('22', plain, ((v1_funct_1 @ sk_D)),
% 6.86/7.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.86/7.07  thf('23', plain,
% 6.86/7.07      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 6.86/7.07         = (k5_relat_1 @ sk_C @ sk_D))),
% 6.86/7.07      inference('demod', [status(thm)], ['21', '22'])).
% 6.86/7.07  thf('24', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))),
% 6.86/7.07      inference('demod', [status(thm)], ['14', '23'])).
% 6.86/7.07  thf(t45_relat_1, axiom,
% 6.86/7.07    (![A:$i]:
% 6.86/7.07     ( ( v1_relat_1 @ A ) =>
% 6.86/7.07       ( ![B:$i]:
% 6.86/7.07         ( ( v1_relat_1 @ B ) =>
% 6.86/7.07           ( r1_tarski @
% 6.86/7.07             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 6.86/7.07  thf('25', plain,
% 6.86/7.07      (![X17 : $i, X18 : $i]:
% 6.86/7.07         (~ (v1_relat_1 @ X17)
% 6.86/7.07          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X18 @ X17)) @ 
% 6.86/7.07             (k2_relat_1 @ X17))
% 6.86/7.07          | ~ (v1_relat_1 @ X18))),
% 6.86/7.07      inference('cnf', [status(esa)], [t45_relat_1])).
% 6.86/7.07  thf(d19_relat_1, axiom,
% 6.86/7.07    (![A:$i,B:$i]:
% 6.86/7.07     ( ( v1_relat_1 @ B ) =>
% 6.86/7.07       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 6.86/7.07  thf('26', plain,
% 6.86/7.07      (![X13 : $i, X14 : $i]:
% 6.86/7.07         (~ (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 6.86/7.07          | (v5_relat_1 @ X13 @ X14)
% 6.86/7.07          | ~ (v1_relat_1 @ X13))),
% 6.86/7.07      inference('cnf', [status(esa)], [d19_relat_1])).
% 6.86/7.07  thf('27', plain,
% 6.86/7.07      (![X0 : $i, X1 : $i]:
% 6.86/7.07         (~ (v1_relat_1 @ X1)
% 6.86/7.07          | ~ (v1_relat_1 @ X0)
% 6.86/7.07          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 6.86/7.07          | (v5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 6.86/7.07      inference('sup-', [status(thm)], ['25', '26'])).
% 6.86/7.07  thf('28', plain,
% 6.86/7.07      (((v5_relat_1 @ (k5_relat_1 @ sk_C @ sk_D) @ (k2_relat_1 @ sk_D))
% 6.86/7.07        | ~ (v1_relat_1 @ sk_D)
% 6.86/7.07        | ~ (v1_relat_1 @ sk_C))),
% 6.86/7.07      inference('sup-', [status(thm)], ['24', '27'])).
% 6.86/7.07  thf('29', plain,
% 6.86/7.07      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 6.86/7.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.86/7.07  thf('30', plain,
% 6.86/7.07      (![X11 : $i, X12 : $i]:
% 6.86/7.07         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 6.86/7.07          | (v1_relat_1 @ X11)
% 6.86/7.07          | ~ (v1_relat_1 @ X12))),
% 6.86/7.07      inference('cnf', [status(esa)], [cc2_relat_1])).
% 6.86/7.07  thf('31', plain,
% 6.86/7.07      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 6.86/7.07      inference('sup-', [status(thm)], ['29', '30'])).
% 6.86/7.07  thf('32', plain,
% 6.86/7.07      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X15 @ X16))),
% 6.86/7.07      inference('cnf', [status(esa)], [fc6_relat_1])).
% 6.86/7.07  thf('33', plain, ((v1_relat_1 @ sk_D)),
% 6.86/7.07      inference('demod', [status(thm)], ['31', '32'])).
% 6.86/7.07  thf('34', plain,
% 6.86/7.07      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.86/7.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.86/7.07  thf('35', plain,
% 6.86/7.07      (![X11 : $i, X12 : $i]:
% 6.86/7.07         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 6.86/7.07          | (v1_relat_1 @ X11)
% 6.86/7.07          | ~ (v1_relat_1 @ X12))),
% 6.86/7.07      inference('cnf', [status(esa)], [cc2_relat_1])).
% 6.86/7.07  thf('36', plain,
% 6.86/7.07      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 6.86/7.07      inference('sup-', [status(thm)], ['34', '35'])).
% 6.86/7.07  thf('37', plain,
% 6.86/7.07      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X15 @ X16))),
% 6.86/7.07      inference('cnf', [status(esa)], [fc6_relat_1])).
% 6.86/7.07  thf('38', plain, ((v1_relat_1 @ sk_C)),
% 6.86/7.07      inference('demod', [status(thm)], ['36', '37'])).
% 6.86/7.07  thf('39', plain,
% 6.86/7.07      ((v5_relat_1 @ (k5_relat_1 @ sk_C @ sk_D) @ (k2_relat_1 @ sk_D))),
% 6.86/7.07      inference('demod', [status(thm)], ['28', '33', '38'])).
% 6.86/7.07  thf('40', plain,
% 6.86/7.07      (![X13 : $i, X14 : $i]:
% 6.86/7.07         (~ (v5_relat_1 @ X13 @ X14)
% 6.86/7.07          | (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 6.86/7.07          | ~ (v1_relat_1 @ X13))),
% 6.86/7.07      inference('cnf', [status(esa)], [d19_relat_1])).
% 6.86/7.07  thf('41', plain,
% 6.86/7.07      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 6.86/7.07        | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ 
% 6.86/7.07           (k2_relat_1 @ sk_D)))),
% 6.86/7.07      inference('sup-', [status(thm)], ['39', '40'])).
% 6.86/7.07  thf('42', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))),
% 6.86/7.07      inference('demod', [status(thm)], ['14', '23'])).
% 6.86/7.07  thf('43', plain,
% 6.86/7.07      ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ 
% 6.86/7.07        (k2_relat_1 @ sk_D))),
% 6.86/7.07      inference('demod', [status(thm)], ['41', '42'])).
% 6.86/7.07  thf(d10_xboole_0, axiom,
% 6.86/7.07    (![A:$i,B:$i]:
% 6.86/7.07     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.86/7.07  thf('44', plain,
% 6.86/7.07      (![X0 : $i, X2 : $i]:
% 6.86/7.07         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 6.86/7.07      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.86/7.07  thf('45', plain,
% 6.86/7.07      ((~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 6.86/7.07           (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 6.86/7.07        | ((k2_relat_1 @ sk_D) = (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))))),
% 6.86/7.07      inference('sup-', [status(thm)], ['43', '44'])).
% 6.86/7.07  thf('46', plain,
% 6.86/7.07      ((r2_relset_1 @ sk_A @ sk_A @ 
% 6.86/7.07        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 6.86/7.07        (k6_partfun1 @ sk_A))),
% 6.86/7.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.86/7.07  thf('47', plain,
% 6.86/7.07      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 6.86/7.07         = (k5_relat_1 @ sk_C @ sk_D))),
% 6.86/7.07      inference('demod', [status(thm)], ['21', '22'])).
% 6.86/7.07  thf('48', plain,
% 6.86/7.07      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 6.86/7.07        (k6_partfun1 @ sk_A))),
% 6.86/7.07      inference('demod', [status(thm)], ['46', '47'])).
% 6.86/7.07  thf('49', plain,
% 6.86/7.07      ((m1_subset_1 @ 
% 6.86/7.07        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 6.86/7.07        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.86/7.07      inference('demod', [status(thm)], ['8', '9'])).
% 6.86/7.07  thf('50', plain,
% 6.86/7.07      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 6.86/7.07         = (k5_relat_1 @ sk_C @ sk_D))),
% 6.86/7.07      inference('demod', [status(thm)], ['21', '22'])).
% 6.86/7.07  thf('51', plain,
% 6.86/7.07      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 6.86/7.07        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.86/7.07      inference('demod', [status(thm)], ['49', '50'])).
% 6.86/7.07  thf(redefinition_r2_relset_1, axiom,
% 6.86/7.07    (![A:$i,B:$i,C:$i,D:$i]:
% 6.86/7.07     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.86/7.07         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.86/7.07       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 6.86/7.07  thf('52', plain,
% 6.86/7.07      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 6.86/7.07         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 6.86/7.07          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 6.86/7.07          | ((X26) = (X29))
% 6.86/7.07          | ~ (r2_relset_1 @ X27 @ X28 @ X26 @ X29))),
% 6.86/7.07      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 6.86/7.07  thf('53', plain,
% 6.86/7.07      (![X0 : $i]:
% 6.86/7.07         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 6.86/7.07          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 6.86/7.07          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 6.86/7.07      inference('sup-', [status(thm)], ['51', '52'])).
% 6.86/7.07  thf('54', plain,
% 6.86/7.07      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 6.86/7.07           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 6.86/7.07        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 6.86/7.07      inference('sup-', [status(thm)], ['48', '53'])).
% 6.86/7.07  thf(t29_relset_1, axiom,
% 6.86/7.07    (![A:$i]:
% 6.86/7.07     ( m1_subset_1 @
% 6.86/7.07       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 6.86/7.07  thf('55', plain,
% 6.86/7.07      (![X30 : $i]:
% 6.86/7.07         (m1_subset_1 @ (k6_relat_1 @ X30) @ 
% 6.86/7.07          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 6.86/7.07      inference('cnf', [status(esa)], [t29_relset_1])).
% 6.86/7.07  thf(redefinition_k6_partfun1, axiom,
% 6.86/7.07    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 6.86/7.07  thf('56', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 6.86/7.07      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 6.86/7.07  thf('57', plain,
% 6.86/7.07      (![X30 : $i]:
% 6.86/7.07         (m1_subset_1 @ (k6_partfun1 @ X30) @ 
% 6.86/7.07          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 6.86/7.07      inference('demod', [status(thm)], ['55', '56'])).
% 6.86/7.07  thf('58', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 6.86/7.07      inference('demod', [status(thm)], ['54', '57'])).
% 6.86/7.07  thf(t71_relat_1, axiom,
% 6.86/7.07    (![A:$i]:
% 6.86/7.07     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 6.86/7.07       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 6.86/7.07  thf('59', plain, (![X20 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 6.86/7.07      inference('cnf', [status(esa)], [t71_relat_1])).
% 6.86/7.07  thf('60', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 6.86/7.07      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 6.86/7.07  thf('61', plain, (![X20 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X20)) = (X20))),
% 6.86/7.07      inference('demod', [status(thm)], ['59', '60'])).
% 6.86/7.07  thf('62', plain,
% 6.86/7.07      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 6.86/7.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.86/7.07  thf(cc2_relset_1, axiom,
% 6.86/7.07    (![A:$i,B:$i,C:$i]:
% 6.86/7.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.86/7.07       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 6.86/7.07  thf('63', plain,
% 6.86/7.07      (![X23 : $i, X24 : $i, X25 : $i]:
% 6.86/7.07         ((v5_relat_1 @ X23 @ X25)
% 6.86/7.07          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 6.86/7.07      inference('cnf', [status(esa)], [cc2_relset_1])).
% 6.86/7.07  thf('64', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 6.86/7.07      inference('sup-', [status(thm)], ['62', '63'])).
% 6.86/7.07  thf('65', plain,
% 6.86/7.07      (![X13 : $i, X14 : $i]:
% 6.86/7.07         (~ (v5_relat_1 @ X13 @ X14)
% 6.86/7.07          | (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 6.86/7.07          | ~ (v1_relat_1 @ X13))),
% 6.86/7.07      inference('cnf', [status(esa)], [d19_relat_1])).
% 6.86/7.07  thf('66', plain,
% 6.86/7.07      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 6.86/7.07      inference('sup-', [status(thm)], ['64', '65'])).
% 6.86/7.07  thf('67', plain, ((v1_relat_1 @ sk_D)),
% 6.86/7.07      inference('demod', [status(thm)], ['31', '32'])).
% 6.86/7.07  thf('68', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 6.86/7.07      inference('demod', [status(thm)], ['66', '67'])).
% 6.86/7.07  thf('69', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 6.86/7.07      inference('demod', [status(thm)], ['54', '57'])).
% 6.86/7.07  thf('70', plain, (![X20 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X20)) = (X20))),
% 6.86/7.07      inference('demod', [status(thm)], ['59', '60'])).
% 6.86/7.07  thf('71', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 6.86/7.07      inference('demod', [status(thm)], ['45', '58', '61', '68', '69', '70'])).
% 6.86/7.07  thf('72', plain,
% 6.86/7.07      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 6.86/7.07      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.86/7.07  thf('73', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 6.86/7.07      inference('simplify', [status(thm)], ['72'])).
% 6.86/7.07  thf('74', plain,
% 6.86/7.07      (![X13 : $i, X14 : $i]:
% 6.86/7.07         (~ (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 6.86/7.07          | (v5_relat_1 @ X13 @ X14)
% 6.86/7.07          | ~ (v1_relat_1 @ X13))),
% 6.86/7.07      inference('cnf', [status(esa)], [d19_relat_1])).
% 6.86/7.07  thf('75', plain,
% 6.86/7.07      (![X0 : $i]:
% 6.86/7.07         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 6.86/7.07      inference('sup-', [status(thm)], ['73', '74'])).
% 6.86/7.07  thf(d3_funct_2, axiom,
% 6.86/7.07    (![A:$i,B:$i]:
% 6.86/7.07     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 6.86/7.07       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 6.86/7.07  thf('76', plain,
% 6.86/7.07      (![X31 : $i, X32 : $i]:
% 6.86/7.07         (((k2_relat_1 @ X32) != (X31))
% 6.86/7.07          | (v2_funct_2 @ X32 @ X31)
% 6.86/7.07          | ~ (v5_relat_1 @ X32 @ X31)
% 6.86/7.07          | ~ (v1_relat_1 @ X32))),
% 6.86/7.07      inference('cnf', [status(esa)], [d3_funct_2])).
% 6.86/7.07  thf('77', plain,
% 6.86/7.07      (![X32 : $i]:
% 6.86/7.07         (~ (v1_relat_1 @ X32)
% 6.86/7.07          | ~ (v5_relat_1 @ X32 @ (k2_relat_1 @ X32))
% 6.86/7.07          | (v2_funct_2 @ X32 @ (k2_relat_1 @ X32)))),
% 6.86/7.07      inference('simplify', [status(thm)], ['76'])).
% 6.86/7.07  thf('78', plain,
% 6.86/7.07      (![X0 : $i]:
% 6.86/7.07         (~ (v1_relat_1 @ X0)
% 6.86/7.07          | (v2_funct_2 @ X0 @ (k2_relat_1 @ X0))
% 6.86/7.07          | ~ (v1_relat_1 @ X0))),
% 6.86/7.07      inference('sup-', [status(thm)], ['75', '77'])).
% 6.86/7.07  thf('79', plain,
% 6.86/7.07      (![X0 : $i]:
% 6.86/7.07         ((v2_funct_2 @ X0 @ (k2_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 6.86/7.07      inference('simplify', [status(thm)], ['78'])).
% 6.86/7.07  thf('80', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 6.86/7.07      inference('sup+', [status(thm)], ['71', '79'])).
% 6.86/7.07  thf('81', plain, ((v1_relat_1 @ sk_D)),
% 6.86/7.07      inference('demod', [status(thm)], ['31', '32'])).
% 6.86/7.07  thf('82', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 6.86/7.07      inference('demod', [status(thm)], ['80', '81'])).
% 6.86/7.07  thf('83', plain,
% 6.86/7.07      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 6.86/7.07      inference('split', [status(esa)], ['0'])).
% 6.86/7.07  thf('84', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 6.86/7.07      inference('sup-', [status(thm)], ['82', '83'])).
% 6.86/7.07  thf('85', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 6.86/7.07      inference('split', [status(esa)], ['0'])).
% 6.86/7.07  thf('86', plain, (~ ((v2_funct_1 @ sk_C))),
% 6.86/7.07      inference('sat_resolution*', [status(thm)], ['84', '85'])).
% 6.86/7.07  thf('87', plain, (~ (v2_funct_1 @ sk_C)),
% 6.86/7.07      inference('simpl_trail', [status(thm)], ['1', '86'])).
% 6.86/7.07  thf('88', plain,
% 6.86/7.07      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.86/7.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.86/7.07  thf(t3_subset, axiom,
% 6.86/7.07    (![A:$i,B:$i]:
% 6.86/7.07     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 6.86/7.07  thf('89', plain,
% 6.86/7.07      (![X8 : $i, X9 : $i]:
% 6.86/7.07         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 6.86/7.07      inference('cnf', [status(esa)], [t3_subset])).
% 6.86/7.07  thf('90', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 6.86/7.07      inference('sup-', [status(thm)], ['88', '89'])).
% 6.86/7.07  thf('91', plain,
% 6.86/7.07      (![X0 : $i, X2 : $i]:
% 6.86/7.07         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 6.86/7.07      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.86/7.07  thf('92', plain,
% 6.86/7.07      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C)
% 6.86/7.07        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C)))),
% 6.86/7.07      inference('sup-', [status(thm)], ['90', '91'])).
% 6.86/7.07  thf('93', plain,
% 6.86/7.07      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 6.86/7.07         = (k5_relat_1 @ sk_C @ sk_D))),
% 6.86/7.07      inference('demod', [status(thm)], ['21', '22'])).
% 6.86/7.07  thf('94', plain,
% 6.86/7.07      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 6.86/7.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.86/7.07  thf(t26_funct_2, axiom,
% 6.86/7.07    (![A:$i,B:$i,C:$i,D:$i]:
% 6.86/7.07     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 6.86/7.07         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.86/7.07       ( ![E:$i]:
% 6.86/7.07         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 6.86/7.07             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 6.86/7.07           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 6.86/7.07             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 6.86/7.07               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 6.86/7.07  thf('95', plain,
% 6.86/7.07      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 6.86/7.07         (~ (v1_funct_1 @ X46)
% 6.86/7.07          | ~ (v1_funct_2 @ X46 @ X47 @ X48)
% 6.86/7.07          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 6.86/7.07          | ~ (v2_funct_1 @ (k1_partfun1 @ X49 @ X47 @ X47 @ X48 @ X50 @ X46))
% 6.86/7.07          | (v2_funct_1 @ X50)
% 6.86/7.07          | ((X48) = (k1_xboole_0))
% 6.86/7.07          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X47)))
% 6.86/7.07          | ~ (v1_funct_2 @ X50 @ X49 @ X47)
% 6.86/7.07          | ~ (v1_funct_1 @ X50))),
% 6.86/7.07      inference('cnf', [status(esa)], [t26_funct_2])).
% 6.86/7.07  thf('96', plain,
% 6.86/7.07      (![X0 : $i, X1 : $i]:
% 6.86/7.07         (~ (v1_funct_1 @ X0)
% 6.86/7.07          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 6.86/7.07          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 6.86/7.07          | ((sk_A) = (k1_xboole_0))
% 6.86/7.07          | (v2_funct_1 @ X0)
% 6.86/7.07          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 6.86/7.07          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 6.86/7.07          | ~ (v1_funct_1 @ sk_D))),
% 6.86/7.07      inference('sup-', [status(thm)], ['94', '95'])).
% 6.86/7.07  thf('97', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 6.86/7.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.86/7.07  thf('98', plain, ((v1_funct_1 @ sk_D)),
% 6.86/7.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.86/7.07  thf('99', plain,
% 6.86/7.07      (![X0 : $i, X1 : $i]:
% 6.86/7.07         (~ (v1_funct_1 @ X0)
% 6.86/7.07          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 6.86/7.07          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 6.86/7.07          | ((sk_A) = (k1_xboole_0))
% 6.86/7.07          | (v2_funct_1 @ X0)
% 6.86/7.07          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 6.86/7.07      inference('demod', [status(thm)], ['96', '97', '98'])).
% 6.86/7.07  thf('100', plain,
% 6.86/7.07      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 6.86/7.07        | (v2_funct_1 @ sk_C)
% 6.86/7.07        | ((sk_A) = (k1_xboole_0))
% 6.86/7.07        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 6.86/7.07        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 6.86/7.07        | ~ (v1_funct_1 @ sk_C))),
% 6.86/7.07      inference('sup-', [status(thm)], ['93', '99'])).
% 6.86/7.07  thf('101', plain,
% 6.86/7.07      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.86/7.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.86/7.07  thf('102', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 6.86/7.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.86/7.07  thf('103', plain, ((v1_funct_1 @ sk_C)),
% 6.86/7.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.86/7.07  thf('104', plain,
% 6.86/7.07      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 6.86/7.07        | (v2_funct_1 @ sk_C)
% 6.86/7.07        | ((sk_A) = (k1_xboole_0)))),
% 6.86/7.07      inference('demod', [status(thm)], ['100', '101', '102', '103'])).
% 6.86/7.07  thf('105', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 6.86/7.07      inference('demod', [status(thm)], ['54', '57'])).
% 6.86/7.07  thf(fc4_funct_1, axiom,
% 6.86/7.07    (![A:$i]:
% 6.86/7.07     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 6.86/7.07       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 6.86/7.07  thf('106', plain, (![X22 : $i]: (v2_funct_1 @ (k6_relat_1 @ X22))),
% 6.86/7.07      inference('cnf', [status(esa)], [fc4_funct_1])).
% 6.86/7.07  thf('107', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 6.86/7.07      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 6.86/7.07  thf('108', plain, (![X22 : $i]: (v2_funct_1 @ (k6_partfun1 @ X22))),
% 6.86/7.07      inference('demod', [status(thm)], ['106', '107'])).
% 6.86/7.07  thf('109', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 6.86/7.07      inference('demod', [status(thm)], ['104', '105', '108'])).
% 6.86/7.07  thf('110', plain, (~ (v2_funct_1 @ sk_C)),
% 6.86/7.07      inference('simpl_trail', [status(thm)], ['1', '86'])).
% 6.86/7.07  thf('111', plain, (((sk_A) = (k1_xboole_0))),
% 6.86/7.07      inference('clc', [status(thm)], ['109', '110'])).
% 6.86/7.07  thf(t113_zfmisc_1, axiom,
% 6.86/7.07    (![A:$i,B:$i]:
% 6.86/7.07     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 6.86/7.07       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 6.86/7.07  thf('112', plain,
% 6.86/7.07      (![X6 : $i, X7 : $i]:
% 6.86/7.07         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 6.86/7.07      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 6.86/7.07  thf('113', plain,
% 6.86/7.07      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 6.86/7.07      inference('simplify', [status(thm)], ['112'])).
% 6.86/7.07  thf('114', plain,
% 6.86/7.07      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 6.86/7.07      inference('simplify', [status(thm)], ['112'])).
% 6.86/7.07  thf('115', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 6.86/7.07      inference('simplify', [status(thm)], ['72'])).
% 6.86/7.07  thf('116', plain,
% 6.86/7.07      (![X8 : $i, X10 : $i]:
% 6.86/7.07         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 6.86/7.07      inference('cnf', [status(esa)], [t3_subset])).
% 6.86/7.07  thf('117', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 6.86/7.07      inference('sup-', [status(thm)], ['115', '116'])).
% 6.86/7.07  thf('118', plain,
% 6.86/7.07      (![X23 : $i, X24 : $i, X25 : $i]:
% 6.86/7.07         ((v5_relat_1 @ X23 @ X25)
% 6.86/7.07          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 6.86/7.07      inference('cnf', [status(esa)], [cc2_relset_1])).
% 6.86/7.07  thf('119', plain,
% 6.86/7.07      (![X0 : $i, X1 : $i]: (v5_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X0)),
% 6.86/7.07      inference('sup-', [status(thm)], ['117', '118'])).
% 6.86/7.07  thf('120', plain, (![X0 : $i]: (v5_relat_1 @ k1_xboole_0 @ X0)),
% 6.86/7.07      inference('sup+', [status(thm)], ['114', '119'])).
% 6.86/7.07  thf('121', plain,
% 6.86/7.07      (![X13 : $i, X14 : $i]:
% 6.86/7.07         (~ (v5_relat_1 @ X13 @ X14)
% 6.86/7.07          | (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 6.86/7.07          | ~ (v1_relat_1 @ X13))),
% 6.86/7.07      inference('cnf', [status(esa)], [d19_relat_1])).
% 6.86/7.07  thf('122', plain,
% 6.86/7.07      (![X0 : $i]:
% 6.86/7.07         (~ (v1_relat_1 @ k1_xboole_0)
% 6.86/7.07          | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0))),
% 6.86/7.07      inference('sup-', [status(thm)], ['120', '121'])).
% 6.86/7.07  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 6.86/7.07  thf('123', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 6.86/7.07      inference('cnf', [status(esa)], [t81_relat_1])).
% 6.86/7.07  thf('124', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 6.86/7.07      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 6.86/7.07  thf('125', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 6.86/7.07      inference('demod', [status(thm)], ['123', '124'])).
% 6.86/7.07  thf('126', plain, (![X21 : $i]: (v1_relat_1 @ (k6_relat_1 @ X21))),
% 6.86/7.07      inference('cnf', [status(esa)], [fc4_funct_1])).
% 6.86/7.07  thf('127', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 6.86/7.07      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 6.86/7.07  thf('128', plain, (![X21 : $i]: (v1_relat_1 @ (k6_partfun1 @ X21))),
% 6.86/7.07      inference('demod', [status(thm)], ['126', '127'])).
% 6.86/7.07  thf('129', plain, ((v1_relat_1 @ k1_xboole_0)),
% 6.86/7.07      inference('sup+', [status(thm)], ['125', '128'])).
% 6.86/7.07  thf(t60_relat_1, axiom,
% 6.86/7.07    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 6.86/7.07     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 6.86/7.07  thf('130', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 6.86/7.07      inference('cnf', [status(esa)], [t60_relat_1])).
% 6.86/7.07  thf('131', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 6.86/7.07      inference('demod', [status(thm)], ['122', '129', '130'])).
% 6.86/7.07  thf('132', plain, (((sk_A) = (k1_xboole_0))),
% 6.86/7.07      inference('clc', [status(thm)], ['109', '110'])).
% 6.86/7.07  thf('133', plain,
% 6.86/7.07      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 6.86/7.07      inference('simplify', [status(thm)], ['112'])).
% 6.86/7.07  thf('134', plain, (((k1_xboole_0) = (sk_C))),
% 6.86/7.07      inference('demod', [status(thm)],
% 6.86/7.07                ['92', '111', '113', '131', '132', '133'])).
% 6.86/7.07  thf('135', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 6.86/7.07      inference('demod', [status(thm)], ['123', '124'])).
% 6.86/7.07  thf('136', plain, (![X22 : $i]: (v2_funct_1 @ (k6_partfun1 @ X22))),
% 6.86/7.07      inference('demod', [status(thm)], ['106', '107'])).
% 6.86/7.07  thf('137', plain, ((v2_funct_1 @ k1_xboole_0)),
% 6.86/7.07      inference('sup+', [status(thm)], ['135', '136'])).
% 6.86/7.07  thf('138', plain, ($false),
% 6.86/7.07      inference('demod', [status(thm)], ['87', '134', '137'])).
% 6.86/7.07  
% 6.86/7.07  % SZS output end Refutation
% 6.86/7.07  
% 6.86/7.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B8Pt32cfhz

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:01 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 750 expanded)
%              Number of leaves         :   46 ( 230 expanded)
%              Depth                    :   23
%              Number of atoms          : 1214 (15419 expanded)
%              Number of equality atoms :   39 ( 166 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ( ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X41 @ X42 @ X44 @ X45 @ X40 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X54 ) ) )
      | ( ( k1_partfun1 @ X50 @ X51 @ X53 @ X54 @ X49 @ X52 )
        = ( k5_relat_1 @ X49 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C_1 @ X0 )
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
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C_1 @ X0 )
        = ( k5_relat_1 @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D )
      = ( k5_relat_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D )
    = ( k5_relat_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9','18'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('20',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_relat_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('21',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('22',plain,(
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

thf('23',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ( v5_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( v5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( v5_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_relat_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('28',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_relat_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('31',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v5_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['25','28','31'])).

thf('33',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v5_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('36',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) ) @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('37',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('38',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) ) )
    | ( ( k2_relat_1 @ sk_D )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D )
    = ( k5_relat_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('41',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9','18'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('43',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( X34 = X37 )
      | ~ ( r2_relset_1 @ X35 @ X36 @ X34 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C_1 @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C_1 @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('46',plain,(
    ! [X47: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X47 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('47',plain,
    ( ( k5_relat_1 @ sk_C_1 @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('48',plain,(
    ! [X23: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('49',plain,(
    ! [X55: $i] :
      ( ( k6_partfun1 @ X55 )
      = ( k6_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('50',plain,(
    ! [X23: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X23 ) )
      = X23 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('52',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v5_relat_1 @ X31 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('53',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v5_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('55',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['26','27'])).

thf('57',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k5_relat_1 @ sk_C_1 @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('59',plain,(
    ! [X23: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X23 ) )
      = X23 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('60',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['38','47','50','57','58','59'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('61',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k2_relat_1 @ X39 )
       != X38 )
      | ( v2_funct_2 @ X39 @ X38 )
      | ~ ( v5_relat_1 @ X39 @ X38 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('62',plain,(
    ! [X39: $i] :
      ( ~ ( v1_relat_1 @ X39 )
      | ~ ( v5_relat_1 @ X39 @ ( k2_relat_1 @ X39 ) )
      | ( v2_funct_2 @ X39 @ ( k2_relat_1 @ X39 ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( X5 != X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('64',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ( v5_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X39: $i] :
      ( ( v2_funct_2 @ X39 @ ( k2_relat_1 @ X39 ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(clc,[status(thm)],['62','66'])).

thf('68',plain,
    ( ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['60','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['26','27'])).

thf('70',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('72',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('74',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','74'])).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('76',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_xboole_0 @ X10 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('77',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('78',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v1_xboole_0 @ X12 )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('79',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D )
    = ( k5_relat_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('82',plain,(
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

thf('83',plain,(
    ! [X56: $i,X57: $i,X58: $i,X59: $i,X60: $i] :
      ( ~ ( v1_funct_1 @ X56 )
      | ~ ( v1_funct_2 @ X56 @ X57 @ X58 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X58 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X59 @ X57 @ X57 @ X58 @ X60 @ X56 ) )
      | ( v2_funct_1 @ X60 )
      | ( X58 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X57 ) ) )
      | ~ ( v1_funct_2 @ X60 @ X59 @ X57 )
      | ~ ( v1_funct_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['81','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['88','89','90','91'])).

thf('93',plain,
    ( ( k5_relat_1 @ sk_C_1 @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('94',plain,(
    ! [X27: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('95',plain,(
    ! [X55: $i] :
      ( ( k6_partfun1 @ X55 )
      = ( k6_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('96',plain,(
    ! [X27: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X27 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( v2_funct_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['92','93','96'])).

thf('98',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','74'])).

thf('99',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['97','98'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('100',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('101',plain,(
    v1_xboole_0 @ sk_C_1 ),
    inference(demod,[status(thm)],['80','99','100'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('102',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(cc2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) ) ) )).

thf('103',plain,(
    ! [X25: $i] :
      ( ( v2_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('106',plain,(
    ! [X24: $i] :
      ( ( v1_funct_1 @ X24 )
      | ~ ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_funct_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['101','107'])).

thf('109',plain,(
    $false ),
    inference(demod,[status(thm)],['75','108'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B8Pt32cfhz
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:21:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.70  % Solved by: fo/fo7.sh
% 0.46/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.70  % done 610 iterations in 0.275s
% 0.46/0.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.70  % SZS output start Refutation
% 0.46/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.70  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.46/0.70  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.46/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.70  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.46/0.70  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.46/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.70  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.46/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.70  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.70  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.46/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.70  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.46/0.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.70  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.46/0.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.70  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.46/0.70  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.46/0.70  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.46/0.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.70  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.70  thf(t29_funct_2, conjecture,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.70       ( ![D:$i]:
% 0.46/0.70         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.46/0.70             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.46/0.70           ( ( r2_relset_1 @
% 0.46/0.70               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.46/0.70               ( k6_partfun1 @ A ) ) =>
% 0.46/0.70             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 0.46/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.70    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.70        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.70            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.70          ( ![D:$i]:
% 0.46/0.70            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.46/0.70                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.46/0.70              ( ( r2_relset_1 @
% 0.46/0.70                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.46/0.70                  ( k6_partfun1 @ A ) ) =>
% 0.46/0.70                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 0.46/0.70    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 0.46/0.70  thf('0', plain, ((~ (v2_funct_1 @ sk_C_1) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('1', plain, ((~ (v2_funct_1 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 0.46/0.70      inference('split', [status(esa)], ['0'])).
% 0.46/0.70  thf('2', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('3', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(dt_k1_partfun1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.46/0.70     ( ( ( v1_funct_1 @ E ) & 
% 0.46/0.70         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.46/0.70         ( v1_funct_1 @ F ) & 
% 0.46/0.70         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.46/0.70       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.46/0.70         ( m1_subset_1 @
% 0.46/0.70           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.46/0.70           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.46/0.70  thf('4', plain,
% 0.46/0.70      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.46/0.70          | ~ (v1_funct_1 @ X40)
% 0.46/0.70          | ~ (v1_funct_1 @ X43)
% 0.46/0.70          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 0.46/0.70          | (m1_subset_1 @ (k1_partfun1 @ X41 @ X42 @ X44 @ X45 @ X40 @ X43) @ 
% 0.46/0.70             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X45))))),
% 0.46/0.70      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.46/0.70  thf('5', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.70         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 0.46/0.70           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.46/0.70          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.46/0.70          | ~ (v1_funct_1 @ X1)
% 0.46/0.70          | ~ (v1_funct_1 @ sk_C_1))),
% 0.46/0.70      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.70  thf('6', plain, ((v1_funct_1 @ sk_C_1)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('7', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.70         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 0.46/0.70           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.46/0.70          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.46/0.70          | ~ (v1_funct_1 @ X1))),
% 0.46/0.70      inference('demod', [status(thm)], ['5', '6'])).
% 0.46/0.70  thf('8', plain,
% 0.46/0.70      ((~ (v1_funct_1 @ sk_D)
% 0.46/0.70        | (m1_subset_1 @ 
% 0.46/0.70           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ 
% 0.46/0.70           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['2', '7'])).
% 0.46/0.70  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('10', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('11', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(redefinition_k1_partfun1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.46/0.70     ( ( ( v1_funct_1 @ E ) & 
% 0.46/0.70         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.46/0.70         ( v1_funct_1 @ F ) & 
% 0.46/0.70         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.46/0.70       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.46/0.70  thf('12', plain,
% 0.46/0.70      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 0.46/0.70          | ~ (v1_funct_1 @ X49)
% 0.46/0.70          | ~ (v1_funct_1 @ X52)
% 0.46/0.70          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X54)))
% 0.46/0.70          | ((k1_partfun1 @ X50 @ X51 @ X53 @ X54 @ X49 @ X52)
% 0.46/0.70              = (k5_relat_1 @ X49 @ X52)))),
% 0.46/0.70      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.46/0.70  thf('13', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.70         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C_1 @ X0)
% 0.46/0.70            = (k5_relat_1 @ sk_C_1 @ X0))
% 0.46/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.46/0.70          | ~ (v1_funct_1 @ X0)
% 0.46/0.70          | ~ (v1_funct_1 @ sk_C_1))),
% 0.46/0.70      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.70  thf('14', plain, ((v1_funct_1 @ sk_C_1)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('15', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.70         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C_1 @ X0)
% 0.46/0.70            = (k5_relat_1 @ sk_C_1 @ X0))
% 0.46/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.46/0.70          | ~ (v1_funct_1 @ X0))),
% 0.46/0.70      inference('demod', [status(thm)], ['13', '14'])).
% 0.46/0.70  thf('16', plain,
% 0.46/0.70      ((~ (v1_funct_1 @ sk_D)
% 0.46/0.70        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D)
% 0.46/0.70            = (k5_relat_1 @ sk_C_1 @ sk_D)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['10', '15'])).
% 0.46/0.70  thf('17', plain, ((v1_funct_1 @ sk_D)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('18', plain,
% 0.46/0.70      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D)
% 0.46/0.70         = (k5_relat_1 @ sk_C_1 @ sk_D))),
% 0.46/0.70      inference('demod', [status(thm)], ['16', '17'])).
% 0.46/0.70  thf('19', plain,
% 0.46/0.70      ((m1_subset_1 @ (k5_relat_1 @ sk_C_1 @ sk_D) @ 
% 0.46/0.70        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.70      inference('demod', [status(thm)], ['8', '9', '18'])).
% 0.46/0.70  thf(cc1_relset_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.70       ( v1_relat_1 @ C ) ))).
% 0.46/0.70  thf('20', plain,
% 0.46/0.70      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.46/0.70         ((v1_relat_1 @ X28)
% 0.46/0.70          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.46/0.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.46/0.70  thf('21', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D))),
% 0.46/0.70      inference('sup-', [status(thm)], ['19', '20'])).
% 0.46/0.70  thf(t45_relat_1, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( v1_relat_1 @ A ) =>
% 0.46/0.70       ( ![B:$i]:
% 0.46/0.70         ( ( v1_relat_1 @ B ) =>
% 0.46/0.70           ( r1_tarski @
% 0.46/0.70             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.46/0.70  thf('22', plain,
% 0.46/0.70      (![X19 : $i, X20 : $i]:
% 0.46/0.70         (~ (v1_relat_1 @ X19)
% 0.46/0.70          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X20 @ X19)) @ 
% 0.46/0.70             (k2_relat_1 @ X19))
% 0.46/0.70          | ~ (v1_relat_1 @ X20))),
% 0.46/0.70      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.46/0.70  thf(d19_relat_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( v1_relat_1 @ B ) =>
% 0.46/0.70       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.46/0.70  thf('23', plain,
% 0.46/0.70      (![X15 : $i, X16 : $i]:
% 0.46/0.70         (~ (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 0.46/0.70          | (v5_relat_1 @ X15 @ X16)
% 0.46/0.70          | ~ (v1_relat_1 @ X15))),
% 0.46/0.70      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.46/0.70  thf('24', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         (~ (v1_relat_1 @ X1)
% 0.46/0.70          | ~ (v1_relat_1 @ X0)
% 0.46/0.70          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.46/0.70          | (v5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['22', '23'])).
% 0.46/0.70  thf('25', plain,
% 0.46/0.70      (((v5_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D) @ (k2_relat_1 @ sk_D))
% 0.46/0.70        | ~ (v1_relat_1 @ sk_D)
% 0.46/0.70        | ~ (v1_relat_1 @ sk_C_1))),
% 0.46/0.70      inference('sup-', [status(thm)], ['21', '24'])).
% 0.46/0.70  thf('26', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('27', plain,
% 0.46/0.70      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.46/0.70         ((v1_relat_1 @ X28)
% 0.46/0.70          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.46/0.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.46/0.70  thf('28', plain, ((v1_relat_1 @ sk_D)),
% 0.46/0.70      inference('sup-', [status(thm)], ['26', '27'])).
% 0.46/0.70  thf('29', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('30', plain,
% 0.46/0.70      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.46/0.70         ((v1_relat_1 @ X28)
% 0.46/0.70          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.46/0.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.46/0.70  thf('31', plain, ((v1_relat_1 @ sk_C_1)),
% 0.46/0.70      inference('sup-', [status(thm)], ['29', '30'])).
% 0.46/0.70  thf('32', plain,
% 0.46/0.70      ((v5_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D) @ (k2_relat_1 @ sk_D))),
% 0.46/0.70      inference('demod', [status(thm)], ['25', '28', '31'])).
% 0.46/0.70  thf('33', plain,
% 0.46/0.70      (![X15 : $i, X16 : $i]:
% 0.46/0.70         (~ (v5_relat_1 @ X15 @ X16)
% 0.46/0.70          | (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 0.46/0.70          | ~ (v1_relat_1 @ X15))),
% 0.46/0.70      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.46/0.70  thf('34', plain,
% 0.46/0.70      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D))
% 0.46/0.70        | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D)) @ 
% 0.46/0.70           (k2_relat_1 @ sk_D)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['32', '33'])).
% 0.46/0.70  thf('35', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D))),
% 0.46/0.70      inference('sup-', [status(thm)], ['19', '20'])).
% 0.46/0.70  thf('36', plain,
% 0.46/0.70      ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D)) @ 
% 0.46/0.70        (k2_relat_1 @ sk_D))),
% 0.46/0.70      inference('demod', [status(thm)], ['34', '35'])).
% 0.46/0.70  thf(d10_xboole_0, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.70  thf('37', plain,
% 0.46/0.70      (![X5 : $i, X7 : $i]:
% 0.46/0.70         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 0.46/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.70  thf('38', plain,
% 0.46/0.70      ((~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 0.46/0.70           (k2_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D)))
% 0.46/0.70        | ((k2_relat_1 @ sk_D) = (k2_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['36', '37'])).
% 0.46/0.70  thf('39', plain,
% 0.46/0.70      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.46/0.70        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ 
% 0.46/0.70        (k6_partfun1 @ sk_A))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('40', plain,
% 0.46/0.70      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D)
% 0.46/0.70         = (k5_relat_1 @ sk_C_1 @ sk_D))),
% 0.46/0.70      inference('demod', [status(thm)], ['16', '17'])).
% 0.46/0.70  thf('41', plain,
% 0.46/0.70      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C_1 @ sk_D) @ 
% 0.46/0.70        (k6_partfun1 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['39', '40'])).
% 0.46/0.70  thf('42', plain,
% 0.46/0.70      ((m1_subset_1 @ (k5_relat_1 @ sk_C_1 @ sk_D) @ 
% 0.46/0.70        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.70      inference('demod', [status(thm)], ['8', '9', '18'])).
% 0.46/0.70  thf(redefinition_r2_relset_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.70     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.46/0.70         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.70       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.46/0.70  thf('43', plain,
% 0.46/0.70      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.46/0.70          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.46/0.70          | ((X34) = (X37))
% 0.46/0.70          | ~ (r2_relset_1 @ X35 @ X36 @ X34 @ X37))),
% 0.46/0.70      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.46/0.70  thf('44', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C_1 @ sk_D) @ X0)
% 0.46/0.70          | ((k5_relat_1 @ sk_C_1 @ sk_D) = (X0))
% 0.46/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['42', '43'])).
% 0.46/0.70  thf('45', plain,
% 0.46/0.70      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.46/0.70           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.46/0.70        | ((k5_relat_1 @ sk_C_1 @ sk_D) = (k6_partfun1 @ sk_A)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['41', '44'])).
% 0.46/0.70  thf(dt_k6_partfun1, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( m1_subset_1 @
% 0.46/0.70         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.46/0.70       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.46/0.70  thf('46', plain,
% 0.46/0.70      (![X47 : $i]:
% 0.46/0.70         (m1_subset_1 @ (k6_partfun1 @ X47) @ 
% 0.46/0.70          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X47)))),
% 0.46/0.70      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.46/0.70  thf('47', plain, (((k5_relat_1 @ sk_C_1 @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['45', '46'])).
% 0.46/0.70  thf(t71_relat_1, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.46/0.70       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.46/0.70  thf('48', plain, (![X23 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 0.46/0.70      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.46/0.70  thf(redefinition_k6_partfun1, axiom,
% 0.46/0.70    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.46/0.70  thf('49', plain, (![X55 : $i]: ((k6_partfun1 @ X55) = (k6_relat_1 @ X55))),
% 0.46/0.70      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.46/0.70  thf('50', plain, (![X23 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X23)) = (X23))),
% 0.46/0.70      inference('demod', [status(thm)], ['48', '49'])).
% 0.46/0.70  thf('51', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(cc2_relset_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.70       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.46/0.70  thf('52', plain,
% 0.46/0.70      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.46/0.70         ((v5_relat_1 @ X31 @ X33)
% 0.46/0.70          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.46/0.70      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.70  thf('53', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 0.46/0.70      inference('sup-', [status(thm)], ['51', '52'])).
% 0.46/0.70  thf('54', plain,
% 0.46/0.70      (![X15 : $i, X16 : $i]:
% 0.46/0.70         (~ (v5_relat_1 @ X15 @ X16)
% 0.46/0.70          | (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 0.46/0.70          | ~ (v1_relat_1 @ X15))),
% 0.46/0.70      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.46/0.70  thf('55', plain,
% 0.46/0.70      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 0.46/0.70      inference('sup-', [status(thm)], ['53', '54'])).
% 0.46/0.70  thf('56', plain, ((v1_relat_1 @ sk_D)),
% 0.46/0.70      inference('sup-', [status(thm)], ['26', '27'])).
% 0.46/0.70  thf('57', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 0.46/0.70      inference('demod', [status(thm)], ['55', '56'])).
% 0.46/0.70  thf('58', plain, (((k5_relat_1 @ sk_C_1 @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['45', '46'])).
% 0.46/0.70  thf('59', plain, (![X23 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X23)) = (X23))),
% 0.46/0.70      inference('demod', [status(thm)], ['48', '49'])).
% 0.46/0.70  thf('60', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['38', '47', '50', '57', '58', '59'])).
% 0.46/0.70  thf(d3_funct_2, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.46/0.70       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.46/0.70  thf('61', plain,
% 0.46/0.70      (![X38 : $i, X39 : $i]:
% 0.46/0.70         (((k2_relat_1 @ X39) != (X38))
% 0.46/0.70          | (v2_funct_2 @ X39 @ X38)
% 0.46/0.70          | ~ (v5_relat_1 @ X39 @ X38)
% 0.46/0.70          | ~ (v1_relat_1 @ X39))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.46/0.70  thf('62', plain,
% 0.46/0.70      (![X39 : $i]:
% 0.46/0.70         (~ (v1_relat_1 @ X39)
% 0.46/0.70          | ~ (v5_relat_1 @ X39 @ (k2_relat_1 @ X39))
% 0.46/0.70          | (v2_funct_2 @ X39 @ (k2_relat_1 @ X39)))),
% 0.46/0.70      inference('simplify', [status(thm)], ['61'])).
% 0.46/0.70  thf('63', plain,
% 0.46/0.70      (![X5 : $i, X6 : $i]: ((r1_tarski @ X5 @ X6) | ((X5) != (X6)))),
% 0.46/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.70  thf('64', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 0.46/0.70      inference('simplify', [status(thm)], ['63'])).
% 0.46/0.70  thf('65', plain,
% 0.46/0.70      (![X15 : $i, X16 : $i]:
% 0.46/0.70         (~ (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 0.46/0.70          | (v5_relat_1 @ X15 @ X16)
% 0.46/0.70          | ~ (v1_relat_1 @ X15))),
% 0.46/0.70      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.46/0.70  thf('66', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['64', '65'])).
% 0.46/0.70  thf('67', plain,
% 0.46/0.70      (![X39 : $i]:
% 0.46/0.70         ((v2_funct_2 @ X39 @ (k2_relat_1 @ X39)) | ~ (v1_relat_1 @ X39))),
% 0.46/0.70      inference('clc', [status(thm)], ['62', '66'])).
% 0.46/0.70  thf('68', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 0.46/0.70      inference('sup+', [status(thm)], ['60', '67'])).
% 0.46/0.70  thf('69', plain, ((v1_relat_1 @ sk_D)),
% 0.46/0.70      inference('sup-', [status(thm)], ['26', '27'])).
% 0.46/0.70  thf('70', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 0.46/0.70      inference('demod', [status(thm)], ['68', '69'])).
% 0.46/0.70  thf('71', plain,
% 0.46/0.70      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 0.46/0.70      inference('split', [status(esa)], ['0'])).
% 0.46/0.70  thf('72', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 0.46/0.70      inference('sup-', [status(thm)], ['70', '71'])).
% 0.46/0.70  thf('73', plain,
% 0.46/0.70      (~ ((v2_funct_1 @ sk_C_1)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 0.46/0.70      inference('split', [status(esa)], ['0'])).
% 0.46/0.70  thf('74', plain, (~ ((v2_funct_1 @ sk_C_1))),
% 0.46/0.70      inference('sat_resolution*', [status(thm)], ['72', '73'])).
% 0.46/0.70  thf('75', plain, (~ (v2_funct_1 @ sk_C_1)),
% 0.46/0.70      inference('simpl_trail', [status(thm)], ['1', '74'])).
% 0.46/0.70  thf(fc4_zfmisc_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.46/0.70  thf('76', plain,
% 0.46/0.70      (![X10 : $i, X11 : $i]:
% 0.46/0.70         (~ (v1_xboole_0 @ X10) | (v1_xboole_0 @ (k2_zfmisc_1 @ X10 @ X11)))),
% 0.46/0.70      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 0.46/0.70  thf('77', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(cc1_subset_1, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( v1_xboole_0 @ A ) =>
% 0.46/0.70       ( ![B:$i]:
% 0.46/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.46/0.70  thf('78', plain,
% 0.46/0.70      (![X12 : $i, X13 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.46/0.70          | (v1_xboole_0 @ X12)
% 0.46/0.70          | ~ (v1_xboole_0 @ X13))),
% 0.46/0.70      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.46/0.70  thf('79', plain,
% 0.46/0.70      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C_1))),
% 0.46/0.70      inference('sup-', [status(thm)], ['77', '78'])).
% 0.46/0.70  thf('80', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C_1))),
% 0.46/0.70      inference('sup-', [status(thm)], ['76', '79'])).
% 0.46/0.70  thf('81', plain,
% 0.46/0.70      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D)
% 0.46/0.70         = (k5_relat_1 @ sk_C_1 @ sk_D))),
% 0.46/0.70      inference('demod', [status(thm)], ['16', '17'])).
% 0.46/0.70  thf('82', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(t26_funct_2, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.70     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.46/0.70         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.70       ( ![E:$i]:
% 0.46/0.70         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.46/0.70             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.46/0.70           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 0.46/0.70             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 0.46/0.70               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 0.46/0.70  thf('83', plain,
% 0.46/0.70      (![X56 : $i, X57 : $i, X58 : $i, X59 : $i, X60 : $i]:
% 0.46/0.70         (~ (v1_funct_1 @ X56)
% 0.46/0.70          | ~ (v1_funct_2 @ X56 @ X57 @ X58)
% 0.46/0.70          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X58)))
% 0.46/0.70          | ~ (v2_funct_1 @ (k1_partfun1 @ X59 @ X57 @ X57 @ X58 @ X60 @ X56))
% 0.46/0.70          | (v2_funct_1 @ X60)
% 0.46/0.70          | ((X58) = (k1_xboole_0))
% 0.46/0.70          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X57)))
% 0.46/0.70          | ~ (v1_funct_2 @ X60 @ X59 @ X57)
% 0.46/0.70          | ~ (v1_funct_1 @ X60))),
% 0.46/0.70      inference('cnf', [status(esa)], [t26_funct_2])).
% 0.46/0.70  thf('84', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         (~ (v1_funct_1 @ X0)
% 0.46/0.70          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.46/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.46/0.70          | ((sk_A) = (k1_xboole_0))
% 0.46/0.70          | (v2_funct_1 @ X0)
% 0.46/0.70          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.46/0.70          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.46/0.70          | ~ (v1_funct_1 @ sk_D))),
% 0.46/0.70      inference('sup-', [status(thm)], ['82', '83'])).
% 0.46/0.70  thf('85', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('86', plain, ((v1_funct_1 @ sk_D)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('87', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         (~ (v1_funct_1 @ X0)
% 0.46/0.70          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.46/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.46/0.70          | ((sk_A) = (k1_xboole_0))
% 0.46/0.70          | (v2_funct_1 @ X0)
% 0.46/0.70          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 0.46/0.70      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.46/0.70  thf('88', plain,
% 0.46/0.70      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C_1 @ sk_D))
% 0.46/0.70        | (v2_funct_1 @ sk_C_1)
% 0.46/0.70        | ((sk_A) = (k1_xboole_0))
% 0.46/0.70        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.46/0.70        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.46/0.70        | ~ (v1_funct_1 @ sk_C_1))),
% 0.46/0.70      inference('sup-', [status(thm)], ['81', '87'])).
% 0.46/0.70  thf('89', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('90', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('91', plain, ((v1_funct_1 @ sk_C_1)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('92', plain,
% 0.46/0.70      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C_1 @ sk_D))
% 0.46/0.70        | (v2_funct_1 @ sk_C_1)
% 0.46/0.70        | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.70      inference('demod', [status(thm)], ['88', '89', '90', '91'])).
% 0.46/0.70  thf('93', plain, (((k5_relat_1 @ sk_C_1 @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['45', '46'])).
% 0.46/0.70  thf(fc4_funct_1, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.46/0.70       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.46/0.70  thf('94', plain, (![X27 : $i]: (v2_funct_1 @ (k6_relat_1 @ X27))),
% 0.46/0.70      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.46/0.70  thf('95', plain, (![X55 : $i]: ((k6_partfun1 @ X55) = (k6_relat_1 @ X55))),
% 0.46/0.70      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.46/0.70  thf('96', plain, (![X27 : $i]: (v2_funct_1 @ (k6_partfun1 @ X27))),
% 0.46/0.70      inference('demod', [status(thm)], ['94', '95'])).
% 0.46/0.70  thf('97', plain, (((v2_funct_1 @ sk_C_1) | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.70      inference('demod', [status(thm)], ['92', '93', '96'])).
% 0.46/0.70  thf('98', plain, (~ (v2_funct_1 @ sk_C_1)),
% 0.46/0.70      inference('simpl_trail', [status(thm)], ['1', '74'])).
% 0.46/0.70  thf('99', plain, (((sk_A) = (k1_xboole_0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['97', '98'])).
% 0.46/0.70  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.46/0.70  thf('100', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.70  thf('101', plain, ((v1_xboole_0 @ sk_C_1)),
% 0.46/0.70      inference('demod', [status(thm)], ['80', '99', '100'])).
% 0.46/0.70  thf(cc1_relat_1, axiom,
% 0.46/0.70    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.46/0.70  thf('102', plain,
% 0.46/0.70      (![X14 : $i]: ((v1_relat_1 @ X14) | ~ (v1_xboole_0 @ X14))),
% 0.46/0.70      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.46/0.70  thf(cc2_funct_1, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( ( v1_xboole_0 @ A ) & ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.70       ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) ))).
% 0.46/0.70  thf('103', plain,
% 0.46/0.70      (![X25 : $i]:
% 0.46/0.70         ((v2_funct_1 @ X25)
% 0.46/0.70          | ~ (v1_funct_1 @ X25)
% 0.46/0.70          | ~ (v1_relat_1 @ X25)
% 0.46/0.70          | ~ (v1_xboole_0 @ X25))),
% 0.46/0.70      inference('cnf', [status(esa)], [cc2_funct_1])).
% 0.46/0.70  thf('104', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (v1_xboole_0 @ X0)
% 0.46/0.70          | ~ (v1_xboole_0 @ X0)
% 0.46/0.70          | ~ (v1_funct_1 @ X0)
% 0.46/0.70          | (v2_funct_1 @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['102', '103'])).
% 0.46/0.70  thf('105', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((v2_funct_1 @ X0) | ~ (v1_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.70      inference('simplify', [status(thm)], ['104'])).
% 0.46/0.70  thf(cc1_funct_1, axiom,
% 0.46/0.70    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 0.46/0.70  thf('106', plain,
% 0.46/0.70      (![X24 : $i]: ((v1_funct_1 @ X24) | ~ (v1_xboole_0 @ X24))),
% 0.46/0.70      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.46/0.70  thf('107', plain, (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v2_funct_1 @ X0))),
% 0.46/0.70      inference('clc', [status(thm)], ['105', '106'])).
% 0.46/0.70  thf('108', plain, ((v2_funct_1 @ sk_C_1)),
% 0.46/0.70      inference('sup-', [status(thm)], ['101', '107'])).
% 0.46/0.70  thf('109', plain, ($false), inference('demod', [status(thm)], ['75', '108'])).
% 0.46/0.70  
% 0.46/0.70  % SZS output end Refutation
% 0.46/0.70  
% 0.55/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

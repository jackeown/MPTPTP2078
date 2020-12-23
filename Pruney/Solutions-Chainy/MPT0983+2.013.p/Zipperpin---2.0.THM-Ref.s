%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gklKuoX4aO

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:02 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 514 expanded)
%              Number of leaves         :   47 ( 170 expanded)
%              Depth                    :   20
%              Number of atoms          : 1319 (9716 expanded)
%              Number of equality atoms :   44 ( 139 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('4',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('7',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('14',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( X28 = X31 )
      | ~ ( r2_relset_1 @ X29 @ X30 @ X28 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','15'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('17',plain,(
    ! [X41: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('18',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('19',plain,(
    ! [X41: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ ( k6_partfun1 @ B ) )
           => ( ( k2_relset_1 @ A @ B @ C )
              = B ) ) ) ) )).

thf('22',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( r2_relset_1 @ X44 @ X44 @ ( k1_partfun1 @ X44 @ X45 @ X45 @ X44 @ X43 @ X46 ) @ ( k6_partfun1 @ X44 ) )
      | ( ( k2_relset_1 @ X45 @ X44 @ X46 )
        = X44 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X46 @ X45 @ X44 )
      | ~ ( v1_funct_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('23',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('24',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( r2_relset_1 @ X44 @ X44 @ ( k1_partfun1 @ X44 @ X45 @ X45 @ X44 @ X43 @ X46 ) @ ( k6_relat_1 @ X44 ) )
      | ( ( k2_relset_1 @ X45 @ X44 @ X46 )
        = X44 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X46 @ X45 @ X44 )
      | ~ ( v1_funct_1 @ X46 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['20','28'])).

thf('30',plain,(
    ! [X41: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('31',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( r2_relset_1 @ X29 @ X30 @ X28 @ X31 )
      | ( X28 != X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('32',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( r2_relset_1 @ X29 @ X30 @ X31 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('35',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X27 @ X25 )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('36',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['29','33','36','37','38','39'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('41',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k2_relat_1 @ X33 )
       != X32 )
      | ( v2_funct_2 @ X33 @ X32 )
      | ~ ( v5_relat_1 @ X33 @ X32 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('42',plain,(
    ! [X33: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ~ ( v5_relat_1 @ X33 @ ( k2_relat_1 @ X33 ) )
      | ( v2_funct_2 @ X33 @ ( k2_relat_1 @ X33 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('45',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v5_relat_1 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('46',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['29','33','36','37','38','39'])).

thf('48',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('49',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('50',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['43','46','47','50'])).

thf('52',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('53',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('55',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('59',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['57','58'])).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('60',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ X10 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf(cc2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) ) ) )).

thf('61',plain,(
    ! [X11: $i] :
      ( ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['59','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('66',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X24 ) ) )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('67',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('69',plain,(
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

thf('70',plain,(
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

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['68','74'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('76',plain,(
    ! [X13: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','76','77','78','79'])).

thf('81',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','55'])).

thf('82',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['80','81'])).

thf(l222_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v5_relat_1 @ k1_xboole_0 @ B )
      & ( v4_relat_1 @ k1_xboole_0 @ A ) ) )).

thf('83',plain,(
    ! [X8: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[l222_relat_1])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('84',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v5_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k2_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('86',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('87',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('88',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['85','88'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('90',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('91',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf('94',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('95',plain,(
    ! [X41: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('96',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('97',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('98',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['96','98'])).

thf('100',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('101',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X24 ) ) )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['99','103'])).

thf('105',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['93','104'])).

thf('106',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['67','82','105'])).

thf('107',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['64','106'])).

thf('108',plain,(
    $false ),
    inference(demod,[status(thm)],['56','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gklKuoX4aO
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:25:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.61/0.85  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.61/0.85  % Solved by: fo/fo7.sh
% 0.61/0.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.85  % done 667 iterations in 0.405s
% 0.61/0.85  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.61/0.85  % SZS output start Refutation
% 0.61/0.85  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.61/0.85  thf(sk_B_type, type, sk_B: $i > $i).
% 0.61/0.85  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.61/0.85  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.61/0.85  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.61/0.85  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.61/0.85  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.61/0.85  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.61/0.85  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.61/0.85  thf(sk_D_type, type, sk_D: $i).
% 0.61/0.85  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.61/0.85  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.61/0.85  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.61/0.85  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.61/0.85  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.61/0.85  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.61/0.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.61/0.85  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.61/0.85  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.61/0.85  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.61/0.85  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.61/0.85  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.61/0.85  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.85  thf(sk_C_type, type, sk_C: $i).
% 0.61/0.85  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.61/0.85  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.61/0.85  thf(t29_funct_2, conjecture,
% 0.61/0.85    (![A:$i,B:$i,C:$i]:
% 0.61/0.85     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.61/0.85         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.61/0.85       ( ![D:$i]:
% 0.61/0.85         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.61/0.85             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.61/0.85           ( ( r2_relset_1 @
% 0.61/0.85               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.61/0.85               ( k6_partfun1 @ A ) ) =>
% 0.61/0.85             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 0.61/0.85  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.85    (~( ![A:$i,B:$i,C:$i]:
% 0.61/0.85        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.61/0.85            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.61/0.85          ( ![D:$i]:
% 0.61/0.85            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.61/0.85                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.61/0.85              ( ( r2_relset_1 @
% 0.61/0.85                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.61/0.85                  ( k6_partfun1 @ A ) ) =>
% 0.61/0.85                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 0.61/0.85    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 0.61/0.85  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 0.61/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.85  thf('1', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.61/0.85      inference('split', [status(esa)], ['0'])).
% 0.61/0.85  thf('2', plain,
% 0.61/0.85      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.61/0.85        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.61/0.85        (k6_partfun1 @ sk_A))),
% 0.61/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.85  thf(redefinition_k6_partfun1, axiom,
% 0.61/0.85    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.61/0.85  thf('3', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 0.61/0.85      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.61/0.85  thf('4', plain,
% 0.61/0.85      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.61/0.85        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.61/0.85        (k6_relat_1 @ sk_A))),
% 0.61/0.85      inference('demod', [status(thm)], ['2', '3'])).
% 0.61/0.85  thf('5', plain,
% 0.61/0.85      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.61/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.85  thf('6', plain,
% 0.61/0.85      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.61/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.85  thf(dt_k1_partfun1, axiom,
% 0.61/0.85    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.61/0.85     ( ( ( v1_funct_1 @ E ) & 
% 0.61/0.85         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.61/0.85         ( v1_funct_1 @ F ) & 
% 0.61/0.85         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.61/0.85       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.61/0.85         ( m1_subset_1 @
% 0.61/0.85           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.61/0.85           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.61/0.85  thf('7', plain,
% 0.61/0.85      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.61/0.85         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.61/0.85          | ~ (v1_funct_1 @ X34)
% 0.61/0.85          | ~ (v1_funct_1 @ X37)
% 0.61/0.85          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.61/0.85          | (m1_subset_1 @ (k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37) @ 
% 0.61/0.85             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X39))))),
% 0.61/0.85      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.61/0.85  thf('8', plain,
% 0.61/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.85         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1) @ 
% 0.61/0.85           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.61/0.85          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.61/0.85          | ~ (v1_funct_1 @ X1)
% 0.61/0.85          | ~ (v1_funct_1 @ sk_C))),
% 0.61/0.85      inference('sup-', [status(thm)], ['6', '7'])).
% 0.61/0.85  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 0.61/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.85  thf('10', plain,
% 0.61/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.85         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1) @ 
% 0.61/0.85           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.61/0.85          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.61/0.85          | ~ (v1_funct_1 @ X1))),
% 0.61/0.85      inference('demod', [status(thm)], ['8', '9'])).
% 0.61/0.85  thf('11', plain,
% 0.61/0.85      ((~ (v1_funct_1 @ sk_D)
% 0.61/0.85        | (m1_subset_1 @ 
% 0.61/0.85           (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.61/0.85           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.61/0.85      inference('sup-', [status(thm)], ['5', '10'])).
% 0.61/0.85  thf('12', plain, ((v1_funct_1 @ sk_D)),
% 0.61/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.85  thf('13', plain,
% 0.61/0.85      ((m1_subset_1 @ 
% 0.61/0.85        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.61/0.85        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.61/0.85      inference('demod', [status(thm)], ['11', '12'])).
% 0.61/0.85  thf(redefinition_r2_relset_1, axiom,
% 0.61/0.85    (![A:$i,B:$i,C:$i,D:$i]:
% 0.61/0.85     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.61/0.85         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.61/0.85       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.61/0.85  thf('14', plain,
% 0.61/0.85      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.61/0.85         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.61/0.85          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.61/0.85          | ((X28) = (X31))
% 0.61/0.85          | ~ (r2_relset_1 @ X29 @ X30 @ X28 @ X31))),
% 0.61/0.85      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.61/0.85  thf('15', plain,
% 0.61/0.85      (![X0 : $i]:
% 0.61/0.85         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.61/0.85             (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ X0)
% 0.61/0.85          | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) = (X0))
% 0.61/0.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.61/0.85      inference('sup-', [status(thm)], ['13', '14'])).
% 0.61/0.85  thf('16', plain,
% 0.61/0.85      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 0.61/0.85           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.61/0.85        | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 0.61/0.85            = (k6_relat_1 @ sk_A)))),
% 0.61/0.85      inference('sup-', [status(thm)], ['4', '15'])).
% 0.61/0.85  thf(dt_k6_partfun1, axiom,
% 0.61/0.85    (![A:$i]:
% 0.61/0.85     ( ( m1_subset_1 @
% 0.61/0.85         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.61/0.85       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.61/0.85  thf('17', plain,
% 0.61/0.85      (![X41 : $i]:
% 0.61/0.85         (m1_subset_1 @ (k6_partfun1 @ X41) @ 
% 0.61/0.85          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))),
% 0.61/0.85      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.61/0.85  thf('18', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 0.61/0.85      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.61/0.85  thf('19', plain,
% 0.61/0.85      (![X41 : $i]:
% 0.61/0.85         (m1_subset_1 @ (k6_relat_1 @ X41) @ 
% 0.61/0.85          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))),
% 0.61/0.85      inference('demod', [status(thm)], ['17', '18'])).
% 0.61/0.85  thf('20', plain,
% 0.61/0.85      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 0.61/0.85         = (k6_relat_1 @ sk_A))),
% 0.61/0.85      inference('demod', [status(thm)], ['16', '19'])).
% 0.61/0.85  thf('21', plain,
% 0.61/0.85      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.61/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.85  thf(t24_funct_2, axiom,
% 0.61/0.85    (![A:$i,B:$i,C:$i]:
% 0.61/0.85     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.61/0.85         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.61/0.85       ( ![D:$i]:
% 0.61/0.85         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.61/0.85             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.61/0.85           ( ( r2_relset_1 @
% 0.61/0.85               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.61/0.85               ( k6_partfun1 @ B ) ) =>
% 0.61/0.85             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.61/0.85  thf('22', plain,
% 0.61/0.85      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.61/0.85         (~ (v1_funct_1 @ X43)
% 0.61/0.85          | ~ (v1_funct_2 @ X43 @ X44 @ X45)
% 0.61/0.85          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 0.61/0.85          | ~ (r2_relset_1 @ X44 @ X44 @ 
% 0.61/0.85               (k1_partfun1 @ X44 @ X45 @ X45 @ X44 @ X43 @ X46) @ 
% 0.61/0.85               (k6_partfun1 @ X44))
% 0.61/0.85          | ((k2_relset_1 @ X45 @ X44 @ X46) = (X44))
% 0.61/0.85          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 0.61/0.85          | ~ (v1_funct_2 @ X46 @ X45 @ X44)
% 0.61/0.85          | ~ (v1_funct_1 @ X46))),
% 0.61/0.85      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.61/0.85  thf('23', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 0.61/0.85      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.61/0.85  thf('24', plain,
% 0.61/0.85      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.61/0.85         (~ (v1_funct_1 @ X43)
% 0.61/0.85          | ~ (v1_funct_2 @ X43 @ X44 @ X45)
% 0.61/0.85          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 0.61/0.85          | ~ (r2_relset_1 @ X44 @ X44 @ 
% 0.61/0.85               (k1_partfun1 @ X44 @ X45 @ X45 @ X44 @ X43 @ X46) @ 
% 0.61/0.85               (k6_relat_1 @ X44))
% 0.61/0.85          | ((k2_relset_1 @ X45 @ X44 @ X46) = (X44))
% 0.61/0.85          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 0.61/0.85          | ~ (v1_funct_2 @ X46 @ X45 @ X44)
% 0.61/0.85          | ~ (v1_funct_1 @ X46))),
% 0.61/0.85      inference('demod', [status(thm)], ['22', '23'])).
% 0.61/0.85  thf('25', plain,
% 0.61/0.85      (![X0 : $i]:
% 0.61/0.85         (~ (v1_funct_1 @ X0)
% 0.61/0.85          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 0.61/0.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 0.61/0.85          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 0.61/0.85          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.61/0.85               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 0.61/0.85               (k6_relat_1 @ sk_A))
% 0.61/0.85          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 0.61/0.85          | ~ (v1_funct_1 @ sk_C))),
% 0.61/0.85      inference('sup-', [status(thm)], ['21', '24'])).
% 0.61/0.85  thf('26', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.61/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.85  thf('27', plain, ((v1_funct_1 @ sk_C)),
% 0.61/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.85  thf('28', plain,
% 0.61/0.85      (![X0 : $i]:
% 0.61/0.85         (~ (v1_funct_1 @ X0)
% 0.61/0.85          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 0.61/0.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 0.61/0.85          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 0.61/0.85          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.61/0.85               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 0.61/0.85               (k6_relat_1 @ sk_A)))),
% 0.61/0.85      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.61/0.85  thf('29', plain,
% 0.61/0.85      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 0.61/0.85           (k6_relat_1 @ sk_A))
% 0.61/0.85        | ((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (sk_A))
% 0.61/0.85        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 0.61/0.85        | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 0.61/0.85        | ~ (v1_funct_1 @ sk_D))),
% 0.61/0.85      inference('sup-', [status(thm)], ['20', '28'])).
% 0.61/0.85  thf('30', plain,
% 0.61/0.85      (![X41 : $i]:
% 0.61/0.85         (m1_subset_1 @ (k6_relat_1 @ X41) @ 
% 0.61/0.85          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))),
% 0.61/0.85      inference('demod', [status(thm)], ['17', '18'])).
% 0.61/0.85  thf('31', plain,
% 0.61/0.85      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.61/0.85         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.61/0.85          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.61/0.85          | (r2_relset_1 @ X29 @ X30 @ X28 @ X31)
% 0.61/0.85          | ((X28) != (X31)))),
% 0.61/0.85      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.61/0.85  thf('32', plain,
% 0.61/0.85      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.61/0.85         ((r2_relset_1 @ X29 @ X30 @ X31 @ X31)
% 0.61/0.85          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.61/0.85      inference('simplify', [status(thm)], ['31'])).
% 0.61/0.85  thf('33', plain,
% 0.61/0.85      (![X0 : $i]:
% 0.61/0.85         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.61/0.85      inference('sup-', [status(thm)], ['30', '32'])).
% 0.61/0.85  thf('34', plain,
% 0.61/0.85      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.61/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.85  thf(redefinition_k2_relset_1, axiom,
% 0.61/0.85    (![A:$i,B:$i,C:$i]:
% 0.61/0.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.85       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.61/0.85  thf('35', plain,
% 0.61/0.85      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.61/0.85         (((k2_relset_1 @ X26 @ X27 @ X25) = (k2_relat_1 @ X25))
% 0.61/0.85          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.61/0.85      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.61/0.85  thf('36', plain,
% 0.61/0.85      (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.61/0.85      inference('sup-', [status(thm)], ['34', '35'])).
% 0.61/0.85  thf('37', plain,
% 0.61/0.85      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.61/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.85  thf('38', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 0.61/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.85  thf('39', plain, ((v1_funct_1 @ sk_D)),
% 0.61/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.85  thf('40', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.61/0.85      inference('demod', [status(thm)], ['29', '33', '36', '37', '38', '39'])).
% 0.61/0.85  thf(d3_funct_2, axiom,
% 0.61/0.85    (![A:$i,B:$i]:
% 0.61/0.85     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.61/0.85       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.61/0.85  thf('41', plain,
% 0.61/0.85      (![X32 : $i, X33 : $i]:
% 0.61/0.85         (((k2_relat_1 @ X33) != (X32))
% 0.61/0.85          | (v2_funct_2 @ X33 @ X32)
% 0.61/0.85          | ~ (v5_relat_1 @ X33 @ X32)
% 0.61/0.85          | ~ (v1_relat_1 @ X33))),
% 0.61/0.85      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.61/0.85  thf('42', plain,
% 0.61/0.85      (![X33 : $i]:
% 0.61/0.85         (~ (v1_relat_1 @ X33)
% 0.61/0.85          | ~ (v5_relat_1 @ X33 @ (k2_relat_1 @ X33))
% 0.61/0.85          | (v2_funct_2 @ X33 @ (k2_relat_1 @ X33)))),
% 0.61/0.85      inference('simplify', [status(thm)], ['41'])).
% 0.61/0.85  thf('43', plain,
% 0.61/0.85      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 0.61/0.85        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 0.61/0.85        | ~ (v1_relat_1 @ sk_D))),
% 0.61/0.85      inference('sup-', [status(thm)], ['40', '42'])).
% 0.61/0.85  thf('44', plain,
% 0.61/0.85      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.61/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.85  thf(cc2_relset_1, axiom,
% 0.61/0.85    (![A:$i,B:$i,C:$i]:
% 0.61/0.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.85       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.61/0.85  thf('45', plain,
% 0.61/0.85      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.61/0.85         ((v5_relat_1 @ X19 @ X21)
% 0.61/0.85          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.61/0.85      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.61/0.85  thf('46', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 0.61/0.85      inference('sup-', [status(thm)], ['44', '45'])).
% 0.61/0.85  thf('47', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.61/0.85      inference('demod', [status(thm)], ['29', '33', '36', '37', '38', '39'])).
% 0.61/0.85  thf('48', plain,
% 0.61/0.85      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.61/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.85  thf(cc1_relset_1, axiom,
% 0.61/0.85    (![A:$i,B:$i,C:$i]:
% 0.61/0.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.85       ( v1_relat_1 @ C ) ))).
% 0.61/0.85  thf('49', plain,
% 0.61/0.85      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.61/0.85         ((v1_relat_1 @ X16)
% 0.61/0.85          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.61/0.85      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.61/0.85  thf('50', plain, ((v1_relat_1 @ sk_D)),
% 0.61/0.85      inference('sup-', [status(thm)], ['48', '49'])).
% 0.61/0.85  thf('51', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 0.61/0.85      inference('demod', [status(thm)], ['43', '46', '47', '50'])).
% 0.61/0.85  thf('52', plain,
% 0.61/0.85      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 0.61/0.85      inference('split', [status(esa)], ['0'])).
% 0.61/0.85  thf('53', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 0.61/0.85      inference('sup-', [status(thm)], ['51', '52'])).
% 0.61/0.85  thf('54', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 0.61/0.85      inference('split', [status(esa)], ['0'])).
% 0.61/0.85  thf('55', plain, (~ ((v2_funct_1 @ sk_C))),
% 0.61/0.85      inference('sat_resolution*', [status(thm)], ['53', '54'])).
% 0.61/0.85  thf('56', plain, (~ (v2_funct_1 @ sk_C)),
% 0.61/0.85      inference('simpl_trail', [status(thm)], ['1', '55'])).
% 0.61/0.85  thf('57', plain,
% 0.61/0.85      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.61/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.85  thf('58', plain,
% 0.61/0.85      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.61/0.85         ((v1_relat_1 @ X16)
% 0.61/0.85          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.61/0.85      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.61/0.85  thf('59', plain, ((v1_relat_1 @ sk_C)),
% 0.61/0.85      inference('sup-', [status(thm)], ['57', '58'])).
% 0.61/0.85  thf(cc1_funct_1, axiom,
% 0.61/0.85    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 0.61/0.85  thf('60', plain, (![X10 : $i]: ((v1_funct_1 @ X10) | ~ (v1_xboole_0 @ X10))),
% 0.61/0.85      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.61/0.85  thf(cc2_funct_1, axiom,
% 0.61/0.85    (![A:$i]:
% 0.61/0.85     ( ( ( v1_xboole_0 @ A ) & ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.61/0.85       ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) ))).
% 0.61/0.85  thf('61', plain,
% 0.61/0.85      (![X11 : $i]:
% 0.61/0.85         ((v2_funct_1 @ X11)
% 0.61/0.85          | ~ (v1_funct_1 @ X11)
% 0.61/0.85          | ~ (v1_relat_1 @ X11)
% 0.61/0.85          | ~ (v1_xboole_0 @ X11))),
% 0.61/0.85      inference('cnf', [status(esa)], [cc2_funct_1])).
% 0.61/0.85  thf('62', plain,
% 0.61/0.85      (![X0 : $i]:
% 0.61/0.85         (~ (v1_xboole_0 @ X0)
% 0.61/0.85          | ~ (v1_xboole_0 @ X0)
% 0.61/0.85          | ~ (v1_relat_1 @ X0)
% 0.61/0.85          | (v2_funct_1 @ X0))),
% 0.61/0.85      inference('sup-', [status(thm)], ['60', '61'])).
% 0.61/0.85  thf('63', plain,
% 0.61/0.85      (![X0 : $i]:
% 0.61/0.85         ((v2_funct_1 @ X0) | ~ (v1_relat_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.61/0.85      inference('simplify', [status(thm)], ['62'])).
% 0.61/0.85  thf('64', plain, ((~ (v1_xboole_0 @ sk_C) | (v2_funct_1 @ sk_C))),
% 0.61/0.85      inference('sup-', [status(thm)], ['59', '63'])).
% 0.61/0.85  thf('65', plain,
% 0.61/0.85      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.61/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.85  thf(cc3_relset_1, axiom,
% 0.61/0.85    (![A:$i,B:$i]:
% 0.61/0.85     ( ( v1_xboole_0 @ A ) =>
% 0.61/0.85       ( ![C:$i]:
% 0.61/0.85         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.85           ( v1_xboole_0 @ C ) ) ) ))).
% 0.61/0.85  thf('66', plain,
% 0.61/0.85      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.61/0.85         (~ (v1_xboole_0 @ X22)
% 0.61/0.85          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X24)))
% 0.61/0.85          | (v1_xboole_0 @ X23))),
% 0.61/0.85      inference('cnf', [status(esa)], [cc3_relset_1])).
% 0.61/0.85  thf('67', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 0.61/0.85      inference('sup-', [status(thm)], ['65', '66'])).
% 0.61/0.85  thf('68', plain,
% 0.61/0.85      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 0.61/0.85         = (k6_relat_1 @ sk_A))),
% 0.61/0.85      inference('demod', [status(thm)], ['16', '19'])).
% 0.61/0.85  thf('69', plain,
% 0.61/0.85      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.61/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.85  thf(t26_funct_2, axiom,
% 0.61/0.85    (![A:$i,B:$i,C:$i,D:$i]:
% 0.61/0.85     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.61/0.85         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.61/0.85       ( ![E:$i]:
% 0.61/0.85         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.61/0.85             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.61/0.85           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 0.61/0.85             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 0.61/0.85               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 0.61/0.85  thf('70', plain,
% 0.61/0.85      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 0.61/0.85         (~ (v1_funct_1 @ X47)
% 0.61/0.85          | ~ (v1_funct_2 @ X47 @ X48 @ X49)
% 0.61/0.85          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 0.61/0.85          | ~ (v2_funct_1 @ (k1_partfun1 @ X50 @ X48 @ X48 @ X49 @ X51 @ X47))
% 0.61/0.85          | (v2_funct_1 @ X51)
% 0.61/0.85          | ((X49) = (k1_xboole_0))
% 0.61/0.85          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X48)))
% 0.61/0.85          | ~ (v1_funct_2 @ X51 @ X50 @ X48)
% 0.61/0.85          | ~ (v1_funct_1 @ X51))),
% 0.61/0.85      inference('cnf', [status(esa)], [t26_funct_2])).
% 0.61/0.85  thf('71', plain,
% 0.61/0.85      (![X0 : $i, X1 : $i]:
% 0.61/0.85         (~ (v1_funct_1 @ X0)
% 0.61/0.85          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 0.61/0.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 0.61/0.85          | ((sk_A) = (k1_xboole_0))
% 0.61/0.85          | (v2_funct_1 @ X0)
% 0.61/0.85          | ~ (v2_funct_1 @ 
% 0.61/0.85               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D))
% 0.61/0.85          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 0.61/0.85          | ~ (v1_funct_1 @ sk_D))),
% 0.61/0.85      inference('sup-', [status(thm)], ['69', '70'])).
% 0.61/0.85  thf('72', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 0.61/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.85  thf('73', plain, ((v1_funct_1 @ sk_D)),
% 0.61/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.85  thf('74', plain,
% 0.61/0.85      (![X0 : $i, X1 : $i]:
% 0.61/0.85         (~ (v1_funct_1 @ X0)
% 0.61/0.85          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 0.61/0.86          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 0.61/0.86          | ((sk_A) = (k1_xboole_0))
% 0.61/0.86          | (v2_funct_1 @ X0)
% 0.61/0.86          | ~ (v2_funct_1 @ 
% 0.61/0.86               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D)))),
% 0.61/0.86      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.61/0.86  thf('75', plain,
% 0.61/0.86      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 0.61/0.86        | (v2_funct_1 @ sk_C)
% 0.61/0.86        | ((sk_A) = (k1_xboole_0))
% 0.61/0.86        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.61/0.86        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 0.61/0.86        | ~ (v1_funct_1 @ sk_C))),
% 0.61/0.86      inference('sup-', [status(thm)], ['68', '74'])).
% 0.61/0.86  thf(fc4_funct_1, axiom,
% 0.61/0.86    (![A:$i]:
% 0.61/0.86     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.61/0.86       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.61/0.86  thf('76', plain, (![X13 : $i]: (v2_funct_1 @ (k6_relat_1 @ X13))),
% 0.61/0.86      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.61/0.86  thf('77', plain,
% 0.61/0.86      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.61/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.86  thf('78', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.61/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.86  thf('79', plain, ((v1_funct_1 @ sk_C)),
% 0.61/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.86  thf('80', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.61/0.86      inference('demod', [status(thm)], ['75', '76', '77', '78', '79'])).
% 0.61/0.86  thf('81', plain, (~ (v2_funct_1 @ sk_C)),
% 0.61/0.86      inference('simpl_trail', [status(thm)], ['1', '55'])).
% 0.61/0.86  thf('82', plain, (((sk_A) = (k1_xboole_0))),
% 0.61/0.86      inference('clc', [status(thm)], ['80', '81'])).
% 0.61/0.86  thf(l222_relat_1, axiom,
% 0.61/0.86    (![A:$i,B:$i]:
% 0.61/0.86     ( ( v5_relat_1 @ k1_xboole_0 @ B ) & ( v4_relat_1 @ k1_xboole_0 @ A ) ))).
% 0.61/0.86  thf('83', plain, (![X8 : $i]: (v5_relat_1 @ k1_xboole_0 @ X8)),
% 0.61/0.86      inference('cnf', [status(esa)], [l222_relat_1])).
% 0.61/0.86  thf(d19_relat_1, axiom,
% 0.61/0.86    (![A:$i,B:$i]:
% 0.61/0.86     ( ( v1_relat_1 @ B ) =>
% 0.61/0.86       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.61/0.86  thf('84', plain,
% 0.61/0.86      (![X6 : $i, X7 : $i]:
% 0.61/0.86         (~ (v5_relat_1 @ X6 @ X7)
% 0.61/0.86          | (r1_tarski @ (k2_relat_1 @ X6) @ X7)
% 0.61/0.86          | ~ (v1_relat_1 @ X6))),
% 0.61/0.86      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.61/0.86  thf('85', plain,
% 0.61/0.86      (![X0 : $i]:
% 0.61/0.86         (~ (v1_relat_1 @ k1_xboole_0)
% 0.61/0.86          | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0))),
% 0.61/0.86      inference('sup-', [status(thm)], ['83', '84'])).
% 0.61/0.86  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.61/0.86  thf('86', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.61/0.86      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.61/0.86  thf('87', plain, (![X12 : $i]: (v1_relat_1 @ (k6_relat_1 @ X12))),
% 0.61/0.86      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.61/0.86  thf('88', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.61/0.86      inference('sup+', [status(thm)], ['86', '87'])).
% 0.61/0.86  thf('89', plain, (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)),
% 0.61/0.86      inference('demod', [status(thm)], ['85', '88'])).
% 0.61/0.86  thf(d1_xboole_0, axiom,
% 0.61/0.86    (![A:$i]:
% 0.61/0.86     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.61/0.86  thf('90', plain,
% 0.61/0.86      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.61/0.86      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.61/0.86  thf(t7_ordinal1, axiom,
% 0.61/0.86    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.61/0.86  thf('91', plain,
% 0.61/0.86      (![X14 : $i, X15 : $i]:
% 0.61/0.86         (~ (r2_hidden @ X14 @ X15) | ~ (r1_tarski @ X15 @ X14))),
% 0.61/0.86      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.61/0.86  thf('92', plain,
% 0.61/0.86      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.61/0.86      inference('sup-', [status(thm)], ['90', '91'])).
% 0.61/0.86  thf('93', plain, ((v1_xboole_0 @ (k2_relat_1 @ k1_xboole_0))),
% 0.61/0.86      inference('sup-', [status(thm)], ['89', '92'])).
% 0.61/0.86  thf('94', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.61/0.86      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.61/0.86  thf('95', plain,
% 0.61/0.86      (![X41 : $i]:
% 0.61/0.86         (m1_subset_1 @ (k6_relat_1 @ X41) @ 
% 0.61/0.86          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))),
% 0.61/0.86      inference('demod', [status(thm)], ['17', '18'])).
% 0.61/0.86  thf('96', plain,
% 0.61/0.86      ((m1_subset_1 @ k1_xboole_0 @ 
% 0.61/0.86        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.61/0.86      inference('sup+', [status(thm)], ['94', '95'])).
% 0.61/0.86  thf(t113_zfmisc_1, axiom,
% 0.61/0.86    (![A:$i,B:$i]:
% 0.61/0.86     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.61/0.86       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.61/0.86  thf('97', plain,
% 0.61/0.86      (![X4 : $i, X5 : $i]:
% 0.61/0.86         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 0.61/0.86      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.61/0.86  thf('98', plain,
% 0.61/0.86      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.61/0.86      inference('simplify', [status(thm)], ['97'])).
% 0.61/0.86  thf('99', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.61/0.86      inference('demod', [status(thm)], ['96', '98'])).
% 0.61/0.86  thf('100', plain,
% 0.61/0.86      (![X4 : $i, X5 : $i]:
% 0.61/0.86         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.61/0.86      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.61/0.86  thf('101', plain,
% 0.61/0.86      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.61/0.86      inference('simplify', [status(thm)], ['100'])).
% 0.61/0.86  thf('102', plain,
% 0.61/0.86      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.61/0.86         (~ (v1_xboole_0 @ X22)
% 0.61/0.86          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X24)))
% 0.61/0.86          | (v1_xboole_0 @ X23))),
% 0.61/0.86      inference('cnf', [status(esa)], [cc3_relset_1])).
% 0.61/0.86  thf('103', plain,
% 0.61/0.86      (![X0 : $i, X1 : $i]:
% 0.61/0.86         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.61/0.86          | (v1_xboole_0 @ X1)
% 0.61/0.86          | ~ (v1_xboole_0 @ X0))),
% 0.61/0.86      inference('sup-', [status(thm)], ['101', '102'])).
% 0.61/0.86  thf('104', plain,
% 0.61/0.86      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ k1_xboole_0))),
% 0.61/0.86      inference('sup-', [status(thm)], ['99', '103'])).
% 0.61/0.86  thf('105', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.61/0.86      inference('sup-', [status(thm)], ['93', '104'])).
% 0.61/0.86  thf('106', plain, ((v1_xboole_0 @ sk_C)),
% 0.61/0.86      inference('demod', [status(thm)], ['67', '82', '105'])).
% 0.61/0.86  thf('107', plain, ((v2_funct_1 @ sk_C)),
% 0.61/0.86      inference('demod', [status(thm)], ['64', '106'])).
% 0.61/0.86  thf('108', plain, ($false), inference('demod', [status(thm)], ['56', '107'])).
% 0.61/0.86  
% 0.61/0.86  % SZS output end Refutation
% 0.61/0.86  
% 0.71/0.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

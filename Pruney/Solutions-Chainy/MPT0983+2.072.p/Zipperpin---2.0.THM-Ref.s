%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PBVojwBeAz

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:12 EST 2020

% Result     : Theorem 4.12s
% Output     : Refutation 4.12s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 579 expanded)
%              Number of leaves         :   44 ( 190 expanded)
%              Depth                    :   14
%              Number of atoms          : 1278 (11038 expanded)
%              Number of equality atoms :   51 ( 178 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

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
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('4',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('6',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( r2_relset_1 @ X43 @ X43 @ ( k1_partfun1 @ X43 @ X44 @ X44 @ X43 @ X42 @ X45 ) @ ( k6_partfun1 @ X43 ) )
      | ( ( k2_relset_1 @ X44 @ X43 @ X45 )
        = X43 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X45 @ X44 @ X43 )
      | ~ ( v1_funct_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('7',plain,(
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('8',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( r2_relset_1 @ X43 @ X43 @ ( k1_partfun1 @ X43 @ X44 @ X44 @ X43 @ X42 @ X45 ) @ ( k6_relat_1 @ X43 ) )
      | ( ( k2_relset_1 @ X44 @ X43 @ X45 )
        = X43 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X45 @ X44 @ X43 )
      | ~ ( v1_funct_1 @ X45 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['4','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('15',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('16',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['13','16','17','18','19'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('21',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k2_relat_1 @ X32 )
       != X31 )
      | ( v2_funct_2 @ X32 @ X31 )
      | ~ ( v5_relat_1 @ X32 @ X31 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('22',plain,(
    ! [X32: $i] :
      ( ~ ( v1_relat_1 @ X32 )
      | ~ ( v5_relat_1 @ X32 @ ( k2_relat_1 @ X32 ) )
      | ( v2_funct_2 @ X32 @ ( k2_relat_1 @ X32 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('25',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v5_relat_1 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('26',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['13','16','17','18','19'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('29',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('30',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['23','26','27','30'])).

thf('32',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('38',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('39',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C_1 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('43',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
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

thf('45',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf('50',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','53'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('55',plain,(
    ! [X40: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('56',plain,(
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('57',plain,(
    ! [X40: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X40 ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['54','57'])).

thf('59',plain,(
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

thf('60',plain,(
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

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['58','64'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('66',plain,(
    ! [X17: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('67',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v2_funct_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66','67','68','69'])).

thf('71',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','35'])).

thf('72',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['70','71'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('73',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('74',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['73'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('75',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('76',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('77',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X40: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X40 ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('79',plain,(
    m1_subset_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('80',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k6_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('82',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('83',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k6_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('85',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('86',plain,(
    r1_tarski @ ( k6_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('88',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('89',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('91',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','93'])).

thf('95',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( k6_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['86','96'])).

thf('98',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('99',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['75','100'])).

thf('102',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['70','71'])).

thf('103',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('104',plain,(
    k1_xboole_0 = sk_C_1 ),
    inference(demod,[status(thm)],['41','72','74','101','102','103'])).

thf('105',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['97','98'])).

thf('106',plain,(
    ! [X17: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('107',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    $false ),
    inference(demod,[status(thm)],['36','104','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PBVojwBeAz
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:50:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.12/4.30  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.12/4.30  % Solved by: fo/fo7.sh
% 4.12/4.30  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.12/4.30  % done 6032 iterations in 3.837s
% 4.12/4.30  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.12/4.30  % SZS output start Refutation
% 4.12/4.30  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 4.12/4.30  thf(sk_B_type, type, sk_B: $i).
% 4.12/4.30  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 4.12/4.30  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.12/4.30  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.12/4.30  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.12/4.30  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 4.12/4.30  thf(sk_D_type, type, sk_D: $i).
% 4.12/4.30  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 4.12/4.30  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.12/4.30  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.12/4.30  thf(sk_C_1_type, type, sk_C_1: $i).
% 4.12/4.30  thf(sk_A_type, type, sk_A: $i).
% 4.12/4.30  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 4.12/4.30  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 4.12/4.30  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.12/4.30  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.12/4.30  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 4.12/4.30  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.12/4.30  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.12/4.30  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 4.12/4.30  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 4.12/4.30  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.12/4.30  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.12/4.30  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.12/4.30  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 4.12/4.30  thf(t29_funct_2, conjecture,
% 4.12/4.30    (![A:$i,B:$i,C:$i]:
% 4.12/4.30     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.12/4.30         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.12/4.30       ( ![D:$i]:
% 4.12/4.30         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.12/4.30             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.12/4.30           ( ( r2_relset_1 @
% 4.12/4.30               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 4.12/4.30               ( k6_partfun1 @ A ) ) =>
% 4.12/4.30             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 4.12/4.30  thf(zf_stmt_0, negated_conjecture,
% 4.12/4.30    (~( ![A:$i,B:$i,C:$i]:
% 4.12/4.30        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.12/4.30            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.12/4.30          ( ![D:$i]:
% 4.12/4.30            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.12/4.30                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.12/4.30              ( ( r2_relset_1 @
% 4.12/4.30                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 4.12/4.30                  ( k6_partfun1 @ A ) ) =>
% 4.12/4.30                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 4.12/4.30    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 4.12/4.30  thf('0', plain, ((~ (v2_funct_1 @ sk_C_1) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 4.12/4.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.30  thf('1', plain, ((~ (v2_funct_1 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 4.12/4.30      inference('split', [status(esa)], ['0'])).
% 4.12/4.30  thf('2', plain,
% 4.12/4.30      ((r2_relset_1 @ sk_A @ sk_A @ 
% 4.12/4.30        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ 
% 4.12/4.30        (k6_partfun1 @ sk_A))),
% 4.12/4.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.30  thf(redefinition_k6_partfun1, axiom,
% 4.12/4.30    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 4.12/4.30  thf('3', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 4.12/4.30      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.12/4.30  thf('4', plain,
% 4.12/4.30      ((r2_relset_1 @ sk_A @ sk_A @ 
% 4.12/4.30        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ 
% 4.12/4.30        (k6_relat_1 @ sk_A))),
% 4.12/4.30      inference('demod', [status(thm)], ['2', '3'])).
% 4.12/4.30  thf('5', plain,
% 4.12/4.30      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.12/4.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.30  thf(t24_funct_2, axiom,
% 4.12/4.30    (![A:$i,B:$i,C:$i]:
% 4.12/4.30     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.12/4.30         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.12/4.30       ( ![D:$i]:
% 4.12/4.30         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.12/4.30             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.12/4.30           ( ( r2_relset_1 @
% 4.12/4.30               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 4.12/4.30               ( k6_partfun1 @ B ) ) =>
% 4.12/4.30             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 4.12/4.30  thf('6', plain,
% 4.12/4.30      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 4.12/4.30         (~ (v1_funct_1 @ X42)
% 4.12/4.30          | ~ (v1_funct_2 @ X42 @ X43 @ X44)
% 4.12/4.30          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 4.12/4.30          | ~ (r2_relset_1 @ X43 @ X43 @ 
% 4.12/4.30               (k1_partfun1 @ X43 @ X44 @ X44 @ X43 @ X42 @ X45) @ 
% 4.12/4.30               (k6_partfun1 @ X43))
% 4.12/4.30          | ((k2_relset_1 @ X44 @ X43 @ X45) = (X43))
% 4.12/4.30          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43)))
% 4.12/4.30          | ~ (v1_funct_2 @ X45 @ X44 @ X43)
% 4.12/4.30          | ~ (v1_funct_1 @ X45))),
% 4.12/4.30      inference('cnf', [status(esa)], [t24_funct_2])).
% 4.12/4.30  thf('7', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 4.12/4.30      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.12/4.30  thf('8', plain,
% 4.12/4.30      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 4.12/4.30         (~ (v1_funct_1 @ X42)
% 4.12/4.30          | ~ (v1_funct_2 @ X42 @ X43 @ X44)
% 4.12/4.30          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 4.12/4.30          | ~ (r2_relset_1 @ X43 @ X43 @ 
% 4.12/4.30               (k1_partfun1 @ X43 @ X44 @ X44 @ X43 @ X42 @ X45) @ 
% 4.12/4.30               (k6_relat_1 @ X43))
% 4.12/4.30          | ((k2_relset_1 @ X44 @ X43 @ X45) = (X43))
% 4.12/4.30          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43)))
% 4.12/4.30          | ~ (v1_funct_2 @ X45 @ X44 @ X43)
% 4.12/4.30          | ~ (v1_funct_1 @ X45))),
% 4.12/4.30      inference('demod', [status(thm)], ['6', '7'])).
% 4.12/4.30  thf('9', plain,
% 4.12/4.30      (![X0 : $i]:
% 4.12/4.30         (~ (v1_funct_1 @ X0)
% 4.12/4.30          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 4.12/4.30          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 4.12/4.30          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 4.12/4.30          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 4.12/4.30               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 4.12/4.30               (k6_relat_1 @ sk_A))
% 4.12/4.30          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)
% 4.12/4.30          | ~ (v1_funct_1 @ sk_C_1))),
% 4.12/4.30      inference('sup-', [status(thm)], ['5', '8'])).
% 4.12/4.30  thf('10', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 4.12/4.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.30  thf('11', plain, ((v1_funct_1 @ sk_C_1)),
% 4.12/4.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.30  thf('12', plain,
% 4.12/4.30      (![X0 : $i]:
% 4.12/4.30         (~ (v1_funct_1 @ X0)
% 4.12/4.30          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 4.12/4.30          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 4.12/4.30          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 4.12/4.30          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 4.12/4.30               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ X0) @ 
% 4.12/4.30               (k6_relat_1 @ sk_A)))),
% 4.12/4.30      inference('demod', [status(thm)], ['9', '10', '11'])).
% 4.12/4.30  thf('13', plain,
% 4.12/4.30      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 4.12/4.30        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 4.12/4.30        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 4.12/4.30        | ~ (v1_funct_1 @ sk_D))),
% 4.12/4.30      inference('sup-', [status(thm)], ['4', '12'])).
% 4.12/4.30  thf('14', plain,
% 4.12/4.30      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.12/4.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.30  thf(redefinition_k2_relset_1, axiom,
% 4.12/4.30    (![A:$i,B:$i,C:$i]:
% 4.12/4.30     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.12/4.30       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 4.12/4.30  thf('15', plain,
% 4.12/4.30      (![X24 : $i, X25 : $i, X26 : $i]:
% 4.12/4.30         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 4.12/4.30          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 4.12/4.30      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.12/4.30  thf('16', plain,
% 4.12/4.30      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 4.12/4.30      inference('sup-', [status(thm)], ['14', '15'])).
% 4.12/4.30  thf('17', plain,
% 4.12/4.30      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.12/4.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.30  thf('18', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 4.12/4.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.30  thf('19', plain, ((v1_funct_1 @ sk_D)),
% 4.12/4.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.30  thf('20', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 4.12/4.30      inference('demod', [status(thm)], ['13', '16', '17', '18', '19'])).
% 4.12/4.30  thf(d3_funct_2, axiom,
% 4.12/4.30    (![A:$i,B:$i]:
% 4.12/4.30     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 4.12/4.30       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 4.12/4.30  thf('21', plain,
% 4.12/4.30      (![X31 : $i, X32 : $i]:
% 4.12/4.30         (((k2_relat_1 @ X32) != (X31))
% 4.12/4.30          | (v2_funct_2 @ X32 @ X31)
% 4.12/4.30          | ~ (v5_relat_1 @ X32 @ X31)
% 4.12/4.30          | ~ (v1_relat_1 @ X32))),
% 4.12/4.30      inference('cnf', [status(esa)], [d3_funct_2])).
% 4.12/4.30  thf('22', plain,
% 4.12/4.30      (![X32 : $i]:
% 4.12/4.30         (~ (v1_relat_1 @ X32)
% 4.12/4.30          | ~ (v5_relat_1 @ X32 @ (k2_relat_1 @ X32))
% 4.12/4.30          | (v2_funct_2 @ X32 @ (k2_relat_1 @ X32)))),
% 4.12/4.30      inference('simplify', [status(thm)], ['21'])).
% 4.12/4.30  thf('23', plain,
% 4.12/4.30      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 4.12/4.30        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 4.12/4.30        | ~ (v1_relat_1 @ sk_D))),
% 4.12/4.30      inference('sup-', [status(thm)], ['20', '22'])).
% 4.12/4.30  thf('24', plain,
% 4.12/4.30      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.12/4.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.30  thf(cc2_relset_1, axiom,
% 4.12/4.30    (![A:$i,B:$i,C:$i]:
% 4.12/4.30     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.12/4.30       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 4.12/4.30  thf('25', plain,
% 4.12/4.30      (![X21 : $i, X22 : $i, X23 : $i]:
% 4.12/4.30         ((v5_relat_1 @ X21 @ X23)
% 4.12/4.30          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 4.12/4.30      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.12/4.30  thf('26', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 4.12/4.30      inference('sup-', [status(thm)], ['24', '25'])).
% 4.12/4.30  thf('27', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 4.12/4.30      inference('demod', [status(thm)], ['13', '16', '17', '18', '19'])).
% 4.12/4.30  thf('28', plain,
% 4.12/4.30      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.12/4.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.30  thf(cc1_relset_1, axiom,
% 4.12/4.30    (![A:$i,B:$i,C:$i]:
% 4.12/4.30     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.12/4.30       ( v1_relat_1 @ C ) ))).
% 4.12/4.30  thf('29', plain,
% 4.12/4.30      (![X18 : $i, X19 : $i, X20 : $i]:
% 4.12/4.30         ((v1_relat_1 @ X18)
% 4.12/4.30          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 4.12/4.30      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.12/4.30  thf('30', plain, ((v1_relat_1 @ sk_D)),
% 4.12/4.30      inference('sup-', [status(thm)], ['28', '29'])).
% 4.12/4.30  thf('31', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 4.12/4.30      inference('demod', [status(thm)], ['23', '26', '27', '30'])).
% 4.12/4.30  thf('32', plain,
% 4.12/4.30      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 4.12/4.30      inference('split', [status(esa)], ['0'])).
% 4.12/4.30  thf('33', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 4.12/4.30      inference('sup-', [status(thm)], ['31', '32'])).
% 4.12/4.30  thf('34', plain,
% 4.12/4.30      (~ ((v2_funct_1 @ sk_C_1)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 4.12/4.30      inference('split', [status(esa)], ['0'])).
% 4.12/4.30  thf('35', plain, (~ ((v2_funct_1 @ sk_C_1))),
% 4.12/4.30      inference('sat_resolution*', [status(thm)], ['33', '34'])).
% 4.12/4.30  thf('36', plain, (~ (v2_funct_1 @ sk_C_1)),
% 4.12/4.30      inference('simpl_trail', [status(thm)], ['1', '35'])).
% 4.12/4.30  thf('37', plain,
% 4.12/4.30      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.12/4.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.30  thf(t3_subset, axiom,
% 4.12/4.30    (![A:$i,B:$i]:
% 4.12/4.30     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.12/4.30  thf('38', plain,
% 4.12/4.30      (![X10 : $i, X11 : $i]:
% 4.12/4.30         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 4.12/4.30      inference('cnf', [status(esa)], [t3_subset])).
% 4.12/4.30  thf('39', plain, ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 4.12/4.30      inference('sup-', [status(thm)], ['37', '38'])).
% 4.12/4.30  thf(d10_xboole_0, axiom,
% 4.12/4.30    (![A:$i,B:$i]:
% 4.12/4.30     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.12/4.30  thf('40', plain,
% 4.12/4.30      (![X4 : $i, X6 : $i]:
% 4.12/4.30         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 4.12/4.30      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.12/4.30  thf('41', plain,
% 4.12/4.30      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C_1)
% 4.12/4.30        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 4.12/4.30      inference('sup-', [status(thm)], ['39', '40'])).
% 4.12/4.30  thf('42', plain,
% 4.12/4.30      ((r2_relset_1 @ sk_A @ sk_A @ 
% 4.12/4.30        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ 
% 4.12/4.30        (k6_relat_1 @ sk_A))),
% 4.12/4.30      inference('demod', [status(thm)], ['2', '3'])).
% 4.12/4.30  thf('43', plain,
% 4.12/4.30      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.12/4.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.30  thf('44', plain,
% 4.12/4.30      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.12/4.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.30  thf(dt_k1_partfun1, axiom,
% 4.12/4.30    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.12/4.30     ( ( ( v1_funct_1 @ E ) & 
% 4.12/4.30         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.12/4.30         ( v1_funct_1 @ F ) & 
% 4.12/4.30         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 4.12/4.30       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 4.12/4.30         ( m1_subset_1 @
% 4.12/4.30           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 4.12/4.30           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 4.12/4.30  thf('45', plain,
% 4.12/4.30      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 4.12/4.30         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 4.12/4.30          | ~ (v1_funct_1 @ X33)
% 4.12/4.30          | ~ (v1_funct_1 @ X36)
% 4.12/4.30          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 4.12/4.30          | (m1_subset_1 @ (k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36) @ 
% 4.12/4.30             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X38))))),
% 4.12/4.30      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 4.12/4.30  thf('46', plain,
% 4.12/4.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.12/4.30         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 4.12/4.30           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 4.12/4.30          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 4.12/4.30          | ~ (v1_funct_1 @ X1)
% 4.12/4.30          | ~ (v1_funct_1 @ sk_C_1))),
% 4.12/4.30      inference('sup-', [status(thm)], ['44', '45'])).
% 4.12/4.30  thf('47', plain, ((v1_funct_1 @ sk_C_1)),
% 4.12/4.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.30  thf('48', plain,
% 4.12/4.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.12/4.30         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 4.12/4.30           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 4.12/4.30          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 4.12/4.30          | ~ (v1_funct_1 @ X1))),
% 4.12/4.30      inference('demod', [status(thm)], ['46', '47'])).
% 4.12/4.30  thf('49', plain,
% 4.12/4.30      ((~ (v1_funct_1 @ sk_D)
% 4.12/4.30        | (m1_subset_1 @ 
% 4.12/4.30           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ 
% 4.12/4.30           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 4.12/4.30      inference('sup-', [status(thm)], ['43', '48'])).
% 4.12/4.30  thf('50', plain, ((v1_funct_1 @ sk_D)),
% 4.12/4.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.30  thf('51', plain,
% 4.12/4.30      ((m1_subset_1 @ 
% 4.12/4.30        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ 
% 4.12/4.30        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.12/4.30      inference('demod', [status(thm)], ['49', '50'])).
% 4.12/4.30  thf(redefinition_r2_relset_1, axiom,
% 4.12/4.30    (![A:$i,B:$i,C:$i,D:$i]:
% 4.12/4.30     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.12/4.30         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.12/4.30       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 4.12/4.30  thf('52', plain,
% 4.12/4.30      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 4.12/4.30         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 4.12/4.30          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 4.12/4.30          | ((X27) = (X30))
% 4.12/4.30          | ~ (r2_relset_1 @ X28 @ X29 @ X27 @ X30))),
% 4.12/4.30      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 4.12/4.30  thf('53', plain,
% 4.12/4.30      (![X0 : $i]:
% 4.12/4.30         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 4.12/4.30             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D) @ X0)
% 4.12/4.30          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D) = (X0))
% 4.12/4.30          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 4.12/4.30      inference('sup-', [status(thm)], ['51', '52'])).
% 4.12/4.30  thf('54', plain,
% 4.12/4.30      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 4.12/4.30           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 4.12/4.30        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D)
% 4.12/4.30            = (k6_relat_1 @ sk_A)))),
% 4.12/4.30      inference('sup-', [status(thm)], ['42', '53'])).
% 4.12/4.30  thf(dt_k6_partfun1, axiom,
% 4.12/4.30    (![A:$i]:
% 4.12/4.30     ( ( m1_subset_1 @
% 4.12/4.30         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 4.12/4.30       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 4.12/4.30  thf('55', plain,
% 4.12/4.30      (![X40 : $i]:
% 4.12/4.30         (m1_subset_1 @ (k6_partfun1 @ X40) @ 
% 4.12/4.30          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X40)))),
% 4.12/4.30      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 4.12/4.30  thf('56', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 4.12/4.30      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.12/4.30  thf('57', plain,
% 4.12/4.30      (![X40 : $i]:
% 4.12/4.30         (m1_subset_1 @ (k6_relat_1 @ X40) @ 
% 4.12/4.30          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X40)))),
% 4.12/4.30      inference('demod', [status(thm)], ['55', '56'])).
% 4.12/4.30  thf('58', plain,
% 4.12/4.30      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C_1 @ sk_D)
% 4.12/4.30         = (k6_relat_1 @ sk_A))),
% 4.12/4.30      inference('demod', [status(thm)], ['54', '57'])).
% 4.12/4.30  thf('59', plain,
% 4.12/4.30      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.12/4.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.30  thf(t26_funct_2, axiom,
% 4.12/4.30    (![A:$i,B:$i,C:$i,D:$i]:
% 4.12/4.30     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 4.12/4.30         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.12/4.30       ( ![E:$i]:
% 4.12/4.30         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 4.12/4.30             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 4.12/4.30           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 4.12/4.30             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 4.12/4.30               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 4.12/4.30  thf('60', plain,
% 4.12/4.30      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 4.12/4.30         (~ (v1_funct_1 @ X46)
% 4.12/4.30          | ~ (v1_funct_2 @ X46 @ X47 @ X48)
% 4.12/4.30          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 4.12/4.30          | ~ (v2_funct_1 @ (k1_partfun1 @ X49 @ X47 @ X47 @ X48 @ X50 @ X46))
% 4.12/4.30          | (v2_funct_1 @ X50)
% 4.12/4.30          | ((X48) = (k1_xboole_0))
% 4.12/4.30          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X47)))
% 4.12/4.30          | ~ (v1_funct_2 @ X50 @ X49 @ X47)
% 4.12/4.30          | ~ (v1_funct_1 @ X50))),
% 4.12/4.30      inference('cnf', [status(esa)], [t26_funct_2])).
% 4.12/4.30  thf('61', plain,
% 4.12/4.30      (![X0 : $i, X1 : $i]:
% 4.12/4.30         (~ (v1_funct_1 @ X0)
% 4.12/4.30          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 4.12/4.30          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 4.12/4.30          | ((sk_A) = (k1_xboole_0))
% 4.12/4.30          | (v2_funct_1 @ X0)
% 4.12/4.30          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 4.12/4.30          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 4.12/4.30          | ~ (v1_funct_1 @ sk_D))),
% 4.12/4.30      inference('sup-', [status(thm)], ['59', '60'])).
% 4.12/4.30  thf('62', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 4.12/4.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.30  thf('63', plain, ((v1_funct_1 @ sk_D)),
% 4.12/4.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.30  thf('64', plain,
% 4.12/4.30      (![X0 : $i, X1 : $i]:
% 4.12/4.30         (~ (v1_funct_1 @ X0)
% 4.12/4.30          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 4.12/4.30          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 4.12/4.30          | ((sk_A) = (k1_xboole_0))
% 4.12/4.30          | (v2_funct_1 @ X0)
% 4.12/4.30          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 4.12/4.30      inference('demod', [status(thm)], ['61', '62', '63'])).
% 4.12/4.30  thf('65', plain,
% 4.12/4.30      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 4.12/4.30        | (v2_funct_1 @ sk_C_1)
% 4.12/4.30        | ((sk_A) = (k1_xboole_0))
% 4.12/4.30        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 4.12/4.30        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)
% 4.12/4.30        | ~ (v1_funct_1 @ sk_C_1))),
% 4.12/4.30      inference('sup-', [status(thm)], ['58', '64'])).
% 4.12/4.30  thf(fc4_funct_1, axiom,
% 4.12/4.30    (![A:$i]:
% 4.12/4.30     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 4.12/4.30       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 4.12/4.30  thf('66', plain, (![X17 : $i]: (v2_funct_1 @ (k6_relat_1 @ X17))),
% 4.12/4.30      inference('cnf', [status(esa)], [fc4_funct_1])).
% 4.12/4.30  thf('67', plain,
% 4.12/4.30      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.12/4.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.30  thf('68', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 4.12/4.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.30  thf('69', plain, ((v1_funct_1 @ sk_C_1)),
% 4.12/4.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.12/4.30  thf('70', plain, (((v2_funct_1 @ sk_C_1) | ((sk_A) = (k1_xboole_0)))),
% 4.12/4.30      inference('demod', [status(thm)], ['65', '66', '67', '68', '69'])).
% 4.12/4.30  thf('71', plain, (~ (v2_funct_1 @ sk_C_1)),
% 4.12/4.30      inference('simpl_trail', [status(thm)], ['1', '35'])).
% 4.12/4.30  thf('72', plain, (((sk_A) = (k1_xboole_0))),
% 4.12/4.30      inference('clc', [status(thm)], ['70', '71'])).
% 4.12/4.30  thf(t113_zfmisc_1, axiom,
% 4.12/4.30    (![A:$i,B:$i]:
% 4.12/4.30     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 4.12/4.30       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 4.12/4.30  thf('73', plain,
% 4.12/4.30      (![X8 : $i, X9 : $i]:
% 4.12/4.30         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 4.12/4.30      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 4.12/4.30  thf('74', plain,
% 4.12/4.30      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 4.12/4.30      inference('simplify', [status(thm)], ['73'])).
% 4.12/4.30  thf(d3_tarski, axiom,
% 4.12/4.30    (![A:$i,B:$i]:
% 4.12/4.30     ( ( r1_tarski @ A @ B ) <=>
% 4.12/4.30       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 4.12/4.30  thf('75', plain,
% 4.12/4.30      (![X1 : $i, X3 : $i]:
% 4.12/4.30         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 4.12/4.30      inference('cnf', [status(esa)], [d3_tarski])).
% 4.12/4.30  thf('76', plain,
% 4.12/4.30      (![X8 : $i, X9 : $i]:
% 4.12/4.30         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 4.12/4.30      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 4.12/4.30  thf('77', plain,
% 4.12/4.30      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 4.12/4.30      inference('simplify', [status(thm)], ['76'])).
% 4.12/4.30  thf('78', plain,
% 4.12/4.30      (![X40 : $i]:
% 4.12/4.30         (m1_subset_1 @ (k6_relat_1 @ X40) @ 
% 4.12/4.30          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X40)))),
% 4.12/4.30      inference('demod', [status(thm)], ['55', '56'])).
% 4.12/4.30  thf('79', plain,
% 4.12/4.30      ((m1_subset_1 @ (k6_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 4.12/4.30      inference('sup+', [status(thm)], ['77', '78'])).
% 4.12/4.30  thf(t5_subset, axiom,
% 4.12/4.30    (![A:$i,B:$i,C:$i]:
% 4.12/4.30     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 4.12/4.30          ( v1_xboole_0 @ C ) ) ))).
% 4.12/4.30  thf('80', plain,
% 4.12/4.30      (![X13 : $i, X14 : $i, X15 : $i]:
% 4.12/4.30         (~ (r2_hidden @ X13 @ X14)
% 4.12/4.30          | ~ (v1_xboole_0 @ X15)
% 4.12/4.30          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 4.12/4.30      inference('cnf', [status(esa)], [t5_subset])).
% 4.12/4.30  thf('81', plain,
% 4.12/4.30      (![X0 : $i]:
% 4.12/4.30         (~ (v1_xboole_0 @ k1_xboole_0)
% 4.12/4.30          | ~ (r2_hidden @ X0 @ (k6_relat_1 @ k1_xboole_0)))),
% 4.12/4.30      inference('sup-', [status(thm)], ['79', '80'])).
% 4.12/4.30  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 4.12/4.30  thf('82', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.12/4.30      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.12/4.30  thf('83', plain,
% 4.12/4.30      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k6_relat_1 @ k1_xboole_0))),
% 4.12/4.30      inference('demod', [status(thm)], ['81', '82'])).
% 4.12/4.30  thf('84', plain,
% 4.12/4.30      ((m1_subset_1 @ (k6_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 4.12/4.30      inference('sup+', [status(thm)], ['77', '78'])).
% 4.12/4.30  thf('85', plain,
% 4.12/4.30      (![X10 : $i, X11 : $i]:
% 4.12/4.30         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 4.12/4.30      inference('cnf', [status(esa)], [t3_subset])).
% 4.12/4.30  thf('86', plain, ((r1_tarski @ (k6_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 4.12/4.30      inference('sup-', [status(thm)], ['84', '85'])).
% 4.12/4.30  thf('87', plain,
% 4.12/4.30      (![X1 : $i, X3 : $i]:
% 4.12/4.30         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 4.12/4.30      inference('cnf', [status(esa)], [d3_tarski])).
% 4.12/4.30  thf('88', plain,
% 4.12/4.30      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 4.12/4.30      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.12/4.30  thf('89', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 4.12/4.30      inference('simplify', [status(thm)], ['88'])).
% 4.12/4.30  thf('90', plain,
% 4.12/4.30      (![X10 : $i, X12 : $i]:
% 4.12/4.30         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 4.12/4.30      inference('cnf', [status(esa)], [t3_subset])).
% 4.12/4.30  thf('91', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 4.12/4.30      inference('sup-', [status(thm)], ['89', '90'])).
% 4.12/4.30  thf('92', plain,
% 4.12/4.30      (![X13 : $i, X14 : $i, X15 : $i]:
% 4.12/4.30         (~ (r2_hidden @ X13 @ X14)
% 4.12/4.30          | ~ (v1_xboole_0 @ X15)
% 4.12/4.30          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 4.12/4.30      inference('cnf', [status(esa)], [t5_subset])).
% 4.12/4.30  thf('93', plain,
% 4.12/4.30      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 4.12/4.30      inference('sup-', [status(thm)], ['91', '92'])).
% 4.12/4.30  thf('94', plain,
% 4.12/4.30      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 4.12/4.30      inference('sup-', [status(thm)], ['87', '93'])).
% 4.12/4.30  thf('95', plain,
% 4.12/4.30      (![X4 : $i, X6 : $i]:
% 4.12/4.30         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 4.12/4.30      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.12/4.30  thf('96', plain,
% 4.12/4.30      (![X0 : $i, X1 : $i]:
% 4.12/4.30         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 4.12/4.30      inference('sup-', [status(thm)], ['94', '95'])).
% 4.12/4.30  thf('97', plain,
% 4.12/4.30      ((((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 4.12/4.30        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 4.12/4.30      inference('sup-', [status(thm)], ['86', '96'])).
% 4.12/4.30  thf('98', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.12/4.30      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.12/4.30  thf('99', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.12/4.30      inference('demod', [status(thm)], ['97', '98'])).
% 4.12/4.30  thf('100', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 4.12/4.30      inference('demod', [status(thm)], ['83', '99'])).
% 4.12/4.30  thf('101', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 4.12/4.30      inference('sup-', [status(thm)], ['75', '100'])).
% 4.12/4.30  thf('102', plain, (((sk_A) = (k1_xboole_0))),
% 4.12/4.30      inference('clc', [status(thm)], ['70', '71'])).
% 4.12/4.30  thf('103', plain,
% 4.12/4.30      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 4.12/4.30      inference('simplify', [status(thm)], ['73'])).
% 4.12/4.30  thf('104', plain, (((k1_xboole_0) = (sk_C_1))),
% 4.12/4.30      inference('demod', [status(thm)], ['41', '72', '74', '101', '102', '103'])).
% 4.12/4.30  thf('105', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.12/4.30      inference('demod', [status(thm)], ['97', '98'])).
% 4.12/4.30  thf('106', plain, (![X17 : $i]: (v2_funct_1 @ (k6_relat_1 @ X17))),
% 4.12/4.30      inference('cnf', [status(esa)], [fc4_funct_1])).
% 4.12/4.30  thf('107', plain, ((v2_funct_1 @ k1_xboole_0)),
% 4.12/4.30      inference('sup+', [status(thm)], ['105', '106'])).
% 4.12/4.30  thf('108', plain, ($false),
% 4.12/4.30      inference('demod', [status(thm)], ['36', '104', '107'])).
% 4.12/4.30  
% 4.12/4.30  % SZS output end Refutation
% 4.12/4.30  
% 4.12/4.31  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

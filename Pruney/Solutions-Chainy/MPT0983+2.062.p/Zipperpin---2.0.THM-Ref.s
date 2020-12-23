%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.syPGZq6kW6

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:10 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 604 expanded)
%              Number of leaves         :   49 ( 200 expanded)
%              Depth                    :   16
%              Number of atoms          : 1385 (11428 expanded)
%              Number of equality atoms :   56 ( 183 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('4',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
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
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ~ ( r2_relset_1 @ X47 @ X47 @ ( k1_partfun1 @ X47 @ X48 @ X48 @ X47 @ X46 @ X49 ) @ ( k6_partfun1 @ X47 ) )
      | ( ( k2_relset_1 @ X48 @ X47 @ X49 )
        = X47 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X47 ) ) )
      | ~ ( v1_funct_2 @ X49 @ X48 @ X47 )
      | ~ ( v1_funct_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('7',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('8',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ~ ( r2_relset_1 @ X47 @ X47 @ ( k1_partfun1 @ X47 @ X48 @ X48 @ X47 @ X46 @ X49 ) @ ( k6_relat_1 @ X47 ) )
      | ( ( k2_relset_1 @ X48 @ X47 @ X49 )
        = X47 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X47 ) ) )
      | ~ ( v1_funct_2 @ X49 @ X48 @ X47 )
      | ~ ( v1_funct_1 @ X49 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_2 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_2 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ( ( k2_relset_1 @ sk_B_2 @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B_2 @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['4','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('15',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('16',plain,
    ( ( k2_relset_1 @ sk_B_2 @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_2 @ sk_D @ sk_B_2 @ sk_A ),
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
    ! [X35: $i,X36: $i] :
      ( ( ( k2_relat_1 @ X36 )
       != X35 )
      | ( v2_funct_2 @ X36 @ X35 )
      | ~ ( v5_relat_1 @ X36 @ X35 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('22',plain,(
    ! [X36: $i] :
      ( ~ ( v1_relat_1 @ X36 )
      | ~ ( v5_relat_1 @ X36 @ ( k2_relat_1 @ X36 ) )
      | ( v2_funct_2 @ X36 @ ( k2_relat_1 @ X36 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('25',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v5_relat_1 @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('26',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['13','16','17','18','19'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('29',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
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
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('39',plain,(
    v4_relat_1 @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['37','38'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('40',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v4_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('44',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['41','44'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('46',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('47',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('51',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_2 @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_2 @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('58',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( X31 = X34 )
      | ~ ( r2_relset_1 @ X32 @ X33 @ X31 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','59'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('61',plain,(
    ! [X44: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X44 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('62',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('63',plain,(
    ! [X44: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X44 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X44 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_A ) ) ),
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

thf('66',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X52 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X53 @ X51 @ X51 @ X52 @ X54 @ X50 ) )
      | ( v2_funct_1 @ X54 )
      | ( X52 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X51 ) ) )
      | ~ ( v1_funct_2 @ X54 @ X53 @ X51 )
      | ~ ( v1_funct_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_2 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_2 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_2 @ sk_B_2 @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_2 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_2 @ sk_D @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_2 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_2 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_2 @ sk_B_2 @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['64','70'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('72',plain,(
    ! [X21: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('73',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v2_funct_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72','73','74','75'])).

thf('77',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','35'])).

thf('78',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['76','77'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('79',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(fc3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ B )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('80',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X8 @ X9 ) )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf('81',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X8 @ X9 ) )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('82',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_xboole_0 @ X6 )
      | ~ ( v1_xboole_0 @ X7 )
      | ( X6 = X7 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = X2 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('84',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('85',plain,(
    ! [X15: $i] :
      ( ( ( k1_relat_1 @ X15 )
       != k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( k6_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X44: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X44 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X44 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('89',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['87','90'])).

thf('92',plain,(
    ! [X44: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X44 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X44 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('93',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['83','93'])).

thf('95',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( v4_relat_1 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v4_relat_1 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['80','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['79','99'])).

thf('101',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v4_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['87','90'])).

thf('104',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('105',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['87','90'])).

thf('107',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('108',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['102','105','108'])).

thf('110',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['76','77'])).

thf('111',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['47','78','109','110'])).

thf(d8_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
      <=> ! [B: $i,C: $i] :
            ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
              & ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
              & ( ( k1_funct_1 @ A @ B )
                = ( k1_funct_1 @ A @ C ) ) )
           => ( B = C ) ) ) ) )).

thf('112',plain,(
    ! [X18: $i] :
      ( ( r2_hidden @ ( sk_C @ X18 ) @ ( k1_relat_1 @ X18 ) )
      | ( v2_funct_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['111','114'])).

thf('116',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('117',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['42','43'])).

thf('119',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['115','116','117','118'])).

thf('120',plain,(
    $false ),
    inference(demod,[status(thm)],['36','119'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.syPGZq6kW6
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:05:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.65/1.86  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.65/1.86  % Solved by: fo/fo7.sh
% 1.65/1.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.65/1.86  % done 1741 iterations in 1.402s
% 1.65/1.86  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.65/1.86  % SZS output start Refutation
% 1.65/1.86  thf(sk_C_type, type, sk_C: $i > $i).
% 1.65/1.86  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.65/1.86  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.65/1.86  thf(sk_A_type, type, sk_A: $i).
% 1.65/1.86  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.65/1.86  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.65/1.86  thf(sk_D_type, type, sk_D: $i).
% 1.65/1.86  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.65/1.86  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.65/1.86  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.65/1.86  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.65/1.86  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.65/1.86  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.65/1.86  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.65/1.86  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.65/1.86  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.65/1.86  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 1.65/1.86  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.65/1.86  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.65/1.86  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.65/1.86  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.65/1.86  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.65/1.86  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.65/1.86  thf(sk_B_2_type, type, sk_B_2: $i).
% 1.65/1.86  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.65/1.86  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.65/1.86  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.65/1.86  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.65/1.86  thf(t29_funct_2, conjecture,
% 1.65/1.86    (![A:$i,B:$i,C:$i]:
% 1.65/1.86     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.65/1.86         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.65/1.86       ( ![D:$i]:
% 1.65/1.86         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.65/1.86             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.65/1.86           ( ( r2_relset_1 @
% 1.65/1.86               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.65/1.86               ( k6_partfun1 @ A ) ) =>
% 1.65/1.86             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 1.65/1.86  thf(zf_stmt_0, negated_conjecture,
% 1.65/1.86    (~( ![A:$i,B:$i,C:$i]:
% 1.65/1.86        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.65/1.86            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.65/1.86          ( ![D:$i]:
% 1.65/1.86            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.65/1.86                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.65/1.86              ( ( r2_relset_1 @
% 1.65/1.86                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.65/1.86                  ( k6_partfun1 @ A ) ) =>
% 1.65/1.86                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 1.65/1.86    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 1.65/1.86  thf('0', plain, ((~ (v2_funct_1 @ sk_C_1) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 1.65/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.86  thf('1', plain, ((~ (v2_funct_1 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 1.65/1.86      inference('split', [status(esa)], ['0'])).
% 1.65/1.86  thf('2', plain,
% 1.65/1.86      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.65/1.86        (k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D) @ 
% 1.65/1.86        (k6_partfun1 @ sk_A))),
% 1.65/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.86  thf(redefinition_k6_partfun1, axiom,
% 1.65/1.86    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.65/1.86  thf('3', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 1.65/1.86      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.65/1.86  thf('4', plain,
% 1.65/1.86      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.65/1.86        (k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D) @ 
% 1.65/1.86        (k6_relat_1 @ sk_A))),
% 1.65/1.86      inference('demod', [status(thm)], ['2', '3'])).
% 1.65/1.86  thf('5', plain,
% 1.65/1.86      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.65/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.86  thf(t24_funct_2, axiom,
% 1.65/1.86    (![A:$i,B:$i,C:$i]:
% 1.65/1.86     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.65/1.86         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.65/1.86       ( ![D:$i]:
% 1.65/1.86         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.65/1.86             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.65/1.86           ( ( r2_relset_1 @
% 1.65/1.86               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 1.65/1.86               ( k6_partfun1 @ B ) ) =>
% 1.65/1.86             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 1.65/1.86  thf('6', plain,
% 1.65/1.86      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 1.65/1.86         (~ (v1_funct_1 @ X46)
% 1.65/1.86          | ~ (v1_funct_2 @ X46 @ X47 @ X48)
% 1.65/1.86          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 1.65/1.86          | ~ (r2_relset_1 @ X47 @ X47 @ 
% 1.65/1.86               (k1_partfun1 @ X47 @ X48 @ X48 @ X47 @ X46 @ X49) @ 
% 1.65/1.86               (k6_partfun1 @ X47))
% 1.65/1.86          | ((k2_relset_1 @ X48 @ X47 @ X49) = (X47))
% 1.65/1.86          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X47)))
% 1.65/1.86          | ~ (v1_funct_2 @ X49 @ X48 @ X47)
% 1.65/1.86          | ~ (v1_funct_1 @ X49))),
% 1.65/1.86      inference('cnf', [status(esa)], [t24_funct_2])).
% 1.65/1.86  thf('7', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 1.65/1.86      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.65/1.86  thf('8', plain,
% 1.65/1.86      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 1.65/1.86         (~ (v1_funct_1 @ X46)
% 1.65/1.86          | ~ (v1_funct_2 @ X46 @ X47 @ X48)
% 1.65/1.86          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 1.65/1.86          | ~ (r2_relset_1 @ X47 @ X47 @ 
% 1.65/1.86               (k1_partfun1 @ X47 @ X48 @ X48 @ X47 @ X46 @ X49) @ 
% 1.65/1.86               (k6_relat_1 @ X47))
% 1.65/1.86          | ((k2_relset_1 @ X48 @ X47 @ X49) = (X47))
% 1.65/1.86          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X47)))
% 1.65/1.86          | ~ (v1_funct_2 @ X49 @ X48 @ X47)
% 1.65/1.86          | ~ (v1_funct_1 @ X49))),
% 1.65/1.86      inference('demod', [status(thm)], ['6', '7'])).
% 1.65/1.86  thf('9', plain,
% 1.65/1.86      (![X0 : $i]:
% 1.65/1.86         (~ (v1_funct_1 @ X0)
% 1.65/1.86          | ~ (v1_funct_2 @ X0 @ sk_B_2 @ sk_A)
% 1.65/1.86          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_A)))
% 1.65/1.86          | ((k2_relset_1 @ sk_B_2 @ sk_A @ X0) = (sk_A))
% 1.65/1.86          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.65/1.86               (k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ X0) @ 
% 1.65/1.86               (k6_relat_1 @ sk_A))
% 1.65/1.86          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2)
% 1.65/1.86          | ~ (v1_funct_1 @ sk_C_1))),
% 1.65/1.86      inference('sup-', [status(thm)], ['5', '8'])).
% 1.65/1.86  thf('10', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2)),
% 1.65/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.86  thf('11', plain, ((v1_funct_1 @ sk_C_1)),
% 1.65/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.86  thf('12', plain,
% 1.65/1.86      (![X0 : $i]:
% 1.65/1.86         (~ (v1_funct_1 @ X0)
% 1.65/1.86          | ~ (v1_funct_2 @ X0 @ sk_B_2 @ sk_A)
% 1.65/1.86          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_A)))
% 1.65/1.86          | ((k2_relset_1 @ sk_B_2 @ sk_A @ X0) = (sk_A))
% 1.65/1.86          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.65/1.86               (k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ X0) @ 
% 1.65/1.86               (k6_relat_1 @ sk_A)))),
% 1.65/1.86      inference('demod', [status(thm)], ['9', '10', '11'])).
% 1.65/1.86  thf('13', plain,
% 1.65/1.86      ((((k2_relset_1 @ sk_B_2 @ sk_A @ sk_D) = (sk_A))
% 1.65/1.86        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_A)))
% 1.65/1.86        | ~ (v1_funct_2 @ sk_D @ sk_B_2 @ sk_A)
% 1.65/1.86        | ~ (v1_funct_1 @ sk_D))),
% 1.65/1.86      inference('sup-', [status(thm)], ['4', '12'])).
% 1.65/1.86  thf('14', plain,
% 1.65/1.86      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_A)))),
% 1.65/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.86  thf(redefinition_k2_relset_1, axiom,
% 1.65/1.86    (![A:$i,B:$i,C:$i]:
% 1.65/1.86     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.65/1.86       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.65/1.86  thf('15', plain,
% 1.65/1.86      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.65/1.86         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 1.65/1.86          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 1.65/1.86      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.65/1.86  thf('16', plain,
% 1.65/1.86      (((k2_relset_1 @ sk_B_2 @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.65/1.86      inference('sup-', [status(thm)], ['14', '15'])).
% 1.65/1.86  thf('17', plain,
% 1.65/1.86      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_A)))),
% 1.65/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.86  thf('18', plain, ((v1_funct_2 @ sk_D @ sk_B_2 @ sk_A)),
% 1.65/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.86  thf('19', plain, ((v1_funct_1 @ sk_D)),
% 1.65/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.86  thf('20', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.65/1.86      inference('demod', [status(thm)], ['13', '16', '17', '18', '19'])).
% 1.65/1.86  thf(d3_funct_2, axiom,
% 1.65/1.86    (![A:$i,B:$i]:
% 1.65/1.86     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 1.65/1.86       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 1.65/1.86  thf('21', plain,
% 1.65/1.86      (![X35 : $i, X36 : $i]:
% 1.65/1.86         (((k2_relat_1 @ X36) != (X35))
% 1.65/1.86          | (v2_funct_2 @ X36 @ X35)
% 1.65/1.86          | ~ (v5_relat_1 @ X36 @ X35)
% 1.65/1.86          | ~ (v1_relat_1 @ X36))),
% 1.65/1.86      inference('cnf', [status(esa)], [d3_funct_2])).
% 1.65/1.86  thf('22', plain,
% 1.65/1.86      (![X36 : $i]:
% 1.65/1.86         (~ (v1_relat_1 @ X36)
% 1.65/1.86          | ~ (v5_relat_1 @ X36 @ (k2_relat_1 @ X36))
% 1.65/1.86          | (v2_funct_2 @ X36 @ (k2_relat_1 @ X36)))),
% 1.65/1.86      inference('simplify', [status(thm)], ['21'])).
% 1.65/1.86  thf('23', plain,
% 1.65/1.86      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 1.65/1.86        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 1.65/1.86        | ~ (v1_relat_1 @ sk_D))),
% 1.65/1.86      inference('sup-', [status(thm)], ['20', '22'])).
% 1.65/1.86  thf('24', plain,
% 1.65/1.86      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_A)))),
% 1.65/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.86  thf(cc2_relset_1, axiom,
% 1.65/1.86    (![A:$i,B:$i,C:$i]:
% 1.65/1.86     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.65/1.86       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.65/1.86  thf('25', plain,
% 1.65/1.86      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.65/1.86         ((v5_relat_1 @ X25 @ X27)
% 1.65/1.86          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 1.65/1.86      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.65/1.86  thf('26', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 1.65/1.86      inference('sup-', [status(thm)], ['24', '25'])).
% 1.65/1.86  thf('27', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.65/1.86      inference('demod', [status(thm)], ['13', '16', '17', '18', '19'])).
% 1.65/1.86  thf('28', plain,
% 1.65/1.86      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_A)))),
% 1.65/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.86  thf(cc1_relset_1, axiom,
% 1.65/1.87    (![A:$i,B:$i,C:$i]:
% 1.65/1.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.65/1.87       ( v1_relat_1 @ C ) ))).
% 1.65/1.87  thf('29', plain,
% 1.65/1.87      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.65/1.87         ((v1_relat_1 @ X22)
% 1.65/1.87          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.65/1.87      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.65/1.87  thf('30', plain, ((v1_relat_1 @ sk_D)),
% 1.65/1.87      inference('sup-', [status(thm)], ['28', '29'])).
% 1.65/1.87  thf('31', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 1.65/1.87      inference('demod', [status(thm)], ['23', '26', '27', '30'])).
% 1.65/1.87  thf('32', plain,
% 1.65/1.87      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 1.65/1.87      inference('split', [status(esa)], ['0'])).
% 1.65/1.87  thf('33', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 1.65/1.87      inference('sup-', [status(thm)], ['31', '32'])).
% 1.65/1.87  thf('34', plain,
% 1.65/1.87      (~ ((v2_funct_1 @ sk_C_1)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 1.65/1.87      inference('split', [status(esa)], ['0'])).
% 1.65/1.87  thf('35', plain, (~ ((v2_funct_1 @ sk_C_1))),
% 1.65/1.87      inference('sat_resolution*', [status(thm)], ['33', '34'])).
% 1.65/1.87  thf('36', plain, (~ (v2_funct_1 @ sk_C_1)),
% 1.65/1.87      inference('simpl_trail', [status(thm)], ['1', '35'])).
% 1.65/1.87  thf('37', plain,
% 1.65/1.87      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('38', plain,
% 1.65/1.87      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.65/1.87         ((v4_relat_1 @ X25 @ X26)
% 1.65/1.87          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 1.65/1.87      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.65/1.87  thf('39', plain, ((v4_relat_1 @ sk_C_1 @ sk_A)),
% 1.65/1.87      inference('sup-', [status(thm)], ['37', '38'])).
% 1.65/1.87  thf(d18_relat_1, axiom,
% 1.65/1.87    (![A:$i,B:$i]:
% 1.65/1.87     ( ( v1_relat_1 @ B ) =>
% 1.65/1.87       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.65/1.87  thf('40', plain,
% 1.65/1.87      (![X13 : $i, X14 : $i]:
% 1.65/1.87         (~ (v4_relat_1 @ X13 @ X14)
% 1.65/1.87          | (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 1.65/1.87          | ~ (v1_relat_1 @ X13))),
% 1.65/1.87      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.65/1.87  thf('41', plain,
% 1.65/1.87      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A))),
% 1.65/1.87      inference('sup-', [status(thm)], ['39', '40'])).
% 1.65/1.87  thf('42', plain,
% 1.65/1.87      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('43', plain,
% 1.65/1.87      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.65/1.87         ((v1_relat_1 @ X22)
% 1.65/1.87          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.65/1.87      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.65/1.87  thf('44', plain, ((v1_relat_1 @ sk_C_1)),
% 1.65/1.87      inference('sup-', [status(thm)], ['42', '43'])).
% 1.65/1.87  thf('45', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A)),
% 1.65/1.87      inference('demod', [status(thm)], ['41', '44'])).
% 1.65/1.87  thf(d10_xboole_0, axiom,
% 1.65/1.87    (![A:$i,B:$i]:
% 1.65/1.87     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.65/1.87  thf('46', plain,
% 1.65/1.87      (![X3 : $i, X5 : $i]:
% 1.65/1.87         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 1.65/1.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.65/1.87  thf('47', plain,
% 1.65/1.87      ((~ (r1_tarski @ sk_A @ (k1_relat_1 @ sk_C_1))
% 1.65/1.87        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.65/1.87      inference('sup-', [status(thm)], ['45', '46'])).
% 1.65/1.87  thf('48', plain,
% 1.65/1.87      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.65/1.87        (k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D) @ 
% 1.65/1.87        (k6_relat_1 @ sk_A))),
% 1.65/1.87      inference('demod', [status(thm)], ['2', '3'])).
% 1.65/1.87  thf('49', plain,
% 1.65/1.87      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_A)))),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('50', plain,
% 1.65/1.87      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf(dt_k1_partfun1, axiom,
% 1.65/1.87    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.65/1.87     ( ( ( v1_funct_1 @ E ) & 
% 1.65/1.87         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.65/1.87         ( v1_funct_1 @ F ) & 
% 1.65/1.87         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.65/1.87       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.65/1.87         ( m1_subset_1 @
% 1.65/1.87           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.65/1.87           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.65/1.87  thf('51', plain,
% 1.65/1.87      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 1.65/1.87         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 1.65/1.87          | ~ (v1_funct_1 @ X37)
% 1.65/1.87          | ~ (v1_funct_1 @ X40)
% 1.65/1.87          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 1.65/1.87          | (m1_subset_1 @ (k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40) @ 
% 1.65/1.87             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X42))))),
% 1.65/1.87      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.65/1.87  thf('52', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.87         ((m1_subset_1 @ 
% 1.65/1.87           (k1_partfun1 @ sk_A @ sk_B_2 @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 1.65/1.87           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.65/1.87          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.65/1.87          | ~ (v1_funct_1 @ X1)
% 1.65/1.87          | ~ (v1_funct_1 @ sk_C_1))),
% 1.65/1.87      inference('sup-', [status(thm)], ['50', '51'])).
% 1.65/1.87  thf('53', plain, ((v1_funct_1 @ sk_C_1)),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('54', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.87         ((m1_subset_1 @ 
% 1.65/1.87           (k1_partfun1 @ sk_A @ sk_B_2 @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 1.65/1.87           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.65/1.87          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.65/1.87          | ~ (v1_funct_1 @ X1))),
% 1.65/1.87      inference('demod', [status(thm)], ['52', '53'])).
% 1.65/1.87  thf('55', plain,
% 1.65/1.87      ((~ (v1_funct_1 @ sk_D)
% 1.65/1.87        | (m1_subset_1 @ 
% 1.65/1.87           (k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D) @ 
% 1.65/1.87           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.65/1.87      inference('sup-', [status(thm)], ['49', '54'])).
% 1.65/1.87  thf('56', plain, ((v1_funct_1 @ sk_D)),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('57', plain,
% 1.65/1.87      ((m1_subset_1 @ 
% 1.65/1.87        (k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D) @ 
% 1.65/1.87        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.65/1.87      inference('demod', [status(thm)], ['55', '56'])).
% 1.65/1.87  thf(redefinition_r2_relset_1, axiom,
% 1.65/1.87    (![A:$i,B:$i,C:$i,D:$i]:
% 1.65/1.87     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.65/1.87         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.65/1.87       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.65/1.87  thf('58', plain,
% 1.65/1.87      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.65/1.87         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.65/1.87          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.65/1.87          | ((X31) = (X34))
% 1.65/1.87          | ~ (r2_relset_1 @ X32 @ X33 @ X31 @ X34))),
% 1.65/1.87      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.65/1.87  thf('59', plain,
% 1.65/1.87      (![X0 : $i]:
% 1.65/1.87         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.65/1.87             (k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D) @ X0)
% 1.65/1.87          | ((k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D)
% 1.65/1.87              = (X0))
% 1.65/1.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.65/1.87      inference('sup-', [status(thm)], ['57', '58'])).
% 1.65/1.87  thf('60', plain,
% 1.65/1.87      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 1.65/1.87           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.65/1.87        | ((k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D)
% 1.65/1.87            = (k6_relat_1 @ sk_A)))),
% 1.65/1.87      inference('sup-', [status(thm)], ['48', '59'])).
% 1.65/1.87  thf(dt_k6_partfun1, axiom,
% 1.65/1.87    (![A:$i]:
% 1.65/1.87     ( ( m1_subset_1 @
% 1.65/1.87         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 1.65/1.87       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 1.65/1.87  thf('61', plain,
% 1.65/1.87      (![X44 : $i]:
% 1.65/1.87         (m1_subset_1 @ (k6_partfun1 @ X44) @ 
% 1.65/1.87          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X44)))),
% 1.65/1.87      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.65/1.87  thf('62', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 1.65/1.87      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.65/1.87  thf('63', plain,
% 1.65/1.87      (![X44 : $i]:
% 1.65/1.87         (m1_subset_1 @ (k6_relat_1 @ X44) @ 
% 1.65/1.87          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X44)))),
% 1.65/1.87      inference('demod', [status(thm)], ['61', '62'])).
% 1.65/1.87  thf('64', plain,
% 1.65/1.87      (((k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D)
% 1.65/1.87         = (k6_relat_1 @ sk_A))),
% 1.65/1.87      inference('demod', [status(thm)], ['60', '63'])).
% 1.65/1.87  thf('65', plain,
% 1.65/1.87      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_A)))),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf(t26_funct_2, axiom,
% 1.65/1.87    (![A:$i,B:$i,C:$i,D:$i]:
% 1.65/1.87     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.65/1.87         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.65/1.87       ( ![E:$i]:
% 1.65/1.87         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.65/1.87             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.65/1.87           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 1.65/1.87             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 1.65/1.87               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 1.65/1.87  thf('66', plain,
% 1.65/1.87      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 1.65/1.87         (~ (v1_funct_1 @ X50)
% 1.65/1.87          | ~ (v1_funct_2 @ X50 @ X51 @ X52)
% 1.65/1.87          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 1.65/1.87          | ~ (v2_funct_1 @ (k1_partfun1 @ X53 @ X51 @ X51 @ X52 @ X54 @ X50))
% 1.65/1.87          | (v2_funct_1 @ X54)
% 1.65/1.87          | ((X52) = (k1_xboole_0))
% 1.65/1.87          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X51)))
% 1.65/1.87          | ~ (v1_funct_2 @ X54 @ X53 @ X51)
% 1.65/1.87          | ~ (v1_funct_1 @ X54))),
% 1.65/1.87      inference('cnf', [status(esa)], [t26_funct_2])).
% 1.65/1.87  thf('67', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         (~ (v1_funct_1 @ X0)
% 1.65/1.87          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_2)
% 1.65/1.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_2)))
% 1.65/1.87          | ((sk_A) = (k1_xboole_0))
% 1.65/1.87          | (v2_funct_1 @ X0)
% 1.65/1.87          | ~ (v2_funct_1 @ 
% 1.65/1.87               (k1_partfun1 @ X1 @ sk_B_2 @ sk_B_2 @ sk_A @ X0 @ sk_D))
% 1.65/1.87          | ~ (v1_funct_2 @ sk_D @ sk_B_2 @ sk_A)
% 1.65/1.87          | ~ (v1_funct_1 @ sk_D))),
% 1.65/1.87      inference('sup-', [status(thm)], ['65', '66'])).
% 1.65/1.87  thf('68', plain, ((v1_funct_2 @ sk_D @ sk_B_2 @ sk_A)),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('69', plain, ((v1_funct_1 @ sk_D)),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('70', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         (~ (v1_funct_1 @ X0)
% 1.65/1.87          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_2)
% 1.65/1.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_2)))
% 1.65/1.87          | ((sk_A) = (k1_xboole_0))
% 1.65/1.87          | (v2_funct_1 @ X0)
% 1.65/1.87          | ~ (v2_funct_1 @ 
% 1.65/1.87               (k1_partfun1 @ X1 @ sk_B_2 @ sk_B_2 @ sk_A @ X0 @ sk_D)))),
% 1.65/1.87      inference('demod', [status(thm)], ['67', '68', '69'])).
% 1.65/1.87  thf('71', plain,
% 1.65/1.87      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 1.65/1.87        | (v2_funct_1 @ sk_C_1)
% 1.65/1.87        | ((sk_A) = (k1_xboole_0))
% 1.65/1.87        | ~ (m1_subset_1 @ sk_C_1 @ 
% 1.65/1.87             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))
% 1.65/1.87        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2)
% 1.65/1.87        | ~ (v1_funct_1 @ sk_C_1))),
% 1.65/1.87      inference('sup-', [status(thm)], ['64', '70'])).
% 1.65/1.87  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 1.65/1.87  thf('72', plain, (![X21 : $i]: (v2_funct_1 @ (k6_relat_1 @ X21))),
% 1.65/1.87      inference('cnf', [status(esa)], [t52_funct_1])).
% 1.65/1.87  thf('73', plain,
% 1.65/1.87      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('74', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2)),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('75', plain, ((v1_funct_1 @ sk_C_1)),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('76', plain, (((v2_funct_1 @ sk_C_1) | ((sk_A) = (k1_xboole_0)))),
% 1.65/1.87      inference('demod', [status(thm)], ['71', '72', '73', '74', '75'])).
% 1.65/1.87  thf('77', plain, (~ (v2_funct_1 @ sk_C_1)),
% 1.65/1.87      inference('simpl_trail', [status(thm)], ['1', '35'])).
% 1.65/1.87  thf('78', plain, (((sk_A) = (k1_xboole_0))),
% 1.65/1.87      inference('clc', [status(thm)], ['76', '77'])).
% 1.65/1.87  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.65/1.87  thf('79', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.65/1.87      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.65/1.87  thf(fc3_zfmisc_1, axiom,
% 1.65/1.87    (![A:$i,B:$i]:
% 1.65/1.87     ( ( v1_xboole_0 @ B ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 1.65/1.87  thf('80', plain,
% 1.65/1.87      (![X8 : $i, X9 : $i]:
% 1.65/1.87         ((v1_xboole_0 @ (k2_zfmisc_1 @ X8 @ X9)) | ~ (v1_xboole_0 @ X9))),
% 1.65/1.87      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 1.65/1.87  thf('81', plain,
% 1.65/1.87      (![X8 : $i, X9 : $i]:
% 1.65/1.87         ((v1_xboole_0 @ (k2_zfmisc_1 @ X8 @ X9)) | ~ (v1_xboole_0 @ X9))),
% 1.65/1.87      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 1.65/1.87  thf(t8_boole, axiom,
% 1.65/1.87    (![A:$i,B:$i]:
% 1.65/1.87     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 1.65/1.87  thf('82', plain,
% 1.65/1.87      (![X6 : $i, X7 : $i]:
% 1.65/1.87         (~ (v1_xboole_0 @ X6) | ~ (v1_xboole_0 @ X7) | ((X6) = (X7)))),
% 1.65/1.87      inference('cnf', [status(esa)], [t8_boole])).
% 1.65/1.87  thf('83', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.87         (~ (v1_xboole_0 @ X0)
% 1.65/1.87          | ((k2_zfmisc_1 @ X1 @ X0) = (X2))
% 1.65/1.87          | ~ (v1_xboole_0 @ X2))),
% 1.65/1.87      inference('sup-', [status(thm)], ['81', '82'])).
% 1.65/1.87  thf(t71_relat_1, axiom,
% 1.65/1.87    (![A:$i]:
% 1.65/1.87     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.65/1.87       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.65/1.87  thf('84', plain, (![X16 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 1.65/1.87      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.65/1.87  thf(t64_relat_1, axiom,
% 1.65/1.87    (![A:$i]:
% 1.65/1.87     ( ( v1_relat_1 @ A ) =>
% 1.65/1.87       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 1.65/1.87           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 1.65/1.87         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 1.65/1.87  thf('85', plain,
% 1.65/1.87      (![X15 : $i]:
% 1.65/1.87         (((k1_relat_1 @ X15) != (k1_xboole_0))
% 1.65/1.87          | ((X15) = (k1_xboole_0))
% 1.65/1.87          | ~ (v1_relat_1 @ X15))),
% 1.65/1.87      inference('cnf', [status(esa)], [t64_relat_1])).
% 1.65/1.87  thf('86', plain,
% 1.65/1.87      (![X0 : $i]:
% 1.65/1.87         (((X0) != (k1_xboole_0))
% 1.65/1.87          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.65/1.87          | ((k6_relat_1 @ X0) = (k1_xboole_0)))),
% 1.65/1.87      inference('sup-', [status(thm)], ['84', '85'])).
% 1.65/1.87  thf('87', plain,
% 1.65/1.87      ((((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 1.65/1.87        | ~ (v1_relat_1 @ (k6_relat_1 @ k1_xboole_0)))),
% 1.65/1.87      inference('simplify', [status(thm)], ['86'])).
% 1.65/1.87  thf('88', plain,
% 1.65/1.87      (![X44 : $i]:
% 1.65/1.87         (m1_subset_1 @ (k6_relat_1 @ X44) @ 
% 1.65/1.87          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X44)))),
% 1.65/1.87      inference('demod', [status(thm)], ['61', '62'])).
% 1.65/1.87  thf('89', plain,
% 1.65/1.87      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.65/1.87         ((v1_relat_1 @ X22)
% 1.65/1.87          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.65/1.87      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.65/1.87  thf('90', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 1.65/1.87      inference('sup-', [status(thm)], ['88', '89'])).
% 1.65/1.87  thf('91', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.65/1.87      inference('demod', [status(thm)], ['87', '90'])).
% 1.65/1.87  thf('92', plain,
% 1.65/1.87      (![X44 : $i]:
% 1.65/1.87         (m1_subset_1 @ (k6_relat_1 @ X44) @ 
% 1.65/1.87          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X44)))),
% 1.65/1.87      inference('demod', [status(thm)], ['61', '62'])).
% 1.65/1.87  thf('93', plain,
% 1.65/1.87      ((m1_subset_1 @ k1_xboole_0 @ 
% 1.65/1.87        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 1.65/1.87      inference('sup+', [status(thm)], ['91', '92'])).
% 1.65/1.87  thf('94', plain,
% 1.65/1.87      (![X0 : $i]:
% 1.65/1.87         ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.65/1.87          | ~ (v1_xboole_0 @ X0)
% 1.65/1.87          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.65/1.87      inference('sup+', [status(thm)], ['83', '93'])).
% 1.65/1.87  thf('95', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.65/1.87      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.65/1.87  thf('96', plain,
% 1.65/1.87      (![X0 : $i]:
% 1.65/1.87         ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.65/1.87          | ~ (v1_xboole_0 @ X0))),
% 1.65/1.87      inference('demod', [status(thm)], ['94', '95'])).
% 1.65/1.87  thf('97', plain,
% 1.65/1.87      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.65/1.87         ((v4_relat_1 @ X25 @ X26)
% 1.65/1.87          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 1.65/1.87      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.65/1.87  thf('98', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 1.65/1.87          | (v4_relat_1 @ k1_xboole_0 @ X1))),
% 1.65/1.87      inference('sup-', [status(thm)], ['96', '97'])).
% 1.65/1.87  thf('99', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         (~ (v1_xboole_0 @ X0) | (v4_relat_1 @ k1_xboole_0 @ X1))),
% 1.65/1.87      inference('sup-', [status(thm)], ['80', '98'])).
% 1.65/1.87  thf('100', plain, (![X0 : $i]: (v4_relat_1 @ k1_xboole_0 @ X0)),
% 1.65/1.87      inference('sup-', [status(thm)], ['79', '99'])).
% 1.65/1.87  thf('101', plain,
% 1.65/1.87      (![X13 : $i, X14 : $i]:
% 1.65/1.87         (~ (v4_relat_1 @ X13 @ X14)
% 1.65/1.87          | (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 1.65/1.87          | ~ (v1_relat_1 @ X13))),
% 1.65/1.87      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.65/1.87  thf('102', plain,
% 1.65/1.87      (![X0 : $i]:
% 1.65/1.87         (~ (v1_relat_1 @ k1_xboole_0)
% 1.65/1.87          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 1.65/1.87      inference('sup-', [status(thm)], ['100', '101'])).
% 1.65/1.87  thf('103', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.65/1.87      inference('demod', [status(thm)], ['87', '90'])).
% 1.65/1.87  thf('104', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 1.65/1.87      inference('sup-', [status(thm)], ['88', '89'])).
% 1.65/1.87  thf('105', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.65/1.87      inference('sup+', [status(thm)], ['103', '104'])).
% 1.65/1.87  thf('106', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.65/1.87      inference('demod', [status(thm)], ['87', '90'])).
% 1.65/1.87  thf('107', plain, (![X16 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 1.65/1.87      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.65/1.87  thf('108', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.65/1.87      inference('sup+', [status(thm)], ['106', '107'])).
% 1.65/1.87  thf('109', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.65/1.87      inference('demod', [status(thm)], ['102', '105', '108'])).
% 1.65/1.87  thf('110', plain, (((sk_A) = (k1_xboole_0))),
% 1.65/1.87      inference('clc', [status(thm)], ['76', '77'])).
% 1.65/1.87  thf('111', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_C_1))),
% 1.65/1.87      inference('demod', [status(thm)], ['47', '78', '109', '110'])).
% 1.65/1.87  thf(d8_funct_1, axiom,
% 1.65/1.87    (![A:$i]:
% 1.65/1.87     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.65/1.87       ( ( v2_funct_1 @ A ) <=>
% 1.65/1.87         ( ![B:$i,C:$i]:
% 1.65/1.87           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 1.65/1.87               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 1.65/1.87               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 1.65/1.87             ( ( B ) = ( C ) ) ) ) ) ))).
% 1.65/1.87  thf('112', plain,
% 1.65/1.87      (![X18 : $i]:
% 1.65/1.87         ((r2_hidden @ (sk_C @ X18) @ (k1_relat_1 @ X18))
% 1.65/1.87          | (v2_funct_1 @ X18)
% 1.65/1.87          | ~ (v1_funct_1 @ X18)
% 1.65/1.87          | ~ (v1_relat_1 @ X18))),
% 1.65/1.87      inference('cnf', [status(esa)], [d8_funct_1])).
% 1.65/1.87  thf(d1_xboole_0, axiom,
% 1.65/1.87    (![A:$i]:
% 1.65/1.87     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.65/1.87  thf('113', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.65/1.87      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.65/1.87  thf('114', plain,
% 1.65/1.87      (![X0 : $i]:
% 1.65/1.87         (~ (v1_relat_1 @ X0)
% 1.65/1.87          | ~ (v1_funct_1 @ X0)
% 1.65/1.87          | (v2_funct_1 @ X0)
% 1.65/1.87          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 1.65/1.87      inference('sup-', [status(thm)], ['112', '113'])).
% 1.65/1.87  thf('115', plain,
% 1.65/1.87      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.65/1.87        | (v2_funct_1 @ sk_C_1)
% 1.65/1.87        | ~ (v1_funct_1 @ sk_C_1)
% 1.65/1.87        | ~ (v1_relat_1 @ sk_C_1))),
% 1.65/1.87      inference('sup-', [status(thm)], ['111', '114'])).
% 1.65/1.87  thf('116', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.65/1.87      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.65/1.87  thf('117', plain, ((v1_funct_1 @ sk_C_1)),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('118', plain, ((v1_relat_1 @ sk_C_1)),
% 1.65/1.87      inference('sup-', [status(thm)], ['42', '43'])).
% 1.65/1.87  thf('119', plain, ((v2_funct_1 @ sk_C_1)),
% 1.65/1.87      inference('demod', [status(thm)], ['115', '116', '117', '118'])).
% 1.65/1.87  thf('120', plain, ($false), inference('demod', [status(thm)], ['36', '119'])).
% 1.65/1.87  
% 1.65/1.87  % SZS output end Refutation
% 1.65/1.87  
% 1.65/1.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

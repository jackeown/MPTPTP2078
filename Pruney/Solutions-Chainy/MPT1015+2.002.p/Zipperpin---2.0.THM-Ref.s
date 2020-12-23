%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bqCCdl8Rk4

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:47 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  253 (5114 expanded)
%              Number of leaves         :   54 (1522 expanded)
%              Depth                    :   34
%              Number of atoms          : 2324 (115470 expanded)
%              Number of equality atoms :  146 (2141 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(rc2_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v1_xboole_0 @ B )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( sk_B @ X0 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t76_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B )
              & ( v2_funct_1 @ B ) )
           => ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ A )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B )
                & ( v2_funct_1 @ B ) )
             => ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_funct_2])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('6',plain,(
    ! [X48: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X48 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(t54_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
         => ( ! [D: $i] :
                ( ( r2_hidden @ D @ A )
               => ( ( k11_relat_1 @ B @ D )
                  = ( k11_relat_1 @ C @ D ) ) )
           => ( r2_relset_1 @ A @ A @ B @ C ) ) ) ) )).

thf('7',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) )
      | ( r2_relset_1 @ X39 @ X39 @ X40 @ X38 )
      | ( r2_hidden @ ( sk_D @ X38 @ X40 @ X39 ) @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[t54_relset_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ ( k6_partfun1 @ X0 ) @ X1 @ X0 ) @ X0 )
      | ( r2_relset_1 @ X0 @ X0 @ X1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_partfun1 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( k6_partfun1 @ sk_A ) @ sk_C @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r2_hidden @ ( sk_D @ ( k6_partfun1 @ sk_A ) @ sk_C @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['9','10'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k5_relat_1 @ X18 @ ( k2_funct_1 @ X18 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( B = k1_xboole_0 )
          | ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) )
              = ( k6_partfun1 @ A ) )
            & ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C )
              = ( k6_partfun1 @ B ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ( X55 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X56 )
      | ~ ( v1_funct_2 @ X56 @ X57 @ X55 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X55 ) ) )
      | ( ( k5_relat_1 @ X56 @ ( k2_funct_1 @ X56 ) )
        = ( k6_partfun1 @ X57 ) )
      | ~ ( v2_funct_1 @ X56 )
      | ( ( k2_relset_1 @ X57 @ X55 @ X56 )
       != X55 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('15',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_A @ sk_C )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('17',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('18',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','18','19','20'])).

thf('22',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B_1 ) @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('25',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X54 ) ) )
      | ( ( k1_partfun1 @ X50 @ X51 @ X53 @ X54 @ X49 @ X52 )
        = ( k5_relat_1 @ X49 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B_1 )
      = ( k5_relat_1 @ sk_C @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B_1 )
    = ( k5_relat_1 @ sk_C @ sk_B_1 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_B_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['22','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('35',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B_1 )
    = ( k5_relat_1 @ sk_C @ sk_B_1 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('42',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('43',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( X31 = X34 )
      | ~ ( r2_relset_1 @ X32 @ X33 @ X31 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_B_1 ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_B_1 )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_B_1 )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['32','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k5_relat_1 @ sk_C @ sk_B_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('49',plain,(
    ! [X62: $i,X63: $i] :
      ( ( ( k1_relset_1 @ X62 @ X62 @ X63 )
        = X62 )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X62 @ X62 ) ) )
      | ~ ( v1_funct_2 @ X63 @ X62 @ X62 )
      | ~ ( v1_funct_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('50',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('54',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('55',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['50','51','52','55'])).

thf(t50_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( ( ( k1_relat_1 @ B )
                = A )
              & ( ( k1_relat_1 @ C )
                = A )
              & ( r1_tarski @ ( k2_relat_1 @ C ) @ A )
              & ( v2_funct_1 @ B )
              & ( ( k5_relat_1 @ C @ B )
                = B ) )
           => ( C
              = ( k6_relat_1 @ A ) ) ) ) ) )).

thf('57',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( X12
        = ( k6_relat_1 @ X13 ) )
      | ( ( k5_relat_1 @ X12 @ X14 )
       != X14 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ( ( k1_relat_1 @ X12 )
       != X13 )
      | ~ ( v2_funct_1 @ X14 )
      | ( ( k1_relat_1 @ X14 )
       != X13 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t50_funct_1])).

thf('58',plain,(
    ! [X12: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( ( k1_relat_1 @ X14 )
       != ( k1_relat_1 @ X12 ) )
      | ~ ( v2_funct_1 @ X14 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X12 ) @ ( k1_relat_1 @ X12 ) )
      | ( ( k5_relat_1 @ X12 @ X14 )
       != X14 )
      | ( X12
        = ( k6_relat_1 @ ( k1_relat_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_C
        = ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
      | ( ( k5_relat_1 @ sk_C @ X0 )
       != X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('61',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('62',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['50','51','52','55'])).

thf('65',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['50','51','52','55'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A )
      | ( sk_C
        = ( k6_relat_1 @ sk_A ) )
      | ( ( k5_relat_1 @ sk_C @ X0 )
       != X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
       != sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','62','63','64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('68',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k7_relset_1 @ X35 @ X36 @ X37 @ X35 )
        = ( k2_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('69',plain,
    ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_A )
    = ( k2_relset_1 @ sk_A @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('71',plain,
    ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_A )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r1_tarski @ ( k7_relset_1 @ A @ B @ D @ C ) @ B ) ) )).

thf('73',plain,(
    ! [X58: $i,X59: $i,X60: $i,X61: $i] :
      ( ( r1_tarski @ ( k7_relset_1 @ X58 @ X59 @ X60 @ X61 ) @ X59 )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X59 ) ) )
      | ~ ( v1_funct_2 @ X60 @ X58 @ X59 )
      | ~ ( v1_funct_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t44_funct_2])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
      | ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ),
    inference('sup+',[status(thm)],['71','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( sk_C
        = ( k6_relat_1 @ sk_A ) )
      | ( ( k5_relat_1 @ sk_C @ X0 )
       != X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
       != sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['66','78'])).

thf('80',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( ( k1_relat_1 @ sk_B_1 )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 )
    | ( sk_C
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('83',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X62: $i,X63: $i] :
      ( ( ( k1_relset_1 @ X62 @ X62 @ X63 )
        = X62 )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X62 @ X62 ) ) )
      | ~ ( v1_funct_2 @ X63 @ X62 @ X62 )
      | ~ ( v1_funct_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('87',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('92',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['87','88','89','92'])).

thf('94',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ( sk_A != sk_A )
    | ( sk_C
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','83','84','93','94'])).

thf('96',plain,
    ( sk_C
    = ( k6_relat_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['95'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('97',plain,(
    ! [X15: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('98',plain,(
    v2_funct_1 @ sk_C ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != sk_A )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','98'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('100',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('101',plain,(
    ! [X11: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('102',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('103',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['87','88','89','92'])).

thf('104',plain,(
    ! [X11: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('105',plain,(
    ! [X10: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('106',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('107',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k1_relat_1 @ X16 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('108',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X18 ) @ X18 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(t59_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
            = ( k2_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
            = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('109',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X17 ) @ X17 ) )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t59_funct_1])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['107','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['106','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['105','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['104','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,
    ( ( ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['103','118'])).

thf('120',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['81','82'])).

thf('121',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['119','120','121','122'])).

thf('124',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k1_relat_1 @ X16 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('125',plain,
    ( ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['119','120','121','122'])).

thf('126',plain,
    ( ( ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) )
      = ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['87','88','89','92'])).

thf('128',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['81','82'])).

thf('129',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['126','127','128','129','130'])).

thf('132',plain,
    ( sk_A
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['123','131'])).

thf('133',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X18 ) @ X18 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('134',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X17 ) @ X17 ) )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t59_funct_1])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ sk_A ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['132','136'])).

thf('138',plain,
    ( sk_A
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['123','131'])).

thf('139',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ sk_A ) )
      = sk_A )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ( ( k2_relat_1 @ ( k6_relat_1 @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['102','139'])).

thf('141',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['81','82'])).

thf('142',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ( ( k2_relat_1 @ ( k6_relat_1 @ sk_A ) )
      = sk_A ) ),
    inference(demod,[status(thm)],['140','141','142'])).

thf('144',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v2_funct_1 @ sk_B_1 )
    | ( ( k2_relat_1 @ ( k6_relat_1 @ sk_A ) )
      = sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['101','143'])).

thf('145',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['81','82'])).

thf('146',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ sk_A ) )
      = sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['144','145','146','147'])).

thf('149',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( ( k2_relat_1 @ ( k6_relat_1 @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['100','148'])).

thf('150',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['81','82'])).

thf('151',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( k2_relat_1 @ ( k6_relat_1 @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['149','150','151'])).

thf('153',plain,
    ( sk_C
    = ( k6_relat_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['95'])).

thf('154',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,
    ( ( sk_A != sk_A )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['99','154'])).

thf('156',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,
    ( ( ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','156'])).

thf('158',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['50','51','52','55'])).

thf('159',plain,
    ( sk_C
    = ( k6_relat_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['95'])).

thf('160',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['60','61'])).

thf('161',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    v2_funct_1 @ sk_C ),
    inference('sup+',[status(thm)],['96','97'])).

thf('163',plain,
    ( ( sk_C
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['157','158','159','160','161','162'])).

thf('164',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( r2_relset_1 @ X32 @ X33 @ X31 @ X34 )
      | ( X31 != X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('168',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( r2_relset_1 @ X32 @ X33 @ X34 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['166','168'])).

thf('170',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['165','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( sk_B @ X0 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('172',plain,(
    ! [X48: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X48 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('173',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('174',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) )
      | ( r2_relset_1 @ X39 @ X39 @ X40 @ X38 )
      | ( r2_hidden @ ( sk_D @ X38 @ X40 @ X39 ) @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[t54_relset_1])).

thf('175',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r2_relset_1 @ X0 @ X0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k6_partfun1 @ X0 ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['172','175'])).

thf('177',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('178',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k6_partfun1 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['176','179'])).

thf('181',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('182',plain,(
    ! [X48: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X48 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('183',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( X31 = X34 )
      | ~ ( r2_relset_1 @ X32 @ X33 @ X31 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('184',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ X1 )
      | ( ( k6_partfun1 @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['181','184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k6_partfun1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['180','185'])).

thf('187',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['171','186'])).

thf('188',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['165','169'])).

thf('189',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['165','169'])).

thf('190',plain,(
    r2_hidden @ ( sk_D @ k1_xboole_0 @ sk_C @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','170','187','188','189'])).

thf('191',plain,
    ( sk_C
    = ( k6_relat_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['95'])).

thf('192',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['165','169'])).

thf('193',plain,
    ( sk_C
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['191','192'])).

thf('194',plain,(
    r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k6_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['190','193'])).

thf('195',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('196',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,(
    $false ),
    inference('sup-',[status(thm)],['4','196'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bqCCdl8Rk4
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:25:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.90/1.13  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.90/1.13  % Solved by: fo/fo7.sh
% 0.90/1.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.13  % done 1190 iterations in 0.643s
% 0.90/1.13  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.90/1.13  % SZS output start Refutation
% 0.90/1.13  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.13  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.90/1.13  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.90/1.13  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.90/1.13  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.90/1.13  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.90/1.13  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.90/1.13  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.13  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.13  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.90/1.13  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.90/1.13  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.90/1.13  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.13  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.90/1.13  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.90/1.13  thf(sk_C_type, type, sk_C: $i).
% 0.90/1.13  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.90/1.13  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.90/1.13  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.13  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.90/1.13  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.90/1.13  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.90/1.13  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.90/1.13  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.90/1.13  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.90/1.13  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.90/1.13  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.90/1.13  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.90/1.13  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.90/1.13  thf(sk_B_type, type, sk_B: $i > $i).
% 0.90/1.13  thf(rc2_subset_1, axiom,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ?[B:$i]:
% 0.90/1.13       ( ( v1_xboole_0 @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.90/1.13  thf('0', plain, (![X0 : $i]: (v1_xboole_0 @ (sk_B @ X0))),
% 0.90/1.13      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.90/1.13  thf(t4_subset_1, axiom,
% 0.90/1.13    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.90/1.13  thf('1', plain,
% 0.90/1.13      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 0.90/1.13      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.90/1.13  thf(cc1_subset_1, axiom,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( v1_xboole_0 @ A ) =>
% 0.90/1.13       ( ![B:$i]:
% 0.90/1.13         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.90/1.13  thf('2', plain,
% 0.90/1.13      (![X2 : $i, X3 : $i]:
% 0.90/1.13         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.90/1.13          | (v1_xboole_0 @ X2)
% 0.90/1.13          | ~ (v1_xboole_0 @ X3))),
% 0.90/1.13      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.90/1.13  thf('3', plain,
% 0.90/1.13      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ k1_xboole_0))),
% 0.90/1.13      inference('sup-', [status(thm)], ['1', '2'])).
% 0.90/1.13  thf('4', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.13      inference('sup-', [status(thm)], ['0', '3'])).
% 0.90/1.13  thf(t76_funct_2, conjecture,
% 0.90/1.13    (![A:$i,B:$i]:
% 0.90/1.13     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.90/1.13         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.90/1.13       ( ![C:$i]:
% 0.90/1.13         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.90/1.13             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.90/1.13           ( ( ( r2_relset_1 @
% 0.90/1.13                 A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B ) & 
% 0.90/1.13               ( v2_funct_1 @ B ) ) =>
% 0.90/1.13             ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ))).
% 0.90/1.13  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.13    (~( ![A:$i,B:$i]:
% 0.90/1.13        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.90/1.13            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.90/1.13          ( ![C:$i]:
% 0.90/1.13            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.90/1.13                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.90/1.13              ( ( ( r2_relset_1 @
% 0.90/1.13                    A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B ) & 
% 0.90/1.13                  ( v2_funct_1 @ B ) ) =>
% 0.90/1.13                ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ) )),
% 0.90/1.13    inference('cnf.neg', [status(esa)], [t76_funct_2])).
% 0.90/1.13  thf('5', plain,
% 0.90/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf(dt_k6_partfun1, axiom,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( m1_subset_1 @
% 0.90/1.13         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.90/1.13       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.90/1.13  thf('6', plain,
% 0.90/1.13      (![X48 : $i]:
% 0.90/1.13         (m1_subset_1 @ (k6_partfun1 @ X48) @ 
% 0.90/1.13          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X48)))),
% 0.90/1.13      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.90/1.13  thf(t54_relset_1, axiom,
% 0.90/1.13    (![A:$i,B:$i]:
% 0.90/1.13     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.90/1.13       ( ![C:$i]:
% 0.90/1.13         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.90/1.13           ( ( ![D:$i]:
% 0.90/1.13               ( ( r2_hidden @ D @ A ) =>
% 0.90/1.13                 ( ( k11_relat_1 @ B @ D ) = ( k11_relat_1 @ C @ D ) ) ) ) =>
% 0.90/1.13             ( r2_relset_1 @ A @ A @ B @ C ) ) ) ) ))).
% 0.90/1.13  thf('7', plain,
% 0.90/1.13      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.90/1.13         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))
% 0.90/1.13          | (r2_relset_1 @ X39 @ X39 @ X40 @ X38)
% 0.90/1.13          | (r2_hidden @ (sk_D @ X38 @ X40 @ X39) @ X39)
% 0.90/1.13          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39))))),
% 0.90/1.13      inference('cnf', [status(esa)], [t54_relset_1])).
% 0.90/1.13  thf('8', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0)))
% 0.90/1.13          | (r2_hidden @ (sk_D @ (k6_partfun1 @ X0) @ X1 @ X0) @ X0)
% 0.90/1.13          | (r2_relset_1 @ X0 @ X0 @ X1 @ (k6_partfun1 @ X0)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['6', '7'])).
% 0.90/1.13  thf('9', plain,
% 0.90/1.13      (((r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_partfun1 @ sk_A))
% 0.90/1.13        | (r2_hidden @ (sk_D @ (k6_partfun1 @ sk_A) @ sk_C @ sk_A) @ sk_A))),
% 0.90/1.13      inference('sup-', [status(thm)], ['5', '8'])).
% 0.90/1.13  thf('10', plain,
% 0.90/1.13      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_partfun1 @ sk_A))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('11', plain,
% 0.90/1.13      ((r2_hidden @ (sk_D @ (k6_partfun1 @ sk_A) @ sk_C @ sk_A) @ sk_A)),
% 0.90/1.13      inference('clc', [status(thm)], ['9', '10'])).
% 0.90/1.13  thf(t61_funct_1, axiom,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.90/1.13       ( ( v2_funct_1 @ A ) =>
% 0.90/1.13         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.90/1.13             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.90/1.13           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.90/1.13             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.90/1.13  thf('12', plain,
% 0.90/1.13      (![X18 : $i]:
% 0.90/1.13         (~ (v2_funct_1 @ X18)
% 0.90/1.13          | ((k5_relat_1 @ X18 @ (k2_funct_1 @ X18))
% 0.90/1.13              = (k6_relat_1 @ (k1_relat_1 @ X18)))
% 0.90/1.13          | ~ (v1_funct_1 @ X18)
% 0.90/1.13          | ~ (v1_relat_1 @ X18))),
% 0.90/1.13      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.90/1.13  thf('13', plain,
% 0.90/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf(t35_funct_2, axiom,
% 0.90/1.13    (![A:$i,B:$i,C:$i]:
% 0.90/1.13     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.90/1.13         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.90/1.13       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.90/1.13         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.90/1.13           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.90/1.13             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.90/1.13  thf('14', plain,
% 0.90/1.13      (![X55 : $i, X56 : $i, X57 : $i]:
% 0.90/1.13         (((X55) = (k1_xboole_0))
% 0.90/1.13          | ~ (v1_funct_1 @ X56)
% 0.90/1.13          | ~ (v1_funct_2 @ X56 @ X57 @ X55)
% 0.90/1.13          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X55)))
% 0.90/1.13          | ((k5_relat_1 @ X56 @ (k2_funct_1 @ X56)) = (k6_partfun1 @ X57))
% 0.90/1.13          | ~ (v2_funct_1 @ X56)
% 0.90/1.13          | ((k2_relset_1 @ X57 @ X55 @ X56) != (X55)))),
% 0.90/1.13      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.90/1.13  thf('15', plain,
% 0.90/1.13      ((((k2_relset_1 @ sk_A @ sk_A @ sk_C) != (sk_A))
% 0.90/1.13        | ~ (v2_funct_1 @ sk_C)
% 0.90/1.13        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.90/1.13        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.90/1.13        | ~ (v1_funct_1 @ sk_C)
% 0.90/1.13        | ((sk_A) = (k1_xboole_0)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['13', '14'])).
% 0.90/1.13  thf('16', plain,
% 0.90/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf(redefinition_k2_relset_1, axiom,
% 0.90/1.13    (![A:$i,B:$i,C:$i]:
% 0.90/1.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.13       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.90/1.13  thf('17', plain,
% 0.90/1.13      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.90/1.13         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 0.90/1.13          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.90/1.13      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.90/1.13  thf('18', plain,
% 0.90/1.13      (((k2_relset_1 @ sk_A @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.90/1.13      inference('sup-', [status(thm)], ['16', '17'])).
% 0.90/1.13  thf('19', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('21', plain,
% 0.90/1.13      ((((k2_relat_1 @ sk_C) != (sk_A))
% 0.90/1.13        | ~ (v2_funct_1 @ sk_C)
% 0.90/1.13        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.90/1.13        | ((sk_A) = (k1_xboole_0)))),
% 0.90/1.13      inference('demod', [status(thm)], ['15', '18', '19', '20'])).
% 0.90/1.13  thf('22', plain,
% 0.90/1.13      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.13        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B_1) @ sk_B_1)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('23', plain,
% 0.90/1.13      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('24', plain,
% 0.90/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf(redefinition_k1_partfun1, axiom,
% 0.90/1.13    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.90/1.13     ( ( ( v1_funct_1 @ E ) & 
% 0.90/1.13         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.90/1.13         ( v1_funct_1 @ F ) & 
% 0.90/1.13         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.90/1.13       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.90/1.13  thf('25', plain,
% 0.90/1.13      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 0.90/1.13         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 0.90/1.13          | ~ (v1_funct_1 @ X49)
% 0.90/1.13          | ~ (v1_funct_1 @ X52)
% 0.90/1.13          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X54)))
% 0.90/1.13          | ((k1_partfun1 @ X50 @ X51 @ X53 @ X54 @ X49 @ X52)
% 0.90/1.13              = (k5_relat_1 @ X49 @ X52)))),
% 0.90/1.13      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.90/1.13  thf('26', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.13         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0)
% 0.90/1.13            = (k5_relat_1 @ sk_C @ X0))
% 0.90/1.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.90/1.13          | ~ (v1_funct_1 @ X0)
% 0.90/1.13          | ~ (v1_funct_1 @ sk_C))),
% 0.90/1.13      inference('sup-', [status(thm)], ['24', '25'])).
% 0.90/1.13  thf('27', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('28', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.13         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0)
% 0.90/1.13            = (k5_relat_1 @ sk_C @ X0))
% 0.90/1.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.90/1.13          | ~ (v1_funct_1 @ X0))),
% 0.90/1.13      inference('demod', [status(thm)], ['26', '27'])).
% 0.90/1.13  thf('29', plain,
% 0.90/1.13      ((~ (v1_funct_1 @ sk_B_1)
% 0.90/1.13        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B_1)
% 0.90/1.13            = (k5_relat_1 @ sk_C @ sk_B_1)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['23', '28'])).
% 0.90/1.13  thf('30', plain, ((v1_funct_1 @ sk_B_1)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('31', plain,
% 0.90/1.13      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B_1)
% 0.90/1.13         = (k5_relat_1 @ sk_C @ sk_B_1))),
% 0.90/1.13      inference('demod', [status(thm)], ['29', '30'])).
% 0.90/1.13  thf('32', plain,
% 0.90/1.13      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_B_1) @ sk_B_1)),
% 0.90/1.13      inference('demod', [status(thm)], ['22', '31'])).
% 0.90/1.13  thf('33', plain,
% 0.90/1.13      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('34', plain,
% 0.90/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf(dt_k1_partfun1, axiom,
% 0.90/1.13    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.90/1.13     ( ( ( v1_funct_1 @ E ) & 
% 0.90/1.13         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.90/1.13         ( v1_funct_1 @ F ) & 
% 0.90/1.13         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.90/1.13       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.90/1.13         ( m1_subset_1 @
% 0.90/1.13           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.90/1.13           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.90/1.13  thf('35', plain,
% 0.90/1.13      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.90/1.13         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 0.90/1.13          | ~ (v1_funct_1 @ X41)
% 0.90/1.13          | ~ (v1_funct_1 @ X44)
% 0.90/1.13          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 0.90/1.13          | (m1_subset_1 @ (k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44) @ 
% 0.90/1.13             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X46))))),
% 0.90/1.13      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.90/1.13  thf('36', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.13         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1) @ 
% 0.90/1.13           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.90/1.13          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.90/1.13          | ~ (v1_funct_1 @ X1)
% 0.90/1.13          | ~ (v1_funct_1 @ sk_C))),
% 0.90/1.13      inference('sup-', [status(thm)], ['34', '35'])).
% 0.90/1.13  thf('37', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('38', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.13         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1) @ 
% 0.90/1.13           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.90/1.13          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.90/1.13          | ~ (v1_funct_1 @ X1))),
% 0.90/1.13      inference('demod', [status(thm)], ['36', '37'])).
% 0.90/1.13  thf('39', plain,
% 0.90/1.13      ((~ (v1_funct_1 @ sk_B_1)
% 0.90/1.13        | (m1_subset_1 @ 
% 0.90/1.13           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B_1) @ 
% 0.90/1.13           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['33', '38'])).
% 0.90/1.13  thf('40', plain, ((v1_funct_1 @ sk_B_1)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('41', plain,
% 0.90/1.13      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B_1)
% 0.90/1.13         = (k5_relat_1 @ sk_C @ sk_B_1))),
% 0.90/1.13      inference('demod', [status(thm)], ['29', '30'])).
% 0.90/1.13  thf('42', plain,
% 0.90/1.13      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_B_1) @ 
% 0.90/1.13        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.13      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.90/1.13  thf(redefinition_r2_relset_1, axiom,
% 0.90/1.13    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.13     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.90/1.13         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.90/1.13       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.90/1.13  thf('43', plain,
% 0.90/1.13      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.90/1.13         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.90/1.13          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.90/1.13          | ((X31) = (X34))
% 0.90/1.13          | ~ (r2_relset_1 @ X32 @ X33 @ X31 @ X34))),
% 0.90/1.13      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.90/1.13  thf('44', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_B_1) @ X0)
% 0.90/1.13          | ((k5_relat_1 @ sk_C @ sk_B_1) = (X0))
% 0.90/1.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['42', '43'])).
% 0.90/1.13  thf('45', plain,
% 0.90/1.13      ((~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.90/1.13        | ((k5_relat_1 @ sk_C @ sk_B_1) = (sk_B_1)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['32', '44'])).
% 0.90/1.13  thf('46', plain,
% 0.90/1.13      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('47', plain, (((k5_relat_1 @ sk_C @ sk_B_1) = (sk_B_1))),
% 0.90/1.13      inference('demod', [status(thm)], ['45', '46'])).
% 0.90/1.13  thf('48', plain,
% 0.90/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf(t67_funct_2, axiom,
% 0.90/1.13    (![A:$i,B:$i]:
% 0.90/1.13     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.90/1.13         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.90/1.13       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.90/1.13  thf('49', plain,
% 0.90/1.13      (![X62 : $i, X63 : $i]:
% 0.90/1.13         (((k1_relset_1 @ X62 @ X62 @ X63) = (X62))
% 0.90/1.13          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X62 @ X62)))
% 0.90/1.13          | ~ (v1_funct_2 @ X63 @ X62 @ X62)
% 0.90/1.13          | ~ (v1_funct_1 @ X63))),
% 0.90/1.13      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.90/1.13  thf('50', plain,
% 0.90/1.13      ((~ (v1_funct_1 @ sk_C)
% 0.90/1.13        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.90/1.13        | ((k1_relset_1 @ sk_A @ sk_A @ sk_C) = (sk_A)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['48', '49'])).
% 0.90/1.13  thf('51', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('52', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('53', plain,
% 0.90/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf(redefinition_k1_relset_1, axiom,
% 0.90/1.13    (![A:$i,B:$i,C:$i]:
% 0.90/1.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.13       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.90/1.13  thf('54', plain,
% 0.90/1.13      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.90/1.13         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 0.90/1.13          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.90/1.13      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.90/1.13  thf('55', plain,
% 0.90/1.13      (((k1_relset_1 @ sk_A @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.90/1.13      inference('sup-', [status(thm)], ['53', '54'])).
% 0.90/1.13  thf('56', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.90/1.13      inference('demod', [status(thm)], ['50', '51', '52', '55'])).
% 0.90/1.13  thf(t50_funct_1, axiom,
% 0.90/1.13    (![A:$i,B:$i]:
% 0.90/1.13     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.90/1.13       ( ![C:$i]:
% 0.90/1.13         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.90/1.13           ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.90/1.13               ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.90/1.13               ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) & ( v2_funct_1 @ B ) & 
% 0.90/1.13               ( ( k5_relat_1 @ C @ B ) = ( B ) ) ) =>
% 0.90/1.13             ( ( C ) = ( k6_relat_1 @ A ) ) ) ) ) ))).
% 0.90/1.13  thf('57', plain,
% 0.90/1.13      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.90/1.13         (~ (v1_relat_1 @ X12)
% 0.90/1.13          | ~ (v1_funct_1 @ X12)
% 0.90/1.13          | ((X12) = (k6_relat_1 @ X13))
% 0.90/1.13          | ((k5_relat_1 @ X12 @ X14) != (X14))
% 0.90/1.13          | ~ (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 0.90/1.13          | ((k1_relat_1 @ X12) != (X13))
% 0.90/1.13          | ~ (v2_funct_1 @ X14)
% 0.90/1.13          | ((k1_relat_1 @ X14) != (X13))
% 0.90/1.13          | ~ (v1_funct_1 @ X14)
% 0.90/1.13          | ~ (v1_relat_1 @ X14))),
% 0.90/1.13      inference('cnf', [status(esa)], [t50_funct_1])).
% 0.90/1.13  thf('58', plain,
% 0.90/1.13      (![X12 : $i, X14 : $i]:
% 0.90/1.13         (~ (v1_relat_1 @ X14)
% 0.90/1.13          | ~ (v1_funct_1 @ X14)
% 0.90/1.13          | ((k1_relat_1 @ X14) != (k1_relat_1 @ X12))
% 0.90/1.13          | ~ (v2_funct_1 @ X14)
% 0.90/1.13          | ~ (r1_tarski @ (k2_relat_1 @ X12) @ (k1_relat_1 @ X12))
% 0.90/1.13          | ((k5_relat_1 @ X12 @ X14) != (X14))
% 0.90/1.13          | ((X12) = (k6_relat_1 @ (k1_relat_1 @ X12)))
% 0.90/1.13          | ~ (v1_funct_1 @ X12)
% 0.90/1.13          | ~ (v1_relat_1 @ X12))),
% 0.90/1.13      inference('simplify', [status(thm)], ['57'])).
% 0.90/1.13  thf('59', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A)
% 0.90/1.13          | ~ (v1_relat_1 @ sk_C)
% 0.90/1.13          | ~ (v1_funct_1 @ sk_C)
% 0.90/1.13          | ((sk_C) = (k6_relat_1 @ (k1_relat_1 @ sk_C)))
% 0.90/1.13          | ((k5_relat_1 @ sk_C @ X0) != (X0))
% 0.90/1.13          | ~ (v2_funct_1 @ X0)
% 0.90/1.13          | ((k1_relat_1 @ X0) != (k1_relat_1 @ sk_C))
% 0.90/1.13          | ~ (v1_funct_1 @ X0)
% 0.90/1.13          | ~ (v1_relat_1 @ X0))),
% 0.90/1.13      inference('sup-', [status(thm)], ['56', '58'])).
% 0.90/1.13  thf('60', plain,
% 0.90/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf(cc1_relset_1, axiom,
% 0.90/1.13    (![A:$i,B:$i,C:$i]:
% 0.90/1.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.13       ( v1_relat_1 @ C ) ))).
% 0.90/1.13  thf('61', plain,
% 0.90/1.13      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.90/1.13         ((v1_relat_1 @ X22)
% 0.90/1.13          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.90/1.13      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.90/1.13  thf('62', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.13      inference('sup-', [status(thm)], ['60', '61'])).
% 0.90/1.13  thf('63', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('64', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.90/1.13      inference('demod', [status(thm)], ['50', '51', '52', '55'])).
% 0.90/1.13  thf('65', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.90/1.13      inference('demod', [status(thm)], ['50', '51', '52', '55'])).
% 0.90/1.13  thf('66', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A)
% 0.90/1.13          | ((sk_C) = (k6_relat_1 @ sk_A))
% 0.90/1.13          | ((k5_relat_1 @ sk_C @ X0) != (X0))
% 0.90/1.13          | ~ (v2_funct_1 @ X0)
% 0.90/1.13          | ((k1_relat_1 @ X0) != (sk_A))
% 0.90/1.13          | ~ (v1_funct_1 @ X0)
% 0.90/1.13          | ~ (v1_relat_1 @ X0))),
% 0.90/1.13      inference('demod', [status(thm)], ['59', '62', '63', '64', '65'])).
% 0.90/1.13  thf('67', plain,
% 0.90/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf(t38_relset_1, axiom,
% 0.90/1.13    (![A:$i,B:$i,C:$i]:
% 0.90/1.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.13       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.90/1.13         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.90/1.13  thf('68', plain,
% 0.90/1.13      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.90/1.13         (((k7_relset_1 @ X35 @ X36 @ X37 @ X35)
% 0.90/1.13            = (k2_relset_1 @ X35 @ X36 @ X37))
% 0.90/1.13          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.90/1.13      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.90/1.13  thf('69', plain,
% 0.90/1.13      (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_A)
% 0.90/1.13         = (k2_relset_1 @ sk_A @ sk_A @ sk_C))),
% 0.90/1.13      inference('sup-', [status(thm)], ['67', '68'])).
% 0.90/1.13  thf('70', plain,
% 0.90/1.13      (((k2_relset_1 @ sk_A @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.90/1.13      inference('sup-', [status(thm)], ['16', '17'])).
% 0.90/1.13  thf('71', plain,
% 0.90/1.13      (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_A) = (k2_relat_1 @ sk_C))),
% 0.90/1.13      inference('demod', [status(thm)], ['69', '70'])).
% 0.90/1.13  thf('72', plain,
% 0.90/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf(t44_funct_2, axiom,
% 0.90/1.13    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.13     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.90/1.13         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.90/1.13       ( r1_tarski @ ( k7_relset_1 @ A @ B @ D @ C ) @ B ) ))).
% 0.90/1.13  thf('73', plain,
% 0.90/1.13      (![X58 : $i, X59 : $i, X60 : $i, X61 : $i]:
% 0.90/1.13         ((r1_tarski @ (k7_relset_1 @ X58 @ X59 @ X60 @ X61) @ X59)
% 0.90/1.13          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X59)))
% 0.90/1.13          | ~ (v1_funct_2 @ X60 @ X58 @ X59)
% 0.90/1.13          | ~ (v1_funct_1 @ X60))),
% 0.90/1.13      inference('cnf', [status(esa)], [t44_funct_2])).
% 0.90/1.13  thf('74', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (v1_funct_1 @ sk_C)
% 0.90/1.13          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.90/1.13          | (r1_tarski @ (k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0) @ sk_A))),
% 0.90/1.13      inference('sup-', [status(thm)], ['72', '73'])).
% 0.90/1.13  thf('75', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('76', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('77', plain,
% 0.90/1.13      (![X0 : $i]: (r1_tarski @ (k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0) @ sk_A)),
% 0.90/1.13      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.90/1.13  thf('78', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A)),
% 0.90/1.13      inference('sup+', [status(thm)], ['71', '77'])).
% 0.90/1.13  thf('79', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (((sk_C) = (k6_relat_1 @ sk_A))
% 0.90/1.13          | ((k5_relat_1 @ sk_C @ X0) != (X0))
% 0.90/1.13          | ~ (v2_funct_1 @ X0)
% 0.90/1.13          | ((k1_relat_1 @ X0) != (sk_A))
% 0.90/1.13          | ~ (v1_funct_1 @ X0)
% 0.90/1.13          | ~ (v1_relat_1 @ X0))),
% 0.90/1.13      inference('demod', [status(thm)], ['66', '78'])).
% 0.90/1.13  thf('80', plain,
% 0.90/1.13      ((((sk_B_1) != (sk_B_1))
% 0.90/1.13        | ~ (v1_relat_1 @ sk_B_1)
% 0.90/1.13        | ~ (v1_funct_1 @ sk_B_1)
% 0.90/1.13        | ((k1_relat_1 @ sk_B_1) != (sk_A))
% 0.90/1.13        | ~ (v2_funct_1 @ sk_B_1)
% 0.90/1.13        | ((sk_C) = (k6_relat_1 @ sk_A)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['47', '79'])).
% 0.90/1.13  thf('81', plain,
% 0.90/1.13      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('82', plain,
% 0.90/1.13      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.90/1.13         ((v1_relat_1 @ X22)
% 0.90/1.13          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.90/1.13      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.90/1.13  thf('83', plain, ((v1_relat_1 @ sk_B_1)),
% 0.90/1.13      inference('sup-', [status(thm)], ['81', '82'])).
% 0.90/1.13  thf('84', plain, ((v1_funct_1 @ sk_B_1)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('85', plain,
% 0.90/1.13      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('86', plain,
% 0.90/1.13      (![X62 : $i, X63 : $i]:
% 0.90/1.13         (((k1_relset_1 @ X62 @ X62 @ X63) = (X62))
% 0.90/1.13          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X62 @ X62)))
% 0.90/1.13          | ~ (v1_funct_2 @ X63 @ X62 @ X62)
% 0.90/1.13          | ~ (v1_funct_1 @ X63))),
% 0.90/1.13      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.90/1.13  thf('87', plain,
% 0.90/1.13      ((~ (v1_funct_1 @ sk_B_1)
% 0.90/1.13        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.90/1.13        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (sk_A)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['85', '86'])).
% 0.90/1.13  thf('88', plain, ((v1_funct_1 @ sk_B_1)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('89', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('90', plain,
% 0.90/1.13      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('91', plain,
% 0.90/1.13      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.90/1.13         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 0.90/1.13          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.90/1.13      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.90/1.13  thf('92', plain,
% 0.90/1.13      (((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (k1_relat_1 @ sk_B_1))),
% 0.90/1.13      inference('sup-', [status(thm)], ['90', '91'])).
% 0.90/1.13  thf('93', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.90/1.13      inference('demod', [status(thm)], ['87', '88', '89', '92'])).
% 0.90/1.13  thf('94', plain, ((v2_funct_1 @ sk_B_1)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('95', plain,
% 0.90/1.13      ((((sk_B_1) != (sk_B_1))
% 0.90/1.13        | ((sk_A) != (sk_A))
% 0.90/1.13        | ((sk_C) = (k6_relat_1 @ sk_A)))),
% 0.90/1.13      inference('demod', [status(thm)], ['80', '83', '84', '93', '94'])).
% 0.90/1.13  thf('96', plain, (((sk_C) = (k6_relat_1 @ sk_A))),
% 0.90/1.13      inference('simplify', [status(thm)], ['95'])).
% 0.90/1.13  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 0.90/1.13  thf('97', plain, (![X15 : $i]: (v2_funct_1 @ (k6_relat_1 @ X15))),
% 0.90/1.13      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.90/1.13  thf('98', plain, ((v2_funct_1 @ sk_C)),
% 0.90/1.13      inference('sup+', [status(thm)], ['96', '97'])).
% 0.90/1.13  thf('99', plain,
% 0.90/1.13      ((((k2_relat_1 @ sk_C) != (sk_A))
% 0.90/1.13        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.90/1.13        | ((sk_A) = (k1_xboole_0)))),
% 0.90/1.13      inference('demod', [status(thm)], ['21', '98'])).
% 0.90/1.13  thf(dt_k2_funct_1, axiom,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.90/1.13       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.90/1.13         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.90/1.13  thf('100', plain,
% 0.90/1.13      (![X10 : $i]:
% 0.90/1.13         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 0.90/1.13          | ~ (v1_funct_1 @ X10)
% 0.90/1.13          | ~ (v1_relat_1 @ X10))),
% 0.90/1.13      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.90/1.13  thf(fc6_funct_1, axiom,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.90/1.13       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.90/1.13         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.90/1.13         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.90/1.13  thf('101', plain,
% 0.90/1.13      (![X11 : $i]:
% 0.90/1.13         ((v2_funct_1 @ (k2_funct_1 @ X11))
% 0.90/1.13          | ~ (v2_funct_1 @ X11)
% 0.90/1.13          | ~ (v1_funct_1 @ X11)
% 0.90/1.13          | ~ (v1_relat_1 @ X11))),
% 0.90/1.13      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.90/1.13  thf('102', plain,
% 0.90/1.13      (![X10 : $i]:
% 0.90/1.13         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 0.90/1.13          | ~ (v1_funct_1 @ X10)
% 0.90/1.13          | ~ (v1_relat_1 @ X10))),
% 0.90/1.13      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.90/1.13  thf('103', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.90/1.13      inference('demod', [status(thm)], ['87', '88', '89', '92'])).
% 0.90/1.13  thf('104', plain,
% 0.90/1.13      (![X11 : $i]:
% 0.90/1.13         ((v2_funct_1 @ (k2_funct_1 @ X11))
% 0.90/1.13          | ~ (v2_funct_1 @ X11)
% 0.90/1.13          | ~ (v1_funct_1 @ X11)
% 0.90/1.13          | ~ (v1_relat_1 @ X11))),
% 0.90/1.13      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.90/1.13  thf('105', plain,
% 0.90/1.13      (![X10 : $i]:
% 0.90/1.13         ((v1_funct_1 @ (k2_funct_1 @ X10))
% 0.90/1.13          | ~ (v1_funct_1 @ X10)
% 0.90/1.13          | ~ (v1_relat_1 @ X10))),
% 0.90/1.13      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.90/1.13  thf('106', plain,
% 0.90/1.13      (![X10 : $i]:
% 0.90/1.13         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 0.90/1.13          | ~ (v1_funct_1 @ X10)
% 0.90/1.13          | ~ (v1_relat_1 @ X10))),
% 0.90/1.13      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.90/1.13  thf(t55_funct_1, axiom,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.90/1.13       ( ( v2_funct_1 @ A ) =>
% 0.90/1.13         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.90/1.13           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.90/1.13  thf('107', plain,
% 0.90/1.13      (![X16 : $i]:
% 0.90/1.13         (~ (v2_funct_1 @ X16)
% 0.90/1.13          | ((k1_relat_1 @ X16) = (k2_relat_1 @ (k2_funct_1 @ X16)))
% 0.90/1.13          | ~ (v1_funct_1 @ X16)
% 0.90/1.13          | ~ (v1_relat_1 @ X16))),
% 0.90/1.13      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.90/1.13  thf('108', plain,
% 0.90/1.13      (![X18 : $i]:
% 0.90/1.13         (~ (v2_funct_1 @ X18)
% 0.90/1.13          | ((k5_relat_1 @ (k2_funct_1 @ X18) @ X18)
% 0.90/1.13              = (k6_relat_1 @ (k2_relat_1 @ X18)))
% 0.90/1.13          | ~ (v1_funct_1 @ X18)
% 0.90/1.13          | ~ (v1_relat_1 @ X18))),
% 0.90/1.13      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.90/1.13  thf(t59_funct_1, axiom,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.90/1.13       ( ( v2_funct_1 @ A ) =>
% 0.90/1.13         ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.90/1.13             ( k2_relat_1 @ A ) ) & 
% 0.90/1.13           ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.90/1.13             ( k2_relat_1 @ A ) ) ) ) ))).
% 0.90/1.13  thf('109', plain,
% 0.90/1.13      (![X17 : $i]:
% 0.90/1.13         (~ (v2_funct_1 @ X17)
% 0.90/1.13          | ((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X17) @ X17))
% 0.90/1.13              = (k2_relat_1 @ X17))
% 0.90/1.13          | ~ (v1_funct_1 @ X17)
% 0.90/1.13          | ~ (v1_relat_1 @ X17))),
% 0.90/1.13      inference('cnf', [status(esa)], [t59_funct_1])).
% 0.90/1.13  thf('110', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (((k1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))) = (k2_relat_1 @ X0))
% 0.90/1.13          | ~ (v1_relat_1 @ X0)
% 0.90/1.13          | ~ (v1_funct_1 @ X0)
% 0.90/1.13          | ~ (v2_funct_1 @ X0)
% 0.90/1.13          | ~ (v1_relat_1 @ X0)
% 0.90/1.13          | ~ (v1_funct_1 @ X0)
% 0.90/1.13          | ~ (v2_funct_1 @ X0))),
% 0.90/1.13      inference('sup+', [status(thm)], ['108', '109'])).
% 0.90/1.13  thf('111', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (v2_funct_1 @ X0)
% 0.90/1.13          | ~ (v1_funct_1 @ X0)
% 0.90/1.13          | ~ (v1_relat_1 @ X0)
% 0.90/1.13          | ((k1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.90/1.13              = (k2_relat_1 @ X0)))),
% 0.90/1.13      inference('simplify', [status(thm)], ['110'])).
% 0.90/1.13  thf('112', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (((k1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.90/1.13            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.90/1.13          | ~ (v1_relat_1 @ X0)
% 0.90/1.13          | ~ (v1_funct_1 @ X0)
% 0.90/1.13          | ~ (v2_funct_1 @ X0)
% 0.90/1.13          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.90/1.13          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.90/1.13          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.90/1.13      inference('sup+', [status(thm)], ['107', '111'])).
% 0.90/1.13  thf('113', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (v1_relat_1 @ X0)
% 0.90/1.13          | ~ (v1_funct_1 @ X0)
% 0.90/1.13          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.90/1.13          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.90/1.13          | ~ (v2_funct_1 @ X0)
% 0.90/1.13          | ~ (v1_funct_1 @ X0)
% 0.90/1.13          | ~ (v1_relat_1 @ X0)
% 0.90/1.13          | ((k1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.90/1.13              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['106', '112'])).
% 0.90/1.13  thf('114', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (((k1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.90/1.13            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.90/1.13          | ~ (v2_funct_1 @ X0)
% 0.90/1.13          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.90/1.13          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.90/1.13          | ~ (v1_funct_1 @ X0)
% 0.90/1.13          | ~ (v1_relat_1 @ X0))),
% 0.90/1.13      inference('simplify', [status(thm)], ['113'])).
% 0.90/1.13  thf('115', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (v1_relat_1 @ X0)
% 0.90/1.13          | ~ (v1_funct_1 @ X0)
% 0.90/1.13          | ~ (v1_relat_1 @ X0)
% 0.90/1.13          | ~ (v1_funct_1 @ X0)
% 0.90/1.13          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.90/1.13          | ~ (v2_funct_1 @ X0)
% 0.90/1.13          | ((k1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.90/1.13              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['105', '114'])).
% 0.90/1.13  thf('116', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (((k1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.90/1.13            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.90/1.13          | ~ (v2_funct_1 @ X0)
% 0.90/1.13          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.90/1.13          | ~ (v1_funct_1 @ X0)
% 0.90/1.13          | ~ (v1_relat_1 @ X0))),
% 0.90/1.13      inference('simplify', [status(thm)], ['115'])).
% 0.90/1.13  thf('117', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (v1_relat_1 @ X0)
% 0.90/1.13          | ~ (v1_funct_1 @ X0)
% 0.90/1.13          | ~ (v2_funct_1 @ X0)
% 0.90/1.13          | ~ (v1_relat_1 @ X0)
% 0.90/1.13          | ~ (v1_funct_1 @ X0)
% 0.90/1.13          | ~ (v2_funct_1 @ X0)
% 0.90/1.13          | ((k1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.90/1.13              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['104', '116'])).
% 0.90/1.13  thf('118', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (((k1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.90/1.13            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.90/1.13          | ~ (v2_funct_1 @ X0)
% 0.90/1.13          | ~ (v1_funct_1 @ X0)
% 0.90/1.13          | ~ (v1_relat_1 @ X0))),
% 0.90/1.13      inference('simplify', [status(thm)], ['117'])).
% 0.90/1.13  thf('119', plain,
% 0.90/1.13      ((((k1_relat_1 @ (k6_relat_1 @ sk_A))
% 0.90/1.13          = (k2_relat_1 @ (k2_funct_1 @ sk_B_1)))
% 0.90/1.13        | ~ (v1_relat_1 @ sk_B_1)
% 0.90/1.13        | ~ (v1_funct_1 @ sk_B_1)
% 0.90/1.13        | ~ (v2_funct_1 @ sk_B_1))),
% 0.90/1.13      inference('sup+', [status(thm)], ['103', '118'])).
% 0.90/1.13  thf('120', plain, ((v1_relat_1 @ sk_B_1)),
% 0.90/1.13      inference('sup-', [status(thm)], ['81', '82'])).
% 0.90/1.13  thf('121', plain, ((v1_funct_1 @ sk_B_1)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('122', plain, ((v2_funct_1 @ sk_B_1)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('123', plain,
% 0.90/1.13      (((k1_relat_1 @ (k6_relat_1 @ sk_A))
% 0.90/1.13         = (k2_relat_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.90/1.13      inference('demod', [status(thm)], ['119', '120', '121', '122'])).
% 0.90/1.13  thf('124', plain,
% 0.90/1.13      (![X16 : $i]:
% 0.90/1.13         (~ (v2_funct_1 @ X16)
% 0.90/1.13          | ((k1_relat_1 @ X16) = (k2_relat_1 @ (k2_funct_1 @ X16)))
% 0.90/1.13          | ~ (v1_funct_1 @ X16)
% 0.90/1.13          | ~ (v1_relat_1 @ X16))),
% 0.90/1.13      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.90/1.13  thf('125', plain,
% 0.90/1.13      (((k1_relat_1 @ (k6_relat_1 @ sk_A))
% 0.90/1.13         = (k2_relat_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.90/1.13      inference('demod', [status(thm)], ['119', '120', '121', '122'])).
% 0.90/1.13  thf('126', plain,
% 0.90/1.13      ((((k1_relat_1 @ (k6_relat_1 @ sk_A)) = (k1_relat_1 @ sk_B_1))
% 0.90/1.13        | ~ (v1_relat_1 @ sk_B_1)
% 0.90/1.13        | ~ (v1_funct_1 @ sk_B_1)
% 0.90/1.13        | ~ (v2_funct_1 @ sk_B_1))),
% 0.90/1.13      inference('sup+', [status(thm)], ['124', '125'])).
% 0.90/1.13  thf('127', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.90/1.13      inference('demod', [status(thm)], ['87', '88', '89', '92'])).
% 0.90/1.13  thf('128', plain, ((v1_relat_1 @ sk_B_1)),
% 0.90/1.13      inference('sup-', [status(thm)], ['81', '82'])).
% 0.90/1.13  thf('129', plain, ((v1_funct_1 @ sk_B_1)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('130', plain, ((v2_funct_1 @ sk_B_1)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('131', plain, (((k1_relat_1 @ (k6_relat_1 @ sk_A)) = (sk_A))),
% 0.90/1.13      inference('demod', [status(thm)], ['126', '127', '128', '129', '130'])).
% 0.90/1.13  thf('132', plain, (((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.90/1.13      inference('demod', [status(thm)], ['123', '131'])).
% 0.90/1.13  thf('133', plain,
% 0.90/1.13      (![X18 : $i]:
% 0.90/1.13         (~ (v2_funct_1 @ X18)
% 0.90/1.13          | ((k5_relat_1 @ (k2_funct_1 @ X18) @ X18)
% 0.90/1.13              = (k6_relat_1 @ (k2_relat_1 @ X18)))
% 0.90/1.13          | ~ (v1_funct_1 @ X18)
% 0.90/1.13          | ~ (v1_relat_1 @ X18))),
% 0.90/1.13      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.90/1.13  thf('134', plain,
% 0.90/1.13      (![X17 : $i]:
% 0.90/1.13         (~ (v2_funct_1 @ X17)
% 0.90/1.13          | ((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X17) @ X17))
% 0.90/1.13              = (k2_relat_1 @ X17))
% 0.90/1.13          | ~ (v1_funct_1 @ X17)
% 0.90/1.13          | ~ (v1_relat_1 @ X17))),
% 0.90/1.13      inference('cnf', [status(esa)], [t59_funct_1])).
% 0.90/1.13  thf('135', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (((k2_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))) = (k2_relat_1 @ X0))
% 0.90/1.13          | ~ (v1_relat_1 @ X0)
% 0.90/1.13          | ~ (v1_funct_1 @ X0)
% 0.90/1.13          | ~ (v2_funct_1 @ X0)
% 0.90/1.13          | ~ (v1_relat_1 @ X0)
% 0.90/1.13          | ~ (v1_funct_1 @ X0)
% 0.90/1.13          | ~ (v2_funct_1 @ X0))),
% 0.90/1.13      inference('sup+', [status(thm)], ['133', '134'])).
% 0.90/1.13  thf('136', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (v2_funct_1 @ X0)
% 0.90/1.13          | ~ (v1_funct_1 @ X0)
% 0.90/1.13          | ~ (v1_relat_1 @ X0)
% 0.90/1.13          | ((k2_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.90/1.13              = (k2_relat_1 @ X0)))),
% 0.90/1.13      inference('simplify', [status(thm)], ['135'])).
% 0.90/1.13  thf('137', plain,
% 0.90/1.13      ((((k2_relat_1 @ (k6_relat_1 @ sk_A))
% 0.90/1.13          = (k2_relat_1 @ (k2_funct_1 @ sk_B_1)))
% 0.90/1.13        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B_1))
% 0.90/1.13        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.90/1.13        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.90/1.13      inference('sup+', [status(thm)], ['132', '136'])).
% 0.90/1.13  thf('138', plain, (((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.90/1.13      inference('demod', [status(thm)], ['123', '131'])).
% 0.90/1.13  thf('139', plain,
% 0.90/1.13      ((((k2_relat_1 @ (k6_relat_1 @ sk_A)) = (sk_A))
% 0.90/1.13        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B_1))
% 0.90/1.13        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.90/1.13        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.90/1.13      inference('demod', [status(thm)], ['137', '138'])).
% 0.90/1.13  thf('140', plain,
% 0.90/1.13      ((~ (v1_relat_1 @ sk_B_1)
% 0.90/1.13        | ~ (v1_funct_1 @ sk_B_1)
% 0.90/1.13        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.90/1.13        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.90/1.13        | ((k2_relat_1 @ (k6_relat_1 @ sk_A)) = (sk_A)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['102', '139'])).
% 0.90/1.13  thf('141', plain, ((v1_relat_1 @ sk_B_1)),
% 0.90/1.13      inference('sup-', [status(thm)], ['81', '82'])).
% 0.90/1.13  thf('142', plain, ((v1_funct_1 @ sk_B_1)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('143', plain,
% 0.90/1.13      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.90/1.13        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 0.90/1.13        | ((k2_relat_1 @ (k6_relat_1 @ sk_A)) = (sk_A)))),
% 0.90/1.13      inference('demod', [status(thm)], ['140', '141', '142'])).
% 0.90/1.13  thf('144', plain,
% 0.90/1.13      ((~ (v1_relat_1 @ sk_B_1)
% 0.90/1.13        | ~ (v1_funct_1 @ sk_B_1)
% 0.90/1.13        | ~ (v2_funct_1 @ sk_B_1)
% 0.90/1.13        | ((k2_relat_1 @ (k6_relat_1 @ sk_A)) = (sk_A))
% 0.90/1.13        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['101', '143'])).
% 0.90/1.13  thf('145', plain, ((v1_relat_1 @ sk_B_1)),
% 0.90/1.13      inference('sup-', [status(thm)], ['81', '82'])).
% 0.90/1.13  thf('146', plain, ((v1_funct_1 @ sk_B_1)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('147', plain, ((v2_funct_1 @ sk_B_1)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('148', plain,
% 0.90/1.13      ((((k2_relat_1 @ (k6_relat_1 @ sk_A)) = (sk_A))
% 0.90/1.13        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1)))),
% 0.90/1.13      inference('demod', [status(thm)], ['144', '145', '146', '147'])).
% 0.90/1.13  thf('149', plain,
% 0.90/1.13      ((~ (v1_relat_1 @ sk_B_1)
% 0.90/1.13        | ~ (v1_funct_1 @ sk_B_1)
% 0.90/1.13        | ((k2_relat_1 @ (k6_relat_1 @ sk_A)) = (sk_A)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['100', '148'])).
% 0.90/1.13  thf('150', plain, ((v1_relat_1 @ sk_B_1)),
% 0.90/1.13      inference('sup-', [status(thm)], ['81', '82'])).
% 0.90/1.13  thf('151', plain, ((v1_funct_1 @ sk_B_1)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('152', plain, (((k2_relat_1 @ (k6_relat_1 @ sk_A)) = (sk_A))),
% 0.90/1.13      inference('demod', [status(thm)], ['149', '150', '151'])).
% 0.90/1.13  thf('153', plain, (((sk_C) = (k6_relat_1 @ sk_A))),
% 0.90/1.13      inference('simplify', [status(thm)], ['95'])).
% 0.90/1.13  thf('154', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.90/1.13      inference('demod', [status(thm)], ['152', '153'])).
% 0.90/1.13  thf('155', plain,
% 0.90/1.13      ((((sk_A) != (sk_A))
% 0.90/1.13        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.90/1.13        | ((sk_A) = (k1_xboole_0)))),
% 0.90/1.13      inference('demod', [status(thm)], ['99', '154'])).
% 0.90/1.13  thf('156', plain,
% 0.90/1.13      ((((sk_A) = (k1_xboole_0))
% 0.90/1.13        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 0.90/1.13      inference('simplify', [status(thm)], ['155'])).
% 0.90/1.13  thf('157', plain,
% 0.90/1.13      ((((k6_relat_1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.90/1.13        | ~ (v1_relat_1 @ sk_C)
% 0.90/1.13        | ~ (v1_funct_1 @ sk_C)
% 0.90/1.13        | ~ (v2_funct_1 @ sk_C)
% 0.90/1.13        | ((sk_A) = (k1_xboole_0)))),
% 0.90/1.13      inference('sup+', [status(thm)], ['12', '156'])).
% 0.90/1.13  thf('158', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.90/1.13      inference('demod', [status(thm)], ['50', '51', '52', '55'])).
% 0.90/1.13  thf('159', plain, (((sk_C) = (k6_relat_1 @ sk_A))),
% 0.90/1.13      inference('simplify', [status(thm)], ['95'])).
% 0.90/1.13  thf('160', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.13      inference('sup-', [status(thm)], ['60', '61'])).
% 0.90/1.13  thf('161', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('162', plain, ((v2_funct_1 @ sk_C)),
% 0.90/1.13      inference('sup+', [status(thm)], ['96', '97'])).
% 0.90/1.13  thf('163', plain,
% 0.90/1.13      ((((sk_C) = (k6_partfun1 @ sk_A)) | ((sk_A) = (k1_xboole_0)))),
% 0.90/1.13      inference('demod', [status(thm)],
% 0.90/1.13                ['157', '158', '159', '160', '161', '162'])).
% 0.90/1.13  thf('164', plain,
% 0.90/1.13      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_partfun1 @ sk_A))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('165', plain,
% 0.90/1.13      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['163', '164'])).
% 0.90/1.13  thf('166', plain,
% 0.90/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('167', plain,
% 0.90/1.13      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.90/1.13         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.90/1.13          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.90/1.13          | (r2_relset_1 @ X32 @ X33 @ X31 @ X34)
% 0.90/1.13          | ((X31) != (X34)))),
% 0.90/1.13      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.90/1.13  thf('168', plain,
% 0.90/1.13      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.90/1.13         ((r2_relset_1 @ X32 @ X33 @ X34 @ X34)
% 0.90/1.13          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.90/1.13      inference('simplify', [status(thm)], ['167'])).
% 0.90/1.13  thf('169', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 0.90/1.13      inference('sup-', [status(thm)], ['166', '168'])).
% 0.90/1.13  thf('170', plain, (((sk_A) = (k1_xboole_0))),
% 0.90/1.13      inference('demod', [status(thm)], ['165', '169'])).
% 0.90/1.13  thf('171', plain, (![X0 : $i]: (v1_xboole_0 @ (sk_B @ X0))),
% 0.90/1.13      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.90/1.13  thf('172', plain,
% 0.90/1.13      (![X48 : $i]:
% 0.90/1.13         (m1_subset_1 @ (k6_partfun1 @ X48) @ 
% 0.90/1.13          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X48)))),
% 0.90/1.13      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.90/1.13  thf('173', plain,
% 0.90/1.13      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 0.90/1.13      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.90/1.13  thf('174', plain,
% 0.90/1.13      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.90/1.13         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))
% 0.90/1.13          | (r2_relset_1 @ X39 @ X39 @ X40 @ X38)
% 0.90/1.13          | (r2_hidden @ (sk_D @ X38 @ X40 @ X39) @ X39)
% 0.90/1.13          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39))))),
% 0.90/1.13      inference('cnf', [status(esa)], [t54_relset_1])).
% 0.90/1.13  thf('175', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0)))
% 0.90/1.13          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.90/1.13          | (r2_relset_1 @ X0 @ X0 @ X1 @ k1_xboole_0))),
% 0.90/1.13      inference('sup-', [status(thm)], ['173', '174'])).
% 0.90/1.13  thf('176', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         ((r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ k1_xboole_0)
% 0.90/1.13          | (r2_hidden @ (sk_D @ k1_xboole_0 @ (k6_partfun1 @ X0) @ X0) @ X0))),
% 0.90/1.13      inference('sup-', [status(thm)], ['172', '175'])).
% 0.90/1.13  thf('177', plain,
% 0.90/1.13      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 0.90/1.13      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.90/1.13  thf(t5_subset, axiom,
% 0.90/1.13    (![A:$i,B:$i,C:$i]:
% 0.90/1.13     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.90/1.13          ( v1_xboole_0 @ C ) ) ))).
% 0.90/1.13  thf('178', plain,
% 0.90/1.13      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.90/1.13         (~ (r2_hidden @ X7 @ X8)
% 0.90/1.13          | ~ (v1_xboole_0 @ X9)
% 0.90/1.13          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.90/1.13      inference('cnf', [status(esa)], [t5_subset])).
% 0.90/1.13  thf('179', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.90/1.13      inference('sup-', [status(thm)], ['177', '178'])).
% 0.90/1.13  thf('180', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 0.90/1.13           (k6_partfun1 @ k1_xboole_0) @ k1_xboole_0)
% 0.90/1.13          | ~ (v1_xboole_0 @ X0))),
% 0.90/1.13      inference('sup-', [status(thm)], ['176', '179'])).
% 0.90/1.13  thf('181', plain,
% 0.90/1.13      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 0.90/1.13      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.90/1.13  thf('182', plain,
% 0.90/1.13      (![X48 : $i]:
% 0.90/1.13         (m1_subset_1 @ (k6_partfun1 @ X48) @ 
% 0.90/1.13          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X48)))),
% 0.90/1.13      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.90/1.13  thf('183', plain,
% 0.90/1.13      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.90/1.13         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.90/1.13          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.90/1.13          | ((X31) = (X34))
% 0.90/1.13          | ~ (r2_relset_1 @ X32 @ X33 @ X31 @ X34))),
% 0.90/1.13      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.90/1.13  thf('184', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         (~ (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ X1)
% 0.90/1.13          | ((k6_partfun1 @ X0) = (X1))
% 0.90/1.13          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['182', '183'])).
% 0.90/1.13  thf('185', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (((k6_partfun1 @ X0) = (k1_xboole_0))
% 0.90/1.13          | ~ (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ k1_xboole_0))),
% 0.90/1.13      inference('sup-', [status(thm)], ['181', '184'])).
% 0.90/1.13  thf('186', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (v1_xboole_0 @ X0) | ((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['180', '185'])).
% 0.90/1.13  thf('187', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.90/1.13      inference('sup-', [status(thm)], ['171', '186'])).
% 0.90/1.13  thf('188', plain, (((sk_A) = (k1_xboole_0))),
% 0.90/1.13      inference('demod', [status(thm)], ['165', '169'])).
% 0.90/1.13  thf('189', plain, (((sk_A) = (k1_xboole_0))),
% 0.90/1.13      inference('demod', [status(thm)], ['165', '169'])).
% 0.90/1.13  thf('190', plain,
% 0.90/1.13      ((r2_hidden @ (sk_D @ k1_xboole_0 @ sk_C @ k1_xboole_0) @ k1_xboole_0)),
% 0.90/1.13      inference('demod', [status(thm)], ['11', '170', '187', '188', '189'])).
% 0.90/1.13  thf('191', plain, (((sk_C) = (k6_relat_1 @ sk_A))),
% 0.90/1.13      inference('simplify', [status(thm)], ['95'])).
% 0.90/1.13  thf('192', plain, (((sk_A) = (k1_xboole_0))),
% 0.90/1.13      inference('demod', [status(thm)], ['165', '169'])).
% 0.90/1.13  thf('193', plain, (((sk_C) = (k6_relat_1 @ k1_xboole_0))),
% 0.90/1.13      inference('demod', [status(thm)], ['191', '192'])).
% 0.90/1.13  thf('194', plain,
% 0.90/1.13      ((r2_hidden @ 
% 0.90/1.13        (sk_D @ k1_xboole_0 @ (k6_relat_1 @ k1_xboole_0) @ k1_xboole_0) @ 
% 0.90/1.13        k1_xboole_0)),
% 0.90/1.13      inference('demod', [status(thm)], ['190', '193'])).
% 0.90/1.13  thf('195', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.90/1.13      inference('sup-', [status(thm)], ['177', '178'])).
% 0.90/1.13  thf('196', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 0.90/1.13      inference('sup-', [status(thm)], ['194', '195'])).
% 0.90/1.13  thf('197', plain, ($false), inference('sup-', [status(thm)], ['4', '196'])).
% 0.90/1.13  
% 0.90/1.13  % SZS output end Refutation
% 0.90/1.13  
% 0.98/1.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

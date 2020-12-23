%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Y2q674jlRx

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:50 EST 2020

% Result     : Theorem 2.25s
% Output     : Refutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :  297 (14985 expanded)
%              Number of leaves         :   56 (4243 expanded)
%              Depth                    :   36
%              Number of atoms          : 2836 (351740 expanded)
%              Number of equality atoms :  250 (4861 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

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

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X25: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k2_relat_1 @ X25 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('2',plain,(
    ! [X25: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k2_relat_1 @ X25 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_1 @ X54 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X56 ) ) )
      | ( ( k1_partfun1 @ X52 @ X53 @ X55 @ X56 @ X51 @ X54 )
        = ( k5_relat_1 @ X51 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
      = ( k5_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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

thf('13',plain,(
    ! [X58: $i,X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ~ ( v1_funct_1 @ X58 )
      | ~ ( v1_funct_2 @ X58 @ X59 @ X60 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X60 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X61 @ X59 @ X59 @ X60 @ X62 @ X58 ) )
      | ( v2_funct_1 @ X62 )
      | ( X60 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X61 @ X59 ) ) )
      | ~ ( v1_funct_2 @ X62 @ X61 @ X59 )
      | ~ ( v1_funct_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_B ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_B ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','19','20','21'])).

thf('23',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('25',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
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

thf('28',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X46 @ X47 @ X49 @ X50 @ X45 @ X48 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X50 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('36',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('37',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( X38 = X41 )
      | ~ ( r2_relset_1 @ X39 @ X40 @ X38 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_B ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_B )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['25','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k5_relat_1 @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','41','42'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('44',plain,(
    ! [X20: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v2_funct_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('45',plain,(
    ! [X20: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v2_funct_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('46',plain,
    ( ( k5_relat_1 @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['39','40'])).

thf(t66_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( v2_funct_1 @ B ) )
           => ( ( k2_funct_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k5_relat_1 @ ( k2_funct_1 @ B ) @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('47',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ( ( k2_funct_1 @ ( k5_relat_1 @ X27 @ X26 ) )
        = ( k5_relat_1 @ ( k2_funct_1 @ X26 ) @ ( k2_funct_1 @ X27 ) ) )
      | ~ ( v2_funct_1 @ X26 )
      | ~ ( v2_funct_1 @ X27 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t66_funct_1])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('49',plain,(
    ! [X66: $i,X67: $i] :
      ( ( ( k1_relset_1 @ X66 @ X66 @ X67 )
        = X66 )
      | ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X66 @ X66 ) ) )
      | ~ ( v1_funct_2 @ X67 @ X66 @ X66 )
      | ~ ( v1_funct_1 @ X67 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('50',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('54',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X32 @ X33 @ X31 )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('55',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['50','51','52','55'])).

thf('57',plain,(
    ! [X20: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v2_funct_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('58',plain,(
    ! [X20: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v2_funct_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('59',plain,(
    ! [X25: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k1_relat_1 @ X25 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t44_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k2_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ( ( k5_relat_1 @ A @ B )
                = A ) )
           => ( B
              = ( k6_relat_1 @ ( k1_relat_1 @ B ) ) ) ) ) ) )).

thf('60',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ( X23
        = ( k6_relat_1 @ ( k1_relat_1 @ X23 ) ) )
      | ( ( k5_relat_1 @ X24 @ X23 )
       != X24 )
      | ( ( k2_relat_1 @ X24 )
       != ( k1_relat_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t44_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('61',plain,(
    ! [X57: $i] :
      ( ( k6_partfun1 @ X57 )
      = ( k6_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('62',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ( X23
        = ( k6_partfun1 @ ( k1_relat_1 @ X23 ) ) )
      | ( ( k5_relat_1 @ X24 @ X23 )
       != X24 )
      | ( ( k2_relat_1 @ X24 )
       != ( k1_relat_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
       != ( k2_funct_1 @ X0 ) )
      | ( X1
        = ( k6_partfun1 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X1
        = ( k6_partfun1 @ ( k1_relat_1 @ X1 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
       != ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
       != ( k2_funct_1 @ X0 ) )
      | ( X1
        = ( k6_partfun1 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X1
        = ( k6_partfun1 @ ( k1_relat_1 @ X1 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
       != ( k2_funct_1 @ X0 ) )
      | ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['57','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X1 ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
       != ( k2_funct_1 @ X0 ) )
      | ( X1
        = ( k6_partfun1 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 )
       != ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['56','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('71',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('72',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('73',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 )
       != ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['68','73','74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k5_relat_1 @ X0 @ sk_B ) )
       != ( k2_funct_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k2_funct_1 @ X0 )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( sk_A
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['47','76'])).

thf('78',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['71','72'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k5_relat_1 @ X0 @ sk_B ) )
       != ( k2_funct_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( sk_A
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['77','78','79','80'])).

thf('82',plain,
    ( ( ( k2_funct_1 @ sk_B )
     != ( k2_funct_1 @ sk_B ) )
    | ( sk_A
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_funct_1 @ sk_C )
      = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['46','81'])).

thf('83',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('86',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('88',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ( k2_funct_1 @ sk_B )
     != ( k2_funct_1 @ sk_B ) )
    | ( sk_A
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_funct_1 @ sk_C )
      = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['82','83','88'])).

thf('90',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_A
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_A
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_funct_1 @ sk_C )
      = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['45','90'])).

thf('92',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['86','87'])).

thf('93',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ( sk_A
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_funct_1 @ sk_C )
      = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_A
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_A
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_funct_1 @ sk_C )
      = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['44','95'])).

thf('97',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['86','87'])).

thf('98',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_A
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_funct_1 @ sk_C )
      = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ( sk_A
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_A
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_funct_1 @ sk_C )
      = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['43','100'])).

thf('102',plain,
    ( ( sk_A
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','101'])).

thf('103',plain,
    ( ( k5_relat_1 @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['39','40'])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('104',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) )
        = ( k9_relat_1 @ X8 @ ( k2_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('105',plain,(
    ! [X10: $i] :
      ( ( ( k10_relat_1 @ X10 @ ( k2_relat_1 @ X10 ) )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k10_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) @ ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_C ) ) )
      = ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['103','106'])).

thf('108',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['71','72'])).

thf('109',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['71','72'])).

thf('110',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['86','87'])).

thf('111',plain,
    ( ( k5_relat_1 @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['39','40'])).

thf('112',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('113',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v5_relat_1 @ X28 @ X30 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('114',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['112','113'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('115',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v5_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k2_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('116',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['86','87'])).

thf('118',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['50','51','52','55'])).

thf(t164_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('120',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X21 @ ( k1_relat_1 @ X22 ) )
      | ~ ( v2_funct_1 @ X22 )
      | ( ( k10_relat_1 @ X22 @ ( k9_relat_1 @ X22 @ X21 ) )
        = X21 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ X0 ) )
        = X0 )
      | ~ ( v2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['71','72'])).

thf('123',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['121','122','123','124'])).

thf('126',plain,
    ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_C ) ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['118','125'])).

thf('127',plain,
    ( ( k5_relat_1 @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['39','40'])).

thf('128',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['50','51','52','55'])).

thf('129',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['107','108','109','110','111','126','127','128'])).

thf('130',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['86','87'])).

thf('131',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['102','129','130','131'])).

thf('133',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_funct_1 @ sk_C )
      = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','41','42'])).

thf('135',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['133','134'])).

thf('136',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','135'])).

thf('137',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['107','108','109','110','111','126','127','128'])).

thf('138',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['86','87'])).

thf('139',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['136','137','138','139'])).

thf('141',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','41','42'])).

thf('142',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_funct_1 @ sk_C )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['140','141'])).

thf('143',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','41','42'])).

thf('144',plain,(
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

thf('145',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ( X63 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X64 )
      | ~ ( v1_funct_2 @ X64 @ X65 @ X63 )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X65 @ X63 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X64 ) @ X64 )
        = ( k6_partfun1 @ X63 ) )
      | ~ ( v2_funct_1 @ X64 )
      | ( ( k2_relset_1 @ X65 @ X63 @ X64 )
       != X63 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('146',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_A @ sk_C )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('148',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( ( k7_relset_1 @ X42 @ X43 @ X44 @ X42 )
        = ( k2_relset_1 @ X42 @ X43 @ X44 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('149',plain,
    ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_A )
    = ( k2_relset_1 @ sk_A @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('151',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( ( k7_relset_1 @ X35 @ X36 @ X34 @ X37 )
        = ( k9_relat_1 @ X34 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,
    ( ( k9_relat_1 @ sk_C @ sk_A )
    = ( k2_relset_1 @ sk_A @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['149','152'])).

thf('154',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v4_relat_1 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('156',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['154','155'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('157',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11
        = ( k7_relat_1 @ X11 @ X12 ) )
      | ~ ( v4_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('158',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['86','87'])).

thf('160',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['158','159'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('161',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X6 @ X7 ) )
        = ( k9_relat_1 @ X6 @ X7 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('162',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['160','161'])).

thf('163',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['86','87'])).

thf('164',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_relset_1 @ sk_A @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['153','164'])).

thf('166',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['146','165','166','167'])).

thf('169',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['107','108','109','110','111','126','127','128'])).

thf('170',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','41','42'])).

thf('173',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X1 ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
       != ( k2_funct_1 @ X0 ) )
      | ( X1
        = ( k6_partfun1 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
       != ( k2_funct_1 @ X0 ) ) ) ),
    inference(eq_res,[status(thm)],['174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
       != ( k2_funct_1 @ X0 ) )
      | ( X0
        = ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k2_funct_1 @ sk_C ) )
    | ( sk_A = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_C
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['173','176'])).

thf('178',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['86','87'])).

thf('179',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    ! [X66: $i,X67: $i] :
      ( ( ( k1_relset_1 @ X66 @ X66 @ X67 )
        = X66 )
      | ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X66 @ X66 ) ) )
      | ~ ( v1_funct_2 @ X67 @ X66 @ X66 )
      | ~ ( v1_funct_1 @ X67 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('182',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X32 @ X33 @ X31 )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('187',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['182','183','184','187'])).

thf('189',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k2_funct_1 @ sk_C ) )
    | ( sk_A = k1_xboole_0 )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_C
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['177','178','179','188'])).

thf('190',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 )
    | ( ( k6_partfun1 @ sk_A )
     != ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['143','189'])).

thf('191',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k2_funct_1 @ sk_C ) )
    | ( sk_C
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['142','191'])).

thf('193',plain,
    ( ( sk_C
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['192'])).

thf('194',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( r2_relset_1 @ X39 @ X40 @ X38 @ X41 )
      | ( X38 != X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('198',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( r2_relset_1 @ X39 @ X40 @ X41 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ) ),
    inference(simplify,[status(thm)],['197'])).

thf('199',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['196','198'])).

thf('200',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['195','199'])).

thf('201',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['195','199'])).

thf('202',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['195','199'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('203',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('204',plain,(
    ! [X57: $i] :
      ( ( k6_partfun1 @ X57 )
      = ( k6_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('205',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X14 ) )
      = X14 ) ),
    inference(demod,[status(thm)],['203','204'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('206',plain,(
    ! [X13: $i] :
      ( ( ( k1_relat_1 @ X13 )
       != k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('207',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k6_partfun1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('208',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('209',plain,(
    ! [X57: $i] :
      ( ( k6_partfun1 @ X57 )
      = ( k6_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('210',plain,(
    ! [X18: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X18 ) ) ),
    inference(demod,[status(thm)],['208','209'])).

thf('211',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k6_partfun1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['207','210'])).

thf('212',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['211'])).

thf('213',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['0','200','201','202','212'])).

thf('214',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['182','183','184','187'])).

thf('215',plain,(
    ! [X13: $i] :
      ( ( ( k1_relat_1 @ X13 )
       != k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('216',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['86','87'])).

thf('218',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['216','217'])).

thf('219',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['195','199'])).

thf('220',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['218','219'])).

thf('221',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['220'])).

thf('222',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['213','221'])).

thf('223',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( r2_relset_1 @ X39 @ X40 @ X41 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ) ),
    inference(simplify,[status(thm)],['197'])).

thf('225',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B ),
    inference('sup-',[status(thm)],['223','224'])).

thf('226',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['195','199'])).

thf('227',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['195','199'])).

thf('228',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['225','226','227'])).

thf('229',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['50','51','52','55'])).

thf('230',plain,(
    ! [X13: $i] :
      ( ( ( k1_relat_1 @ X13 )
       != k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('231',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['229','230'])).

thf('232',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['71','72'])).

thf('233',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['231','232'])).

thf('234',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['195','199'])).

thf('235',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['233','234'])).

thf('236',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['235'])).

thf('237',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['235'])).

thf('238',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['228','236','237'])).

thf('239',plain,(
    $false ),
    inference(demod,[status(thm)],['222','238'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Y2q674jlRx
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:28:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.25/2.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.25/2.45  % Solved by: fo/fo7.sh
% 2.25/2.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.25/2.45  % done 2381 iterations in 1.985s
% 2.25/2.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.25/2.45  % SZS output start Refutation
% 2.25/2.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.25/2.45  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.25/2.45  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.25/2.45  thf(sk_A_type, type, sk_A: $i).
% 2.25/2.45  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.25/2.45  thf(sk_B_type, type, sk_B: $i).
% 2.25/2.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.25/2.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.25/2.45  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 2.25/2.45  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.25/2.45  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 2.25/2.45  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 2.25/2.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.25/2.45  thf(sk_C_type, type, sk_C: $i).
% 2.25/2.45  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.25/2.45  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.25/2.45  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.25/2.45  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.25/2.45  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.25/2.45  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.25/2.45  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.25/2.45  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.25/2.45  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.25/2.45  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.25/2.45  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.25/2.45  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.25/2.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.25/2.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.25/2.45  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.25/2.45  thf(t76_funct_2, conjecture,
% 2.25/2.45    (![A:$i,B:$i]:
% 2.25/2.45     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 2.25/2.45         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 2.25/2.45       ( ![C:$i]:
% 2.25/2.45         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 2.25/2.45             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 2.25/2.45           ( ( ( r2_relset_1 @
% 2.25/2.45                 A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B ) & 
% 2.25/2.45               ( v2_funct_1 @ B ) ) =>
% 2.25/2.45             ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ))).
% 2.25/2.45  thf(zf_stmt_0, negated_conjecture,
% 2.25/2.45    (~( ![A:$i,B:$i]:
% 2.25/2.45        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 2.25/2.45            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 2.25/2.45          ( ![C:$i]:
% 2.25/2.45            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 2.25/2.45                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 2.25/2.45              ( ( ( r2_relset_1 @
% 2.25/2.45                    A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B ) & 
% 2.25/2.45                  ( v2_funct_1 @ B ) ) =>
% 2.25/2.45                ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ) )),
% 2.25/2.45    inference('cnf.neg', [status(esa)], [t76_funct_2])).
% 2.25/2.45  thf('0', plain,
% 2.25/2.45      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_partfun1 @ sk_A))),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf(t55_funct_1, axiom,
% 2.25/2.45    (![A:$i]:
% 2.25/2.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.25/2.45       ( ( v2_funct_1 @ A ) =>
% 2.25/2.45         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 2.25/2.45           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.25/2.45  thf('1', plain,
% 2.25/2.45      (![X25 : $i]:
% 2.25/2.45         (~ (v2_funct_1 @ X25)
% 2.25/2.45          | ((k2_relat_1 @ X25) = (k1_relat_1 @ (k2_funct_1 @ X25)))
% 2.25/2.45          | ~ (v1_funct_1 @ X25)
% 2.25/2.45          | ~ (v1_relat_1 @ X25))),
% 2.25/2.45      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.25/2.45  thf('2', plain,
% 2.25/2.45      (![X25 : $i]:
% 2.25/2.45         (~ (v2_funct_1 @ X25)
% 2.25/2.45          | ((k2_relat_1 @ X25) = (k1_relat_1 @ (k2_funct_1 @ X25)))
% 2.25/2.45          | ~ (v1_funct_1 @ X25)
% 2.25/2.45          | ~ (v1_relat_1 @ X25))),
% 2.25/2.45      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.25/2.45  thf('3', plain,
% 2.25/2.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('4', plain,
% 2.25/2.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf(redefinition_k1_partfun1, axiom,
% 2.25/2.45    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.25/2.45     ( ( ( v1_funct_1 @ E ) & 
% 2.25/2.45         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.25/2.45         ( v1_funct_1 @ F ) & 
% 2.25/2.45         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.25/2.45       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.25/2.45  thf('5', plain,
% 2.25/2.45      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 2.25/2.45         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53)))
% 2.25/2.45          | ~ (v1_funct_1 @ X51)
% 2.25/2.45          | ~ (v1_funct_1 @ X54)
% 2.25/2.45          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X56)))
% 2.25/2.45          | ((k1_partfun1 @ X52 @ X53 @ X55 @ X56 @ X51 @ X54)
% 2.25/2.45              = (k5_relat_1 @ X51 @ X54)))),
% 2.25/2.45      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 2.25/2.45  thf('6', plain,
% 2.25/2.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.25/2.45         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0)
% 2.25/2.45            = (k5_relat_1 @ sk_C @ X0))
% 2.25/2.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.25/2.45          | ~ (v1_funct_1 @ X0)
% 2.25/2.45          | ~ (v1_funct_1 @ sk_C))),
% 2.25/2.45      inference('sup-', [status(thm)], ['4', '5'])).
% 2.25/2.45  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('8', plain,
% 2.25/2.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.25/2.45         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0)
% 2.25/2.45            = (k5_relat_1 @ sk_C @ X0))
% 2.25/2.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.25/2.45          | ~ (v1_funct_1 @ X0))),
% 2.25/2.45      inference('demod', [status(thm)], ['6', '7'])).
% 2.25/2.45  thf('9', plain,
% 2.25/2.45      ((~ (v1_funct_1 @ sk_B)
% 2.25/2.45        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 2.25/2.45            = (k5_relat_1 @ sk_C @ sk_B)))),
% 2.25/2.45      inference('sup-', [status(thm)], ['3', '8'])).
% 2.25/2.45  thf('10', plain, ((v1_funct_1 @ sk_B)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('11', plain,
% 2.25/2.45      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 2.25/2.45         = (k5_relat_1 @ sk_C @ sk_B))),
% 2.25/2.45      inference('demod', [status(thm)], ['9', '10'])).
% 2.25/2.45  thf('12', plain,
% 2.25/2.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf(t26_funct_2, axiom,
% 2.25/2.45    (![A:$i,B:$i,C:$i,D:$i]:
% 2.25/2.45     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.25/2.45         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.25/2.45       ( ![E:$i]:
% 2.25/2.45         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.25/2.45             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.25/2.45           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 2.25/2.45             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 2.25/2.45               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 2.25/2.45  thf('13', plain,
% 2.25/2.45      (![X58 : $i, X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 2.25/2.45         (~ (v1_funct_1 @ X58)
% 2.25/2.45          | ~ (v1_funct_2 @ X58 @ X59 @ X60)
% 2.25/2.45          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X60)))
% 2.25/2.45          | ~ (v2_funct_1 @ (k1_partfun1 @ X61 @ X59 @ X59 @ X60 @ X62 @ X58))
% 2.25/2.45          | (v2_funct_1 @ X62)
% 2.25/2.45          | ((X60) = (k1_xboole_0))
% 2.25/2.45          | ~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X61 @ X59)))
% 2.25/2.45          | ~ (v1_funct_2 @ X62 @ X61 @ X59)
% 2.25/2.45          | ~ (v1_funct_1 @ X62))),
% 2.25/2.45      inference('cnf', [status(esa)], [t26_funct_2])).
% 2.25/2.45  thf('14', plain,
% 2.25/2.45      (![X0 : $i, X1 : $i]:
% 2.25/2.45         (~ (v1_funct_1 @ X0)
% 2.25/2.45          | ~ (v1_funct_2 @ X0 @ X1 @ sk_A)
% 2.25/2.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 2.25/2.45          | ((sk_A) = (k1_xboole_0))
% 2.25/2.45          | (v2_funct_1 @ X0)
% 2.25/2.45          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B))
% 2.25/2.45          | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 2.25/2.45          | ~ (v1_funct_1 @ sk_B))),
% 2.25/2.45      inference('sup-', [status(thm)], ['12', '13'])).
% 2.25/2.45  thf('15', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('16', plain, ((v1_funct_1 @ sk_B)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('17', plain,
% 2.25/2.45      (![X0 : $i, X1 : $i]:
% 2.25/2.45         (~ (v1_funct_1 @ X0)
% 2.25/2.45          | ~ (v1_funct_2 @ X0 @ X1 @ sk_A)
% 2.25/2.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 2.25/2.45          | ((sk_A) = (k1_xboole_0))
% 2.25/2.45          | (v2_funct_1 @ X0)
% 2.25/2.45          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B)))),
% 2.25/2.45      inference('demod', [status(thm)], ['14', '15', '16'])).
% 2.25/2.45  thf('18', plain,
% 2.25/2.45      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_B))
% 2.25/2.45        | (v2_funct_1 @ sk_C)
% 2.25/2.45        | ((sk_A) = (k1_xboole_0))
% 2.25/2.45        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.25/2.45        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 2.25/2.45        | ~ (v1_funct_1 @ sk_C))),
% 2.25/2.45      inference('sup-', [status(thm)], ['11', '17'])).
% 2.25/2.45  thf('19', plain,
% 2.25/2.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('20', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('22', plain,
% 2.25/2.45      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_B))
% 2.25/2.45        | (v2_funct_1 @ sk_C)
% 2.25/2.45        | ((sk_A) = (k1_xboole_0)))),
% 2.25/2.45      inference('demod', [status(thm)], ['18', '19', '20', '21'])).
% 2.25/2.45  thf('23', plain,
% 2.25/2.45      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.25/2.45        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ sk_B)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('24', plain,
% 2.25/2.45      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 2.25/2.45         = (k5_relat_1 @ sk_C @ sk_B))),
% 2.25/2.45      inference('demod', [status(thm)], ['9', '10'])).
% 2.25/2.45  thf('25', plain,
% 2.25/2.45      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_B) @ sk_B)),
% 2.25/2.45      inference('demod', [status(thm)], ['23', '24'])).
% 2.25/2.45  thf('26', plain,
% 2.25/2.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('27', plain,
% 2.25/2.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf(dt_k1_partfun1, axiom,
% 2.25/2.45    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.25/2.45     ( ( ( v1_funct_1 @ E ) & 
% 2.25/2.45         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.25/2.45         ( v1_funct_1 @ F ) & 
% 2.25/2.45         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.25/2.45       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.25/2.45         ( m1_subset_1 @
% 2.25/2.45           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.25/2.45           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.25/2.45  thf('28', plain,
% 2.25/2.45      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 2.25/2.45         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 2.25/2.45          | ~ (v1_funct_1 @ X45)
% 2.25/2.45          | ~ (v1_funct_1 @ X48)
% 2.25/2.45          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 2.25/2.45          | (m1_subset_1 @ (k1_partfun1 @ X46 @ X47 @ X49 @ X50 @ X45 @ X48) @ 
% 2.25/2.45             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X50))))),
% 2.25/2.45      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.25/2.45  thf('29', plain,
% 2.25/2.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.25/2.45         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1) @ 
% 2.25/2.45           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.25/2.45          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.25/2.45          | ~ (v1_funct_1 @ X1)
% 2.25/2.45          | ~ (v1_funct_1 @ sk_C))),
% 2.25/2.45      inference('sup-', [status(thm)], ['27', '28'])).
% 2.25/2.45  thf('30', plain, ((v1_funct_1 @ sk_C)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('31', plain,
% 2.25/2.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.25/2.45         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1) @ 
% 2.25/2.45           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.25/2.45          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.25/2.45          | ~ (v1_funct_1 @ X1))),
% 2.25/2.45      inference('demod', [status(thm)], ['29', '30'])).
% 2.25/2.45  thf('32', plain,
% 2.25/2.45      ((~ (v1_funct_1 @ sk_B)
% 2.25/2.45        | (m1_subset_1 @ 
% 2.25/2.45           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ 
% 2.25/2.45           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.25/2.45      inference('sup-', [status(thm)], ['26', '31'])).
% 2.25/2.45  thf('33', plain, ((v1_funct_1 @ sk_B)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('34', plain,
% 2.25/2.45      ((m1_subset_1 @ 
% 2.25/2.45        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ 
% 2.25/2.45        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.25/2.45      inference('demod', [status(thm)], ['32', '33'])).
% 2.25/2.45  thf('35', plain,
% 2.25/2.45      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 2.25/2.45         = (k5_relat_1 @ sk_C @ sk_B))),
% 2.25/2.45      inference('demod', [status(thm)], ['9', '10'])).
% 2.25/2.45  thf('36', plain,
% 2.25/2.45      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_B) @ 
% 2.25/2.45        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.25/2.45      inference('demod', [status(thm)], ['34', '35'])).
% 2.25/2.45  thf(redefinition_r2_relset_1, axiom,
% 2.25/2.45    (![A:$i,B:$i,C:$i,D:$i]:
% 2.25/2.45     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.25/2.45         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.25/2.45       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.25/2.45  thf('37', plain,
% 2.25/2.45      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 2.25/2.45         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 2.25/2.45          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 2.25/2.45          | ((X38) = (X41))
% 2.25/2.45          | ~ (r2_relset_1 @ X39 @ X40 @ X38 @ X41))),
% 2.25/2.45      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.25/2.45  thf('38', plain,
% 2.25/2.45      (![X0 : $i]:
% 2.25/2.45         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_B) @ X0)
% 2.25/2.45          | ((k5_relat_1 @ sk_C @ sk_B) = (X0))
% 2.25/2.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.25/2.45      inference('sup-', [status(thm)], ['36', '37'])).
% 2.25/2.45  thf('39', plain,
% 2.25/2.45      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.25/2.45        | ((k5_relat_1 @ sk_C @ sk_B) = (sk_B)))),
% 2.25/2.45      inference('sup-', [status(thm)], ['25', '38'])).
% 2.25/2.45  thf('40', plain,
% 2.25/2.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('41', plain, (((k5_relat_1 @ sk_C @ sk_B) = (sk_B))),
% 2.25/2.45      inference('demod', [status(thm)], ['39', '40'])).
% 2.25/2.45  thf('42', plain, ((v2_funct_1 @ sk_B)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('43', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 2.25/2.45      inference('demod', [status(thm)], ['22', '41', '42'])).
% 2.25/2.45  thf(fc6_funct_1, axiom,
% 2.25/2.45    (![A:$i]:
% 2.25/2.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 2.25/2.45       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 2.25/2.45         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 2.25/2.45         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 2.25/2.45  thf('44', plain,
% 2.25/2.45      (![X20 : $i]:
% 2.25/2.45         ((v1_relat_1 @ (k2_funct_1 @ X20))
% 2.25/2.45          | ~ (v2_funct_1 @ X20)
% 2.25/2.45          | ~ (v1_funct_1 @ X20)
% 2.25/2.45          | ~ (v1_relat_1 @ X20))),
% 2.25/2.45      inference('cnf', [status(esa)], [fc6_funct_1])).
% 2.25/2.45  thf('45', plain,
% 2.25/2.45      (![X20 : $i]:
% 2.25/2.45         ((v1_funct_1 @ (k2_funct_1 @ X20))
% 2.25/2.45          | ~ (v2_funct_1 @ X20)
% 2.25/2.45          | ~ (v1_funct_1 @ X20)
% 2.25/2.45          | ~ (v1_relat_1 @ X20))),
% 2.25/2.45      inference('cnf', [status(esa)], [fc6_funct_1])).
% 2.25/2.45  thf('46', plain, (((k5_relat_1 @ sk_C @ sk_B) = (sk_B))),
% 2.25/2.45      inference('demod', [status(thm)], ['39', '40'])).
% 2.25/2.45  thf(t66_funct_1, axiom,
% 2.25/2.45    (![A:$i]:
% 2.25/2.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.25/2.45       ( ![B:$i]:
% 2.25/2.45         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.25/2.45           ( ( ( v2_funct_1 @ A ) & ( v2_funct_1 @ B ) ) =>
% 2.25/2.45             ( ( k2_funct_1 @ ( k5_relat_1 @ A @ B ) ) =
% 2.25/2.45               ( k5_relat_1 @ ( k2_funct_1 @ B ) @ ( k2_funct_1 @ A ) ) ) ) ) ) ))).
% 2.25/2.45  thf('47', plain,
% 2.25/2.45      (![X26 : $i, X27 : $i]:
% 2.25/2.45         (~ (v1_relat_1 @ X26)
% 2.25/2.45          | ~ (v1_funct_1 @ X26)
% 2.25/2.45          | ((k2_funct_1 @ (k5_relat_1 @ X27 @ X26))
% 2.25/2.45              = (k5_relat_1 @ (k2_funct_1 @ X26) @ (k2_funct_1 @ X27)))
% 2.25/2.45          | ~ (v2_funct_1 @ X26)
% 2.25/2.45          | ~ (v2_funct_1 @ X27)
% 2.25/2.45          | ~ (v1_funct_1 @ X27)
% 2.25/2.45          | ~ (v1_relat_1 @ X27))),
% 2.25/2.45      inference('cnf', [status(esa)], [t66_funct_1])).
% 2.25/2.45  thf('48', plain,
% 2.25/2.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf(t67_funct_2, axiom,
% 2.25/2.45    (![A:$i,B:$i]:
% 2.25/2.45     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 2.25/2.45         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 2.25/2.45       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 2.25/2.45  thf('49', plain,
% 2.25/2.45      (![X66 : $i, X67 : $i]:
% 2.25/2.45         (((k1_relset_1 @ X66 @ X66 @ X67) = (X66))
% 2.25/2.45          | ~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X66 @ X66)))
% 2.25/2.45          | ~ (v1_funct_2 @ X67 @ X66 @ X66)
% 2.25/2.45          | ~ (v1_funct_1 @ X67))),
% 2.25/2.45      inference('cnf', [status(esa)], [t67_funct_2])).
% 2.25/2.45  thf('50', plain,
% 2.25/2.45      ((~ (v1_funct_1 @ sk_B)
% 2.25/2.45        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 2.25/2.45        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A)))),
% 2.25/2.45      inference('sup-', [status(thm)], ['48', '49'])).
% 2.25/2.45  thf('51', plain, ((v1_funct_1 @ sk_B)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('52', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('53', plain,
% 2.25/2.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf(redefinition_k1_relset_1, axiom,
% 2.25/2.45    (![A:$i,B:$i,C:$i]:
% 2.25/2.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.25/2.45       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.25/2.45  thf('54', plain,
% 2.25/2.45      (![X31 : $i, X32 : $i, X33 : $i]:
% 2.25/2.45         (((k1_relset_1 @ X32 @ X33 @ X31) = (k1_relat_1 @ X31))
% 2.25/2.45          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 2.25/2.45      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.25/2.45  thf('55', plain,
% 2.25/2.45      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 2.25/2.45      inference('sup-', [status(thm)], ['53', '54'])).
% 2.25/2.45  thf('56', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 2.25/2.45      inference('demod', [status(thm)], ['50', '51', '52', '55'])).
% 2.25/2.45  thf('57', plain,
% 2.25/2.45      (![X20 : $i]:
% 2.25/2.45         ((v1_funct_1 @ (k2_funct_1 @ X20))
% 2.25/2.45          | ~ (v2_funct_1 @ X20)
% 2.25/2.45          | ~ (v1_funct_1 @ X20)
% 2.25/2.45          | ~ (v1_relat_1 @ X20))),
% 2.25/2.45      inference('cnf', [status(esa)], [fc6_funct_1])).
% 2.25/2.45  thf('58', plain,
% 2.25/2.45      (![X20 : $i]:
% 2.25/2.45         ((v1_relat_1 @ (k2_funct_1 @ X20))
% 2.25/2.45          | ~ (v2_funct_1 @ X20)
% 2.25/2.45          | ~ (v1_funct_1 @ X20)
% 2.25/2.45          | ~ (v1_relat_1 @ X20))),
% 2.25/2.45      inference('cnf', [status(esa)], [fc6_funct_1])).
% 2.25/2.45  thf('59', plain,
% 2.25/2.45      (![X25 : $i]:
% 2.25/2.45         (~ (v2_funct_1 @ X25)
% 2.25/2.45          | ((k1_relat_1 @ X25) = (k2_relat_1 @ (k2_funct_1 @ X25)))
% 2.25/2.45          | ~ (v1_funct_1 @ X25)
% 2.25/2.45          | ~ (v1_relat_1 @ X25))),
% 2.25/2.45      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.25/2.45  thf(t44_funct_1, axiom,
% 2.25/2.45    (![A:$i]:
% 2.25/2.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.25/2.45       ( ![B:$i]:
% 2.25/2.45         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.25/2.45           ( ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 2.25/2.45               ( ( k5_relat_1 @ A @ B ) = ( A ) ) ) =>
% 2.25/2.45             ( ( B ) = ( k6_relat_1 @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 2.25/2.45  thf('60', plain,
% 2.25/2.45      (![X23 : $i, X24 : $i]:
% 2.25/2.45         (~ (v1_relat_1 @ X23)
% 2.25/2.45          | ~ (v1_funct_1 @ X23)
% 2.25/2.45          | ((X23) = (k6_relat_1 @ (k1_relat_1 @ X23)))
% 2.25/2.45          | ((k5_relat_1 @ X24 @ X23) != (X24))
% 2.25/2.45          | ((k2_relat_1 @ X24) != (k1_relat_1 @ X23))
% 2.25/2.45          | ~ (v1_funct_1 @ X24)
% 2.25/2.45          | ~ (v1_relat_1 @ X24))),
% 2.25/2.45      inference('cnf', [status(esa)], [t44_funct_1])).
% 2.25/2.45  thf(redefinition_k6_partfun1, axiom,
% 2.25/2.45    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.25/2.45  thf('61', plain, (![X57 : $i]: ((k6_partfun1 @ X57) = (k6_relat_1 @ X57))),
% 2.25/2.45      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.25/2.45  thf('62', plain,
% 2.25/2.45      (![X23 : $i, X24 : $i]:
% 2.25/2.45         (~ (v1_relat_1 @ X23)
% 2.25/2.45          | ~ (v1_funct_1 @ X23)
% 2.25/2.45          | ((X23) = (k6_partfun1 @ (k1_relat_1 @ X23)))
% 2.25/2.45          | ((k5_relat_1 @ X24 @ X23) != (X24))
% 2.25/2.45          | ((k2_relat_1 @ X24) != (k1_relat_1 @ X23))
% 2.25/2.45          | ~ (v1_funct_1 @ X24)
% 2.25/2.45          | ~ (v1_relat_1 @ X24))),
% 2.25/2.45      inference('demod', [status(thm)], ['60', '61'])).
% 2.25/2.45  thf('63', plain,
% 2.25/2.45      (![X0 : $i, X1 : $i]:
% 2.25/2.45         (((k1_relat_1 @ X0) != (k1_relat_1 @ X1))
% 2.25/2.45          | ~ (v1_relat_1 @ X0)
% 2.25/2.45          | ~ (v1_funct_1 @ X0)
% 2.25/2.45          | ~ (v2_funct_1 @ X0)
% 2.25/2.45          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.25/2.45          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.25/2.45          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X1) != (k2_funct_1 @ X0))
% 2.25/2.45          | ((X1) = (k6_partfun1 @ (k1_relat_1 @ X1)))
% 2.25/2.45          | ~ (v1_funct_1 @ X1)
% 2.25/2.45          | ~ (v1_relat_1 @ X1))),
% 2.25/2.45      inference('sup-', [status(thm)], ['59', '62'])).
% 2.25/2.45  thf('64', plain,
% 2.25/2.45      (![X0 : $i, X1 : $i]:
% 2.25/2.45         (~ (v1_relat_1 @ X0)
% 2.25/2.45          | ~ (v1_funct_1 @ X0)
% 2.25/2.45          | ~ (v2_funct_1 @ X0)
% 2.25/2.45          | ~ (v1_relat_1 @ X1)
% 2.25/2.45          | ~ (v1_funct_1 @ X1)
% 2.25/2.45          | ((X1) = (k6_partfun1 @ (k1_relat_1 @ X1)))
% 2.25/2.45          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X1) != (k2_funct_1 @ X0))
% 2.25/2.45          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.25/2.45          | ~ (v2_funct_1 @ X0)
% 2.25/2.45          | ~ (v1_funct_1 @ X0)
% 2.25/2.45          | ~ (v1_relat_1 @ X0)
% 2.25/2.45          | ((k1_relat_1 @ X0) != (k1_relat_1 @ X1)))),
% 2.25/2.45      inference('sup-', [status(thm)], ['58', '63'])).
% 2.25/2.45  thf('65', plain,
% 2.25/2.45      (![X0 : $i, X1 : $i]:
% 2.25/2.45         (((k1_relat_1 @ X0) != (k1_relat_1 @ X1))
% 2.25/2.45          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.25/2.45          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X1) != (k2_funct_1 @ X0))
% 2.25/2.45          | ((X1) = (k6_partfun1 @ (k1_relat_1 @ X1)))
% 2.25/2.45          | ~ (v1_funct_1 @ X1)
% 2.25/2.45          | ~ (v1_relat_1 @ X1)
% 2.25/2.45          | ~ (v2_funct_1 @ X0)
% 2.25/2.45          | ~ (v1_funct_1 @ X0)
% 2.25/2.45          | ~ (v1_relat_1 @ X0))),
% 2.25/2.45      inference('simplify', [status(thm)], ['64'])).
% 2.25/2.45  thf('66', plain,
% 2.25/2.45      (![X0 : $i, X1 : $i]:
% 2.25/2.45         (~ (v1_relat_1 @ X0)
% 2.25/2.45          | ~ (v1_funct_1 @ X0)
% 2.25/2.45          | ~ (v2_funct_1 @ X0)
% 2.25/2.45          | ~ (v1_relat_1 @ X0)
% 2.25/2.45          | ~ (v1_funct_1 @ X0)
% 2.25/2.45          | ~ (v2_funct_1 @ X0)
% 2.25/2.45          | ~ (v1_relat_1 @ X1)
% 2.25/2.45          | ~ (v1_funct_1 @ X1)
% 2.25/2.45          | ((X1) = (k6_partfun1 @ (k1_relat_1 @ X1)))
% 2.25/2.45          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X1) != (k2_funct_1 @ X0))
% 2.25/2.45          | ((k1_relat_1 @ X0) != (k1_relat_1 @ X1)))),
% 2.25/2.45      inference('sup-', [status(thm)], ['57', '65'])).
% 2.25/2.45  thf('67', plain,
% 2.25/2.45      (![X0 : $i, X1 : $i]:
% 2.25/2.45         (((k1_relat_1 @ X0) != (k1_relat_1 @ X1))
% 2.25/2.45          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X1) != (k2_funct_1 @ X0))
% 2.25/2.45          | ((X1) = (k6_partfun1 @ (k1_relat_1 @ X1)))
% 2.25/2.45          | ~ (v1_funct_1 @ X1)
% 2.25/2.45          | ~ (v1_relat_1 @ X1)
% 2.25/2.45          | ~ (v2_funct_1 @ X0)
% 2.25/2.45          | ~ (v1_funct_1 @ X0)
% 2.25/2.45          | ~ (v1_relat_1 @ X0))),
% 2.25/2.45      inference('simplify', [status(thm)], ['66'])).
% 2.25/2.45  thf('68', plain,
% 2.25/2.45      (![X0 : $i]:
% 2.25/2.45         (((sk_A) != (k1_relat_1 @ X0))
% 2.25/2.45          | ~ (v1_relat_1 @ sk_B)
% 2.25/2.45          | ~ (v1_funct_1 @ sk_B)
% 2.25/2.45          | ~ (v2_funct_1 @ sk_B)
% 2.25/2.45          | ~ (v1_relat_1 @ X0)
% 2.25/2.45          | ~ (v1_funct_1 @ X0)
% 2.25/2.45          | ((X0) = (k6_partfun1 @ (k1_relat_1 @ X0)))
% 2.25/2.45          | ((k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0) != (k2_funct_1 @ sk_B)))),
% 2.25/2.45      inference('sup-', [status(thm)], ['56', '67'])).
% 2.25/2.45  thf('69', plain,
% 2.25/2.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf(cc2_relat_1, axiom,
% 2.25/2.45    (![A:$i]:
% 2.25/2.45     ( ( v1_relat_1 @ A ) =>
% 2.25/2.45       ( ![B:$i]:
% 2.25/2.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.25/2.45  thf('70', plain,
% 2.25/2.45      (![X0 : $i, X1 : $i]:
% 2.25/2.45         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 2.25/2.45          | (v1_relat_1 @ X0)
% 2.25/2.45          | ~ (v1_relat_1 @ X1))),
% 2.25/2.45      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.25/2.45  thf('71', plain,
% 2.25/2.45      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 2.25/2.45      inference('sup-', [status(thm)], ['69', '70'])).
% 2.25/2.45  thf(fc6_relat_1, axiom,
% 2.25/2.45    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.25/2.45  thf('72', plain,
% 2.25/2.45      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 2.25/2.45      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.25/2.45  thf('73', plain, ((v1_relat_1 @ sk_B)),
% 2.25/2.45      inference('demod', [status(thm)], ['71', '72'])).
% 2.25/2.45  thf('74', plain, ((v1_funct_1 @ sk_B)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('75', plain, ((v2_funct_1 @ sk_B)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('76', plain,
% 2.25/2.45      (![X0 : $i]:
% 2.25/2.45         (((sk_A) != (k1_relat_1 @ X0))
% 2.25/2.45          | ~ (v1_relat_1 @ X0)
% 2.25/2.45          | ~ (v1_funct_1 @ X0)
% 2.25/2.45          | ((X0) = (k6_partfun1 @ (k1_relat_1 @ X0)))
% 2.25/2.45          | ((k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0) != (k2_funct_1 @ sk_B)))),
% 2.25/2.45      inference('demod', [status(thm)], ['68', '73', '74', '75'])).
% 2.25/2.45  thf('77', plain,
% 2.25/2.45      (![X0 : $i]:
% 2.25/2.45         (((k2_funct_1 @ (k5_relat_1 @ X0 @ sk_B)) != (k2_funct_1 @ sk_B))
% 2.25/2.45          | ~ (v1_relat_1 @ X0)
% 2.25/2.45          | ~ (v1_funct_1 @ X0)
% 2.25/2.45          | ~ (v2_funct_1 @ X0)
% 2.25/2.45          | ~ (v2_funct_1 @ sk_B)
% 2.25/2.45          | ~ (v1_funct_1 @ sk_B)
% 2.25/2.45          | ~ (v1_relat_1 @ sk_B)
% 2.25/2.45          | ((k2_funct_1 @ X0)
% 2.25/2.45              = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 2.25/2.45          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.25/2.45          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.25/2.45          | ((sk_A) != (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 2.25/2.45      inference('sup-', [status(thm)], ['47', '76'])).
% 2.25/2.45  thf('78', plain, ((v2_funct_1 @ sk_B)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('79', plain, ((v1_funct_1 @ sk_B)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('80', plain, ((v1_relat_1 @ sk_B)),
% 2.25/2.45      inference('demod', [status(thm)], ['71', '72'])).
% 2.25/2.45  thf('81', plain,
% 2.25/2.45      (![X0 : $i]:
% 2.25/2.45         (((k2_funct_1 @ (k5_relat_1 @ X0 @ sk_B)) != (k2_funct_1 @ sk_B))
% 2.25/2.45          | ~ (v1_relat_1 @ X0)
% 2.25/2.45          | ~ (v1_funct_1 @ X0)
% 2.25/2.45          | ~ (v2_funct_1 @ X0)
% 2.25/2.45          | ((k2_funct_1 @ X0)
% 2.25/2.45              = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 2.25/2.45          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.25/2.45          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.25/2.45          | ((sk_A) != (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 2.25/2.45      inference('demod', [status(thm)], ['77', '78', '79', '80'])).
% 2.25/2.45  thf('82', plain,
% 2.25/2.45      ((((k2_funct_1 @ sk_B) != (k2_funct_1 @ sk_B))
% 2.25/2.45        | ((sk_A) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 2.25/2.45        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.25/2.45        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 2.25/2.45        | ((k2_funct_1 @ sk_C)
% 2.25/2.45            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 2.25/2.45        | ~ (v2_funct_1 @ sk_C)
% 2.25/2.45        | ~ (v1_funct_1 @ sk_C)
% 2.25/2.45        | ~ (v1_relat_1 @ sk_C))),
% 2.25/2.45      inference('sup-', [status(thm)], ['46', '81'])).
% 2.25/2.45  thf('83', plain, ((v1_funct_1 @ sk_C)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('84', plain,
% 2.25/2.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('85', plain,
% 2.25/2.45      (![X0 : $i, X1 : $i]:
% 2.25/2.45         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 2.25/2.45          | (v1_relat_1 @ X0)
% 2.25/2.45          | ~ (v1_relat_1 @ X1))),
% 2.25/2.45      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.25/2.45  thf('86', plain,
% 2.25/2.45      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_C))),
% 2.25/2.45      inference('sup-', [status(thm)], ['84', '85'])).
% 2.25/2.45  thf('87', plain,
% 2.25/2.45      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 2.25/2.45      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.25/2.45  thf('88', plain, ((v1_relat_1 @ sk_C)),
% 2.25/2.45      inference('demod', [status(thm)], ['86', '87'])).
% 2.25/2.45  thf('89', plain,
% 2.25/2.45      ((((k2_funct_1 @ sk_B) != (k2_funct_1 @ sk_B))
% 2.25/2.45        | ((sk_A) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 2.25/2.45        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.25/2.45        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 2.25/2.45        | ((k2_funct_1 @ sk_C)
% 2.25/2.45            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 2.25/2.45        | ~ (v2_funct_1 @ sk_C))),
% 2.25/2.45      inference('demod', [status(thm)], ['82', '83', '88'])).
% 2.25/2.45  thf('90', plain,
% 2.25/2.45      ((~ (v2_funct_1 @ sk_C)
% 2.25/2.45        | ((k2_funct_1 @ sk_C)
% 2.25/2.45            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 2.25/2.45        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 2.25/2.45        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.25/2.45        | ((sk_A) != (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 2.25/2.45      inference('simplify', [status(thm)], ['89'])).
% 2.25/2.45  thf('91', plain,
% 2.25/2.45      ((~ (v1_relat_1 @ sk_C)
% 2.25/2.45        | ~ (v1_funct_1 @ sk_C)
% 2.25/2.45        | ~ (v2_funct_1 @ sk_C)
% 2.25/2.45        | ((sk_A) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 2.25/2.45        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.25/2.45        | ((k2_funct_1 @ sk_C)
% 2.25/2.45            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 2.25/2.45        | ~ (v2_funct_1 @ sk_C))),
% 2.25/2.45      inference('sup-', [status(thm)], ['45', '90'])).
% 2.25/2.45  thf('92', plain, ((v1_relat_1 @ sk_C)),
% 2.25/2.45      inference('demod', [status(thm)], ['86', '87'])).
% 2.25/2.45  thf('93', plain, ((v1_funct_1 @ sk_C)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('94', plain,
% 2.25/2.45      ((~ (v2_funct_1 @ sk_C)
% 2.25/2.45        | ((sk_A) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 2.25/2.45        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.25/2.45        | ((k2_funct_1 @ sk_C)
% 2.25/2.45            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 2.25/2.45        | ~ (v2_funct_1 @ sk_C))),
% 2.25/2.45      inference('demod', [status(thm)], ['91', '92', '93'])).
% 2.25/2.45  thf('95', plain,
% 2.25/2.45      ((((k2_funct_1 @ sk_C)
% 2.25/2.45          = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 2.25/2.45        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.25/2.45        | ((sk_A) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 2.25/2.45        | ~ (v2_funct_1 @ sk_C))),
% 2.25/2.45      inference('simplify', [status(thm)], ['94'])).
% 2.25/2.45  thf('96', plain,
% 2.25/2.45      ((~ (v1_relat_1 @ sk_C)
% 2.25/2.45        | ~ (v1_funct_1 @ sk_C)
% 2.25/2.45        | ~ (v2_funct_1 @ sk_C)
% 2.25/2.45        | ~ (v2_funct_1 @ sk_C)
% 2.25/2.45        | ((sk_A) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 2.25/2.45        | ((k2_funct_1 @ sk_C)
% 2.25/2.45            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 2.25/2.45      inference('sup-', [status(thm)], ['44', '95'])).
% 2.25/2.45  thf('97', plain, ((v1_relat_1 @ sk_C)),
% 2.25/2.45      inference('demod', [status(thm)], ['86', '87'])).
% 2.25/2.45  thf('98', plain, ((v1_funct_1 @ sk_C)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('99', plain,
% 2.25/2.45      ((~ (v2_funct_1 @ sk_C)
% 2.25/2.45        | ~ (v2_funct_1 @ sk_C)
% 2.25/2.45        | ((sk_A) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 2.25/2.45        | ((k2_funct_1 @ sk_C)
% 2.25/2.45            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 2.25/2.45      inference('demod', [status(thm)], ['96', '97', '98'])).
% 2.25/2.45  thf('100', plain,
% 2.25/2.45      ((((k2_funct_1 @ sk_C)
% 2.25/2.45          = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 2.25/2.45        | ((sk_A) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 2.25/2.45        | ~ (v2_funct_1 @ sk_C))),
% 2.25/2.45      inference('simplify', [status(thm)], ['99'])).
% 2.25/2.45  thf('101', plain,
% 2.25/2.45      ((((sk_A) = (k1_xboole_0))
% 2.25/2.45        | ((sk_A) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 2.25/2.45        | ((k2_funct_1 @ sk_C)
% 2.25/2.45            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 2.25/2.45      inference('sup-', [status(thm)], ['43', '100'])).
% 2.25/2.45  thf('102', plain,
% 2.25/2.45      ((((sk_A) != (k2_relat_1 @ sk_C))
% 2.25/2.45        | ~ (v1_relat_1 @ sk_C)
% 2.25/2.45        | ~ (v1_funct_1 @ sk_C)
% 2.25/2.45        | ~ (v2_funct_1 @ sk_C)
% 2.25/2.45        | ((k2_funct_1 @ sk_C)
% 2.25/2.45            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 2.25/2.45        | ((sk_A) = (k1_xboole_0)))),
% 2.25/2.45      inference('sup-', [status(thm)], ['2', '101'])).
% 2.25/2.45  thf('103', plain, (((k5_relat_1 @ sk_C @ sk_B) = (sk_B))),
% 2.25/2.45      inference('demod', [status(thm)], ['39', '40'])).
% 2.25/2.45  thf(t160_relat_1, axiom,
% 2.25/2.45    (![A:$i]:
% 2.25/2.45     ( ( v1_relat_1 @ A ) =>
% 2.25/2.45       ( ![B:$i]:
% 2.25/2.45         ( ( v1_relat_1 @ B ) =>
% 2.25/2.45           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 2.25/2.45             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 2.25/2.45  thf('104', plain,
% 2.25/2.45      (![X8 : $i, X9 : $i]:
% 2.25/2.45         (~ (v1_relat_1 @ X8)
% 2.25/2.45          | ((k2_relat_1 @ (k5_relat_1 @ X9 @ X8))
% 2.25/2.45              = (k9_relat_1 @ X8 @ (k2_relat_1 @ X9)))
% 2.25/2.45          | ~ (v1_relat_1 @ X9))),
% 2.25/2.45      inference('cnf', [status(esa)], [t160_relat_1])).
% 2.25/2.45  thf(t169_relat_1, axiom,
% 2.25/2.45    (![A:$i]:
% 2.25/2.45     ( ( v1_relat_1 @ A ) =>
% 2.25/2.45       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 2.25/2.45  thf('105', plain,
% 2.25/2.45      (![X10 : $i]:
% 2.25/2.45         (((k10_relat_1 @ X10 @ (k2_relat_1 @ X10)) = (k1_relat_1 @ X10))
% 2.25/2.45          | ~ (v1_relat_1 @ X10))),
% 2.25/2.45      inference('cnf', [status(esa)], [t169_relat_1])).
% 2.25/2.45  thf('106', plain,
% 2.25/2.45      (![X0 : $i, X1 : $i]:
% 2.25/2.45         (((k10_relat_1 @ (k5_relat_1 @ X0 @ X1) @ 
% 2.25/2.45            (k9_relat_1 @ X1 @ (k2_relat_1 @ X0)))
% 2.25/2.45            = (k1_relat_1 @ (k5_relat_1 @ X0 @ X1)))
% 2.25/2.45          | ~ (v1_relat_1 @ X0)
% 2.25/2.45          | ~ (v1_relat_1 @ X1)
% 2.25/2.45          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 2.25/2.45      inference('sup+', [status(thm)], ['104', '105'])).
% 2.25/2.45  thf('107', plain,
% 2.25/2.45      ((~ (v1_relat_1 @ sk_B)
% 2.25/2.45        | ~ (v1_relat_1 @ sk_B)
% 2.25/2.45        | ~ (v1_relat_1 @ sk_C)
% 2.25/2.45        | ((k10_relat_1 @ (k5_relat_1 @ sk_C @ sk_B) @ 
% 2.25/2.45            (k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_C)))
% 2.25/2.45            = (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B))))),
% 2.25/2.45      inference('sup-', [status(thm)], ['103', '106'])).
% 2.25/2.45  thf('108', plain, ((v1_relat_1 @ sk_B)),
% 2.25/2.45      inference('demod', [status(thm)], ['71', '72'])).
% 2.25/2.45  thf('109', plain, ((v1_relat_1 @ sk_B)),
% 2.25/2.45      inference('demod', [status(thm)], ['71', '72'])).
% 2.25/2.45  thf('110', plain, ((v1_relat_1 @ sk_C)),
% 2.25/2.45      inference('demod', [status(thm)], ['86', '87'])).
% 2.25/2.45  thf('111', plain, (((k5_relat_1 @ sk_C @ sk_B) = (sk_B))),
% 2.25/2.45      inference('demod', [status(thm)], ['39', '40'])).
% 2.25/2.45  thf('112', plain,
% 2.25/2.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf(cc2_relset_1, axiom,
% 2.25/2.45    (![A:$i,B:$i,C:$i]:
% 2.25/2.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.25/2.45       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.25/2.45  thf('113', plain,
% 2.25/2.45      (![X28 : $i, X29 : $i, X30 : $i]:
% 2.25/2.45         ((v5_relat_1 @ X28 @ X30)
% 2.25/2.45          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 2.25/2.45      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.25/2.45  thf('114', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 2.25/2.45      inference('sup-', [status(thm)], ['112', '113'])).
% 2.25/2.45  thf(d19_relat_1, axiom,
% 2.25/2.45    (![A:$i,B:$i]:
% 2.25/2.45     ( ( v1_relat_1 @ B ) =>
% 2.25/2.45       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 2.25/2.45  thf('115', plain,
% 2.25/2.45      (![X2 : $i, X3 : $i]:
% 2.25/2.45         (~ (v5_relat_1 @ X2 @ X3)
% 2.25/2.45          | (r1_tarski @ (k2_relat_1 @ X2) @ X3)
% 2.25/2.45          | ~ (v1_relat_1 @ X2))),
% 2.25/2.45      inference('cnf', [status(esa)], [d19_relat_1])).
% 2.25/2.45  thf('116', plain,
% 2.25/2.45      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A))),
% 2.25/2.45      inference('sup-', [status(thm)], ['114', '115'])).
% 2.25/2.45  thf('117', plain, ((v1_relat_1 @ sk_C)),
% 2.25/2.45      inference('demod', [status(thm)], ['86', '87'])).
% 2.25/2.45  thf('118', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A)),
% 2.25/2.45      inference('demod', [status(thm)], ['116', '117'])).
% 2.25/2.45  thf('119', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 2.25/2.45      inference('demod', [status(thm)], ['50', '51', '52', '55'])).
% 2.25/2.45  thf(t164_funct_1, axiom,
% 2.25/2.45    (![A:$i,B:$i]:
% 2.25/2.45     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.25/2.45       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 2.25/2.45         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 2.25/2.45  thf('120', plain,
% 2.25/2.45      (![X21 : $i, X22 : $i]:
% 2.25/2.45         (~ (r1_tarski @ X21 @ (k1_relat_1 @ X22))
% 2.25/2.45          | ~ (v2_funct_1 @ X22)
% 2.25/2.45          | ((k10_relat_1 @ X22 @ (k9_relat_1 @ X22 @ X21)) = (X21))
% 2.25/2.45          | ~ (v1_funct_1 @ X22)
% 2.25/2.45          | ~ (v1_relat_1 @ X22))),
% 2.25/2.45      inference('cnf', [status(esa)], [t164_funct_1])).
% 2.25/2.45  thf('121', plain,
% 2.25/2.45      (![X0 : $i]:
% 2.25/2.45         (~ (r1_tarski @ X0 @ sk_A)
% 2.25/2.45          | ~ (v1_relat_1 @ sk_B)
% 2.25/2.45          | ~ (v1_funct_1 @ sk_B)
% 2.25/2.45          | ((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ X0)) = (X0))
% 2.25/2.45          | ~ (v2_funct_1 @ sk_B))),
% 2.25/2.45      inference('sup-', [status(thm)], ['119', '120'])).
% 2.25/2.45  thf('122', plain, ((v1_relat_1 @ sk_B)),
% 2.25/2.45      inference('demod', [status(thm)], ['71', '72'])).
% 2.25/2.45  thf('123', plain, ((v1_funct_1 @ sk_B)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('124', plain, ((v2_funct_1 @ sk_B)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('125', plain,
% 2.25/2.45      (![X0 : $i]:
% 2.25/2.45         (~ (r1_tarski @ X0 @ sk_A)
% 2.25/2.45          | ((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ X0)) = (X0)))),
% 2.25/2.45      inference('demod', [status(thm)], ['121', '122', '123', '124'])).
% 2.25/2.45  thf('126', plain,
% 2.25/2.45      (((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_C)))
% 2.25/2.45         = (k2_relat_1 @ sk_C))),
% 2.25/2.45      inference('sup-', [status(thm)], ['118', '125'])).
% 2.25/2.45  thf('127', plain, (((k5_relat_1 @ sk_C @ sk_B) = (sk_B))),
% 2.25/2.45      inference('demod', [status(thm)], ['39', '40'])).
% 2.25/2.45  thf('128', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 2.25/2.45      inference('demod', [status(thm)], ['50', '51', '52', '55'])).
% 2.25/2.45  thf('129', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 2.25/2.45      inference('demod', [status(thm)],
% 2.25/2.45                ['107', '108', '109', '110', '111', '126', '127', '128'])).
% 2.25/2.45  thf('130', plain, ((v1_relat_1 @ sk_C)),
% 2.25/2.45      inference('demod', [status(thm)], ['86', '87'])).
% 2.25/2.45  thf('131', plain, ((v1_funct_1 @ sk_C)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('132', plain,
% 2.25/2.45      ((((sk_A) != (sk_A))
% 2.25/2.45        | ~ (v2_funct_1 @ sk_C)
% 2.25/2.45        | ((k2_funct_1 @ sk_C)
% 2.25/2.45            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 2.25/2.45        | ((sk_A) = (k1_xboole_0)))),
% 2.25/2.45      inference('demod', [status(thm)], ['102', '129', '130', '131'])).
% 2.25/2.45  thf('133', plain,
% 2.25/2.45      ((((sk_A) = (k1_xboole_0))
% 2.25/2.45        | ((k2_funct_1 @ sk_C)
% 2.25/2.45            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 2.25/2.45        | ~ (v2_funct_1 @ sk_C))),
% 2.25/2.45      inference('simplify', [status(thm)], ['132'])).
% 2.25/2.45  thf('134', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 2.25/2.45      inference('demod', [status(thm)], ['22', '41', '42'])).
% 2.25/2.45  thf('135', plain,
% 2.25/2.45      ((((k2_funct_1 @ sk_C)
% 2.25/2.45          = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 2.25/2.45        | ((sk_A) = (k1_xboole_0)))),
% 2.25/2.45      inference('clc', [status(thm)], ['133', '134'])).
% 2.25/2.45  thf('136', plain,
% 2.25/2.45      ((((k2_funct_1 @ sk_C) = (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 2.25/2.45        | ~ (v1_relat_1 @ sk_C)
% 2.25/2.45        | ~ (v1_funct_1 @ sk_C)
% 2.25/2.45        | ~ (v2_funct_1 @ sk_C)
% 2.25/2.45        | ((sk_A) = (k1_xboole_0)))),
% 2.25/2.45      inference('sup+', [status(thm)], ['1', '135'])).
% 2.25/2.45  thf('137', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 2.25/2.45      inference('demod', [status(thm)],
% 2.25/2.45                ['107', '108', '109', '110', '111', '126', '127', '128'])).
% 2.25/2.45  thf('138', plain, ((v1_relat_1 @ sk_C)),
% 2.25/2.45      inference('demod', [status(thm)], ['86', '87'])).
% 2.25/2.45  thf('139', plain, ((v1_funct_1 @ sk_C)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('140', plain,
% 2.25/2.45      ((((k2_funct_1 @ sk_C) = (k6_partfun1 @ sk_A))
% 2.25/2.45        | ~ (v2_funct_1 @ sk_C)
% 2.25/2.45        | ((sk_A) = (k1_xboole_0)))),
% 2.25/2.45      inference('demod', [status(thm)], ['136', '137', '138', '139'])).
% 2.25/2.45  thf('141', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 2.25/2.45      inference('demod', [status(thm)], ['22', '41', '42'])).
% 2.25/2.45  thf('142', plain,
% 2.25/2.45      ((((sk_A) = (k1_xboole_0)) | ((k2_funct_1 @ sk_C) = (k6_partfun1 @ sk_A)))),
% 2.25/2.45      inference('clc', [status(thm)], ['140', '141'])).
% 2.25/2.45  thf('143', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 2.25/2.45      inference('demod', [status(thm)], ['22', '41', '42'])).
% 2.25/2.45  thf('144', plain,
% 2.25/2.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf(t35_funct_2, axiom,
% 2.25/2.45    (![A:$i,B:$i,C:$i]:
% 2.25/2.45     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.25/2.45         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.25/2.45       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 2.25/2.45         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.25/2.45           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 2.25/2.45             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 2.25/2.45  thf('145', plain,
% 2.25/2.45      (![X63 : $i, X64 : $i, X65 : $i]:
% 2.25/2.45         (((X63) = (k1_xboole_0))
% 2.25/2.45          | ~ (v1_funct_1 @ X64)
% 2.25/2.45          | ~ (v1_funct_2 @ X64 @ X65 @ X63)
% 2.25/2.45          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X65 @ X63)))
% 2.25/2.45          | ((k5_relat_1 @ (k2_funct_1 @ X64) @ X64) = (k6_partfun1 @ X63))
% 2.25/2.45          | ~ (v2_funct_1 @ X64)
% 2.25/2.45          | ((k2_relset_1 @ X65 @ X63 @ X64) != (X63)))),
% 2.25/2.45      inference('cnf', [status(esa)], [t35_funct_2])).
% 2.25/2.45  thf('146', plain,
% 2.25/2.45      ((((k2_relset_1 @ sk_A @ sk_A @ sk_C) != (sk_A))
% 2.25/2.45        | ~ (v2_funct_1 @ sk_C)
% 2.25/2.45        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_A))
% 2.25/2.45        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 2.25/2.45        | ~ (v1_funct_1 @ sk_C)
% 2.25/2.45        | ((sk_A) = (k1_xboole_0)))),
% 2.25/2.45      inference('sup-', [status(thm)], ['144', '145'])).
% 2.25/2.45  thf('147', plain,
% 2.25/2.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf(t38_relset_1, axiom,
% 2.25/2.45    (![A:$i,B:$i,C:$i]:
% 2.25/2.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.25/2.45       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 2.25/2.45         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.25/2.45  thf('148', plain,
% 2.25/2.45      (![X42 : $i, X43 : $i, X44 : $i]:
% 2.25/2.45         (((k7_relset_1 @ X42 @ X43 @ X44 @ X42)
% 2.25/2.45            = (k2_relset_1 @ X42 @ X43 @ X44))
% 2.25/2.45          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43))))),
% 2.25/2.45      inference('cnf', [status(esa)], [t38_relset_1])).
% 2.25/2.45  thf('149', plain,
% 2.25/2.45      (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_A)
% 2.25/2.45         = (k2_relset_1 @ sk_A @ sk_A @ sk_C))),
% 2.25/2.45      inference('sup-', [status(thm)], ['147', '148'])).
% 2.25/2.45  thf('150', plain,
% 2.25/2.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf(redefinition_k7_relset_1, axiom,
% 2.25/2.45    (![A:$i,B:$i,C:$i,D:$i]:
% 2.25/2.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.25/2.45       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 2.25/2.45  thf('151', plain,
% 2.25/2.45      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 2.25/2.45         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 2.25/2.45          | ((k7_relset_1 @ X35 @ X36 @ X34 @ X37) = (k9_relat_1 @ X34 @ X37)))),
% 2.25/2.45      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 2.25/2.45  thf('152', plain,
% 2.25/2.45      (![X0 : $i]:
% 2.25/2.45         ((k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 2.25/2.45      inference('sup-', [status(thm)], ['150', '151'])).
% 2.25/2.45  thf('153', plain,
% 2.25/2.45      (((k9_relat_1 @ sk_C @ sk_A) = (k2_relset_1 @ sk_A @ sk_A @ sk_C))),
% 2.25/2.45      inference('demod', [status(thm)], ['149', '152'])).
% 2.25/2.45  thf('154', plain,
% 2.25/2.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('155', plain,
% 2.25/2.45      (![X28 : $i, X29 : $i, X30 : $i]:
% 2.25/2.45         ((v4_relat_1 @ X28 @ X29)
% 2.25/2.45          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 2.25/2.45      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.25/2.45  thf('156', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 2.25/2.45      inference('sup-', [status(thm)], ['154', '155'])).
% 2.25/2.45  thf(t209_relat_1, axiom,
% 2.25/2.45    (![A:$i,B:$i]:
% 2.25/2.45     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 2.25/2.45       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 2.25/2.45  thf('157', plain,
% 2.25/2.45      (![X11 : $i, X12 : $i]:
% 2.25/2.45         (((X11) = (k7_relat_1 @ X11 @ X12))
% 2.25/2.45          | ~ (v4_relat_1 @ X11 @ X12)
% 2.25/2.45          | ~ (v1_relat_1 @ X11))),
% 2.25/2.45      inference('cnf', [status(esa)], [t209_relat_1])).
% 2.25/2.45  thf('158', plain,
% 2.25/2.45      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 2.25/2.45      inference('sup-', [status(thm)], ['156', '157'])).
% 2.25/2.45  thf('159', plain, ((v1_relat_1 @ sk_C)),
% 2.25/2.45      inference('demod', [status(thm)], ['86', '87'])).
% 2.25/2.45  thf('160', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 2.25/2.45      inference('demod', [status(thm)], ['158', '159'])).
% 2.25/2.45  thf(t148_relat_1, axiom,
% 2.25/2.45    (![A:$i,B:$i]:
% 2.25/2.45     ( ( v1_relat_1 @ B ) =>
% 2.25/2.45       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 2.25/2.45  thf('161', plain,
% 2.25/2.45      (![X6 : $i, X7 : $i]:
% 2.25/2.45         (((k2_relat_1 @ (k7_relat_1 @ X6 @ X7)) = (k9_relat_1 @ X6 @ X7))
% 2.25/2.45          | ~ (v1_relat_1 @ X6))),
% 2.25/2.45      inference('cnf', [status(esa)], [t148_relat_1])).
% 2.25/2.45  thf('162', plain,
% 2.25/2.45      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))
% 2.25/2.45        | ~ (v1_relat_1 @ sk_C))),
% 2.25/2.45      inference('sup+', [status(thm)], ['160', '161'])).
% 2.25/2.45  thf('163', plain, ((v1_relat_1 @ sk_C)),
% 2.25/2.45      inference('demod', [status(thm)], ['86', '87'])).
% 2.25/2.45  thf('164', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 2.25/2.45      inference('demod', [status(thm)], ['162', '163'])).
% 2.25/2.45  thf('165', plain,
% 2.25/2.45      (((k2_relat_1 @ sk_C) = (k2_relset_1 @ sk_A @ sk_A @ sk_C))),
% 2.25/2.45      inference('demod', [status(thm)], ['153', '164'])).
% 2.25/2.45  thf('166', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('167', plain, ((v1_funct_1 @ sk_C)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('168', plain,
% 2.25/2.45      ((((k2_relat_1 @ sk_C) != (sk_A))
% 2.25/2.45        | ~ (v2_funct_1 @ sk_C)
% 2.25/2.45        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_A))
% 2.25/2.45        | ((sk_A) = (k1_xboole_0)))),
% 2.25/2.45      inference('demod', [status(thm)], ['146', '165', '166', '167'])).
% 2.25/2.45  thf('169', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 2.25/2.45      inference('demod', [status(thm)],
% 2.25/2.45                ['107', '108', '109', '110', '111', '126', '127', '128'])).
% 2.25/2.45  thf('170', plain,
% 2.25/2.45      ((((sk_A) != (sk_A))
% 2.25/2.45        | ~ (v2_funct_1 @ sk_C)
% 2.25/2.45        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_A))
% 2.25/2.45        | ((sk_A) = (k1_xboole_0)))),
% 2.25/2.45      inference('demod', [status(thm)], ['168', '169'])).
% 2.25/2.45  thf('171', plain,
% 2.25/2.45      ((((sk_A) = (k1_xboole_0))
% 2.25/2.45        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_A))
% 2.25/2.45        | ~ (v2_funct_1 @ sk_C))),
% 2.25/2.45      inference('simplify', [status(thm)], ['170'])).
% 2.25/2.45  thf('172', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 2.25/2.45      inference('demod', [status(thm)], ['22', '41', '42'])).
% 2.25/2.45  thf('173', plain,
% 2.25/2.45      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_A))
% 2.25/2.45        | ((sk_A) = (k1_xboole_0)))),
% 2.25/2.45      inference('clc', [status(thm)], ['171', '172'])).
% 2.25/2.45  thf('174', plain,
% 2.25/2.45      (![X0 : $i, X1 : $i]:
% 2.25/2.45         (((k1_relat_1 @ X0) != (k1_relat_1 @ X1))
% 2.25/2.45          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X1) != (k2_funct_1 @ X0))
% 2.25/2.45          | ((X1) = (k6_partfun1 @ (k1_relat_1 @ X1)))
% 2.25/2.45          | ~ (v1_funct_1 @ X1)
% 2.25/2.45          | ~ (v1_relat_1 @ X1)
% 2.25/2.45          | ~ (v2_funct_1 @ X0)
% 2.25/2.45          | ~ (v1_funct_1 @ X0)
% 2.25/2.45          | ~ (v1_relat_1 @ X0))),
% 2.25/2.45      inference('simplify', [status(thm)], ['66'])).
% 2.25/2.45  thf('175', plain,
% 2.25/2.45      (![X0 : $i]:
% 2.25/2.45         (~ (v1_relat_1 @ X0)
% 2.25/2.45          | ~ (v1_funct_1 @ X0)
% 2.25/2.45          | ~ (v2_funct_1 @ X0)
% 2.25/2.45          | ~ (v1_relat_1 @ X0)
% 2.25/2.45          | ~ (v1_funct_1 @ X0)
% 2.25/2.45          | ((X0) = (k6_partfun1 @ (k1_relat_1 @ X0)))
% 2.25/2.45          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0) != (k2_funct_1 @ X0)))),
% 2.25/2.45      inference('eq_res', [status(thm)], ['174'])).
% 2.25/2.45  thf('176', plain,
% 2.25/2.45      (![X0 : $i]:
% 2.25/2.45         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0) != (k2_funct_1 @ X0))
% 2.25/2.45          | ((X0) = (k6_partfun1 @ (k1_relat_1 @ X0)))
% 2.25/2.45          | ~ (v2_funct_1 @ X0)
% 2.25/2.45          | ~ (v1_funct_1 @ X0)
% 2.25/2.45          | ~ (v1_relat_1 @ X0))),
% 2.25/2.45      inference('simplify', [status(thm)], ['175'])).
% 2.25/2.45  thf('177', plain,
% 2.25/2.45      ((((k6_partfun1 @ sk_A) != (k2_funct_1 @ sk_C))
% 2.25/2.45        | ((sk_A) = (k1_xboole_0))
% 2.25/2.45        | ~ (v1_relat_1 @ sk_C)
% 2.25/2.45        | ~ (v1_funct_1 @ sk_C)
% 2.25/2.45        | ~ (v2_funct_1 @ sk_C)
% 2.25/2.45        | ((sk_C) = (k6_partfun1 @ (k1_relat_1 @ sk_C))))),
% 2.25/2.45      inference('sup-', [status(thm)], ['173', '176'])).
% 2.25/2.45  thf('178', plain, ((v1_relat_1 @ sk_C)),
% 2.25/2.45      inference('demod', [status(thm)], ['86', '87'])).
% 2.25/2.45  thf('179', plain, ((v1_funct_1 @ sk_C)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('180', plain,
% 2.25/2.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('181', plain,
% 2.25/2.45      (![X66 : $i, X67 : $i]:
% 2.25/2.45         (((k1_relset_1 @ X66 @ X66 @ X67) = (X66))
% 2.25/2.45          | ~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X66 @ X66)))
% 2.25/2.45          | ~ (v1_funct_2 @ X67 @ X66 @ X66)
% 2.25/2.45          | ~ (v1_funct_1 @ X67))),
% 2.25/2.45      inference('cnf', [status(esa)], [t67_funct_2])).
% 2.25/2.45  thf('182', plain,
% 2.25/2.45      ((~ (v1_funct_1 @ sk_C)
% 2.25/2.45        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 2.25/2.45        | ((k1_relset_1 @ sk_A @ sk_A @ sk_C) = (sk_A)))),
% 2.25/2.45      inference('sup-', [status(thm)], ['180', '181'])).
% 2.25/2.45  thf('183', plain, ((v1_funct_1 @ sk_C)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('184', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('185', plain,
% 2.25/2.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('186', plain,
% 2.25/2.45      (![X31 : $i, X32 : $i, X33 : $i]:
% 2.25/2.45         (((k1_relset_1 @ X32 @ X33 @ X31) = (k1_relat_1 @ X31))
% 2.25/2.45          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 2.25/2.45      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.25/2.45  thf('187', plain,
% 2.25/2.45      (((k1_relset_1 @ sk_A @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 2.25/2.45      inference('sup-', [status(thm)], ['185', '186'])).
% 2.25/2.45  thf('188', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 2.25/2.45      inference('demod', [status(thm)], ['182', '183', '184', '187'])).
% 2.25/2.45  thf('189', plain,
% 2.25/2.45      ((((k6_partfun1 @ sk_A) != (k2_funct_1 @ sk_C))
% 2.25/2.45        | ((sk_A) = (k1_xboole_0))
% 2.25/2.45        | ~ (v2_funct_1 @ sk_C)
% 2.25/2.45        | ((sk_C) = (k6_partfun1 @ sk_A)))),
% 2.25/2.45      inference('demod', [status(thm)], ['177', '178', '179', '188'])).
% 2.25/2.45  thf('190', plain,
% 2.25/2.45      ((((sk_A) = (k1_xboole_0))
% 2.25/2.45        | ((sk_C) = (k6_partfun1 @ sk_A))
% 2.25/2.45        | ((sk_A) = (k1_xboole_0))
% 2.25/2.45        | ((k6_partfun1 @ sk_A) != (k2_funct_1 @ sk_C)))),
% 2.25/2.45      inference('sup-', [status(thm)], ['143', '189'])).
% 2.25/2.45  thf('191', plain,
% 2.25/2.45      ((((k6_partfun1 @ sk_A) != (k2_funct_1 @ sk_C))
% 2.25/2.45        | ((sk_C) = (k6_partfun1 @ sk_A))
% 2.25/2.45        | ((sk_A) = (k1_xboole_0)))),
% 2.25/2.45      inference('simplify', [status(thm)], ['190'])).
% 2.25/2.45  thf('192', plain,
% 2.25/2.45      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 2.25/2.45        | ((sk_A) = (k1_xboole_0))
% 2.25/2.45        | ((sk_A) = (k1_xboole_0))
% 2.25/2.45        | ((sk_C) = (k6_partfun1 @ sk_A)))),
% 2.25/2.45      inference('sup-', [status(thm)], ['142', '191'])).
% 2.25/2.45  thf('193', plain,
% 2.25/2.45      ((((sk_C) = (k6_partfun1 @ sk_A)) | ((sk_A) = (k1_xboole_0)))),
% 2.25/2.45      inference('simplify', [status(thm)], ['192'])).
% 2.25/2.45  thf('194', plain,
% 2.25/2.45      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_partfun1 @ sk_A))),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('195', plain,
% 2.25/2.45      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 2.25/2.45      inference('sup-', [status(thm)], ['193', '194'])).
% 2.25/2.45  thf('196', plain,
% 2.25/2.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('197', plain,
% 2.25/2.45      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 2.25/2.45         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 2.25/2.45          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 2.25/2.45          | (r2_relset_1 @ X39 @ X40 @ X38 @ X41)
% 2.25/2.45          | ((X38) != (X41)))),
% 2.25/2.45      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.25/2.45  thf('198', plain,
% 2.25/2.45      (![X39 : $i, X40 : $i, X41 : $i]:
% 2.25/2.45         ((r2_relset_1 @ X39 @ X40 @ X41 @ X41)
% 2.25/2.45          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 2.25/2.45      inference('simplify', [status(thm)], ['197'])).
% 2.25/2.45  thf('199', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 2.25/2.45      inference('sup-', [status(thm)], ['196', '198'])).
% 2.25/2.45  thf('200', plain, (((sk_A) = (k1_xboole_0))),
% 2.25/2.45      inference('demod', [status(thm)], ['195', '199'])).
% 2.25/2.45  thf('201', plain, (((sk_A) = (k1_xboole_0))),
% 2.25/2.45      inference('demod', [status(thm)], ['195', '199'])).
% 2.25/2.45  thf('202', plain, (((sk_A) = (k1_xboole_0))),
% 2.25/2.45      inference('demod', [status(thm)], ['195', '199'])).
% 2.25/2.45  thf(t71_relat_1, axiom,
% 2.25/2.45    (![A:$i]:
% 2.25/2.45     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 2.25/2.45       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 2.25/2.45  thf('203', plain, (![X14 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X14)) = (X14))),
% 2.25/2.45      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.25/2.45  thf('204', plain, (![X57 : $i]: ((k6_partfun1 @ X57) = (k6_relat_1 @ X57))),
% 2.25/2.45      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.25/2.45  thf('205', plain,
% 2.25/2.45      (![X14 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X14)) = (X14))),
% 2.25/2.45      inference('demod', [status(thm)], ['203', '204'])).
% 2.25/2.45  thf(t64_relat_1, axiom,
% 2.25/2.45    (![A:$i]:
% 2.25/2.45     ( ( v1_relat_1 @ A ) =>
% 2.25/2.45       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 2.25/2.45           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 2.25/2.45         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 2.25/2.45  thf('206', plain,
% 2.25/2.45      (![X13 : $i]:
% 2.25/2.45         (((k1_relat_1 @ X13) != (k1_xboole_0))
% 2.25/2.45          | ((X13) = (k1_xboole_0))
% 2.25/2.45          | ~ (v1_relat_1 @ X13))),
% 2.25/2.45      inference('cnf', [status(esa)], [t64_relat_1])).
% 2.25/2.45  thf('207', plain,
% 2.25/2.45      (![X0 : $i]:
% 2.25/2.45         (((X0) != (k1_xboole_0))
% 2.25/2.45          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 2.25/2.45          | ((k6_partfun1 @ X0) = (k1_xboole_0)))),
% 2.25/2.45      inference('sup-', [status(thm)], ['205', '206'])).
% 2.25/2.45  thf(fc4_funct_1, axiom,
% 2.25/2.45    (![A:$i]:
% 2.25/2.45     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 2.25/2.45       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 2.25/2.45  thf('208', plain, (![X18 : $i]: (v1_relat_1 @ (k6_relat_1 @ X18))),
% 2.25/2.45      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.25/2.45  thf('209', plain, (![X57 : $i]: ((k6_partfun1 @ X57) = (k6_relat_1 @ X57))),
% 2.25/2.45      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.25/2.45  thf('210', plain, (![X18 : $i]: (v1_relat_1 @ (k6_partfun1 @ X18))),
% 2.25/2.45      inference('demod', [status(thm)], ['208', '209'])).
% 2.25/2.45  thf('211', plain,
% 2.25/2.45      (![X0 : $i]:
% 2.25/2.45         (((X0) != (k1_xboole_0)) | ((k6_partfun1 @ X0) = (k1_xboole_0)))),
% 2.25/2.45      inference('demod', [status(thm)], ['207', '210'])).
% 2.25/2.45  thf('212', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.25/2.45      inference('simplify', [status(thm)], ['211'])).
% 2.25/2.45  thf('213', plain,
% 2.25/2.45      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ k1_xboole_0)),
% 2.25/2.45      inference('demod', [status(thm)], ['0', '200', '201', '202', '212'])).
% 2.25/2.45  thf('214', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 2.25/2.45      inference('demod', [status(thm)], ['182', '183', '184', '187'])).
% 2.25/2.45  thf('215', plain,
% 2.25/2.45      (![X13 : $i]:
% 2.25/2.45         (((k1_relat_1 @ X13) != (k1_xboole_0))
% 2.25/2.45          | ((X13) = (k1_xboole_0))
% 2.25/2.45          | ~ (v1_relat_1 @ X13))),
% 2.25/2.45      inference('cnf', [status(esa)], [t64_relat_1])).
% 2.25/2.45  thf('216', plain,
% 2.25/2.45      ((((sk_A) != (k1_xboole_0))
% 2.25/2.45        | ~ (v1_relat_1 @ sk_C)
% 2.25/2.45        | ((sk_C) = (k1_xboole_0)))),
% 2.25/2.45      inference('sup-', [status(thm)], ['214', '215'])).
% 2.25/2.45  thf('217', plain, ((v1_relat_1 @ sk_C)),
% 2.25/2.45      inference('demod', [status(thm)], ['86', '87'])).
% 2.25/2.45  thf('218', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 2.25/2.45      inference('demod', [status(thm)], ['216', '217'])).
% 2.25/2.45  thf('219', plain, (((sk_A) = (k1_xboole_0))),
% 2.25/2.45      inference('demod', [status(thm)], ['195', '199'])).
% 2.25/2.45  thf('220', plain,
% 2.25/2.45      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 2.25/2.45      inference('demod', [status(thm)], ['218', '219'])).
% 2.25/2.45  thf('221', plain, (((sk_C) = (k1_xboole_0))),
% 2.25/2.45      inference('simplify', [status(thm)], ['220'])).
% 2.25/2.45  thf('222', plain,
% 2.25/2.45      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 2.25/2.45      inference('demod', [status(thm)], ['213', '221'])).
% 2.25/2.45  thf('223', plain,
% 2.25/2.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.25/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.25/2.45  thf('224', plain,
% 2.25/2.45      (![X39 : $i, X40 : $i, X41 : $i]:
% 2.25/2.45         ((r2_relset_1 @ X39 @ X40 @ X41 @ X41)
% 2.25/2.45          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 2.25/2.45      inference('simplify', [status(thm)], ['197'])).
% 2.25/2.45  thf('225', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 2.25/2.45      inference('sup-', [status(thm)], ['223', '224'])).
% 2.25/2.45  thf('226', plain, (((sk_A) = (k1_xboole_0))),
% 2.25/2.45      inference('demod', [status(thm)], ['195', '199'])).
% 2.25/2.45  thf('227', plain, (((sk_A) = (k1_xboole_0))),
% 2.25/2.45      inference('demod', [status(thm)], ['195', '199'])).
% 2.25/2.45  thf('228', plain, ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_B)),
% 2.25/2.45      inference('demod', [status(thm)], ['225', '226', '227'])).
% 2.25/2.45  thf('229', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 2.25/2.45      inference('demod', [status(thm)], ['50', '51', '52', '55'])).
% 2.25/2.45  thf('230', plain,
% 2.25/2.45      (![X13 : $i]:
% 2.25/2.45         (((k1_relat_1 @ X13) != (k1_xboole_0))
% 2.25/2.45          | ((X13) = (k1_xboole_0))
% 2.25/2.45          | ~ (v1_relat_1 @ X13))),
% 2.25/2.45      inference('cnf', [status(esa)], [t64_relat_1])).
% 2.25/2.45  thf('231', plain,
% 2.25/2.45      ((((sk_A) != (k1_xboole_0))
% 2.25/2.45        | ~ (v1_relat_1 @ sk_B)
% 2.25/2.45        | ((sk_B) = (k1_xboole_0)))),
% 2.25/2.45      inference('sup-', [status(thm)], ['229', '230'])).
% 2.25/2.45  thf('232', plain, ((v1_relat_1 @ sk_B)),
% 2.25/2.45      inference('demod', [status(thm)], ['71', '72'])).
% 2.25/2.45  thf('233', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 2.25/2.45      inference('demod', [status(thm)], ['231', '232'])).
% 2.25/2.45  thf('234', plain, (((sk_A) = (k1_xboole_0))),
% 2.25/2.45      inference('demod', [status(thm)], ['195', '199'])).
% 2.25/2.45  thf('235', plain,
% 2.25/2.45      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 2.25/2.45      inference('demod', [status(thm)], ['233', '234'])).
% 2.25/2.45  thf('236', plain, (((sk_B) = (k1_xboole_0))),
% 2.25/2.45      inference('simplify', [status(thm)], ['235'])).
% 2.25/2.45  thf('237', plain, (((sk_B) = (k1_xboole_0))),
% 2.25/2.45      inference('simplify', [status(thm)], ['235'])).
% 2.25/2.45  thf('238', plain,
% 2.25/2.45      ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 2.25/2.45      inference('demod', [status(thm)], ['228', '236', '237'])).
% 2.25/2.45  thf('239', plain, ($false), inference('demod', [status(thm)], ['222', '238'])).
% 2.25/2.45  
% 2.25/2.45  % SZS output end Refutation
% 2.25/2.45  
% 2.25/2.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

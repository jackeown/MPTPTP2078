%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qoWNsOCUCf

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:05 EST 2020

% Result     : Theorem 4.32s
% Output     : Refutation 4.32s
% Verified   : 
% Statistics : Number of formulae       :  312 (1517 expanded)
%              Number of leaves         :   51 ( 469 expanded)
%              Depth                    :   26
%              Number of atoms          : 2876 (36445 expanded)
%              Number of equality atoms :  217 (2485 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t36_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ C )
                = B )
              & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
              & ( v2_funct_1 @ C ) )
           => ( ( A = k1_xboole_0 )
              | ( B = k1_xboole_0 )
              | ( D
                = ( k2_funct_1 @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( ( ( k2_relset_1 @ A @ B @ C )
                  = B )
                & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
                & ( v2_funct_1 @ C ) )
             => ( ( A = k1_xboole_0 )
                | ( B = k1_xboole_0 )
                | ( D
                  = ( k2_funct_1 @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('2',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('4',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
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

thf('6',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( X50 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_2 @ X51 @ X52 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X50 ) ) )
      | ( ( k5_relat_1 @ X51 @ ( k2_funct_1 @ X51 ) )
        = ( k6_partfun1 @ X52 ) )
      | ~ ( v2_funct_1 @ X51 )
      | ( ( k2_relset_1 @ X52 @ X50 @ X51 )
       != X50 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('7',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('8',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( X50 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_2 @ X51 @ X52 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X50 ) ) )
      | ( ( k5_relat_1 @ X51 @ ( k2_funct_1 @ X51 ) )
        = ( k6_relat_1 @ X52 ) )
      | ~ ( v2_funct_1 @ X51 )
      | ( ( k2_relset_1 @ X52 @ X50 @ X51 )
       != X50 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('12',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','12','13','14'])).

thf('16',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

thf('18',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('20',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( r2_relset_1 @ X38 @ X38 @ ( k1_partfun1 @ X38 @ X39 @ X39 @ X38 @ X37 @ X40 ) @ ( k6_partfun1 @ X38 ) )
      | ( ( k2_relset_1 @ X39 @ X38 @ X40 )
        = X38 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X38 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('23',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('24',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( r2_relset_1 @ X38 @ X38 @ ( k1_partfun1 @ X38 @ X39 @ X39 @ X38 @ X37 @ X40 ) @ ( k6_relat_1 @ X38 ) )
      | ( ( k2_relset_1 @ X39 @ X38 @ X40 )
        = X38 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X38 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['20','28'])).

thf('30',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['29','30','31','32','33'])).

thf('35',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','34'])).

thf('36',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
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

thf('39',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( ( k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33 )
        = ( k5_relat_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('47',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('48',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
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

thf('51',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('58',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('59',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( X18 = X21 )
      | ~ ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','60'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('62',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('63',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('64',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['61','64'])).

thf('66',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['45','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_2 @ D @ A @ B )
        & ( v1_funct_1 @ D ) )
     => ! [E: $i] :
          ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
            & ( v1_funct_2 @ E @ B @ C )
            & ( v1_funct_1 @ E ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ D )
                = B )
              & ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) )
           => ( ( ( v2_funct_1 @ E )
                & ( v2_funct_1 @ D ) )
              | ( ( B != k1_xboole_0 )
                & ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i] :
      ( ( zip_tseitin_1 @ C @ B )
     => ( ( C = k1_xboole_0 )
        & ( B != k1_xboole_0 ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [E: $i,D: $i] :
      ( ( zip_tseitin_0 @ E @ D )
     => ( ( v2_funct_1 @ D )
        & ( v2_funct_1 @ E ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
              & ( ( k2_relset_1 @ A @ B @ D )
                = B ) )
           => ( ( zip_tseitin_1 @ C @ B )
              | ( zip_tseitin_0 @ E @ D ) ) ) ) ) )).

thf('68',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ( zip_tseitin_0 @ X45 @ X48 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X49 @ X46 @ X46 @ X47 @ X48 @ X45 ) )
      | ( zip_tseitin_1 @ X47 @ X46 )
      | ( ( k2_relset_1 @ X49 @ X46 @ X48 )
       != X46 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X46 ) ) )
      | ~ ( v1_funct_2 @ X48 @ X49 @ X46 )
      | ~ ( v1_funct_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['66','72'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('74',plain,(
    ! [X11: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('75',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['73','74','75','76','77','78'])).

thf('80',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X43: $i,X44: $i] :
      ( ( X43 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('82',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X41: $i,X42: $i] :
      ( ( v2_funct_1 @ X42 )
      | ~ ( zip_tseitin_0 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('86',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['36','86'])).

thf('88',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('89',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_funct_1 @ X9 )
        = ( k4_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('90',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k2_funct_1 @ sk_D )
      = ( k4_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['0','1'])).

thf('92',plain,
    ( ( ( k2_funct_1 @ sk_D )
      = ( k4_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['84','85'])).

thf('94',plain,
    ( ( k2_funct_1 @ sk_D )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k5_relat_1 @ sk_D @ ( k4_relat_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['87','94'])).

thf('96',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['61','64'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('97',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('101',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['0','1'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['98','101','102'])).

thf('104',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k4_relat_1 @ sk_D ) )
      = ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['95','103'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('105',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('107',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['0','1'])).

thf('108',plain,(
    ! [X1: $i] :
      ( ( ( k2_relat_1 @ X1 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('109',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('110',plain,(
    ! [X8: $i] :
      ( ( ( k7_relat_1 @ X8 @ ( k1_relat_1 @ X8 ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('111',plain,
    ( ( ( k7_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) )
      = ( k4_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k7_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) )
      = ( k4_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['106','111'])).

thf('113',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['0','1'])).

thf('114',plain,
    ( ( k7_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['112','113'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('115',plain,(
    ! [X5: $i] :
      ( ( ( k5_relat_1 @ X5 @ ( k6_relat_1 @ ( k2_relat_1 @ X5 ) ) )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('116',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k7_relat_1 @ X7 @ X6 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X6 ) @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('117',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('120',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('121',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['118','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['115','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_D ) ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_D ) ) @ ( k4_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['114','127'])).

thf('129',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('131',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('132',plain,(
    ! [X5: $i] :
      ( ( ( k5_relat_1 @ X5 @ ( k6_relat_1 @ ( k2_relat_1 @ X5 ) ) )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('133',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_D ) ) )
      = ( k4_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_D ) ) )
      = ( k4_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['130','133'])).

thf('135',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['0','1'])).

thf('136',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_D ) ) )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,
    ( ( ( k4_relat_1 @ sk_D )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_D ) ) @ ( k4_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['128','129','136'])).

thf('138',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k4_relat_1 @ sk_D )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_D ) ) @ ( k4_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['105','137'])).

thf('139',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['0','1'])).

thf('140',plain,
    ( ( k4_relat_1 @ sk_D )
    = ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_D ) ) @ ( k4_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['29','30','31','32','33'])).

thf('142',plain,
    ( ( k4_relat_1 @ sk_D )
    = ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k4_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('145',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X5: $i] :
      ( ( ( k5_relat_1 @ X5 @ ( k6_relat_1 @ ( k2_relat_1 @ X5 ) ) )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('149',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('150',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['99','100'])).

thf('151',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,
    ( ( k2_funct_1 @ sk_D )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['92','93'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('153',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('154',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['152','153'])).

thf('155',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['0','1'])).

thf('156',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['154','155','156'])).

thf('158',plain,
    ( ( k4_relat_1 @ sk_D )
    = sk_C ),
    inference(demod,[status(thm)],['104','142','151','157'])).

thf('159',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','158'])).

thf('160',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['145','146'])).

thf('161',plain,
    ( ( k1_relat_1 @ sk_D )
    = sk_B ),
    inference('sup+',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X8: $i] :
      ( ( ( k7_relat_1 @ X8 @ ( k1_relat_1 @ X8 ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('163',plain,
    ( ( ( k7_relat_1 @ sk_D @ sk_B )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['161','162'])).

thf('164',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['61','64'])).

thf('165',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( X50 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_2 @ X51 @ X52 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X50 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X51 ) @ X51 )
        = ( k6_partfun1 @ X50 ) )
      | ~ ( v2_funct_1 @ X51 )
      | ( ( k2_relset_1 @ X52 @ X50 @ X51 )
       != X50 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('167',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('168',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( X50 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_2 @ X51 @ X52 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X50 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X51 ) @ X51 )
        = ( k6_relat_1 @ X50 ) )
      | ~ ( v2_funct_1 @ X51 )
      | ( ( k2_relset_1 @ X52 @ X50 @ X51 )
       != X50 ) ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['165','168'])).

thf('170',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_funct_1 @ X9 )
        = ( k4_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('174',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['99','100'])).

thf('176',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['174','175','176'])).

thf('178',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['169','170','171','177','178','179'])).

thf('181',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['180'])).

thf('182',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['181','182'])).

thf('184',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['183','184'])).

thf('186',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['174','175','176'])).

thf('187',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('188',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['186','187'])).

thf('189',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['99','100'])).

thf('190',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['188','189','190'])).

thf('192',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['99','100'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['185','191','192'])).

thf('194',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['164','193'])).

thf('195',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['29','30','31','32','33'])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('197',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k6_relat_1 @ sk_A ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_D ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['195','196'])).

thf('198',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['0','1'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['197','198'])).

thf('200',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['29','30','31','32','33'])).

thf('201',plain,(
    ! [X5: $i] :
      ( ( ( k5_relat_1 @ X5 @ ( k6_relat_1 @ ( k2_relat_1 @ X5 ) ) )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('202',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k6_relat_1 @ sk_A ) )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['200','201'])).

thf('203',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['0','1'])).

thf('204',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_relat_1 @ sk_A ) )
    = sk_D ),
    inference(demod,[status(thm)],['202','203'])).

thf('205',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('206',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k7_relat_1 @ X7 @ X6 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X6 ) @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('207',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['205','206'])).

thf('208',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ sk_D @ ( k6_relat_1 @ sk_A ) ) @ X0 )
        = ( k5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['204','207'])).

thf('209',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['0','1'])).

thf('210',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('211',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['0','1'])).

thf('212',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_relat_1 @ sk_A ) )
    = sk_D ),
    inference(demod,[status(thm)],['202','203'])).

thf('213',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_D @ X0 )
      = ( k5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['208','209','210','211','212'])).

thf('214',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_D @ X0 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_D ) ) ),
    inference('sup+',[status(thm)],['199','213'])).

thf('215',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( X50 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_2 @ X51 @ X52 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X50 ) ) )
      | ( ( k5_relat_1 @ X51 @ ( k2_funct_1 @ X51 ) )
        = ( k6_relat_1 @ X52 ) )
      | ~ ( v2_funct_1 @ X51 )
      | ( ( k2_relset_1 @ X52 @ X50 @ X51 )
       != X50 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('217',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['174','175','176'])).

thf('221',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['217','218','219','220','221','222'])).

thf('224',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['223'])).

thf('225',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,
    ( ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['224','225'])).

thf('227',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['185','191','192'])).

thf('228',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k4_relat_1 @ sk_C ) )
      = ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['226','227'])).

thf('229',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['99','100'])).

thf('230',plain,(
    ! [X1: $i] :
      ( ( ( k2_relat_1 @ X1 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('231',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['229','230'])).

thf('232',plain,(
    ! [X8: $i] :
      ( ( ( k7_relat_1 @ X8 @ ( k1_relat_1 @ X8 ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('233',plain,
    ( ( ( k7_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['231','232'])).

thf('234',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['188','189','190'])).

thf('235',plain,
    ( ( k7_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['233','234'])).

thf('236',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['145','146'])).

thf('237',plain,
    ( ( k7_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_B )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['235','236'])).

thf('238',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('239',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_relat_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['237','238'])).

thf('240',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['99','100'])).

thf('241',plain,(
    ! [X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('242',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['240','241'])).

thf('243',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['240','241'])).

thf('244',plain,(
    ! [X5: $i] :
      ( ( ( k5_relat_1 @ X5 @ ( k6_relat_1 @ ( k2_relat_1 @ X5 ) ) )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('245',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['243','244'])).

thf('246',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['188','189','190'])).

thf('247',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['245','246'])).

thf('248',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['188','189','190'])).

thf('249',plain,
    ( ( k4_relat_1 @ sk_C )
    = ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['239','242','247','248'])).

thf('250',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['188','189','190'])).

thf('251',plain,
    ( ( k4_relat_1 @ sk_C )
    = ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['228','249','250'])).

thf('252',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['0','1'])).

thf('253',plain,
    ( ( k7_relat_1 @ sk_D @ sk_B )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['194','214','251','252'])).

thf('254',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['0','1'])).

thf('255',plain,
    ( ( k4_relat_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['163','253','254'])).

thf('256',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['174','175','176'])).

thf('258',plain,(
    sk_D
 != ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['256','257'])).

thf('259',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['255','258'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qoWNsOCUCf
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:39:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 4.32/4.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.32/4.54  % Solved by: fo/fo7.sh
% 4.32/4.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.32/4.54  % done 3346 iterations in 4.079s
% 4.32/4.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.32/4.54  % SZS output start Refutation
% 4.32/4.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.32/4.54  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 4.32/4.54  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 4.32/4.54  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 4.32/4.54  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 4.32/4.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.32/4.54  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 4.32/4.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.32/4.54  thf(sk_B_type, type, sk_B: $i).
% 4.32/4.54  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 4.32/4.54  thf(sk_A_type, type, sk_A: $i).
% 4.32/4.54  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 4.32/4.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.32/4.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.32/4.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 4.32/4.54  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 4.32/4.54  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 4.32/4.54  thf(sk_C_type, type, sk_C: $i).
% 4.32/4.54  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 4.32/4.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.32/4.54  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 4.32/4.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.32/4.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.32/4.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.32/4.54  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 4.32/4.54  thf(sk_D_type, type, sk_D: $i).
% 4.32/4.54  thf(t36_funct_2, conjecture,
% 4.32/4.54    (![A:$i,B:$i,C:$i]:
% 4.32/4.54     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.32/4.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.32/4.54       ( ![D:$i]:
% 4.32/4.54         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.32/4.54             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.32/4.54           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 4.32/4.54               ( r2_relset_1 @
% 4.32/4.54                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 4.32/4.54                 ( k6_partfun1 @ A ) ) & 
% 4.32/4.54               ( v2_funct_1 @ C ) ) =>
% 4.32/4.54             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 4.32/4.54               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 4.32/4.54  thf(zf_stmt_0, negated_conjecture,
% 4.32/4.54    (~( ![A:$i,B:$i,C:$i]:
% 4.32/4.54        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.32/4.54            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.32/4.54          ( ![D:$i]:
% 4.32/4.54            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.32/4.54                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.32/4.54              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 4.32/4.54                  ( r2_relset_1 @
% 4.32/4.54                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 4.32/4.54                    ( k6_partfun1 @ A ) ) & 
% 4.32/4.54                  ( v2_funct_1 @ C ) ) =>
% 4.32/4.54                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 4.32/4.54                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 4.32/4.54    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 4.32/4.54  thf('0', plain,
% 4.32/4.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.32/4.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.54  thf(cc1_relset_1, axiom,
% 4.32/4.54    (![A:$i,B:$i,C:$i]:
% 4.32/4.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.32/4.54       ( v1_relat_1 @ C ) ))).
% 4.32/4.54  thf('1', plain,
% 4.32/4.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 4.32/4.54         ((v1_relat_1 @ X12)
% 4.32/4.54          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 4.32/4.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.32/4.54  thf('2', plain, ((v1_relat_1 @ sk_D)),
% 4.32/4.54      inference('sup-', [status(thm)], ['0', '1'])).
% 4.32/4.54  thf(t37_relat_1, axiom,
% 4.32/4.54    (![A:$i]:
% 4.32/4.54     ( ( v1_relat_1 @ A ) =>
% 4.32/4.54       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 4.32/4.54         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 4.32/4.54  thf('3', plain,
% 4.32/4.54      (![X1 : $i]:
% 4.32/4.54         (((k1_relat_1 @ X1) = (k2_relat_1 @ (k4_relat_1 @ X1)))
% 4.32/4.54          | ~ (v1_relat_1 @ X1))),
% 4.32/4.54      inference('cnf', [status(esa)], [t37_relat_1])).
% 4.32/4.54  thf('4', plain, (((k1_relat_1 @ sk_D) = (k2_relat_1 @ (k4_relat_1 @ sk_D)))),
% 4.32/4.54      inference('sup-', [status(thm)], ['2', '3'])).
% 4.32/4.54  thf('5', plain,
% 4.32/4.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.32/4.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.54  thf(t35_funct_2, axiom,
% 4.32/4.54    (![A:$i,B:$i,C:$i]:
% 4.32/4.54     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.32/4.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.32/4.54       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 4.32/4.54         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 4.32/4.54           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 4.32/4.54             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 4.32/4.54  thf('6', plain,
% 4.32/4.54      (![X50 : $i, X51 : $i, X52 : $i]:
% 4.32/4.54         (((X50) = (k1_xboole_0))
% 4.32/4.54          | ~ (v1_funct_1 @ X51)
% 4.32/4.54          | ~ (v1_funct_2 @ X51 @ X52 @ X50)
% 4.32/4.54          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 4.32/4.54          | ((k5_relat_1 @ X51 @ (k2_funct_1 @ X51)) = (k6_partfun1 @ X52))
% 4.32/4.54          | ~ (v2_funct_1 @ X51)
% 4.32/4.54          | ((k2_relset_1 @ X52 @ X50 @ X51) != (X50)))),
% 4.32/4.54      inference('cnf', [status(esa)], [t35_funct_2])).
% 4.32/4.54  thf(redefinition_k6_partfun1, axiom,
% 4.32/4.54    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 4.32/4.54  thf('7', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 4.32/4.54      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.32/4.54  thf('8', plain,
% 4.32/4.54      (![X50 : $i, X51 : $i, X52 : $i]:
% 4.32/4.54         (((X50) = (k1_xboole_0))
% 4.32/4.54          | ~ (v1_funct_1 @ X51)
% 4.32/4.54          | ~ (v1_funct_2 @ X51 @ X52 @ X50)
% 4.32/4.54          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 4.32/4.54          | ((k5_relat_1 @ X51 @ (k2_funct_1 @ X51)) = (k6_relat_1 @ X52))
% 4.32/4.54          | ~ (v2_funct_1 @ X51)
% 4.32/4.54          | ((k2_relset_1 @ X52 @ X50 @ X51) != (X50)))),
% 4.32/4.54      inference('demod', [status(thm)], ['6', '7'])).
% 4.32/4.54  thf('9', plain,
% 4.32/4.54      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 4.32/4.54        | ~ (v2_funct_1 @ sk_D)
% 4.32/4.54        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 4.32/4.54        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 4.32/4.54        | ~ (v1_funct_1 @ sk_D)
% 4.32/4.54        | ((sk_A) = (k1_xboole_0)))),
% 4.32/4.54      inference('sup-', [status(thm)], ['5', '8'])).
% 4.32/4.54  thf('10', plain,
% 4.32/4.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.32/4.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.54  thf(redefinition_k2_relset_1, axiom,
% 4.32/4.54    (![A:$i,B:$i,C:$i]:
% 4.32/4.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.32/4.54       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 4.32/4.54  thf('11', plain,
% 4.32/4.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 4.32/4.54         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 4.32/4.54          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 4.32/4.54      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.32/4.54  thf('12', plain,
% 4.32/4.54      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 4.32/4.54      inference('sup-', [status(thm)], ['10', '11'])).
% 4.32/4.54  thf('13', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 4.32/4.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.54  thf('14', plain, ((v1_funct_1 @ sk_D)),
% 4.32/4.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.54  thf('15', plain,
% 4.32/4.54      ((((k2_relat_1 @ sk_D) != (sk_A))
% 4.32/4.54        | ~ (v2_funct_1 @ sk_D)
% 4.32/4.54        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 4.32/4.54        | ((sk_A) = (k1_xboole_0)))),
% 4.32/4.54      inference('demod', [status(thm)], ['9', '12', '13', '14'])).
% 4.32/4.54  thf('16', plain, (((sk_A) != (k1_xboole_0))),
% 4.32/4.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.54  thf('17', plain,
% 4.32/4.54      ((((k2_relat_1 @ sk_D) != (sk_A))
% 4.32/4.54        | ~ (v2_funct_1 @ sk_D)
% 4.32/4.54        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B)))),
% 4.32/4.54      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 4.32/4.54  thf('18', plain,
% 4.32/4.54      ((r2_relset_1 @ sk_A @ sk_A @ 
% 4.32/4.54        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 4.32/4.54        (k6_partfun1 @ sk_A))),
% 4.32/4.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.54  thf('19', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 4.32/4.54      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.32/4.54  thf('20', plain,
% 4.32/4.54      ((r2_relset_1 @ sk_A @ sk_A @ 
% 4.32/4.54        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 4.32/4.54        (k6_relat_1 @ sk_A))),
% 4.32/4.54      inference('demod', [status(thm)], ['18', '19'])).
% 4.32/4.54  thf('21', plain,
% 4.32/4.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.32/4.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.54  thf(t24_funct_2, axiom,
% 4.32/4.54    (![A:$i,B:$i,C:$i]:
% 4.32/4.54     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.32/4.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.32/4.54       ( ![D:$i]:
% 4.32/4.54         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.32/4.54             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.32/4.54           ( ( r2_relset_1 @
% 4.32/4.54               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 4.32/4.54               ( k6_partfun1 @ B ) ) =>
% 4.32/4.54             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 4.32/4.54  thf('22', plain,
% 4.32/4.54      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 4.32/4.54         (~ (v1_funct_1 @ X37)
% 4.32/4.54          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 4.32/4.54          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 4.32/4.54          | ~ (r2_relset_1 @ X38 @ X38 @ 
% 4.32/4.54               (k1_partfun1 @ X38 @ X39 @ X39 @ X38 @ X37 @ X40) @ 
% 4.32/4.54               (k6_partfun1 @ X38))
% 4.32/4.54          | ((k2_relset_1 @ X39 @ X38 @ X40) = (X38))
% 4.32/4.54          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 4.32/4.54          | ~ (v1_funct_2 @ X40 @ X39 @ X38)
% 4.32/4.54          | ~ (v1_funct_1 @ X40))),
% 4.32/4.54      inference('cnf', [status(esa)], [t24_funct_2])).
% 4.32/4.54  thf('23', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 4.32/4.54      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.32/4.54  thf('24', plain,
% 4.32/4.54      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 4.32/4.54         (~ (v1_funct_1 @ X37)
% 4.32/4.54          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 4.32/4.54          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 4.32/4.54          | ~ (r2_relset_1 @ X38 @ X38 @ 
% 4.32/4.54               (k1_partfun1 @ X38 @ X39 @ X39 @ X38 @ X37 @ X40) @ 
% 4.32/4.54               (k6_relat_1 @ X38))
% 4.32/4.54          | ((k2_relset_1 @ X39 @ X38 @ X40) = (X38))
% 4.32/4.54          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 4.32/4.54          | ~ (v1_funct_2 @ X40 @ X39 @ X38)
% 4.32/4.54          | ~ (v1_funct_1 @ X40))),
% 4.32/4.54      inference('demod', [status(thm)], ['22', '23'])).
% 4.32/4.54  thf('25', plain,
% 4.32/4.54      (![X0 : $i]:
% 4.32/4.54         (~ (v1_funct_1 @ X0)
% 4.32/4.54          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 4.32/4.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 4.32/4.54          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 4.32/4.54          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 4.32/4.54               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 4.32/4.54               (k6_relat_1 @ sk_A))
% 4.32/4.54          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 4.32/4.54          | ~ (v1_funct_1 @ sk_C))),
% 4.32/4.54      inference('sup-', [status(thm)], ['21', '24'])).
% 4.32/4.54  thf('26', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 4.32/4.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.54  thf('27', plain, ((v1_funct_1 @ sk_C)),
% 4.32/4.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.54  thf('28', plain,
% 4.32/4.54      (![X0 : $i]:
% 4.32/4.54         (~ (v1_funct_1 @ X0)
% 4.32/4.54          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 4.32/4.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 4.32/4.54          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 4.32/4.54          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 4.32/4.54               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 4.32/4.54               (k6_relat_1 @ sk_A)))),
% 4.32/4.54      inference('demod', [status(thm)], ['25', '26', '27'])).
% 4.32/4.54  thf('29', plain,
% 4.32/4.54      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 4.32/4.54        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 4.32/4.54        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 4.32/4.54        | ~ (v1_funct_1 @ sk_D))),
% 4.32/4.54      inference('sup-', [status(thm)], ['20', '28'])).
% 4.32/4.54  thf('30', plain,
% 4.32/4.54      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 4.32/4.54      inference('sup-', [status(thm)], ['10', '11'])).
% 4.32/4.54  thf('31', plain,
% 4.32/4.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.32/4.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.54  thf('32', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 4.32/4.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.54  thf('33', plain, ((v1_funct_1 @ sk_D)),
% 4.32/4.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.54  thf('34', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 4.32/4.54      inference('demod', [status(thm)], ['29', '30', '31', '32', '33'])).
% 4.32/4.54  thf('35', plain,
% 4.32/4.54      ((((sk_A) != (sk_A))
% 4.32/4.54        | ~ (v2_funct_1 @ sk_D)
% 4.32/4.54        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B)))),
% 4.32/4.54      inference('demod', [status(thm)], ['17', '34'])).
% 4.32/4.54  thf('36', plain,
% 4.32/4.54      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 4.32/4.54        | ~ (v2_funct_1 @ sk_D))),
% 4.32/4.54      inference('simplify', [status(thm)], ['35'])).
% 4.32/4.54  thf('37', plain,
% 4.32/4.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.32/4.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.54  thf('38', plain,
% 4.32/4.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.32/4.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.54  thf(redefinition_k1_partfun1, axiom,
% 4.32/4.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.32/4.54     ( ( ( v1_funct_1 @ E ) & 
% 4.32/4.54         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.32/4.54         ( v1_funct_1 @ F ) & 
% 4.32/4.54         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 4.32/4.54       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 4.32/4.54  thf('39', plain,
% 4.32/4.54      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 4.32/4.54         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 4.32/4.54          | ~ (v1_funct_1 @ X30)
% 4.32/4.54          | ~ (v1_funct_1 @ X33)
% 4.32/4.54          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 4.32/4.54          | ((k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33)
% 4.32/4.54              = (k5_relat_1 @ X30 @ X33)))),
% 4.32/4.54      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 4.32/4.54  thf('40', plain,
% 4.32/4.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.32/4.54         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 4.32/4.54            = (k5_relat_1 @ sk_C @ X0))
% 4.32/4.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 4.32/4.54          | ~ (v1_funct_1 @ X0)
% 4.32/4.54          | ~ (v1_funct_1 @ sk_C))),
% 4.32/4.54      inference('sup-', [status(thm)], ['38', '39'])).
% 4.32/4.54  thf('41', plain, ((v1_funct_1 @ sk_C)),
% 4.32/4.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.54  thf('42', plain,
% 4.32/4.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.32/4.54         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 4.32/4.54            = (k5_relat_1 @ sk_C @ X0))
% 4.32/4.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 4.32/4.54          | ~ (v1_funct_1 @ X0))),
% 4.32/4.54      inference('demod', [status(thm)], ['40', '41'])).
% 4.32/4.54  thf('43', plain,
% 4.32/4.54      ((~ (v1_funct_1 @ sk_D)
% 4.32/4.54        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.32/4.54            = (k5_relat_1 @ sk_C @ sk_D)))),
% 4.32/4.54      inference('sup-', [status(thm)], ['37', '42'])).
% 4.32/4.54  thf('44', plain, ((v1_funct_1 @ sk_D)),
% 4.32/4.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.54  thf('45', plain,
% 4.32/4.54      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.32/4.54         = (k5_relat_1 @ sk_C @ sk_D))),
% 4.32/4.54      inference('demod', [status(thm)], ['43', '44'])).
% 4.32/4.54  thf('46', plain,
% 4.32/4.54      ((r2_relset_1 @ sk_A @ sk_A @ 
% 4.32/4.54        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 4.32/4.54        (k6_relat_1 @ sk_A))),
% 4.32/4.54      inference('demod', [status(thm)], ['18', '19'])).
% 4.32/4.54  thf('47', plain,
% 4.32/4.54      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.32/4.54         = (k5_relat_1 @ sk_C @ sk_D))),
% 4.32/4.54      inference('demod', [status(thm)], ['43', '44'])).
% 4.32/4.54  thf('48', plain,
% 4.32/4.54      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 4.32/4.54        (k6_relat_1 @ sk_A))),
% 4.32/4.54      inference('demod', [status(thm)], ['46', '47'])).
% 4.32/4.54  thf('49', plain,
% 4.32/4.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.32/4.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.54  thf('50', plain,
% 4.32/4.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.32/4.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.54  thf(dt_k1_partfun1, axiom,
% 4.32/4.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.32/4.54     ( ( ( v1_funct_1 @ E ) & 
% 4.32/4.54         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.32/4.54         ( v1_funct_1 @ F ) & 
% 4.32/4.54         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 4.32/4.54       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 4.32/4.54         ( m1_subset_1 @
% 4.32/4.54           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 4.32/4.54           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 4.32/4.54  thf('51', plain,
% 4.32/4.54      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 4.32/4.54         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 4.32/4.54          | ~ (v1_funct_1 @ X22)
% 4.32/4.54          | ~ (v1_funct_1 @ X25)
% 4.32/4.54          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 4.32/4.54          | (m1_subset_1 @ (k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25) @ 
% 4.32/4.54             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X27))))),
% 4.32/4.54      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 4.32/4.54  thf('52', plain,
% 4.32/4.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.32/4.54         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 4.32/4.54           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 4.32/4.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 4.32/4.54          | ~ (v1_funct_1 @ X1)
% 4.32/4.54          | ~ (v1_funct_1 @ sk_C))),
% 4.32/4.54      inference('sup-', [status(thm)], ['50', '51'])).
% 4.32/4.54  thf('53', plain, ((v1_funct_1 @ sk_C)),
% 4.32/4.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.54  thf('54', plain,
% 4.32/4.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.32/4.54         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 4.32/4.54           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 4.32/4.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 4.32/4.54          | ~ (v1_funct_1 @ X1))),
% 4.32/4.54      inference('demod', [status(thm)], ['52', '53'])).
% 4.32/4.54  thf('55', plain,
% 4.32/4.54      ((~ (v1_funct_1 @ sk_D)
% 4.32/4.54        | (m1_subset_1 @ 
% 4.32/4.54           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 4.32/4.54           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 4.32/4.54      inference('sup-', [status(thm)], ['49', '54'])).
% 4.32/4.54  thf('56', plain, ((v1_funct_1 @ sk_D)),
% 4.32/4.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.54  thf('57', plain,
% 4.32/4.54      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.32/4.54         = (k5_relat_1 @ sk_C @ sk_D))),
% 4.32/4.54      inference('demod', [status(thm)], ['43', '44'])).
% 4.32/4.54  thf('58', plain,
% 4.32/4.54      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 4.32/4.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.32/4.54      inference('demod', [status(thm)], ['55', '56', '57'])).
% 4.32/4.54  thf(redefinition_r2_relset_1, axiom,
% 4.32/4.54    (![A:$i,B:$i,C:$i,D:$i]:
% 4.32/4.54     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.32/4.54         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.32/4.54       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 4.32/4.54  thf('59', plain,
% 4.32/4.54      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 4.32/4.54         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 4.32/4.54          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 4.32/4.54          | ((X18) = (X21))
% 4.32/4.54          | ~ (r2_relset_1 @ X19 @ X20 @ X18 @ X21))),
% 4.32/4.54      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 4.32/4.54  thf('60', plain,
% 4.32/4.54      (![X0 : $i]:
% 4.32/4.54         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 4.32/4.54          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 4.32/4.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 4.32/4.54      inference('sup-', [status(thm)], ['58', '59'])).
% 4.32/4.54  thf('61', plain,
% 4.32/4.54      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 4.32/4.54           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 4.32/4.54        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A)))),
% 4.32/4.54      inference('sup-', [status(thm)], ['48', '60'])).
% 4.32/4.54  thf(dt_k6_partfun1, axiom,
% 4.32/4.54    (![A:$i]:
% 4.32/4.54     ( ( m1_subset_1 @
% 4.32/4.54         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 4.32/4.54       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 4.32/4.54  thf('62', plain,
% 4.32/4.54      (![X29 : $i]:
% 4.32/4.54         (m1_subset_1 @ (k6_partfun1 @ X29) @ 
% 4.32/4.54          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 4.32/4.54      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 4.32/4.54  thf('63', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 4.32/4.54      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.32/4.54  thf('64', plain,
% 4.32/4.54      (![X29 : $i]:
% 4.32/4.54         (m1_subset_1 @ (k6_relat_1 @ X29) @ 
% 4.32/4.54          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 4.32/4.54      inference('demod', [status(thm)], ['62', '63'])).
% 4.32/4.54  thf('65', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 4.32/4.54      inference('demod', [status(thm)], ['61', '64'])).
% 4.32/4.54  thf('66', plain,
% 4.32/4.54      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 4.32/4.54         = (k6_relat_1 @ sk_A))),
% 4.32/4.54      inference('demod', [status(thm)], ['45', '65'])).
% 4.32/4.54  thf('67', plain,
% 4.32/4.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.32/4.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.54  thf(t30_funct_2, axiom,
% 4.32/4.54    (![A:$i,B:$i,C:$i,D:$i]:
% 4.32/4.54     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.32/4.54         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 4.32/4.54       ( ![E:$i]:
% 4.32/4.54         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 4.32/4.54             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 4.32/4.54           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 4.32/4.54               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 4.32/4.54             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 4.32/4.54               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 4.32/4.54  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 4.32/4.54  thf(zf_stmt_2, axiom,
% 4.32/4.54    (![C:$i,B:$i]:
% 4.32/4.54     ( ( zip_tseitin_1 @ C @ B ) =>
% 4.32/4.54       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 4.32/4.54  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 4.32/4.54  thf(zf_stmt_4, axiom,
% 4.32/4.54    (![E:$i,D:$i]:
% 4.32/4.54     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 4.32/4.54  thf(zf_stmt_5, axiom,
% 4.32/4.54    (![A:$i,B:$i,C:$i,D:$i]:
% 4.32/4.54     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 4.32/4.54         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.32/4.54       ( ![E:$i]:
% 4.32/4.54         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 4.32/4.54             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 4.32/4.54           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 4.32/4.54               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 4.32/4.54             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 4.32/4.54  thf('68', plain,
% 4.32/4.54      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 4.32/4.54         (~ (v1_funct_1 @ X45)
% 4.32/4.54          | ~ (v1_funct_2 @ X45 @ X46 @ X47)
% 4.32/4.54          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 4.32/4.54          | (zip_tseitin_0 @ X45 @ X48)
% 4.32/4.54          | ~ (v2_funct_1 @ (k1_partfun1 @ X49 @ X46 @ X46 @ X47 @ X48 @ X45))
% 4.32/4.54          | (zip_tseitin_1 @ X47 @ X46)
% 4.32/4.54          | ((k2_relset_1 @ X49 @ X46 @ X48) != (X46))
% 4.32/4.54          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X46)))
% 4.32/4.54          | ~ (v1_funct_2 @ X48 @ X49 @ X46)
% 4.32/4.54          | ~ (v1_funct_1 @ X48))),
% 4.32/4.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.32/4.54  thf('69', plain,
% 4.32/4.54      (![X0 : $i, X1 : $i]:
% 4.32/4.54         (~ (v1_funct_1 @ X0)
% 4.32/4.54          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 4.32/4.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 4.32/4.54          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 4.32/4.54          | (zip_tseitin_1 @ sk_A @ sk_B)
% 4.32/4.54          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 4.32/4.54          | (zip_tseitin_0 @ sk_D @ X0)
% 4.32/4.54          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 4.32/4.54          | ~ (v1_funct_1 @ sk_D))),
% 4.32/4.54      inference('sup-', [status(thm)], ['67', '68'])).
% 4.32/4.54  thf('70', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 4.32/4.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.54  thf('71', plain, ((v1_funct_1 @ sk_D)),
% 4.32/4.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.54  thf('72', plain,
% 4.32/4.54      (![X0 : $i, X1 : $i]:
% 4.32/4.54         (~ (v1_funct_1 @ X0)
% 4.32/4.54          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 4.32/4.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 4.32/4.54          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 4.32/4.54          | (zip_tseitin_1 @ sk_A @ sk_B)
% 4.32/4.54          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 4.32/4.54          | (zip_tseitin_0 @ sk_D @ X0))),
% 4.32/4.54      inference('demod', [status(thm)], ['69', '70', '71'])).
% 4.32/4.54  thf('73', plain,
% 4.32/4.54      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 4.32/4.54        | (zip_tseitin_0 @ sk_D @ sk_C)
% 4.32/4.54        | (zip_tseitin_1 @ sk_A @ sk_B)
% 4.32/4.54        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 4.32/4.54        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 4.32/4.54        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 4.32/4.54        | ~ (v1_funct_1 @ sk_C))),
% 4.32/4.54      inference('sup-', [status(thm)], ['66', '72'])).
% 4.32/4.54  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 4.32/4.54  thf('74', plain, (![X11 : $i]: (v2_funct_1 @ (k6_relat_1 @ X11))),
% 4.32/4.54      inference('cnf', [status(esa)], [t52_funct_1])).
% 4.32/4.54  thf('75', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 4.32/4.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.54  thf('76', plain,
% 4.32/4.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.32/4.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.54  thf('77', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 4.32/4.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.54  thf('78', plain, ((v1_funct_1 @ sk_C)),
% 4.32/4.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.54  thf('79', plain,
% 4.32/4.54      (((zip_tseitin_0 @ sk_D @ sk_C)
% 4.32/4.54        | (zip_tseitin_1 @ sk_A @ sk_B)
% 4.32/4.54        | ((sk_B) != (sk_B)))),
% 4.32/4.54      inference('demod', [status(thm)], ['73', '74', '75', '76', '77', '78'])).
% 4.32/4.54  thf('80', plain,
% 4.32/4.54      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 4.32/4.54      inference('simplify', [status(thm)], ['79'])).
% 4.32/4.54  thf('81', plain,
% 4.32/4.54      (![X43 : $i, X44 : $i]:
% 4.32/4.54         (((X43) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X43 @ X44))),
% 4.32/4.54      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.32/4.54  thf('82', plain,
% 4.32/4.54      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 4.32/4.54      inference('sup-', [status(thm)], ['80', '81'])).
% 4.32/4.54  thf('83', plain, (((sk_A) != (k1_xboole_0))),
% 4.32/4.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.54  thf('84', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 4.32/4.54      inference('simplify_reflect-', [status(thm)], ['82', '83'])).
% 4.32/4.54  thf('85', plain,
% 4.32/4.54      (![X41 : $i, X42 : $i]:
% 4.32/4.54         ((v2_funct_1 @ X42) | ~ (zip_tseitin_0 @ X42 @ X41))),
% 4.32/4.54      inference('cnf', [status(esa)], [zf_stmt_4])).
% 4.32/4.54  thf('86', plain, ((v2_funct_1 @ sk_D)),
% 4.32/4.54      inference('sup-', [status(thm)], ['84', '85'])).
% 4.32/4.54  thf('87', plain,
% 4.32/4.54      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 4.32/4.54      inference('demod', [status(thm)], ['36', '86'])).
% 4.32/4.54  thf('88', plain, ((v1_funct_1 @ sk_D)),
% 4.32/4.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.54  thf(d9_funct_1, axiom,
% 4.32/4.54    (![A:$i]:
% 4.32/4.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.32/4.54       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 4.32/4.54  thf('89', plain,
% 4.32/4.54      (![X9 : $i]:
% 4.32/4.54         (~ (v2_funct_1 @ X9)
% 4.32/4.54          | ((k2_funct_1 @ X9) = (k4_relat_1 @ X9))
% 4.32/4.54          | ~ (v1_funct_1 @ X9)
% 4.32/4.54          | ~ (v1_relat_1 @ X9))),
% 4.32/4.54      inference('cnf', [status(esa)], [d9_funct_1])).
% 4.32/4.54  thf('90', plain,
% 4.32/4.54      ((~ (v1_relat_1 @ sk_D)
% 4.32/4.54        | ((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))
% 4.32/4.54        | ~ (v2_funct_1 @ sk_D))),
% 4.32/4.54      inference('sup-', [status(thm)], ['88', '89'])).
% 4.32/4.54  thf('91', plain, ((v1_relat_1 @ sk_D)),
% 4.32/4.54      inference('sup-', [status(thm)], ['0', '1'])).
% 4.32/4.54  thf('92', plain,
% 4.32/4.54      ((((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 4.32/4.54      inference('demod', [status(thm)], ['90', '91'])).
% 4.32/4.54  thf('93', plain, ((v2_funct_1 @ sk_D)),
% 4.32/4.54      inference('sup-', [status(thm)], ['84', '85'])).
% 4.32/4.54  thf('94', plain, (((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))),
% 4.32/4.54      inference('demod', [status(thm)], ['92', '93'])).
% 4.32/4.54  thf('95', plain,
% 4.32/4.54      (((k5_relat_1 @ sk_D @ (k4_relat_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 4.32/4.54      inference('demod', [status(thm)], ['87', '94'])).
% 4.32/4.54  thf('96', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 4.32/4.54      inference('demod', [status(thm)], ['61', '64'])).
% 4.32/4.54  thf(t55_relat_1, axiom,
% 4.32/4.54    (![A:$i]:
% 4.32/4.54     ( ( v1_relat_1 @ A ) =>
% 4.32/4.54       ( ![B:$i]:
% 4.32/4.54         ( ( v1_relat_1 @ B ) =>
% 4.32/4.54           ( ![C:$i]:
% 4.32/4.54             ( ( v1_relat_1 @ C ) =>
% 4.32/4.54               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 4.32/4.54                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 4.32/4.54  thf('97', plain,
% 4.32/4.54      (![X2 : $i, X3 : $i, X4 : $i]:
% 4.32/4.54         (~ (v1_relat_1 @ X2)
% 4.32/4.54          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 4.32/4.54              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 4.32/4.54          | ~ (v1_relat_1 @ X4)
% 4.32/4.54          | ~ (v1_relat_1 @ X3))),
% 4.32/4.54      inference('cnf', [status(esa)], [t55_relat_1])).
% 4.32/4.54  thf('98', plain,
% 4.32/4.54      (![X0 : $i]:
% 4.32/4.54         (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ X0)
% 4.32/4.54            = (k5_relat_1 @ sk_C @ (k5_relat_1 @ sk_D @ X0)))
% 4.32/4.54          | ~ (v1_relat_1 @ sk_C)
% 4.32/4.54          | ~ (v1_relat_1 @ X0)
% 4.32/4.54          | ~ (v1_relat_1 @ sk_D))),
% 4.32/4.54      inference('sup+', [status(thm)], ['96', '97'])).
% 4.32/4.54  thf('99', plain,
% 4.32/4.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.32/4.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.54  thf('100', plain,
% 4.32/4.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 4.32/4.54         ((v1_relat_1 @ X12)
% 4.32/4.54          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 4.32/4.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.32/4.54  thf('101', plain, ((v1_relat_1 @ sk_C)),
% 4.32/4.54      inference('sup-', [status(thm)], ['99', '100'])).
% 4.32/4.54  thf('102', plain, ((v1_relat_1 @ sk_D)),
% 4.32/4.54      inference('sup-', [status(thm)], ['0', '1'])).
% 4.32/4.54  thf('103', plain,
% 4.32/4.54      (![X0 : $i]:
% 4.32/4.54         (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ X0)
% 4.32/4.54            = (k5_relat_1 @ sk_C @ (k5_relat_1 @ sk_D @ X0)))
% 4.32/4.54          | ~ (v1_relat_1 @ X0))),
% 4.32/4.54      inference('demod', [status(thm)], ['98', '101', '102'])).
% 4.32/4.54  thf('104', plain,
% 4.32/4.54      ((((k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k4_relat_1 @ sk_D))
% 4.32/4.54          = (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)))
% 4.32/4.54        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_D)))),
% 4.32/4.54      inference('sup+', [status(thm)], ['95', '103'])).
% 4.32/4.54  thf(dt_k4_relat_1, axiom,
% 4.32/4.54    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 4.32/4.54  thf('105', plain,
% 4.32/4.54      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 4.32/4.54      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 4.32/4.54  thf('106', plain,
% 4.32/4.54      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 4.32/4.54      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 4.32/4.54  thf('107', plain, ((v1_relat_1 @ sk_D)),
% 4.32/4.54      inference('sup-', [status(thm)], ['0', '1'])).
% 4.32/4.54  thf('108', plain,
% 4.32/4.54      (![X1 : $i]:
% 4.32/4.54         (((k2_relat_1 @ X1) = (k1_relat_1 @ (k4_relat_1 @ X1)))
% 4.32/4.54          | ~ (v1_relat_1 @ X1))),
% 4.32/4.54      inference('cnf', [status(esa)], [t37_relat_1])).
% 4.32/4.54  thf('109', plain,
% 4.32/4.54      (((k2_relat_1 @ sk_D) = (k1_relat_1 @ (k4_relat_1 @ sk_D)))),
% 4.32/4.54      inference('sup-', [status(thm)], ['107', '108'])).
% 4.32/4.54  thf(t98_relat_1, axiom,
% 4.32/4.54    (![A:$i]:
% 4.32/4.54     ( ( v1_relat_1 @ A ) =>
% 4.32/4.54       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 4.32/4.54  thf('110', plain,
% 4.32/4.54      (![X8 : $i]:
% 4.32/4.54         (((k7_relat_1 @ X8 @ (k1_relat_1 @ X8)) = (X8)) | ~ (v1_relat_1 @ X8))),
% 4.32/4.54      inference('cnf', [status(esa)], [t98_relat_1])).
% 4.32/4.54  thf('111', plain,
% 4.32/4.54      ((((k7_relat_1 @ (k4_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D))
% 4.32/4.54          = (k4_relat_1 @ sk_D))
% 4.32/4.54        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_D)))),
% 4.32/4.54      inference('sup+', [status(thm)], ['109', '110'])).
% 4.32/4.54  thf('112', plain,
% 4.32/4.54      ((~ (v1_relat_1 @ sk_D)
% 4.32/4.54        | ((k7_relat_1 @ (k4_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D))
% 4.32/4.54            = (k4_relat_1 @ sk_D)))),
% 4.32/4.54      inference('sup-', [status(thm)], ['106', '111'])).
% 4.32/4.54  thf('113', plain, ((v1_relat_1 @ sk_D)),
% 4.32/4.54      inference('sup-', [status(thm)], ['0', '1'])).
% 4.32/4.54  thf('114', plain,
% 4.32/4.54      (((k7_relat_1 @ (k4_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D))
% 4.32/4.54         = (k4_relat_1 @ sk_D))),
% 4.32/4.54      inference('demod', [status(thm)], ['112', '113'])).
% 4.32/4.54  thf(t80_relat_1, axiom,
% 4.32/4.54    (![A:$i]:
% 4.32/4.54     ( ( v1_relat_1 @ A ) =>
% 4.32/4.54       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 4.32/4.54  thf('115', plain,
% 4.32/4.54      (![X5 : $i]:
% 4.32/4.54         (((k5_relat_1 @ X5 @ (k6_relat_1 @ (k2_relat_1 @ X5))) = (X5))
% 4.32/4.54          | ~ (v1_relat_1 @ X5))),
% 4.32/4.54      inference('cnf', [status(esa)], [t80_relat_1])).
% 4.32/4.54  thf(t94_relat_1, axiom,
% 4.32/4.54    (![A:$i,B:$i]:
% 4.32/4.54     ( ( v1_relat_1 @ B ) =>
% 4.32/4.54       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 4.32/4.54  thf('116', plain,
% 4.32/4.54      (![X6 : $i, X7 : $i]:
% 4.32/4.54         (((k7_relat_1 @ X7 @ X6) = (k5_relat_1 @ (k6_relat_1 @ X6) @ X7))
% 4.32/4.54          | ~ (v1_relat_1 @ X7))),
% 4.32/4.54      inference('cnf', [status(esa)], [t94_relat_1])).
% 4.32/4.54  thf('117', plain,
% 4.32/4.54      (![X2 : $i, X3 : $i, X4 : $i]:
% 4.32/4.54         (~ (v1_relat_1 @ X2)
% 4.32/4.54          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 4.32/4.54              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 4.32/4.54          | ~ (v1_relat_1 @ X4)
% 4.32/4.54          | ~ (v1_relat_1 @ X3))),
% 4.32/4.54      inference('cnf', [status(esa)], [t55_relat_1])).
% 4.32/4.54  thf('118', plain,
% 4.32/4.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.32/4.54         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 4.32/4.54            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 4.32/4.54          | ~ (v1_relat_1 @ X1)
% 4.32/4.54          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 4.32/4.54          | ~ (v1_relat_1 @ X2)
% 4.32/4.54          | ~ (v1_relat_1 @ X1))),
% 4.32/4.54      inference('sup+', [status(thm)], ['116', '117'])).
% 4.32/4.54  thf('119', plain,
% 4.32/4.54      (![X29 : $i]:
% 4.32/4.54         (m1_subset_1 @ (k6_relat_1 @ X29) @ 
% 4.32/4.54          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 4.32/4.54      inference('demod', [status(thm)], ['62', '63'])).
% 4.32/4.54  thf('120', plain,
% 4.32/4.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 4.32/4.54         ((v1_relat_1 @ X12)
% 4.32/4.54          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 4.32/4.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.32/4.54  thf('121', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 4.32/4.54      inference('sup-', [status(thm)], ['119', '120'])).
% 4.32/4.54  thf('122', plain,
% 4.32/4.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.32/4.54         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 4.32/4.54            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 4.32/4.54          | ~ (v1_relat_1 @ X1)
% 4.32/4.54          | ~ (v1_relat_1 @ X2)
% 4.32/4.54          | ~ (v1_relat_1 @ X1))),
% 4.32/4.54      inference('demod', [status(thm)], ['118', '121'])).
% 4.32/4.54  thf('123', plain,
% 4.32/4.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.32/4.54         (~ (v1_relat_1 @ X2)
% 4.32/4.54          | ~ (v1_relat_1 @ X1)
% 4.32/4.54          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 4.32/4.54              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 4.32/4.54      inference('simplify', [status(thm)], ['122'])).
% 4.32/4.54  thf('124', plain,
% 4.32/4.54      (![X0 : $i, X1 : $i]:
% 4.32/4.54         (((k5_relat_1 @ (k7_relat_1 @ X0 @ X1) @ 
% 4.32/4.54            (k6_relat_1 @ (k2_relat_1 @ X0)))
% 4.32/4.54            = (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 4.32/4.54          | ~ (v1_relat_1 @ X0)
% 4.32/4.54          | ~ (v1_relat_1 @ X0)
% 4.32/4.54          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))),
% 4.32/4.54      inference('sup+', [status(thm)], ['115', '123'])).
% 4.32/4.54  thf('125', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 4.32/4.54      inference('sup-', [status(thm)], ['119', '120'])).
% 4.32/4.54  thf('126', plain,
% 4.32/4.54      (![X0 : $i, X1 : $i]:
% 4.32/4.54         (((k5_relat_1 @ (k7_relat_1 @ X0 @ X1) @ 
% 4.32/4.54            (k6_relat_1 @ (k2_relat_1 @ X0)))
% 4.32/4.54            = (k5_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 4.32/4.54          | ~ (v1_relat_1 @ X0)
% 4.32/4.54          | ~ (v1_relat_1 @ X0))),
% 4.32/4.54      inference('demod', [status(thm)], ['124', '125'])).
% 4.32/4.54  thf('127', plain,
% 4.32/4.54      (![X0 : $i, X1 : $i]:
% 4.32/4.54         (~ (v1_relat_1 @ X0)
% 4.32/4.54          | ((k5_relat_1 @ (k7_relat_1 @ X0 @ X1) @ 
% 4.32/4.54              (k6_relat_1 @ (k2_relat_1 @ X0)))
% 4.32/4.54              = (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 4.32/4.54      inference('simplify', [status(thm)], ['126'])).
% 4.32/4.54  thf('128', plain,
% 4.32/4.54      ((((k5_relat_1 @ (k4_relat_1 @ sk_D) @ 
% 4.32/4.54          (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_D))))
% 4.32/4.54          = (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_D)) @ 
% 4.32/4.54             (k4_relat_1 @ sk_D)))
% 4.32/4.54        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_D)))),
% 4.32/4.54      inference('sup+', [status(thm)], ['114', '127'])).
% 4.32/4.54  thf('129', plain,
% 4.32/4.54      (((k1_relat_1 @ sk_D) = (k2_relat_1 @ (k4_relat_1 @ sk_D)))),
% 4.32/4.54      inference('sup-', [status(thm)], ['2', '3'])).
% 4.32/4.54  thf('130', plain,
% 4.32/4.54      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 4.32/4.54      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 4.32/4.54  thf('131', plain,
% 4.32/4.54      (((k1_relat_1 @ sk_D) = (k2_relat_1 @ (k4_relat_1 @ sk_D)))),
% 4.32/4.54      inference('sup-', [status(thm)], ['2', '3'])).
% 4.32/4.54  thf('132', plain,
% 4.32/4.54      (![X5 : $i]:
% 4.32/4.54         (((k5_relat_1 @ X5 @ (k6_relat_1 @ (k2_relat_1 @ X5))) = (X5))
% 4.32/4.54          | ~ (v1_relat_1 @ X5))),
% 4.32/4.54      inference('cnf', [status(esa)], [t80_relat_1])).
% 4.32/4.54  thf('133', plain,
% 4.32/4.54      ((((k5_relat_1 @ (k4_relat_1 @ sk_D) @ (k6_relat_1 @ (k1_relat_1 @ sk_D)))
% 4.32/4.54          = (k4_relat_1 @ sk_D))
% 4.32/4.54        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_D)))),
% 4.32/4.54      inference('sup+', [status(thm)], ['131', '132'])).
% 4.32/4.54  thf('134', plain,
% 4.32/4.54      ((~ (v1_relat_1 @ sk_D)
% 4.32/4.54        | ((k5_relat_1 @ (k4_relat_1 @ sk_D) @ 
% 4.32/4.54            (k6_relat_1 @ (k1_relat_1 @ sk_D))) = (k4_relat_1 @ sk_D)))),
% 4.32/4.54      inference('sup-', [status(thm)], ['130', '133'])).
% 4.32/4.54  thf('135', plain, ((v1_relat_1 @ sk_D)),
% 4.32/4.54      inference('sup-', [status(thm)], ['0', '1'])).
% 4.32/4.54  thf('136', plain,
% 4.32/4.54      (((k5_relat_1 @ (k4_relat_1 @ sk_D) @ (k6_relat_1 @ (k1_relat_1 @ sk_D)))
% 4.32/4.54         = (k4_relat_1 @ sk_D))),
% 4.32/4.54      inference('demod', [status(thm)], ['134', '135'])).
% 4.32/4.54  thf('137', plain,
% 4.32/4.54      ((((k4_relat_1 @ sk_D)
% 4.32/4.54          = (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_D)) @ 
% 4.32/4.54             (k4_relat_1 @ sk_D)))
% 4.32/4.54        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_D)))),
% 4.32/4.54      inference('demod', [status(thm)], ['128', '129', '136'])).
% 4.32/4.54  thf('138', plain,
% 4.32/4.54      ((~ (v1_relat_1 @ sk_D)
% 4.32/4.54        | ((k4_relat_1 @ sk_D)
% 4.32/4.54            = (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_D)) @ 
% 4.32/4.54               (k4_relat_1 @ sk_D))))),
% 4.32/4.54      inference('sup-', [status(thm)], ['105', '137'])).
% 4.32/4.54  thf('139', plain, ((v1_relat_1 @ sk_D)),
% 4.32/4.54      inference('sup-', [status(thm)], ['0', '1'])).
% 4.32/4.54  thf('140', plain,
% 4.32/4.54      (((k4_relat_1 @ sk_D)
% 4.32/4.54         = (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_D)) @ 
% 4.32/4.54            (k4_relat_1 @ sk_D)))),
% 4.32/4.54      inference('demod', [status(thm)], ['138', '139'])).
% 4.32/4.54  thf('141', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 4.32/4.54      inference('demod', [status(thm)], ['29', '30', '31', '32', '33'])).
% 4.32/4.54  thf('142', plain,
% 4.32/4.54      (((k4_relat_1 @ sk_D)
% 4.32/4.54         = (k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k4_relat_1 @ sk_D)))),
% 4.32/4.54      inference('demod', [status(thm)], ['140', '141'])).
% 4.32/4.54  thf('143', plain,
% 4.32/4.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.32/4.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.54  thf('144', plain,
% 4.32/4.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 4.32/4.54         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 4.32/4.54          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 4.32/4.54      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.32/4.54  thf('145', plain,
% 4.32/4.54      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 4.32/4.54      inference('sup-', [status(thm)], ['143', '144'])).
% 4.32/4.54  thf('146', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 4.32/4.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.54  thf('147', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 4.32/4.54      inference('sup+', [status(thm)], ['145', '146'])).
% 4.32/4.54  thf('148', plain,
% 4.32/4.54      (![X5 : $i]:
% 4.32/4.54         (((k5_relat_1 @ X5 @ (k6_relat_1 @ (k2_relat_1 @ X5))) = (X5))
% 4.32/4.54          | ~ (v1_relat_1 @ X5))),
% 4.32/4.54      inference('cnf', [status(esa)], [t80_relat_1])).
% 4.32/4.54  thf('149', plain,
% 4.32/4.54      ((((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) = (sk_C))
% 4.32/4.54        | ~ (v1_relat_1 @ sk_C))),
% 4.32/4.54      inference('sup+', [status(thm)], ['147', '148'])).
% 4.32/4.54  thf('150', plain, ((v1_relat_1 @ sk_C)),
% 4.32/4.55      inference('sup-', [status(thm)], ['99', '100'])).
% 4.32/4.55  thf('151', plain, (((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) = (sk_C))),
% 4.32/4.55      inference('demod', [status(thm)], ['149', '150'])).
% 4.32/4.55  thf('152', plain, (((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))),
% 4.32/4.55      inference('demod', [status(thm)], ['92', '93'])).
% 4.32/4.55  thf(dt_k2_funct_1, axiom,
% 4.32/4.55    (![A:$i]:
% 4.32/4.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.32/4.55       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 4.32/4.55         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 4.32/4.55  thf('153', plain,
% 4.32/4.55      (![X10 : $i]:
% 4.32/4.55         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 4.32/4.55          | ~ (v1_funct_1 @ X10)
% 4.32/4.55          | ~ (v1_relat_1 @ X10))),
% 4.32/4.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.32/4.55  thf('154', plain,
% 4.32/4.55      (((v1_relat_1 @ (k4_relat_1 @ sk_D))
% 4.32/4.55        | ~ (v1_relat_1 @ sk_D)
% 4.32/4.55        | ~ (v1_funct_1 @ sk_D))),
% 4.32/4.55      inference('sup+', [status(thm)], ['152', '153'])).
% 4.32/4.55  thf('155', plain, ((v1_relat_1 @ sk_D)),
% 4.32/4.55      inference('sup-', [status(thm)], ['0', '1'])).
% 4.32/4.55  thf('156', plain, ((v1_funct_1 @ sk_D)),
% 4.32/4.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.55  thf('157', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_D))),
% 4.32/4.55      inference('demod', [status(thm)], ['154', '155', '156'])).
% 4.32/4.55  thf('158', plain, (((k4_relat_1 @ sk_D) = (sk_C))),
% 4.32/4.55      inference('demod', [status(thm)], ['104', '142', '151', '157'])).
% 4.32/4.55  thf('159', plain, (((k1_relat_1 @ sk_D) = (k2_relat_1 @ sk_C))),
% 4.32/4.55      inference('demod', [status(thm)], ['4', '158'])).
% 4.32/4.55  thf('160', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 4.32/4.55      inference('sup+', [status(thm)], ['145', '146'])).
% 4.32/4.55  thf('161', plain, (((k1_relat_1 @ sk_D) = (sk_B))),
% 4.32/4.55      inference('sup+', [status(thm)], ['159', '160'])).
% 4.32/4.55  thf('162', plain,
% 4.32/4.55      (![X8 : $i]:
% 4.32/4.55         (((k7_relat_1 @ X8 @ (k1_relat_1 @ X8)) = (X8)) | ~ (v1_relat_1 @ X8))),
% 4.32/4.55      inference('cnf', [status(esa)], [t98_relat_1])).
% 4.32/4.55  thf('163', plain,
% 4.32/4.55      ((((k7_relat_1 @ sk_D @ sk_B) = (sk_D)) | ~ (v1_relat_1 @ sk_D))),
% 4.32/4.55      inference('sup+', [status(thm)], ['161', '162'])).
% 4.32/4.55  thf('164', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 4.32/4.55      inference('demod', [status(thm)], ['61', '64'])).
% 4.32/4.55  thf('165', plain,
% 4.32/4.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.32/4.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.55  thf('166', plain,
% 4.32/4.55      (![X50 : $i, X51 : $i, X52 : $i]:
% 4.32/4.55         (((X50) = (k1_xboole_0))
% 4.32/4.55          | ~ (v1_funct_1 @ X51)
% 4.32/4.55          | ~ (v1_funct_2 @ X51 @ X52 @ X50)
% 4.32/4.55          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 4.32/4.55          | ((k5_relat_1 @ (k2_funct_1 @ X51) @ X51) = (k6_partfun1 @ X50))
% 4.32/4.55          | ~ (v2_funct_1 @ X51)
% 4.32/4.55          | ((k2_relset_1 @ X52 @ X50 @ X51) != (X50)))),
% 4.32/4.55      inference('cnf', [status(esa)], [t35_funct_2])).
% 4.32/4.55  thf('167', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 4.32/4.55      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.32/4.55  thf('168', plain,
% 4.32/4.55      (![X50 : $i, X51 : $i, X52 : $i]:
% 4.32/4.55         (((X50) = (k1_xboole_0))
% 4.32/4.55          | ~ (v1_funct_1 @ X51)
% 4.32/4.55          | ~ (v1_funct_2 @ X51 @ X52 @ X50)
% 4.32/4.55          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 4.32/4.55          | ((k5_relat_1 @ (k2_funct_1 @ X51) @ X51) = (k6_relat_1 @ X50))
% 4.32/4.55          | ~ (v2_funct_1 @ X51)
% 4.32/4.55          | ((k2_relset_1 @ X52 @ X50 @ X51) != (X50)))),
% 4.32/4.55      inference('demod', [status(thm)], ['166', '167'])).
% 4.32/4.55  thf('169', plain,
% 4.32/4.55      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 4.32/4.55        | ~ (v2_funct_1 @ sk_C)
% 4.32/4.55        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 4.32/4.55        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 4.32/4.55        | ~ (v1_funct_1 @ sk_C)
% 4.32/4.55        | ((sk_B) = (k1_xboole_0)))),
% 4.32/4.55      inference('sup-', [status(thm)], ['165', '168'])).
% 4.32/4.55  thf('170', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 4.32/4.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.55  thf('171', plain, ((v2_funct_1 @ sk_C)),
% 4.32/4.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.55  thf('172', plain, ((v1_funct_1 @ sk_C)),
% 4.32/4.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.55  thf('173', plain,
% 4.32/4.55      (![X9 : $i]:
% 4.32/4.55         (~ (v2_funct_1 @ X9)
% 4.32/4.55          | ((k2_funct_1 @ X9) = (k4_relat_1 @ X9))
% 4.32/4.55          | ~ (v1_funct_1 @ X9)
% 4.32/4.55          | ~ (v1_relat_1 @ X9))),
% 4.32/4.55      inference('cnf', [status(esa)], [d9_funct_1])).
% 4.32/4.55  thf('174', plain,
% 4.32/4.55      ((~ (v1_relat_1 @ sk_C)
% 4.32/4.55        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 4.32/4.55        | ~ (v2_funct_1 @ sk_C))),
% 4.32/4.55      inference('sup-', [status(thm)], ['172', '173'])).
% 4.32/4.55  thf('175', plain, ((v1_relat_1 @ sk_C)),
% 4.32/4.55      inference('sup-', [status(thm)], ['99', '100'])).
% 4.32/4.55  thf('176', plain, ((v2_funct_1 @ sk_C)),
% 4.32/4.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.55  thf('177', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 4.32/4.55      inference('demod', [status(thm)], ['174', '175', '176'])).
% 4.32/4.55  thf('178', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 4.32/4.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.55  thf('179', plain, ((v1_funct_1 @ sk_C)),
% 4.32/4.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.55  thf('180', plain,
% 4.32/4.55      ((((sk_B) != (sk_B))
% 4.32/4.55        | ((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 4.32/4.55        | ((sk_B) = (k1_xboole_0)))),
% 4.32/4.55      inference('demod', [status(thm)],
% 4.32/4.55                ['169', '170', '171', '177', '178', '179'])).
% 4.32/4.55  thf('181', plain,
% 4.32/4.55      ((((sk_B) = (k1_xboole_0))
% 4.32/4.55        | ((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B)))),
% 4.32/4.55      inference('simplify', [status(thm)], ['180'])).
% 4.32/4.55  thf('182', plain, (((sk_B) != (k1_xboole_0))),
% 4.32/4.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.55  thf('183', plain,
% 4.32/4.55      (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))),
% 4.32/4.55      inference('simplify_reflect-', [status(thm)], ['181', '182'])).
% 4.32/4.55  thf('184', plain,
% 4.32/4.55      (![X2 : $i, X3 : $i, X4 : $i]:
% 4.32/4.55         (~ (v1_relat_1 @ X2)
% 4.32/4.55          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 4.32/4.55              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 4.32/4.55          | ~ (v1_relat_1 @ X4)
% 4.32/4.55          | ~ (v1_relat_1 @ X3))),
% 4.32/4.55      inference('cnf', [status(esa)], [t55_relat_1])).
% 4.32/4.55  thf('185', plain,
% 4.32/4.55      (![X0 : $i]:
% 4.32/4.55         (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 4.32/4.55            = (k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 4.32/4.55          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 4.32/4.55          | ~ (v1_relat_1 @ X0)
% 4.32/4.55          | ~ (v1_relat_1 @ sk_C))),
% 4.32/4.55      inference('sup+', [status(thm)], ['183', '184'])).
% 4.32/4.55  thf('186', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 4.32/4.55      inference('demod', [status(thm)], ['174', '175', '176'])).
% 4.32/4.55  thf('187', plain,
% 4.32/4.55      (![X10 : $i]:
% 4.32/4.55         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 4.32/4.55          | ~ (v1_funct_1 @ X10)
% 4.32/4.55          | ~ (v1_relat_1 @ X10))),
% 4.32/4.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.32/4.55  thf('188', plain,
% 4.32/4.55      (((v1_relat_1 @ (k4_relat_1 @ sk_C))
% 4.32/4.55        | ~ (v1_relat_1 @ sk_C)
% 4.32/4.55        | ~ (v1_funct_1 @ sk_C))),
% 4.32/4.55      inference('sup+', [status(thm)], ['186', '187'])).
% 4.32/4.55  thf('189', plain, ((v1_relat_1 @ sk_C)),
% 4.32/4.55      inference('sup-', [status(thm)], ['99', '100'])).
% 4.32/4.55  thf('190', plain, ((v1_funct_1 @ sk_C)),
% 4.32/4.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.55  thf('191', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 4.32/4.55      inference('demod', [status(thm)], ['188', '189', '190'])).
% 4.32/4.55  thf('192', plain, ((v1_relat_1 @ sk_C)),
% 4.32/4.55      inference('sup-', [status(thm)], ['99', '100'])).
% 4.32/4.55  thf('193', plain,
% 4.32/4.55      (![X0 : $i]:
% 4.32/4.55         (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 4.32/4.55            = (k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 4.32/4.55          | ~ (v1_relat_1 @ X0))),
% 4.32/4.55      inference('demod', [status(thm)], ['185', '191', '192'])).
% 4.32/4.55  thf('194', plain,
% 4.32/4.55      ((((k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_D)
% 4.32/4.55          = (k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_relat_1 @ sk_A)))
% 4.32/4.55        | ~ (v1_relat_1 @ sk_D))),
% 4.32/4.55      inference('sup+', [status(thm)], ['164', '193'])).
% 4.32/4.55  thf('195', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 4.32/4.55      inference('demod', [status(thm)], ['29', '30', '31', '32', '33'])).
% 4.32/4.55  thf('196', plain,
% 4.32/4.55      (![X0 : $i, X1 : $i]:
% 4.32/4.55         (~ (v1_relat_1 @ X0)
% 4.32/4.55          | ((k5_relat_1 @ (k7_relat_1 @ X0 @ X1) @ 
% 4.32/4.55              (k6_relat_1 @ (k2_relat_1 @ X0)))
% 4.32/4.55              = (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 4.32/4.55      inference('simplify', [status(thm)], ['126'])).
% 4.32/4.55  thf('197', plain,
% 4.32/4.55      (![X0 : $i]:
% 4.32/4.55         (((k5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ (k6_relat_1 @ sk_A))
% 4.32/4.55            = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_D))
% 4.32/4.55          | ~ (v1_relat_1 @ sk_D))),
% 4.32/4.55      inference('sup+', [status(thm)], ['195', '196'])).
% 4.32/4.55  thf('198', plain, ((v1_relat_1 @ sk_D)),
% 4.32/4.55      inference('sup-', [status(thm)], ['0', '1'])).
% 4.32/4.55  thf('199', plain,
% 4.32/4.55      (![X0 : $i]:
% 4.32/4.55         ((k5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ (k6_relat_1 @ sk_A))
% 4.32/4.55           = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_D))),
% 4.32/4.55      inference('demod', [status(thm)], ['197', '198'])).
% 4.32/4.55  thf('200', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 4.32/4.55      inference('demod', [status(thm)], ['29', '30', '31', '32', '33'])).
% 4.32/4.55  thf('201', plain,
% 4.32/4.55      (![X5 : $i]:
% 4.32/4.55         (((k5_relat_1 @ X5 @ (k6_relat_1 @ (k2_relat_1 @ X5))) = (X5))
% 4.32/4.55          | ~ (v1_relat_1 @ X5))),
% 4.32/4.55      inference('cnf', [status(esa)], [t80_relat_1])).
% 4.32/4.55  thf('202', plain,
% 4.32/4.55      ((((k5_relat_1 @ sk_D @ (k6_relat_1 @ sk_A)) = (sk_D))
% 4.32/4.55        | ~ (v1_relat_1 @ sk_D))),
% 4.32/4.55      inference('sup+', [status(thm)], ['200', '201'])).
% 4.32/4.55  thf('203', plain, ((v1_relat_1 @ sk_D)),
% 4.32/4.55      inference('sup-', [status(thm)], ['0', '1'])).
% 4.32/4.55  thf('204', plain, (((k5_relat_1 @ sk_D @ (k6_relat_1 @ sk_A)) = (sk_D))),
% 4.32/4.55      inference('demod', [status(thm)], ['202', '203'])).
% 4.32/4.55  thf('205', plain,
% 4.32/4.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.32/4.55         (~ (v1_relat_1 @ X2)
% 4.32/4.55          | ~ (v1_relat_1 @ X1)
% 4.32/4.55          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 4.32/4.55              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 4.32/4.55      inference('simplify', [status(thm)], ['122'])).
% 4.32/4.55  thf('206', plain,
% 4.32/4.55      (![X6 : $i, X7 : $i]:
% 4.32/4.55         (((k7_relat_1 @ X7 @ X6) = (k5_relat_1 @ (k6_relat_1 @ X6) @ X7))
% 4.32/4.55          | ~ (v1_relat_1 @ X7))),
% 4.32/4.55      inference('cnf', [status(esa)], [t94_relat_1])).
% 4.32/4.55  thf('207', plain,
% 4.32/4.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.32/4.55         (((k7_relat_1 @ (k5_relat_1 @ X2 @ X0) @ X1)
% 4.32/4.55            = (k5_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 4.32/4.55          | ~ (v1_relat_1 @ X2)
% 4.32/4.55          | ~ (v1_relat_1 @ X0)
% 4.32/4.55          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X0)))),
% 4.32/4.55      inference('sup+', [status(thm)], ['205', '206'])).
% 4.32/4.55  thf('208', plain,
% 4.32/4.55      (![X0 : $i]:
% 4.32/4.55         (~ (v1_relat_1 @ sk_D)
% 4.32/4.55          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 4.32/4.55          | ~ (v1_relat_1 @ sk_D)
% 4.32/4.55          | ((k7_relat_1 @ (k5_relat_1 @ sk_D @ (k6_relat_1 @ sk_A)) @ X0)
% 4.32/4.55              = (k5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ (k6_relat_1 @ sk_A))))),
% 4.32/4.55      inference('sup-', [status(thm)], ['204', '207'])).
% 4.32/4.55  thf('209', plain, ((v1_relat_1 @ sk_D)),
% 4.32/4.55      inference('sup-', [status(thm)], ['0', '1'])).
% 4.32/4.55  thf('210', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 4.32/4.55      inference('sup-', [status(thm)], ['119', '120'])).
% 4.32/4.55  thf('211', plain, ((v1_relat_1 @ sk_D)),
% 4.32/4.55      inference('sup-', [status(thm)], ['0', '1'])).
% 4.32/4.55  thf('212', plain, (((k5_relat_1 @ sk_D @ (k6_relat_1 @ sk_A)) = (sk_D))),
% 4.32/4.55      inference('demod', [status(thm)], ['202', '203'])).
% 4.32/4.55  thf('213', plain,
% 4.32/4.55      (![X0 : $i]:
% 4.32/4.55         ((k7_relat_1 @ sk_D @ X0)
% 4.32/4.55           = (k5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ (k6_relat_1 @ sk_A)))),
% 4.32/4.55      inference('demod', [status(thm)], ['208', '209', '210', '211', '212'])).
% 4.32/4.55  thf('214', plain,
% 4.32/4.55      (![X0 : $i]:
% 4.32/4.55         ((k7_relat_1 @ sk_D @ X0) = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_D))),
% 4.32/4.55      inference('sup+', [status(thm)], ['199', '213'])).
% 4.32/4.55  thf('215', plain,
% 4.32/4.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.32/4.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.55  thf('216', plain,
% 4.32/4.55      (![X50 : $i, X51 : $i, X52 : $i]:
% 4.32/4.55         (((X50) = (k1_xboole_0))
% 4.32/4.55          | ~ (v1_funct_1 @ X51)
% 4.32/4.55          | ~ (v1_funct_2 @ X51 @ X52 @ X50)
% 4.32/4.55          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 4.32/4.55          | ((k5_relat_1 @ X51 @ (k2_funct_1 @ X51)) = (k6_relat_1 @ X52))
% 4.32/4.55          | ~ (v2_funct_1 @ X51)
% 4.32/4.55          | ((k2_relset_1 @ X52 @ X50 @ X51) != (X50)))),
% 4.32/4.55      inference('demod', [status(thm)], ['6', '7'])).
% 4.32/4.55  thf('217', plain,
% 4.32/4.55      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 4.32/4.55        | ~ (v2_funct_1 @ sk_C)
% 4.32/4.55        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 4.32/4.55        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 4.32/4.55        | ~ (v1_funct_1 @ sk_C)
% 4.32/4.55        | ((sk_B) = (k1_xboole_0)))),
% 4.32/4.55      inference('sup-', [status(thm)], ['215', '216'])).
% 4.32/4.55  thf('218', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 4.32/4.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.55  thf('219', plain, ((v2_funct_1 @ sk_C)),
% 4.32/4.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.55  thf('220', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 4.32/4.55      inference('demod', [status(thm)], ['174', '175', '176'])).
% 4.32/4.55  thf('221', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 4.32/4.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.55  thf('222', plain, ((v1_funct_1 @ sk_C)),
% 4.32/4.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.55  thf('223', plain,
% 4.32/4.55      ((((sk_B) != (sk_B))
% 4.32/4.55        | ((k5_relat_1 @ sk_C @ (k4_relat_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 4.32/4.55        | ((sk_B) = (k1_xboole_0)))),
% 4.32/4.55      inference('demod', [status(thm)],
% 4.32/4.55                ['217', '218', '219', '220', '221', '222'])).
% 4.32/4.55  thf('224', plain,
% 4.32/4.55      ((((sk_B) = (k1_xboole_0))
% 4.32/4.55        | ((k5_relat_1 @ sk_C @ (k4_relat_1 @ sk_C)) = (k6_relat_1 @ sk_A)))),
% 4.32/4.55      inference('simplify', [status(thm)], ['223'])).
% 4.32/4.55  thf('225', plain, (((sk_B) != (k1_xboole_0))),
% 4.32/4.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.55  thf('226', plain,
% 4.32/4.55      (((k5_relat_1 @ sk_C @ (k4_relat_1 @ sk_C)) = (k6_relat_1 @ sk_A))),
% 4.32/4.55      inference('simplify_reflect-', [status(thm)], ['224', '225'])).
% 4.32/4.55  thf('227', plain,
% 4.32/4.55      (![X0 : $i]:
% 4.32/4.55         (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 4.32/4.55            = (k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 4.32/4.55          | ~ (v1_relat_1 @ X0))),
% 4.32/4.55      inference('demod', [status(thm)], ['185', '191', '192'])).
% 4.32/4.55  thf('228', plain,
% 4.32/4.55      ((((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k4_relat_1 @ sk_C))
% 4.32/4.55          = (k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_relat_1 @ sk_A)))
% 4.32/4.55        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 4.32/4.55      inference('sup+', [status(thm)], ['226', '227'])).
% 4.32/4.55  thf('229', plain, ((v1_relat_1 @ sk_C)),
% 4.32/4.55      inference('sup-', [status(thm)], ['99', '100'])).
% 4.32/4.55  thf('230', plain,
% 4.32/4.55      (![X1 : $i]:
% 4.32/4.55         (((k2_relat_1 @ X1) = (k1_relat_1 @ (k4_relat_1 @ X1)))
% 4.32/4.55          | ~ (v1_relat_1 @ X1))),
% 4.32/4.55      inference('cnf', [status(esa)], [t37_relat_1])).
% 4.32/4.55  thf('231', plain,
% 4.32/4.55      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 4.32/4.55      inference('sup-', [status(thm)], ['229', '230'])).
% 4.32/4.55  thf('232', plain,
% 4.32/4.55      (![X8 : $i]:
% 4.32/4.55         (((k7_relat_1 @ X8 @ (k1_relat_1 @ X8)) = (X8)) | ~ (v1_relat_1 @ X8))),
% 4.32/4.55      inference('cnf', [status(esa)], [t98_relat_1])).
% 4.32/4.55  thf('233', plain,
% 4.32/4.55      ((((k7_relat_1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 4.32/4.55          = (k4_relat_1 @ sk_C))
% 4.32/4.55        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 4.32/4.55      inference('sup+', [status(thm)], ['231', '232'])).
% 4.32/4.55  thf('234', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 4.32/4.55      inference('demod', [status(thm)], ['188', '189', '190'])).
% 4.32/4.55  thf('235', plain,
% 4.32/4.55      (((k7_relat_1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 4.32/4.55         = (k4_relat_1 @ sk_C))),
% 4.32/4.55      inference('demod', [status(thm)], ['233', '234'])).
% 4.32/4.55  thf('236', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 4.32/4.55      inference('sup+', [status(thm)], ['145', '146'])).
% 4.32/4.55  thf('237', plain,
% 4.32/4.55      (((k7_relat_1 @ (k4_relat_1 @ sk_C) @ sk_B) = (k4_relat_1 @ sk_C))),
% 4.32/4.55      inference('demod', [status(thm)], ['235', '236'])).
% 4.32/4.55  thf('238', plain,
% 4.32/4.55      (![X0 : $i, X1 : $i]:
% 4.32/4.55         (~ (v1_relat_1 @ X0)
% 4.32/4.55          | ((k5_relat_1 @ (k7_relat_1 @ X0 @ X1) @ 
% 4.32/4.55              (k6_relat_1 @ (k2_relat_1 @ X0)))
% 4.32/4.55              = (k5_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 4.32/4.55      inference('simplify', [status(thm)], ['126'])).
% 4.32/4.55  thf('239', plain,
% 4.32/4.55      ((((k5_relat_1 @ (k4_relat_1 @ sk_C) @ 
% 4.32/4.55          (k6_relat_1 @ (k2_relat_1 @ (k4_relat_1 @ sk_C))))
% 4.32/4.55          = (k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k4_relat_1 @ sk_C)))
% 4.32/4.55        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 4.32/4.55      inference('sup+', [status(thm)], ['237', '238'])).
% 4.32/4.55  thf('240', plain, ((v1_relat_1 @ sk_C)),
% 4.32/4.55      inference('sup-', [status(thm)], ['99', '100'])).
% 4.32/4.55  thf('241', plain,
% 4.32/4.55      (![X1 : $i]:
% 4.32/4.55         (((k1_relat_1 @ X1) = (k2_relat_1 @ (k4_relat_1 @ X1)))
% 4.32/4.55          | ~ (v1_relat_1 @ X1))),
% 4.32/4.55      inference('cnf', [status(esa)], [t37_relat_1])).
% 4.32/4.55  thf('242', plain,
% 4.32/4.55      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 4.32/4.55      inference('sup-', [status(thm)], ['240', '241'])).
% 4.32/4.55  thf('243', plain,
% 4.32/4.55      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 4.32/4.55      inference('sup-', [status(thm)], ['240', '241'])).
% 4.32/4.55  thf('244', plain,
% 4.32/4.55      (![X5 : $i]:
% 4.32/4.55         (((k5_relat_1 @ X5 @ (k6_relat_1 @ (k2_relat_1 @ X5))) = (X5))
% 4.32/4.55          | ~ (v1_relat_1 @ X5))),
% 4.32/4.55      inference('cnf', [status(esa)], [t80_relat_1])).
% 4.32/4.55  thf('245', plain,
% 4.32/4.55      ((((k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_relat_1 @ (k1_relat_1 @ sk_C)))
% 4.32/4.55          = (k4_relat_1 @ sk_C))
% 4.32/4.55        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 4.32/4.55      inference('sup+', [status(thm)], ['243', '244'])).
% 4.32/4.55  thf('246', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 4.32/4.55      inference('demod', [status(thm)], ['188', '189', '190'])).
% 4.32/4.55  thf('247', plain,
% 4.32/4.55      (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_relat_1 @ (k1_relat_1 @ sk_C)))
% 4.32/4.55         = (k4_relat_1 @ sk_C))),
% 4.32/4.55      inference('demod', [status(thm)], ['245', '246'])).
% 4.32/4.55  thf('248', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 4.32/4.55      inference('demod', [status(thm)], ['188', '189', '190'])).
% 4.32/4.55  thf('249', plain,
% 4.32/4.55      (((k4_relat_1 @ sk_C)
% 4.32/4.55         = (k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k4_relat_1 @ sk_C)))),
% 4.32/4.55      inference('demod', [status(thm)], ['239', '242', '247', '248'])).
% 4.32/4.55  thf('250', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 4.32/4.55      inference('demod', [status(thm)], ['188', '189', '190'])).
% 4.32/4.55  thf('251', plain,
% 4.32/4.55      (((k4_relat_1 @ sk_C)
% 4.32/4.55         = (k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_relat_1 @ sk_A)))),
% 4.32/4.55      inference('demod', [status(thm)], ['228', '249', '250'])).
% 4.32/4.55  thf('252', plain, ((v1_relat_1 @ sk_D)),
% 4.32/4.55      inference('sup-', [status(thm)], ['0', '1'])).
% 4.32/4.55  thf('253', plain, (((k7_relat_1 @ sk_D @ sk_B) = (k4_relat_1 @ sk_C))),
% 4.32/4.55      inference('demod', [status(thm)], ['194', '214', '251', '252'])).
% 4.32/4.55  thf('254', plain, ((v1_relat_1 @ sk_D)),
% 4.32/4.55      inference('sup-', [status(thm)], ['0', '1'])).
% 4.32/4.55  thf('255', plain, (((k4_relat_1 @ sk_C) = (sk_D))),
% 4.32/4.55      inference('demod', [status(thm)], ['163', '253', '254'])).
% 4.32/4.55  thf('256', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 4.32/4.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.32/4.55  thf('257', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 4.32/4.55      inference('demod', [status(thm)], ['174', '175', '176'])).
% 4.32/4.55  thf('258', plain, (((sk_D) != (k4_relat_1 @ sk_C))),
% 4.32/4.55      inference('demod', [status(thm)], ['256', '257'])).
% 4.32/4.55  thf('259', plain, ($false),
% 4.32/4.55      inference('simplify_reflect-', [status(thm)], ['255', '258'])).
% 4.32/4.55  
% 4.32/4.55  % SZS output end Refutation
% 4.32/4.55  
% 4.32/4.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

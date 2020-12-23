%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lNdPVvBqLa

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:02 EST 2020

% Result     : Theorem 9.52s
% Output     : Refutation 9.52s
% Verified   : 
% Statistics : Number of formulae       :  193 ( 936 expanded)
%              Number of leaves         :   51 ( 305 expanded)
%              Depth                    :   13
%              Number of atoms          : 1458 (20106 expanded)
%              Number of equality atoms :  121 ( 453 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t87_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( v3_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ ( k6_partfun1 @ A ) )
           => ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( v3_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ A )
              & ( v3_funct_2 @ C @ A @ A )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ ( k6_partfun1 @ A ) )
             => ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k2_funct_2 @ A @ B )
        = ( k2_funct_1 @ B ) ) ) )).

thf('2',plain,(
    ! [X60: $i,X61: $i] :
      ( ( ( k2_funct_2 @ X61 @ X60 )
        = ( k2_funct_1 @ X60 ) )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X61 @ X61 ) ) )
      | ~ ( v3_funct_2 @ X60 @ X61 @ X61 )
      | ~ ( v1_funct_2 @ X60 @ X61 @ X61 )
      | ~ ( v1_funct_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B )
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('8',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('9',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C_1 ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_funct_2,axiom,(
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

thf('11',plain,(
    ! [X67: $i,X68: $i,X69: $i,X70: $i] :
      ( ~ ( v1_funct_1 @ X67 )
      | ~ ( v1_funct_2 @ X67 @ X68 @ X69 )
      | ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X68 @ X69 ) ) )
      | ( X67
        = ( k2_funct_1 @ X70 ) )
      | ~ ( r2_relset_1 @ X69 @ X69 @ ( k1_partfun1 @ X69 @ X68 @ X68 @ X69 @ X70 @ X67 ) @ ( k6_partfun1 @ X69 ) )
      | ( X68 = k1_xboole_0 )
      | ( X69 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X70 )
      | ( ( k2_relset_1 @ X69 @ X68 @ X70 )
       != X68 )
      | ~ ( m1_subset_1 @ X70 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X69 @ X68 ) ) )
      | ~ ( v1_funct_2 @ X70 @ X69 @ X68 )
      | ~ ( v1_funct_1 @ X70 ) ) ),
    inference(cnf,[status(esa)],[t36_funct_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C_1 ) @ ( k6_partfun1 @ sk_A ) )
      | ( sk_C_1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C_1 ) @ ( k6_partfun1 @ sk_A ) )
      | ( sk_C_1
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( sk_C_1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C_1 ) @ ( k6_partfun1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C_1
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('22',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( ( k2_relset_1 @ X41 @ X42 @ X40 )
        = ( k2_relat_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('23',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) ) ) ) )).

thf('25',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( v1_funct_1 @ X47 )
      | ~ ( v3_funct_2 @ X47 @ X48 @ X49 )
      | ( v2_funct_2 @ X47 @ X49 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('26',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['26','27','28'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('30',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( v2_funct_2 @ X51 @ X50 )
      | ( ( k2_relat_1 @ X51 )
        = X50 )
      | ~ ( v5_relat_1 @ X51 @ X50 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('33',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v1_relat_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('36',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v5_relat_1 @ X34 @ X36 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('37',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['31','34','37'])).

thf('39',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['23','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( v1_funct_1 @ X47 )
      | ~ ( v3_funct_2 @ X47 @ X48 @ X49 )
      | ( v2_funct_1 @ X47 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('42',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ( sk_A != sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C_1
      = ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','19','20','39','45'])).

thf('47',plain,
    ( ( sk_C_1
      = ( k2_funct_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('49',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('51',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ( r2_relset_1 @ X44 @ X45 @ X43 @ X46 )
      | ( X43 != X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('52',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( r2_relset_1 @ X44 @ X45 @ X46 @ X46 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','53'])).

thf('55',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','53'])).

thf('56',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('58',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('59',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('60',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('61',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ X6 )
      | ( X5 = X6 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('63',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('64',plain,(
    ! [X62: $i] :
      ( ( k6_partfun1 @ X62 )
      = ( k6_relat_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('65',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['63','64'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('66',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('67',plain,(
    ! [X62: $i] :
      ( ( k6_partfun1 @ X62 )
      = ( k6_relat_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('68',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X18 ) )
      = X18 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['65','68'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('70',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X21 @ ( k1_relat_1 @ X22 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X22 @ X21 ) )
        = X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ k1_xboole_0 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['63','64'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('73',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('74',plain,(
    ! [X62: $i] :
      ( ( k6_partfun1 @ X62 )
      = ( k6_relat_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('75',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X23 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['72','75'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('77',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('78',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('79',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v4_relat_1 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('81',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('82',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X16
        = ( k7_relat_1 @ X16 @ X17 ) )
      | ~ ( v4_relat_1 @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['72','75'])).

thf('85',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['65','68'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference(demod,[status(thm)],['71','76','85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X1 ) ) ),
    inference('sup-',[status(thm)],['62','87'])).

thf('89',plain,
    ( ( k1_xboole_0 = sk_C_1 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','88'])).

thf('90',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','53'])).

thf('91',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','53'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('92',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('93',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('95',plain,(
    k1_xboole_0 = sk_C_1 ),
    inference(demod,[status(thm)],['89','90','91','93','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('98',plain,(
    r1_tarski @ sk_B @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X1 ) ) ),
    inference('sup-',[status(thm)],['62','87'])).

thf('100',plain,
    ( ( k1_xboole_0 = sk_B )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','53'])).

thf('102',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','53'])).

thf('103',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['92'])).

thf('104',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('105',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['100','101','102','103','104'])).

thf('106',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['63','64'])).

thf('107',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X18 ) )
      = X18 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('108',plain,(
    ! [X20: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X20 ) ) @ X20 )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('109',plain,(
    ! [X62: $i] :
      ( ( k6_partfun1 @ X62 )
      = ( k6_relat_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('110',plain,(
    ! [X20: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X20 ) ) @ X20 )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['107','110'])).

thf('112',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X23 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf(t64_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) )
              & ( ( k5_relat_1 @ B @ A )
                = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('114',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ~ ( v1_funct_1 @ X27 )
      | ( X27
        = ( k2_funct_1 @ X28 ) )
      | ( ( k5_relat_1 @ X27 @ X28 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X28 ) ) )
      | ( ( k2_relat_1 @ X27 )
       != ( k1_relat_1 @ X28 ) )
      | ~ ( v2_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('115',plain,(
    ! [X62: $i] :
      ( ( k6_partfun1 @ X62 )
      = ( k6_relat_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('116',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ~ ( v1_funct_1 @ X27 )
      | ( X27
        = ( k2_funct_1 @ X28 ) )
      | ( ( k5_relat_1 @ X27 @ X28 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X28 ) ) )
      | ( ( k2_relat_1 @ X27 )
       != ( k1_relat_1 @ X28 ) )
      | ~ ( v2_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ X0 )
       != ( k6_partfun1 @ ( k2_relat_1 @ ( k6_partfun1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k6_partfun1 @ X0 ) )
       != ( k1_relat_1 @ ( k6_partfun1 @ X0 ) ) )
      | ( ( k6_partfun1 @ X0 )
        = ( k2_funct_1 @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['113','116'])).

thf('118',plain,(
    ! [X19: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('119',plain,(
    ! [X62: $i] :
      ( ( k6_partfun1 @ X62 )
      = ( k6_relat_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('120',plain,(
    ! [X19: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X23 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('122',plain,(
    ! [X24: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('123',plain,(
    ! [X62: $i] :
      ( ( k6_partfun1 @ X62 )
      = ( k6_relat_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('124',plain,(
    ! [X24: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X24 ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('125',plain,(
    ! [X26: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('126',plain,(
    ! [X62: $i] :
      ( ( k6_partfun1 @ X62 )
      = ( k6_relat_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('127',plain,(
    ! [X26: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X26 ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X19: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('129',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X18 ) )
      = X18 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('130',plain,(
    ! [X24: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X24 ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('131',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X23 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ X0 )
       != ( k6_partfun1 @ X0 ) )
      | ( X0 != X0 )
      | ( ( k6_partfun1 @ X0 )
        = ( k2_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['117','120','121','124','127','128','129','130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( k6_partfun1 @ X0 )
      = ( k2_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = ( k2_funct_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['106','133'])).

thf('135',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['63','64'])).

thf('136',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('138',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( r2_relset_1 @ X44 @ X45 @ X46 @ X46 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    $false ),
    inference(demod,[status(thm)],['56','95','105','136','139'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lNdPVvBqLa
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:28:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 9.52/9.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 9.52/9.72  % Solved by: fo/fo7.sh
% 9.52/9.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.52/9.72  % done 11210 iterations in 9.275s
% 9.52/9.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 9.52/9.72  % SZS output start Refutation
% 9.52/9.72  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 9.52/9.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 9.52/9.72  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 9.52/9.72  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 9.52/9.72  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 9.52/9.72  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 9.52/9.72  thf(sk_B_type, type, sk_B: $i).
% 9.52/9.72  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 9.52/9.72  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 9.52/9.72  thf(sk_C_1_type, type, sk_C_1: $i).
% 9.52/9.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 9.52/9.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 9.52/9.72  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 9.52/9.72  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 9.52/9.72  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 9.52/9.72  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 9.52/9.72  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 9.52/9.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 9.52/9.72  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 9.52/9.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 9.52/9.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 9.52/9.72  thf(sk_A_type, type, sk_A: $i).
% 9.52/9.72  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 9.52/9.72  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 9.52/9.72  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 9.52/9.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 9.52/9.72  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 9.52/9.72  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 9.52/9.72  thf(t87_funct_2, conjecture,
% 9.52/9.72    (![A:$i,B:$i]:
% 9.52/9.72     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 9.52/9.72         ( v3_funct_2 @ B @ A @ A ) & 
% 9.52/9.72         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 9.52/9.72       ( ![C:$i]:
% 9.52/9.72         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 9.52/9.72             ( v3_funct_2 @ C @ A @ A ) & 
% 9.52/9.72             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 9.52/9.72           ( ( r2_relset_1 @
% 9.52/9.72               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 9.52/9.72               ( k6_partfun1 @ A ) ) =>
% 9.52/9.72             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 9.52/9.72  thf(zf_stmt_0, negated_conjecture,
% 9.52/9.72    (~( ![A:$i,B:$i]:
% 9.52/9.72        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 9.52/9.72            ( v3_funct_2 @ B @ A @ A ) & 
% 9.52/9.72            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 9.52/9.72          ( ![C:$i]:
% 9.52/9.72            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 9.52/9.72                ( v3_funct_2 @ C @ A @ A ) & 
% 9.52/9.72                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 9.52/9.72              ( ( r2_relset_1 @
% 9.52/9.72                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 9.52/9.72                  ( k6_partfun1 @ A ) ) =>
% 9.52/9.72                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 9.52/9.72    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 9.52/9.72  thf('0', plain,
% 9.52/9.72      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 9.52/9.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.52/9.72  thf('1', plain,
% 9.52/9.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.52/9.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.52/9.72  thf(redefinition_k2_funct_2, axiom,
% 9.52/9.72    (![A:$i,B:$i]:
% 9.52/9.72     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 9.52/9.72         ( v3_funct_2 @ B @ A @ A ) & 
% 9.52/9.72         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 9.52/9.72       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 9.52/9.72  thf('2', plain,
% 9.52/9.72      (![X60 : $i, X61 : $i]:
% 9.52/9.72         (((k2_funct_2 @ X61 @ X60) = (k2_funct_1 @ X60))
% 9.52/9.72          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X61 @ X61)))
% 9.52/9.72          | ~ (v3_funct_2 @ X60 @ X61 @ X61)
% 9.52/9.72          | ~ (v1_funct_2 @ X60 @ X61 @ X61)
% 9.52/9.72          | ~ (v1_funct_1 @ X60))),
% 9.52/9.72      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 9.52/9.72  thf('3', plain,
% 9.52/9.72      ((~ (v1_funct_1 @ sk_B)
% 9.52/9.72        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 9.52/9.72        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 9.52/9.72        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 9.52/9.72      inference('sup-', [status(thm)], ['1', '2'])).
% 9.52/9.72  thf('4', plain, ((v1_funct_1 @ sk_B)),
% 9.52/9.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.52/9.72  thf('5', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 9.52/9.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.52/9.72  thf('6', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 9.52/9.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.52/9.72  thf('7', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 9.52/9.72      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 9.52/9.72  thf('8', plain,
% 9.52/9.72      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ (k2_funct_1 @ sk_B))),
% 9.52/9.72      inference('demod', [status(thm)], ['0', '7'])).
% 9.52/9.72  thf('9', plain,
% 9.52/9.72      ((r2_relset_1 @ sk_A @ sk_A @ 
% 9.52/9.72        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C_1) @ 
% 9.52/9.72        (k6_partfun1 @ sk_A))),
% 9.52/9.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.52/9.72  thf('10', plain,
% 9.52/9.72      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.52/9.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.52/9.72  thf(t36_funct_2, axiom,
% 9.52/9.72    (![A:$i,B:$i,C:$i]:
% 9.52/9.72     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 9.52/9.72         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 9.52/9.72       ( ![D:$i]:
% 9.52/9.72         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 9.52/9.72             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 9.52/9.72           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 9.52/9.72               ( r2_relset_1 @
% 9.52/9.72                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 9.52/9.72                 ( k6_partfun1 @ A ) ) & 
% 9.52/9.72               ( v2_funct_1 @ C ) ) =>
% 9.52/9.72             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 9.52/9.72               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 9.52/9.72  thf('11', plain,
% 9.52/9.72      (![X67 : $i, X68 : $i, X69 : $i, X70 : $i]:
% 9.52/9.72         (~ (v1_funct_1 @ X67)
% 9.52/9.72          | ~ (v1_funct_2 @ X67 @ X68 @ X69)
% 9.52/9.72          | ~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X68 @ X69)))
% 9.52/9.72          | ((X67) = (k2_funct_1 @ X70))
% 9.52/9.72          | ~ (r2_relset_1 @ X69 @ X69 @ 
% 9.52/9.72               (k1_partfun1 @ X69 @ X68 @ X68 @ X69 @ X70 @ X67) @ 
% 9.52/9.72               (k6_partfun1 @ X69))
% 9.52/9.72          | ((X68) = (k1_xboole_0))
% 9.52/9.72          | ((X69) = (k1_xboole_0))
% 9.52/9.72          | ~ (v2_funct_1 @ X70)
% 9.52/9.72          | ((k2_relset_1 @ X69 @ X68 @ X70) != (X68))
% 9.52/9.72          | ~ (m1_subset_1 @ X70 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X69 @ X68)))
% 9.52/9.72          | ~ (v1_funct_2 @ X70 @ X69 @ X68)
% 9.52/9.72          | ~ (v1_funct_1 @ X70))),
% 9.52/9.72      inference('cnf', [status(esa)], [t36_funct_2])).
% 9.52/9.72  thf('12', plain,
% 9.52/9.72      (![X0 : $i]:
% 9.52/9.72         (~ (v1_funct_1 @ X0)
% 9.52/9.72          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 9.52/9.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 9.52/9.72          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 9.52/9.72          | ~ (v2_funct_1 @ X0)
% 9.52/9.72          | ((sk_A) = (k1_xboole_0))
% 9.52/9.72          | ((sk_A) = (k1_xboole_0))
% 9.52/9.72          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 9.52/9.72               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C_1) @ 
% 9.52/9.72               (k6_partfun1 @ sk_A))
% 9.52/9.72          | ((sk_C_1) = (k2_funct_1 @ X0))
% 9.52/9.72          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_A)
% 9.52/9.72          | ~ (v1_funct_1 @ sk_C_1))),
% 9.52/9.72      inference('sup-', [status(thm)], ['10', '11'])).
% 9.52/9.72  thf('13', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_A)),
% 9.52/9.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.52/9.72  thf('14', plain, ((v1_funct_1 @ sk_C_1)),
% 9.52/9.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.52/9.72  thf('15', plain,
% 9.52/9.72      (![X0 : $i]:
% 9.52/9.72         (~ (v1_funct_1 @ X0)
% 9.52/9.72          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 9.52/9.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 9.52/9.72          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 9.52/9.72          | ~ (v2_funct_1 @ X0)
% 9.52/9.72          | ((sk_A) = (k1_xboole_0))
% 9.52/9.72          | ((sk_A) = (k1_xboole_0))
% 9.52/9.72          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 9.52/9.72               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C_1) @ 
% 9.52/9.72               (k6_partfun1 @ sk_A))
% 9.52/9.72          | ((sk_C_1) = (k2_funct_1 @ X0)))),
% 9.52/9.72      inference('demod', [status(thm)], ['12', '13', '14'])).
% 9.52/9.72  thf('16', plain,
% 9.52/9.72      (![X0 : $i]:
% 9.52/9.72         (((sk_C_1) = (k2_funct_1 @ X0))
% 9.52/9.72          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 9.52/9.72               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C_1) @ 
% 9.52/9.72               (k6_partfun1 @ sk_A))
% 9.52/9.72          | ((sk_A) = (k1_xboole_0))
% 9.52/9.72          | ~ (v2_funct_1 @ X0)
% 9.52/9.72          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 9.52/9.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 9.52/9.72          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 9.52/9.72          | ~ (v1_funct_1 @ X0))),
% 9.52/9.72      inference('simplify', [status(thm)], ['15'])).
% 9.52/9.72  thf('17', plain,
% 9.52/9.72      ((~ (v1_funct_1 @ sk_B)
% 9.52/9.72        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 9.52/9.72        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 9.52/9.72        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 9.52/9.72        | ~ (v2_funct_1 @ sk_B)
% 9.52/9.72        | ((sk_A) = (k1_xboole_0))
% 9.52/9.72        | ((sk_C_1) = (k2_funct_1 @ sk_B)))),
% 9.52/9.72      inference('sup-', [status(thm)], ['9', '16'])).
% 9.52/9.72  thf('18', plain, ((v1_funct_1 @ sk_B)),
% 9.52/9.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.52/9.72  thf('19', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 9.52/9.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.52/9.72  thf('20', plain,
% 9.52/9.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.52/9.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.52/9.72  thf('21', plain,
% 9.52/9.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.52/9.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.52/9.72  thf(redefinition_k2_relset_1, axiom,
% 9.52/9.72    (![A:$i,B:$i,C:$i]:
% 9.52/9.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.52/9.72       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 9.52/9.72  thf('22', plain,
% 9.52/9.72      (![X40 : $i, X41 : $i, X42 : $i]:
% 9.52/9.72         (((k2_relset_1 @ X41 @ X42 @ X40) = (k2_relat_1 @ X40))
% 9.52/9.72          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 9.52/9.72      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 9.52/9.72  thf('23', plain,
% 9.52/9.72      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 9.52/9.72      inference('sup-', [status(thm)], ['21', '22'])).
% 9.52/9.72  thf('24', plain,
% 9.52/9.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.52/9.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.52/9.72  thf(cc2_funct_2, axiom,
% 9.52/9.72    (![A:$i,B:$i,C:$i]:
% 9.52/9.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.52/9.72       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 9.52/9.72         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 9.52/9.72  thf('25', plain,
% 9.52/9.72      (![X47 : $i, X48 : $i, X49 : $i]:
% 9.52/9.72         (~ (v1_funct_1 @ X47)
% 9.52/9.72          | ~ (v3_funct_2 @ X47 @ X48 @ X49)
% 9.52/9.72          | (v2_funct_2 @ X47 @ X49)
% 9.52/9.72          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49))))),
% 9.52/9.72      inference('cnf', [status(esa)], [cc2_funct_2])).
% 9.52/9.72  thf('26', plain,
% 9.52/9.72      (((v2_funct_2 @ sk_B @ sk_A)
% 9.52/9.72        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 9.52/9.72        | ~ (v1_funct_1 @ sk_B))),
% 9.52/9.72      inference('sup-', [status(thm)], ['24', '25'])).
% 9.52/9.72  thf('27', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 9.52/9.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.52/9.72  thf('28', plain, ((v1_funct_1 @ sk_B)),
% 9.52/9.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.52/9.72  thf('29', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 9.52/9.72      inference('demod', [status(thm)], ['26', '27', '28'])).
% 9.52/9.72  thf(d3_funct_2, axiom,
% 9.52/9.72    (![A:$i,B:$i]:
% 9.52/9.72     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 9.52/9.72       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 9.52/9.72  thf('30', plain,
% 9.52/9.72      (![X50 : $i, X51 : $i]:
% 9.52/9.72         (~ (v2_funct_2 @ X51 @ X50)
% 9.52/9.72          | ((k2_relat_1 @ X51) = (X50))
% 9.52/9.72          | ~ (v5_relat_1 @ X51 @ X50)
% 9.52/9.72          | ~ (v1_relat_1 @ X51))),
% 9.52/9.72      inference('cnf', [status(esa)], [d3_funct_2])).
% 9.52/9.72  thf('31', plain,
% 9.52/9.72      ((~ (v1_relat_1 @ sk_B)
% 9.52/9.72        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 9.52/9.72        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 9.52/9.72      inference('sup-', [status(thm)], ['29', '30'])).
% 9.52/9.72  thf('32', plain,
% 9.52/9.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.52/9.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.52/9.72  thf(cc1_relset_1, axiom,
% 9.52/9.72    (![A:$i,B:$i,C:$i]:
% 9.52/9.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.52/9.72       ( v1_relat_1 @ C ) ))).
% 9.52/9.72  thf('33', plain,
% 9.52/9.72      (![X31 : $i, X32 : $i, X33 : $i]:
% 9.52/9.72         ((v1_relat_1 @ X31)
% 9.52/9.72          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 9.52/9.72      inference('cnf', [status(esa)], [cc1_relset_1])).
% 9.52/9.72  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 9.52/9.72      inference('sup-', [status(thm)], ['32', '33'])).
% 9.52/9.72  thf('35', plain,
% 9.52/9.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.52/9.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.52/9.72  thf(cc2_relset_1, axiom,
% 9.52/9.72    (![A:$i,B:$i,C:$i]:
% 9.52/9.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.52/9.72       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 9.52/9.72  thf('36', plain,
% 9.52/9.72      (![X34 : $i, X35 : $i, X36 : $i]:
% 9.52/9.72         ((v5_relat_1 @ X34 @ X36)
% 9.52/9.72          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 9.52/9.72      inference('cnf', [status(esa)], [cc2_relset_1])).
% 9.52/9.72  thf('37', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 9.52/9.72      inference('sup-', [status(thm)], ['35', '36'])).
% 9.52/9.72  thf('38', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 9.52/9.72      inference('demod', [status(thm)], ['31', '34', '37'])).
% 9.52/9.72  thf('39', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 9.52/9.72      inference('demod', [status(thm)], ['23', '38'])).
% 9.52/9.72  thf('40', plain,
% 9.52/9.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.52/9.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.52/9.72  thf('41', plain,
% 9.52/9.72      (![X47 : $i, X48 : $i, X49 : $i]:
% 9.52/9.72         (~ (v1_funct_1 @ X47)
% 9.52/9.72          | ~ (v3_funct_2 @ X47 @ X48 @ X49)
% 9.52/9.72          | (v2_funct_1 @ X47)
% 9.52/9.72          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49))))),
% 9.52/9.72      inference('cnf', [status(esa)], [cc2_funct_2])).
% 9.52/9.72  thf('42', plain,
% 9.52/9.72      (((v2_funct_1 @ sk_B)
% 9.52/9.72        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 9.52/9.72        | ~ (v1_funct_1 @ sk_B))),
% 9.52/9.72      inference('sup-', [status(thm)], ['40', '41'])).
% 9.52/9.72  thf('43', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 9.52/9.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.52/9.72  thf('44', plain, ((v1_funct_1 @ sk_B)),
% 9.52/9.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.52/9.72  thf('45', plain, ((v2_funct_1 @ sk_B)),
% 9.52/9.72      inference('demod', [status(thm)], ['42', '43', '44'])).
% 9.52/9.72  thf('46', plain,
% 9.52/9.72      ((((sk_A) != (sk_A))
% 9.52/9.72        | ((sk_A) = (k1_xboole_0))
% 9.52/9.72        | ((sk_C_1) = (k2_funct_1 @ sk_B)))),
% 9.52/9.72      inference('demod', [status(thm)], ['17', '18', '19', '20', '39', '45'])).
% 9.52/9.72  thf('47', plain,
% 9.52/9.72      ((((sk_C_1) = (k2_funct_1 @ sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 9.52/9.72      inference('simplify', [status(thm)], ['46'])).
% 9.52/9.72  thf('48', plain,
% 9.52/9.72      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ (k2_funct_1 @ sk_B))),
% 9.52/9.72      inference('demod', [status(thm)], ['0', '7'])).
% 9.52/9.72  thf('49', plain,
% 9.52/9.72      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_C_1)
% 9.52/9.72        | ((sk_A) = (k1_xboole_0)))),
% 9.52/9.72      inference('sup-', [status(thm)], ['47', '48'])).
% 9.52/9.72  thf('50', plain,
% 9.52/9.72      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.52/9.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.52/9.72  thf(redefinition_r2_relset_1, axiom,
% 9.52/9.72    (![A:$i,B:$i,C:$i,D:$i]:
% 9.52/9.72     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 9.52/9.72         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 9.52/9.72       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 9.52/9.72  thf('51', plain,
% 9.52/9.72      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 9.52/9.72         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 9.52/9.72          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 9.52/9.72          | (r2_relset_1 @ X44 @ X45 @ X43 @ X46)
% 9.52/9.72          | ((X43) != (X46)))),
% 9.52/9.72      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 9.52/9.72  thf('52', plain,
% 9.52/9.72      (![X44 : $i, X45 : $i, X46 : $i]:
% 9.52/9.72         ((r2_relset_1 @ X44 @ X45 @ X46 @ X46)
% 9.52/9.72          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45))))),
% 9.52/9.72      inference('simplify', [status(thm)], ['51'])).
% 9.52/9.72  thf('53', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_C_1)),
% 9.52/9.72      inference('sup-', [status(thm)], ['50', '52'])).
% 9.52/9.72  thf('54', plain, (((sk_A) = (k1_xboole_0))),
% 9.52/9.72      inference('demod', [status(thm)], ['49', '53'])).
% 9.52/9.72  thf('55', plain, (((sk_A) = (k1_xboole_0))),
% 9.52/9.72      inference('demod', [status(thm)], ['49', '53'])).
% 9.52/9.72  thf('56', plain,
% 9.52/9.72      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 @ 
% 9.52/9.72          (k2_funct_1 @ sk_B))),
% 9.52/9.72      inference('demod', [status(thm)], ['8', '54', '55'])).
% 9.52/9.72  thf('57', plain,
% 9.52/9.72      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.52/9.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.52/9.72  thf(t3_subset, axiom,
% 9.52/9.72    (![A:$i,B:$i]:
% 9.52/9.72     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 9.52/9.72  thf('58', plain,
% 9.52/9.72      (![X13 : $i, X14 : $i]:
% 9.52/9.72         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 9.52/9.72      inference('cnf', [status(esa)], [t3_subset])).
% 9.52/9.72  thf('59', plain, ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 9.52/9.72      inference('sup-', [status(thm)], ['57', '58'])).
% 9.52/9.72  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 9.52/9.72  thf('60', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 9.52/9.72      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 9.52/9.72  thf(t8_boole, axiom,
% 9.52/9.72    (![A:$i,B:$i]:
% 9.52/9.72     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 9.52/9.72  thf('61', plain,
% 9.52/9.72      (![X5 : $i, X6 : $i]:
% 9.52/9.72         (~ (v1_xboole_0 @ X5) | ~ (v1_xboole_0 @ X6) | ((X5) = (X6)))),
% 9.52/9.72      inference('cnf', [status(esa)], [t8_boole])).
% 9.52/9.72  thf('62', plain,
% 9.52/9.72      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 9.52/9.73      inference('sup-', [status(thm)], ['60', '61'])).
% 9.52/9.73  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 9.52/9.73  thf('63', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 9.52/9.73      inference('cnf', [status(esa)], [t81_relat_1])).
% 9.52/9.73  thf(redefinition_k6_partfun1, axiom,
% 9.52/9.73    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 9.52/9.73  thf('64', plain, (![X62 : $i]: ((k6_partfun1 @ X62) = (k6_relat_1 @ X62))),
% 9.52/9.73      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 9.52/9.73  thf('65', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 9.52/9.73      inference('demod', [status(thm)], ['63', '64'])).
% 9.52/9.73  thf(t71_relat_1, axiom,
% 9.52/9.73    (![A:$i]:
% 9.52/9.73     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 9.52/9.73       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 9.52/9.73  thf('66', plain, (![X18 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 9.52/9.73      inference('cnf', [status(esa)], [t71_relat_1])).
% 9.52/9.73  thf('67', plain, (![X62 : $i]: ((k6_partfun1 @ X62) = (k6_relat_1 @ X62))),
% 9.52/9.73      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 9.52/9.73  thf('68', plain, (![X18 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X18)) = (X18))),
% 9.52/9.73      inference('demod', [status(thm)], ['66', '67'])).
% 9.52/9.73  thf('69', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 9.52/9.73      inference('sup+', [status(thm)], ['65', '68'])).
% 9.52/9.73  thf(t91_relat_1, axiom,
% 9.52/9.73    (![A:$i,B:$i]:
% 9.52/9.73     ( ( v1_relat_1 @ B ) =>
% 9.52/9.73       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 9.52/9.73         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 9.52/9.73  thf('70', plain,
% 9.52/9.73      (![X21 : $i, X22 : $i]:
% 9.52/9.73         (~ (r1_tarski @ X21 @ (k1_relat_1 @ X22))
% 9.52/9.73          | ((k1_relat_1 @ (k7_relat_1 @ X22 @ X21)) = (X21))
% 9.52/9.73          | ~ (v1_relat_1 @ X22))),
% 9.52/9.73      inference('cnf', [status(esa)], [t91_relat_1])).
% 9.52/9.73  thf('71', plain,
% 9.52/9.73      (![X0 : $i]:
% 9.52/9.73         (~ (r1_tarski @ X0 @ k1_xboole_0)
% 9.52/9.73          | ~ (v1_relat_1 @ k1_xboole_0)
% 9.52/9.73          | ((k1_relat_1 @ (k7_relat_1 @ k1_xboole_0 @ X0)) = (X0)))),
% 9.52/9.73      inference('sup-', [status(thm)], ['69', '70'])).
% 9.52/9.73  thf('72', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 9.52/9.73      inference('demod', [status(thm)], ['63', '64'])).
% 9.52/9.73  thf(fc3_funct_1, axiom,
% 9.52/9.73    (![A:$i]:
% 9.52/9.73     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 9.52/9.73       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 9.52/9.73  thf('73', plain, (![X23 : $i]: (v1_relat_1 @ (k6_relat_1 @ X23))),
% 9.52/9.73      inference('cnf', [status(esa)], [fc3_funct_1])).
% 9.52/9.73  thf('74', plain, (![X62 : $i]: ((k6_partfun1 @ X62) = (k6_relat_1 @ X62))),
% 9.52/9.73      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 9.52/9.73  thf('75', plain, (![X23 : $i]: (v1_relat_1 @ (k6_partfun1 @ X23))),
% 9.52/9.73      inference('demod', [status(thm)], ['73', '74'])).
% 9.52/9.73  thf('76', plain, ((v1_relat_1 @ k1_xboole_0)),
% 9.52/9.73      inference('sup+', [status(thm)], ['72', '75'])).
% 9.52/9.73  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 9.52/9.73  thf('77', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 9.52/9.73      inference('cnf', [status(esa)], [t2_xboole_1])).
% 9.52/9.73  thf('78', plain,
% 9.52/9.73      (![X13 : $i, X15 : $i]:
% 9.52/9.73         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 9.52/9.73      inference('cnf', [status(esa)], [t3_subset])).
% 9.52/9.73  thf('79', plain,
% 9.52/9.73      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 9.52/9.73      inference('sup-', [status(thm)], ['77', '78'])).
% 9.52/9.73  thf('80', plain,
% 9.52/9.73      (![X34 : $i, X35 : $i, X36 : $i]:
% 9.52/9.73         ((v4_relat_1 @ X34 @ X35)
% 9.52/9.73          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 9.52/9.73      inference('cnf', [status(esa)], [cc2_relset_1])).
% 9.52/9.73  thf('81', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 9.52/9.73      inference('sup-', [status(thm)], ['79', '80'])).
% 9.52/9.73  thf(t209_relat_1, axiom,
% 9.52/9.73    (![A:$i,B:$i]:
% 9.52/9.73     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 9.52/9.73       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 9.52/9.73  thf('82', plain,
% 9.52/9.73      (![X16 : $i, X17 : $i]:
% 9.52/9.73         (((X16) = (k7_relat_1 @ X16 @ X17))
% 9.52/9.73          | ~ (v4_relat_1 @ X16 @ X17)
% 9.52/9.73          | ~ (v1_relat_1 @ X16))),
% 9.52/9.73      inference('cnf', [status(esa)], [t209_relat_1])).
% 9.52/9.73  thf('83', plain,
% 9.52/9.73      (![X0 : $i]:
% 9.52/9.73         (~ (v1_relat_1 @ k1_xboole_0)
% 9.52/9.73          | ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0)))),
% 9.52/9.73      inference('sup-', [status(thm)], ['81', '82'])).
% 9.52/9.73  thf('84', plain, ((v1_relat_1 @ k1_xboole_0)),
% 9.52/9.73      inference('sup+', [status(thm)], ['72', '75'])).
% 9.52/9.73  thf('85', plain,
% 9.52/9.73      (![X0 : $i]: ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0))),
% 9.52/9.73      inference('demod', [status(thm)], ['83', '84'])).
% 9.52/9.73  thf('86', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 9.52/9.73      inference('sup+', [status(thm)], ['65', '68'])).
% 9.52/9.73  thf('87', plain,
% 9.52/9.73      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((k1_xboole_0) = (X0)))),
% 9.52/9.73      inference('demod', [status(thm)], ['71', '76', '85', '86'])).
% 9.52/9.73  thf('88', plain,
% 9.52/9.73      (![X0 : $i, X1 : $i]:
% 9.52/9.73         (~ (r1_tarski @ X1 @ X0)
% 9.52/9.73          | ~ (v1_xboole_0 @ X0)
% 9.52/9.73          | ((k1_xboole_0) = (X1)))),
% 9.52/9.73      inference('sup-', [status(thm)], ['62', '87'])).
% 9.52/9.73  thf('89', plain,
% 9.52/9.73      ((((k1_xboole_0) = (sk_C_1))
% 9.52/9.73        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.52/9.73      inference('sup-', [status(thm)], ['59', '88'])).
% 9.52/9.73  thf('90', plain, (((sk_A) = (k1_xboole_0))),
% 9.52/9.73      inference('demod', [status(thm)], ['49', '53'])).
% 9.52/9.73  thf('91', plain, (((sk_A) = (k1_xboole_0))),
% 9.52/9.73      inference('demod', [status(thm)], ['49', '53'])).
% 9.52/9.73  thf(t113_zfmisc_1, axiom,
% 9.52/9.73    (![A:$i,B:$i]:
% 9.52/9.73     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 9.52/9.73       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 9.52/9.73  thf('92', plain,
% 9.52/9.73      (![X8 : $i, X9 : $i]:
% 9.52/9.73         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 9.52/9.73      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 9.52/9.73  thf('93', plain,
% 9.52/9.73      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 9.52/9.73      inference('simplify', [status(thm)], ['92'])).
% 9.52/9.73  thf('94', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 9.52/9.73      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 9.52/9.73  thf('95', plain, (((k1_xboole_0) = (sk_C_1))),
% 9.52/9.73      inference('demod', [status(thm)], ['89', '90', '91', '93', '94'])).
% 9.52/9.73  thf('96', plain,
% 9.52/9.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.52/9.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.52/9.73  thf('97', plain,
% 9.52/9.73      (![X13 : $i, X14 : $i]:
% 9.52/9.73         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 9.52/9.73      inference('cnf', [status(esa)], [t3_subset])).
% 9.52/9.73  thf('98', plain, ((r1_tarski @ sk_B @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 9.52/9.73      inference('sup-', [status(thm)], ['96', '97'])).
% 9.52/9.73  thf('99', plain,
% 9.52/9.73      (![X0 : $i, X1 : $i]:
% 9.52/9.73         (~ (r1_tarski @ X1 @ X0)
% 9.52/9.73          | ~ (v1_xboole_0 @ X0)
% 9.52/9.73          | ((k1_xboole_0) = (X1)))),
% 9.52/9.73      inference('sup-', [status(thm)], ['62', '87'])).
% 9.52/9.73  thf('100', plain,
% 9.52/9.73      ((((k1_xboole_0) = (sk_B))
% 9.52/9.73        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.52/9.73      inference('sup-', [status(thm)], ['98', '99'])).
% 9.52/9.73  thf('101', plain, (((sk_A) = (k1_xboole_0))),
% 9.52/9.73      inference('demod', [status(thm)], ['49', '53'])).
% 9.52/9.73  thf('102', plain, (((sk_A) = (k1_xboole_0))),
% 9.52/9.73      inference('demod', [status(thm)], ['49', '53'])).
% 9.52/9.73  thf('103', plain,
% 9.52/9.73      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 9.52/9.73      inference('simplify', [status(thm)], ['92'])).
% 9.52/9.73  thf('104', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 9.52/9.73      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 9.52/9.73  thf('105', plain, (((k1_xboole_0) = (sk_B))),
% 9.52/9.73      inference('demod', [status(thm)], ['100', '101', '102', '103', '104'])).
% 9.52/9.73  thf('106', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 9.52/9.73      inference('demod', [status(thm)], ['63', '64'])).
% 9.52/9.73  thf('107', plain,
% 9.52/9.73      (![X18 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X18)) = (X18))),
% 9.52/9.73      inference('demod', [status(thm)], ['66', '67'])).
% 9.52/9.73  thf(t78_relat_1, axiom,
% 9.52/9.73    (![A:$i]:
% 9.52/9.73     ( ( v1_relat_1 @ A ) =>
% 9.52/9.73       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 9.52/9.73  thf('108', plain,
% 9.52/9.73      (![X20 : $i]:
% 9.52/9.73         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X20)) @ X20) = (X20))
% 9.52/9.73          | ~ (v1_relat_1 @ X20))),
% 9.52/9.73      inference('cnf', [status(esa)], [t78_relat_1])).
% 9.52/9.73  thf('109', plain, (![X62 : $i]: ((k6_partfun1 @ X62) = (k6_relat_1 @ X62))),
% 9.52/9.73      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 9.52/9.73  thf('110', plain,
% 9.52/9.73      (![X20 : $i]:
% 9.52/9.73         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X20)) @ X20) = (X20))
% 9.52/9.73          | ~ (v1_relat_1 @ X20))),
% 9.52/9.73      inference('demod', [status(thm)], ['108', '109'])).
% 9.52/9.73  thf('111', plain,
% 9.52/9.73      (![X0 : $i]:
% 9.52/9.73         (((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 9.52/9.73            = (k6_partfun1 @ X0))
% 9.52/9.73          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 9.52/9.73      inference('sup+', [status(thm)], ['107', '110'])).
% 9.52/9.73  thf('112', plain, (![X23 : $i]: (v1_relat_1 @ (k6_partfun1 @ X23))),
% 9.52/9.73      inference('demod', [status(thm)], ['73', '74'])).
% 9.52/9.73  thf('113', plain,
% 9.52/9.73      (![X0 : $i]:
% 9.52/9.73         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 9.52/9.73           = (k6_partfun1 @ X0))),
% 9.52/9.73      inference('demod', [status(thm)], ['111', '112'])).
% 9.52/9.73  thf(t64_funct_1, axiom,
% 9.52/9.73    (![A:$i]:
% 9.52/9.73     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 9.52/9.73       ( ![B:$i]:
% 9.52/9.73         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 9.52/9.73           ( ( ( v2_funct_1 @ A ) & 
% 9.52/9.73               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 9.52/9.73               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 9.52/9.73             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 9.52/9.73  thf('114', plain,
% 9.52/9.73      (![X27 : $i, X28 : $i]:
% 9.52/9.73         (~ (v1_relat_1 @ X27)
% 9.52/9.73          | ~ (v1_funct_1 @ X27)
% 9.52/9.73          | ((X27) = (k2_funct_1 @ X28))
% 9.52/9.73          | ((k5_relat_1 @ X27 @ X28) != (k6_relat_1 @ (k2_relat_1 @ X28)))
% 9.52/9.73          | ((k2_relat_1 @ X27) != (k1_relat_1 @ X28))
% 9.52/9.73          | ~ (v2_funct_1 @ X28)
% 9.52/9.73          | ~ (v1_funct_1 @ X28)
% 9.52/9.73          | ~ (v1_relat_1 @ X28))),
% 9.52/9.73      inference('cnf', [status(esa)], [t64_funct_1])).
% 9.52/9.73  thf('115', plain, (![X62 : $i]: ((k6_partfun1 @ X62) = (k6_relat_1 @ X62))),
% 9.52/9.73      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 9.52/9.73  thf('116', plain,
% 9.52/9.73      (![X27 : $i, X28 : $i]:
% 9.52/9.73         (~ (v1_relat_1 @ X27)
% 9.52/9.73          | ~ (v1_funct_1 @ X27)
% 9.52/9.73          | ((X27) = (k2_funct_1 @ X28))
% 9.52/9.73          | ((k5_relat_1 @ X27 @ X28) != (k6_partfun1 @ (k2_relat_1 @ X28)))
% 9.52/9.73          | ((k2_relat_1 @ X27) != (k1_relat_1 @ X28))
% 9.52/9.73          | ~ (v2_funct_1 @ X28)
% 9.52/9.73          | ~ (v1_funct_1 @ X28)
% 9.52/9.73          | ~ (v1_relat_1 @ X28))),
% 9.52/9.73      inference('demod', [status(thm)], ['114', '115'])).
% 9.52/9.73  thf('117', plain,
% 9.52/9.73      (![X0 : $i]:
% 9.52/9.73         (((k6_partfun1 @ X0)
% 9.52/9.73            != (k6_partfun1 @ (k2_relat_1 @ (k6_partfun1 @ X0))))
% 9.52/9.73          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 9.52/9.73          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 9.52/9.73          | ~ (v2_funct_1 @ (k6_partfun1 @ X0))
% 9.52/9.73          | ((k2_relat_1 @ (k6_partfun1 @ X0))
% 9.52/9.73              != (k1_relat_1 @ (k6_partfun1 @ X0)))
% 9.52/9.73          | ((k6_partfun1 @ X0) = (k2_funct_1 @ (k6_partfun1 @ X0)))
% 9.52/9.73          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 9.52/9.73          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 9.52/9.73      inference('sup-', [status(thm)], ['113', '116'])).
% 9.52/9.73  thf('118', plain, (![X19 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X19)) = (X19))),
% 9.52/9.73      inference('cnf', [status(esa)], [t71_relat_1])).
% 9.52/9.73  thf('119', plain, (![X62 : $i]: ((k6_partfun1 @ X62) = (k6_relat_1 @ X62))),
% 9.52/9.73      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 9.52/9.73  thf('120', plain,
% 9.52/9.73      (![X19 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X19)) = (X19))),
% 9.52/9.73      inference('demod', [status(thm)], ['118', '119'])).
% 9.52/9.73  thf('121', plain, (![X23 : $i]: (v1_relat_1 @ (k6_partfun1 @ X23))),
% 9.52/9.73      inference('demod', [status(thm)], ['73', '74'])).
% 9.52/9.73  thf('122', plain, (![X24 : $i]: (v1_funct_1 @ (k6_relat_1 @ X24))),
% 9.52/9.73      inference('cnf', [status(esa)], [fc3_funct_1])).
% 9.52/9.73  thf('123', plain, (![X62 : $i]: ((k6_partfun1 @ X62) = (k6_relat_1 @ X62))),
% 9.52/9.73      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 9.52/9.73  thf('124', plain, (![X24 : $i]: (v1_funct_1 @ (k6_partfun1 @ X24))),
% 9.52/9.73      inference('demod', [status(thm)], ['122', '123'])).
% 9.52/9.73  thf(fc4_funct_1, axiom,
% 9.52/9.73    (![A:$i]:
% 9.52/9.73     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 9.52/9.73       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 9.52/9.73  thf('125', plain, (![X26 : $i]: (v2_funct_1 @ (k6_relat_1 @ X26))),
% 9.52/9.73      inference('cnf', [status(esa)], [fc4_funct_1])).
% 9.52/9.73  thf('126', plain, (![X62 : $i]: ((k6_partfun1 @ X62) = (k6_relat_1 @ X62))),
% 9.52/9.73      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 9.52/9.73  thf('127', plain, (![X26 : $i]: (v2_funct_1 @ (k6_partfun1 @ X26))),
% 9.52/9.73      inference('demod', [status(thm)], ['125', '126'])).
% 9.52/9.73  thf('128', plain,
% 9.52/9.73      (![X19 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X19)) = (X19))),
% 9.52/9.73      inference('demod', [status(thm)], ['118', '119'])).
% 9.52/9.73  thf('129', plain,
% 9.52/9.73      (![X18 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X18)) = (X18))),
% 9.52/9.73      inference('demod', [status(thm)], ['66', '67'])).
% 9.52/9.73  thf('130', plain, (![X24 : $i]: (v1_funct_1 @ (k6_partfun1 @ X24))),
% 9.52/9.73      inference('demod', [status(thm)], ['122', '123'])).
% 9.52/9.73  thf('131', plain, (![X23 : $i]: (v1_relat_1 @ (k6_partfun1 @ X23))),
% 9.52/9.73      inference('demod', [status(thm)], ['73', '74'])).
% 9.52/9.73  thf('132', plain,
% 9.52/9.73      (![X0 : $i]:
% 9.52/9.73         (((k6_partfun1 @ X0) != (k6_partfun1 @ X0))
% 9.52/9.73          | ((X0) != (X0))
% 9.52/9.73          | ((k6_partfun1 @ X0) = (k2_funct_1 @ (k6_partfun1 @ X0))))),
% 9.52/9.73      inference('demod', [status(thm)],
% 9.52/9.73                ['117', '120', '121', '124', '127', '128', '129', '130', '131'])).
% 9.52/9.73  thf('133', plain,
% 9.52/9.73      (![X0 : $i]: ((k6_partfun1 @ X0) = (k2_funct_1 @ (k6_partfun1 @ X0)))),
% 9.52/9.73      inference('simplify', [status(thm)], ['132'])).
% 9.52/9.73  thf('134', plain,
% 9.52/9.73      (((k6_partfun1 @ k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))),
% 9.52/9.73      inference('sup+', [status(thm)], ['106', '133'])).
% 9.52/9.73  thf('135', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 9.52/9.73      inference('demod', [status(thm)], ['63', '64'])).
% 9.52/9.73  thf('136', plain, (((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))),
% 9.52/9.73      inference('sup+', [status(thm)], ['134', '135'])).
% 9.52/9.73  thf('137', plain,
% 9.52/9.73      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 9.52/9.73      inference('sup-', [status(thm)], ['77', '78'])).
% 9.52/9.73  thf('138', plain,
% 9.52/9.73      (![X44 : $i, X45 : $i, X46 : $i]:
% 9.52/9.73         ((r2_relset_1 @ X44 @ X45 @ X46 @ X46)
% 9.52/9.73          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45))))),
% 9.52/9.73      inference('simplify', [status(thm)], ['51'])).
% 9.52/9.73  thf('139', plain,
% 9.52/9.73      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 9.52/9.73      inference('sup-', [status(thm)], ['137', '138'])).
% 9.52/9.73  thf('140', plain, ($false),
% 9.52/9.73      inference('demod', [status(thm)], ['56', '95', '105', '136', '139'])).
% 9.52/9.73  
% 9.52/9.73  % SZS output end Refutation
% 9.52/9.73  
% 9.52/9.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

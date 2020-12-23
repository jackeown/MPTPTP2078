%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.R4rt2AIWp9

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:12 EST 2020

% Result     : Theorem 5.55s
% Output     : Refutation 5.55s
% Verified   : 
% Statistics : Number of formulae       :  389 (3499 expanded)
%              Number of leaves         :   59 (1048 expanded)
%              Depth                    :   51
%              Number of atoms          : 3855 (88881 expanded)
%              Number of equality atoms :  218 (5844 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
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

thf('1',plain,(
    ! [X66: $i,X67: $i,X68: $i] :
      ( ( X66 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X67 )
      | ~ ( v1_funct_2 @ X67 @ X68 @ X66 )
      | ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X68 @ X66 ) ) )
      | ( ( k5_relat_1 @ X67 @ ( k2_funct_1 @ X67 ) )
        = ( k6_partfun1 @ X68 ) )
      | ~ ( v2_funct_1 @ X67 )
      | ( ( k2_relset_1 @ X68 @ X66 @ X67 )
       != X66 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('2',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A_1 @ sk_D )
     != sk_A_1 )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A_1 )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('4',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k2_relset_1 @ X32 @ X33 @ X31 )
        = ( k2_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('5',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A_1 )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','5','6','7'])).

thf('9',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A_1 )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('13',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ( ( k1_partfun1 @ X47 @ X48 @ X50 @ X51 @ X46 @ X49 )
        = ( k5_relat_1 @ X46 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
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

thf('21',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_funct_2 @ X53 @ X54 @ X55 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X55 ) ) )
      | ~ ( r2_relset_1 @ X54 @ X54 @ ( k1_partfun1 @ X54 @ X55 @ X55 @ X54 @ X53 @ X56 ) @ ( k6_partfun1 @ X54 ) )
      | ( ( k2_relset_1 @ X55 @ X54 @ X56 )
        = X54 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X54 ) ) )
      | ~ ( v1_funct_2 @ X56 @ X55 @ X54 )
      | ~ ( v1_funct_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A_1 @ X0 )
        = sk_A_1 )
      | ~ ( r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A_1 ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_funct_2 @ sk_C @ sk_A_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A_1 @ X0 )
        = sk_A_1 )
      | ~ ( r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A_1 ) ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ~ ( r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A_1 ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A_1 @ sk_D )
      = sk_A_1 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A_1 )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('29',plain,(
    r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A_1 ),
    inference(demod,[status(thm)],['26','29','30','31','32','33'])).

thf('35',plain,
    ( ( sk_A_1 != sk_A_1 )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','34'])).

thf('36',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('38',plain,(
    r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('39',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('41',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_A_1 ) ) ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('48',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_A_1 ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('49',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( X34 = X37 )
      | ~ ( r2_relset_1 @ X35 @ X36 @ X34 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_A_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_A_1 ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['38','50'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('52',plain,(
    ! [X45: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X45 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('53',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['37','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
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

thf('56',plain,(
    ! [X61: $i,X62: $i,X63: $i,X64: $i,X65: $i] :
      ( ~ ( v1_funct_1 @ X61 )
      | ~ ( v1_funct_2 @ X61 @ X62 @ X63 )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X62 @ X63 ) ) )
      | ( zip_tseitin_0 @ X61 @ X64 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X65 @ X62 @ X62 @ X63 @ X64 @ X61 ) )
      | ( zip_tseitin_1 @ X63 @ X62 )
      | ( ( k2_relset_1 @ X65 @ X62 @ X64 )
       != X62 )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X65 @ X62 ) ) )
      | ~ ( v1_funct_2 @ X64 @ X65 @ X62 )
      | ~ ( v1_funct_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A_1 @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A_1 @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A_1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A_1 @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A_1 @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A_1 ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A_1 @ sk_B )
    | ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['54','60'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('62',plain,(
    ! [X20: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('63',plain,(
    ! [X52: $i] :
      ( ( k6_partfun1 @ X52 )
      = ( k6_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('64',plain,(
    ! [X20: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X20 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_2 @ sk_C @ sk_A_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A_1 @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['61','64','65','66','67','68'])).

thf('70',plain,
    ( ( zip_tseitin_1 @ sk_A_1 @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X59: $i,X60: $i] :
      ( ( X59 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('72',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X57: $i,X58: $i] :
      ( ( v2_funct_1 @ X58 )
      | ~ ( zip_tseitin_0 @ X58 @ X57 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('76',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['36','76'])).

thf('78',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['51','52'])).

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

thf('79',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ( X23
        = ( k2_funct_1 @ X24 ) )
      | ( ( k5_relat_1 @ X23 @ X24 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X24 ) ) )
      | ( ( k2_relat_1 @ X23 )
       != ( k1_relat_1 @ X24 ) )
      | ~ ( v2_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('80',plain,(
    ! [X52: $i] :
      ( ( k6_partfun1 @ X52 )
      = ( k6_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('81',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ( X23
        = ( k2_funct_1 @ X24 ) )
      | ( ( k5_relat_1 @ X23 @ X24 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X24 ) ) )
      | ( ( k2_relat_1 @ X23 )
       != ( k1_relat_1 @ X24 ) )
      | ~ ( v2_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( k6_partfun1 @ sk_A_1 )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A_1 ),
    inference(demod,[status(thm)],['26','29','30','31','32','33'])).

thf('84',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('85',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('86',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('87',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('88',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k2_relset_1 @ X32 @ X33 @ X31 )
        = ( k2_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('92',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('98',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('100',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ( k6_partfun1 @ sk_A_1 )
     != ( k6_partfun1 @ sk_A_1 ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['82','83','88','89','94','95','100'])).

thf('102',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['74','75'])).

thf('104',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('105',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('106',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['36','76'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('107',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) ) @ ( k2_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('108',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) ) @ ( k2_relat_1 @ ( k6_partfun1 @ sk_B ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['106','109'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('111',plain,(
    ! [X21: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v2_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('112',plain,(
    ! [X16: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('113',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('114',plain,(
    ! [X21: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v2_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('115',plain,(
    ! [X16: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('116',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
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

thf('117',plain,(
    ! [X22: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k1_relat_1 @ X22 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('118',plain,(
    ! [X22: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k2_relat_1 @ X22 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('119',plain,(
    ! [X16: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('120',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('121',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('122',plain,(
    ! [X21: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v2_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('123',plain,(
    ! [X16: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('124',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('125',plain,(
    ! [X22: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k1_relat_1 @ X22 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('126',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('127',plain,(
    ! [X22: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k2_relat_1 @ X22 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('128',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('129',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['128'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('130',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X7 )
      | ( v4_relat_1 @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['127','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['126','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['125','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['124','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['123','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['122','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v4_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['121','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['120','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['119','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['118','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['117','151'])).

thf('153',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['128'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['116','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['115','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['114','159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('164',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v4_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['162','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['161','167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['113','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['112','170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['111','172'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['173'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('175',plain,(
    ! [X14: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X14 ) ) @ X14 )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('176',plain,(
    ! [X52: $i] :
      ( ( k6_partfun1 @ X52 )
      = ( k6_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('177',plain,(
    ! [X14: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X14 ) ) @ X14 )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('178',plain,(
    ! [X14: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X14 ) ) @ X14 )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('179',plain,(
    ! [X14: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X14 ) ) @ X14 )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('180',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A_1 ),
    inference(demod,[status(thm)],['26','29','30','31','32','33'])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A_1 @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ sk_D ) ) )
      | ( ( k2_relat_1 @ sk_D )
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ sk_D ) ) )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A_1 ),
    inference(demod,[status(thm)],['26','29','30','31','32','33'])).

thf('184',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['86','87'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A_1 @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ sk_D ) ) )
      | ( sk_A_1
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ sk_D ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['182','183','184'])).

thf('186',plain,
    ( ~ ( r1_tarski @ sk_A_1 @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) )
    | ( sk_A_1
      = ( k2_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['179','185'])).

thf('187',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A_1 ),
    inference(demod,[status(thm)],['26','29','30','31','32','33'])).

thf('188',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['128'])).

thf('189',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['86','87'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('190',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('191',plain,(
    ! [X52: $i] :
      ( ( k6_partfun1 @ X52 )
      = ( k6_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('192',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X17 ) ) ),
    inference(demod,[status(thm)],['190','191'])).

thf('193',plain,
    ( sk_A_1
    = ( k2_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['186','187','188','189','192'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('194',plain,(
    ! [X15: $i] :
      ( ( ( k5_relat_1 @ X15 @ ( k6_relat_1 @ ( k2_relat_1 @ X15 ) ) )
        = X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('195',plain,(
    ! [X52: $i] :
      ( ( k6_partfun1 @ X52 )
      = ( k6_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('196',plain,(
    ! [X15: $i] :
      ( ( ( k5_relat_1 @ X15 @ ( k6_partfun1 @ ( k2_relat_1 @ X15 ) ) )
        = X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(demod,[status(thm)],['194','195'])).

thf('197',plain,
    ( ( ( k5_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D ) @ ( k6_partfun1 @ sk_A_1 ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D ) ) ),
    inference('sup+',[status(thm)],['193','196'])).

thf('198',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k5_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D ) @ ( k6_partfun1 @ sk_A_1 ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['178','197'])).

thf('199',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['86','87'])).

thf('200',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['86','87'])).

thf('201',plain,
    ( ( k5_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D ) @ ( k6_partfun1 @ sk_A_1 ) )
    = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D ) ),
    inference(demod,[status(thm)],['198','199','200'])).

thf('202',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ sk_A_1 ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['177','201'])).

thf('203',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A_1 ),
    inference(demod,[status(thm)],['26','29','30','31','32','33'])).

thf('204',plain,(
    ! [X15: $i] :
      ( ( ( k5_relat_1 @ X15 @ ( k6_partfun1 @ ( k2_relat_1 @ X15 ) ) )
        = X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(demod,[status(thm)],['194','195'])).

thf('205',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ sk_A_1 ) )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['203','204'])).

thf('206',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['86','87'])).

thf('207',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ sk_A_1 ) )
    = sk_D ),
    inference(demod,[status(thm)],['205','206'])).

thf('208',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['86','87'])).

thf('209',plain,
    ( sk_D
    = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D ) ),
    inference(demod,[status(thm)],['202','207','208'])).

thf('210',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t67_funct_1,axiom,(
    ! [A: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('211',plain,(
    ! [X27: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X27 ) )
      = ( k6_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_1])).

thf('212',plain,(
    ! [X52: $i] :
      ( ( k6_partfun1 @ X52 )
      = ( k6_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('213',plain,(
    ! [X52: $i] :
      ( ( k6_partfun1 @ X52 )
      = ( k6_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('214',plain,(
    ! [X27: $i] :
      ( ( k2_funct_1 @ ( k6_partfun1 @ X27 ) )
      = ( k6_partfun1 @ X27 ) ) ),
    inference(demod,[status(thm)],['211','212','213'])).

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

thf('215',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_funct_1 @ X25 )
      | ( ( k2_funct_1 @ ( k5_relat_1 @ X26 @ X25 ) )
        = ( k5_relat_1 @ ( k2_funct_1 @ X25 ) @ ( k2_funct_1 @ X26 ) ) )
      | ~ ( v2_funct_1 @ X25 )
      | ~ ( v2_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t66_funct_1])).

thf('216',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) ) @ ( k2_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('217',plain,(
    ! [X12: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('218',plain,(
    ! [X52: $i] :
      ( ( k6_partfun1 @ X52 )
      = ( k6_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('219',plain,(
    ! [X12: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X12 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['217','218'])).

thf('220',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X7 )
      | ( v4_relat_1 @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('221',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( v4_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['219','220'])).

thf('222',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X17 ) ) ),
    inference(demod,[status(thm)],['190','191'])).

thf('223',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( v4_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['221','222'])).

thf('224',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['216','223'])).

thf('225',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['215','224'])).

thf('226',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( v4_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['214','225'])).

thf('227',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X17 ) ) ),
    inference(demod,[status(thm)],['190','191'])).

thf('228',plain,(
    ! [X20: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X20 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('229',plain,(
    ! [X18: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('230',plain,(
    ! [X52: $i] :
      ( ( k6_partfun1 @ X52 )
      = ( k6_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('231',plain,(
    ! [X18: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X18 ) ) ),
    inference(demod,[status(thm)],['229','230'])).

thf('232',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X17 ) ) ),
    inference(demod,[status(thm)],['190','191'])).

thf('233',plain,(
    ! [X27: $i] :
      ( ( k2_funct_1 @ ( k6_partfun1 @ X27 ) )
      = ( k6_partfun1 @ X27 ) ) ),
    inference(demod,[status(thm)],['211','212','213'])).

thf('234',plain,(
    ! [X13: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('235',plain,(
    ! [X52: $i] :
      ( ( k6_partfun1 @ X52 )
      = ( k6_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('236',plain,(
    ! [X13: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X13 ) )
      = X13 ) ),
    inference(demod,[status(thm)],['234','235'])).

thf('237',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ( v4_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['226','227','228','231','232','233','236'])).

thf('238',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v4_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) ) ) ) @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['210','237'])).

thf('239',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) ) ) ) @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['238'])).

thf('240',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v4_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('241',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ) ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['239','240'])).

thf('242',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X17 ) ) ),
    inference(demod,[status(thm)],['190','191'])).

thf('243',plain,(
    ! [X12: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X12 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['217','218'])).

thf('244',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['241','242','243'])).

thf('245',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('246',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ) )
      | ( X0
        = ( k2_relat_1 @ ( k2_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['244','245'])).

thf('247',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k2_relat_1 @ ( k2_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D ) ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['209','246'])).

thf('248',plain,
    ( sk_D
    = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D ) ),
    inference(demod,[status(thm)],['202','207','208'])).

thf('249',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['86','87'])).

thf('250',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['247','248','249','250'])).

thf('252',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['174','251'])).

thf('253',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['86','87'])).

thf('254',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,
    ( ~ ( v2_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['252','253','254'])).

thf('256',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['255'])).

thf('257',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['74','75'])).

thf('258',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['256','257'])).

thf('259',plain,(
    ! [X13: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X13 ) )
      = X13 ) ),
    inference(demod,[status(thm)],['234','235'])).

thf('260',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('261',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v4_relat_1 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('262',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['260','261'])).

thf('263',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v4_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('264',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['262','263'])).

thf('265',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['86','87'])).

thf('266',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['264','265'])).

thf('267',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['256','257'])).

thf('268',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['36','76'])).

thf('269',plain,(
    ! [X13: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X13 ) )
      = X13 ) ),
    inference(demod,[status(thm)],['234','235'])).

thf('270',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['86','87'])).

thf('271',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = sk_B )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['110','258','259','266','267','268','269','270'])).

thf('272',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = sk_B ) ),
    inference('sup-',[status(thm)],['105','271'])).

thf('273',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['86','87'])).

thf('274',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('275',plain,
    ( ( k1_relat_1 @ sk_D )
    = sk_B ),
    inference(demod,[status(thm)],['272','273','274'])).

thf('276',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['104','275'])).

thf('277',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['276'])).

thf('278',plain,
    ( ( k5_relat_1 @ sk_D @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['77','277'])).

thf('279',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ( X23
        = ( k2_funct_1 @ X24 ) )
      | ( ( k5_relat_1 @ X23 @ X24 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X24 ) ) )
      | ( ( k2_relat_1 @ X23 )
       != ( k1_relat_1 @ X24 ) )
      | ~ ( v2_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('280',plain,
    ( ( ( k6_partfun1 @ sk_B )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_D )
     != ( k1_relat_1 @ sk_C ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['278','279'])).

thf('281',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['92','93'])).

thf('282',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['98','99'])).

thf('283',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('284',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('285',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A_1 ),
    inference(demod,[status(thm)],['26','29','30','31','32','33'])).

thf('286',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('287',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v4_relat_1 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('288',plain,(
    v4_relat_1 @ sk_C @ sk_A_1 ),
    inference('sup-',[status(thm)],['286','287'])).

thf('289',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v4_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('290',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['288','289'])).

thf('291',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['98','99'])).

thf('292',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A_1 ),
    inference(demod,[status(thm)],['290','291'])).

thf('293',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('294',plain,
    ( ~ ( r1_tarski @ sk_A_1 @ ( k1_relat_1 @ sk_C ) )
    | ( sk_A_1
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['292','293'])).

thf('295',plain,(
    ! [X22: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k1_relat_1 @ X22 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('296',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('297',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('298',plain,(
    ! [X66: $i,X67: $i,X68: $i] :
      ( ( X66 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X67 )
      | ~ ( v1_funct_2 @ X67 @ X68 @ X66 )
      | ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X68 @ X66 ) ) )
      | ( ( k5_relat_1 @ X67 @ ( k2_funct_1 @ X67 ) )
        = ( k6_partfun1 @ X68 ) )
      | ~ ( v2_funct_1 @ X67 )
      | ( ( k2_relset_1 @ X68 @ X66 @ X67 )
       != X66 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('299',plain,
    ( ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A_1 ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['297','298'])).

thf('300',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('301',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('302',plain,(
    v1_funct_2 @ sk_C @ sk_A_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('303',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('304',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A_1 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['299','300','301','302','303'])).

thf('305',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A_1 ) ) ),
    inference(simplify,[status(thm)],['304'])).

thf('306',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('307',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A_1 ) ),
    inference('simplify_reflect-',[status(thm)],['305','306'])).

thf('308',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) ) @ ( k2_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('309',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k6_partfun1 @ sk_A_1 ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['307','308'])).

thf('310',plain,(
    ! [X13: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X13 ) )
      = X13 ) ),
    inference(demod,[status(thm)],['234','235'])).

thf('311',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['98','99'])).

thf('312',plain,
    ( ( r1_tarski @ sk_A_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['309','310','311'])).

thf('313',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ sk_A_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['296','312'])).

thf('314',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['98','99'])).

thf('315',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('316',plain,(
    r1_tarski @ sk_A_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['313','314','315'])).

thf('317',plain,
    ( ( r1_tarski @ sk_A_1 @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['295','316'])).

thf('318',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['98','99'])).

thf('319',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('320',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('321',plain,(
    r1_tarski @ sk_A_1 @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['317','318','319','320'])).

thf('322',plain,
    ( sk_A_1
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['294','321'])).

thf('323',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('324',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['86','87'])).

thf('325',plain,
    ( ( ( k6_partfun1 @ sk_B )
     != ( k6_partfun1 @ sk_B ) )
    | ( sk_A_1 != sk_A_1 )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['280','281','282','283','284','285','322','323','324'])).

thf('326',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['325'])).

thf('327',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('328',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['326','327'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.R4rt2AIWp9
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:45:33 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 5.55/5.76  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.55/5.76  % Solved by: fo/fo7.sh
% 5.55/5.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.55/5.76  % done 5024 iterations in 5.302s
% 5.55/5.76  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.55/5.76  % SZS output start Refutation
% 5.55/5.76  thf(sk_B_type, type, sk_B: $i).
% 5.55/5.76  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 5.55/5.76  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 5.55/5.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.55/5.76  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 5.55/5.76  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 5.55/5.76  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 5.55/5.76  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 5.55/5.76  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 5.55/5.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.55/5.76  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 5.55/5.76  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.55/5.76  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 5.55/5.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.55/5.76  thf(sk_C_type, type, sk_C: $i).
% 5.55/5.76  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 5.55/5.76  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 5.55/5.76  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 5.55/5.76  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 5.55/5.76  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.55/5.76  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 5.55/5.76  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 5.55/5.76  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 5.55/5.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.55/5.76  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 5.55/5.76  thf(sk_A_1_type, type, sk_A_1: $i).
% 5.55/5.76  thf(sk_D_type, type, sk_D: $i).
% 5.55/5.76  thf(t36_funct_2, conjecture,
% 5.55/5.76    (![A:$i,B:$i,C:$i]:
% 5.55/5.76     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.55/5.76         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.55/5.76       ( ![D:$i]:
% 5.55/5.76         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 5.55/5.76             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 5.55/5.76           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 5.55/5.76               ( r2_relset_1 @
% 5.55/5.76                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 5.55/5.76                 ( k6_partfun1 @ A ) ) & 
% 5.55/5.76               ( v2_funct_1 @ C ) ) =>
% 5.55/5.76             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 5.55/5.76               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 5.55/5.76  thf(zf_stmt_0, negated_conjecture,
% 5.55/5.76    (~( ![A:$i,B:$i,C:$i]:
% 5.55/5.76        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.55/5.76            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.55/5.76          ( ![D:$i]:
% 5.55/5.76            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 5.55/5.76                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 5.55/5.76              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 5.55/5.76                  ( r2_relset_1 @
% 5.55/5.76                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 5.55/5.76                    ( k6_partfun1 @ A ) ) & 
% 5.55/5.76                  ( v2_funct_1 @ C ) ) =>
% 5.55/5.76                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 5.55/5.76                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 5.55/5.76    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 5.55/5.76  thf('0', plain,
% 5.55/5.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf(t35_funct_2, axiom,
% 5.55/5.76    (![A:$i,B:$i,C:$i]:
% 5.55/5.76     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.55/5.76         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.55/5.76       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 5.55/5.76         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 5.55/5.76           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 5.55/5.76             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 5.55/5.76  thf('1', plain,
% 5.55/5.76      (![X66 : $i, X67 : $i, X68 : $i]:
% 5.55/5.76         (((X66) = (k1_xboole_0))
% 5.55/5.76          | ~ (v1_funct_1 @ X67)
% 5.55/5.76          | ~ (v1_funct_2 @ X67 @ X68 @ X66)
% 5.55/5.76          | ~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X68 @ X66)))
% 5.55/5.76          | ((k5_relat_1 @ X67 @ (k2_funct_1 @ X67)) = (k6_partfun1 @ X68))
% 5.55/5.76          | ~ (v2_funct_1 @ X67)
% 5.55/5.76          | ((k2_relset_1 @ X68 @ X66 @ X67) != (X66)))),
% 5.55/5.76      inference('cnf', [status(esa)], [t35_funct_2])).
% 5.55/5.76  thf('2', plain,
% 5.55/5.76      ((((k2_relset_1 @ sk_B @ sk_A_1 @ sk_D) != (sk_A_1))
% 5.55/5.76        | ~ (v2_funct_1 @ sk_D)
% 5.55/5.76        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 5.55/5.76        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A_1)
% 5.55/5.76        | ~ (v1_funct_1 @ sk_D)
% 5.55/5.76        | ((sk_A_1) = (k1_xboole_0)))),
% 5.55/5.76      inference('sup-', [status(thm)], ['0', '1'])).
% 5.55/5.76  thf('3', plain,
% 5.55/5.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf(redefinition_k2_relset_1, axiom,
% 5.55/5.76    (![A:$i,B:$i,C:$i]:
% 5.55/5.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.55/5.76       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 5.55/5.76  thf('4', plain,
% 5.55/5.76      (![X31 : $i, X32 : $i, X33 : $i]:
% 5.55/5.76         (((k2_relset_1 @ X32 @ X33 @ X31) = (k2_relat_1 @ X31))
% 5.55/5.76          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 5.55/5.76      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 5.55/5.76  thf('5', plain,
% 5.55/5.76      (((k2_relset_1 @ sk_B @ sk_A_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 5.55/5.76      inference('sup-', [status(thm)], ['3', '4'])).
% 5.55/5.76  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A_1)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('8', plain,
% 5.55/5.76      ((((k2_relat_1 @ sk_D) != (sk_A_1))
% 5.55/5.76        | ~ (v2_funct_1 @ sk_D)
% 5.55/5.76        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 5.55/5.76        | ((sk_A_1) = (k1_xboole_0)))),
% 5.55/5.76      inference('demod', [status(thm)], ['2', '5', '6', '7'])).
% 5.55/5.76  thf('9', plain, (((sk_A_1) != (k1_xboole_0))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('10', plain,
% 5.55/5.76      ((((k2_relat_1 @ sk_D) != (sk_A_1))
% 5.55/5.76        | ~ (v2_funct_1 @ sk_D)
% 5.55/5.76        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 5.55/5.76      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 5.55/5.76  thf('11', plain,
% 5.55/5.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('12', plain,
% 5.55/5.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf(redefinition_k1_partfun1, axiom,
% 5.55/5.76    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 5.55/5.76     ( ( ( v1_funct_1 @ E ) & 
% 5.55/5.76         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.55/5.76         ( v1_funct_1 @ F ) & 
% 5.55/5.76         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 5.55/5.76       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 5.55/5.76  thf('13', plain,
% 5.55/5.76      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 5.55/5.76         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 5.55/5.76          | ~ (v1_funct_1 @ X46)
% 5.55/5.76          | ~ (v1_funct_1 @ X49)
% 5.55/5.76          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 5.55/5.76          | ((k1_partfun1 @ X47 @ X48 @ X50 @ X51 @ X46 @ X49)
% 5.55/5.76              = (k5_relat_1 @ X46 @ X49)))),
% 5.55/5.76      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 5.55/5.76  thf('14', plain,
% 5.55/5.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.55/5.76         (((k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 5.55/5.76            = (k5_relat_1 @ sk_C @ X0))
% 5.55/5.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ sk_C))),
% 5.55/5.76      inference('sup-', [status(thm)], ['12', '13'])).
% 5.55/5.76  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('16', plain,
% 5.55/5.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.55/5.76         (((k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 5.55/5.76            = (k5_relat_1 @ sk_C @ X0))
% 5.55/5.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 5.55/5.76          | ~ (v1_funct_1 @ X0))),
% 5.55/5.76      inference('demod', [status(thm)], ['14', '15'])).
% 5.55/5.76  thf('17', plain,
% 5.55/5.76      ((~ (v1_funct_1 @ sk_D)
% 5.55/5.76        | ((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 5.55/5.76            = (k5_relat_1 @ sk_C @ sk_D)))),
% 5.55/5.76      inference('sup-', [status(thm)], ['11', '16'])).
% 5.55/5.76  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('19', plain,
% 5.55/5.76      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 5.55/5.76         = (k5_relat_1 @ sk_C @ sk_D))),
% 5.55/5.76      inference('demod', [status(thm)], ['17', '18'])).
% 5.55/5.76  thf('20', plain,
% 5.55/5.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf(t24_funct_2, axiom,
% 5.55/5.76    (![A:$i,B:$i,C:$i]:
% 5.55/5.76     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.55/5.76         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.55/5.76       ( ![D:$i]:
% 5.55/5.76         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 5.55/5.76             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 5.55/5.76           ( ( r2_relset_1 @
% 5.55/5.76               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 5.55/5.76               ( k6_partfun1 @ B ) ) =>
% 5.55/5.76             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 5.55/5.76  thf('21', plain,
% 5.55/5.76      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 5.55/5.76         (~ (v1_funct_1 @ X53)
% 5.55/5.76          | ~ (v1_funct_2 @ X53 @ X54 @ X55)
% 5.55/5.76          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X55)))
% 5.55/5.76          | ~ (r2_relset_1 @ X54 @ X54 @ 
% 5.55/5.76               (k1_partfun1 @ X54 @ X55 @ X55 @ X54 @ X53 @ X56) @ 
% 5.55/5.76               (k6_partfun1 @ X54))
% 5.55/5.76          | ((k2_relset_1 @ X55 @ X54 @ X56) = (X54))
% 5.55/5.76          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X54)))
% 5.55/5.76          | ~ (v1_funct_2 @ X56 @ X55 @ X54)
% 5.55/5.76          | ~ (v1_funct_1 @ X56))),
% 5.55/5.76      inference('cnf', [status(esa)], [t24_funct_2])).
% 5.55/5.76  thf('22', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         (~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A_1)
% 5.55/5.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))
% 5.55/5.76          | ((k2_relset_1 @ sk_B @ sk_A_1 @ X0) = (sk_A_1))
% 5.55/5.76          | ~ (r2_relset_1 @ sk_A_1 @ sk_A_1 @ 
% 5.55/5.76               (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ X0) @ 
% 5.55/5.76               (k6_partfun1 @ sk_A_1))
% 5.55/5.76          | ~ (v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)
% 5.55/5.76          | ~ (v1_funct_1 @ sk_C))),
% 5.55/5.76      inference('sup-', [status(thm)], ['20', '21'])).
% 5.55/5.76  thf('23', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('24', plain, ((v1_funct_1 @ sk_C)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('25', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         (~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A_1)
% 5.55/5.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))
% 5.55/5.76          | ((k2_relset_1 @ sk_B @ sk_A_1 @ X0) = (sk_A_1))
% 5.55/5.76          | ~ (r2_relset_1 @ sk_A_1 @ sk_A_1 @ 
% 5.55/5.76               (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ X0) @ 
% 5.55/5.76               (k6_partfun1 @ sk_A_1)))),
% 5.55/5.76      inference('demod', [status(thm)], ['22', '23', '24'])).
% 5.55/5.76  thf('26', plain,
% 5.55/5.76      ((~ (r2_relset_1 @ sk_A_1 @ sk_A_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 5.55/5.76           (k6_partfun1 @ sk_A_1))
% 5.55/5.76        | ((k2_relset_1 @ sk_B @ sk_A_1 @ sk_D) = (sk_A_1))
% 5.55/5.76        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))
% 5.55/5.76        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A_1)
% 5.55/5.76        | ~ (v1_funct_1 @ sk_D))),
% 5.55/5.76      inference('sup-', [status(thm)], ['19', '25'])).
% 5.55/5.76  thf('27', plain,
% 5.55/5.76      ((r2_relset_1 @ sk_A_1 @ sk_A_1 @ 
% 5.55/5.76        (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D) @ 
% 5.55/5.76        (k6_partfun1 @ sk_A_1))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('28', plain,
% 5.55/5.76      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 5.55/5.76         = (k5_relat_1 @ sk_C @ sk_D))),
% 5.55/5.76      inference('demod', [status(thm)], ['17', '18'])).
% 5.55/5.76  thf('29', plain,
% 5.55/5.76      ((r2_relset_1 @ sk_A_1 @ sk_A_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 5.55/5.76        (k6_partfun1 @ sk_A_1))),
% 5.55/5.76      inference('demod', [status(thm)], ['27', '28'])).
% 5.55/5.76  thf('30', plain,
% 5.55/5.76      (((k2_relset_1 @ sk_B @ sk_A_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 5.55/5.76      inference('sup-', [status(thm)], ['3', '4'])).
% 5.55/5.76  thf('31', plain,
% 5.55/5.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('32', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A_1)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('33', plain, ((v1_funct_1 @ sk_D)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('34', plain, (((k2_relat_1 @ sk_D) = (sk_A_1))),
% 5.55/5.76      inference('demod', [status(thm)], ['26', '29', '30', '31', '32', '33'])).
% 5.55/5.76  thf('35', plain,
% 5.55/5.76      ((((sk_A_1) != (sk_A_1))
% 5.55/5.76        | ~ (v2_funct_1 @ sk_D)
% 5.55/5.76        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 5.55/5.76      inference('demod', [status(thm)], ['10', '34'])).
% 5.55/5.76  thf('36', plain,
% 5.55/5.76      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 5.55/5.76        | ~ (v2_funct_1 @ sk_D))),
% 5.55/5.76      inference('simplify', [status(thm)], ['35'])).
% 5.55/5.76  thf('37', plain,
% 5.55/5.76      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 5.55/5.76         = (k5_relat_1 @ sk_C @ sk_D))),
% 5.55/5.76      inference('demod', [status(thm)], ['17', '18'])).
% 5.55/5.76  thf('38', plain,
% 5.55/5.76      ((r2_relset_1 @ sk_A_1 @ sk_A_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 5.55/5.76        (k6_partfun1 @ sk_A_1))),
% 5.55/5.76      inference('demod', [status(thm)], ['27', '28'])).
% 5.55/5.76  thf('39', plain,
% 5.55/5.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('40', plain,
% 5.55/5.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf(dt_k1_partfun1, axiom,
% 5.55/5.76    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 5.55/5.76     ( ( ( v1_funct_1 @ E ) & 
% 5.55/5.76         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.55/5.76         ( v1_funct_1 @ F ) & 
% 5.55/5.76         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 5.55/5.76       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 5.55/5.76         ( m1_subset_1 @
% 5.55/5.76           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 5.55/5.76           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 5.55/5.76  thf('41', plain,
% 5.55/5.76      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 5.55/5.76         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 5.55/5.76          | ~ (v1_funct_1 @ X38)
% 5.55/5.76          | ~ (v1_funct_1 @ X41)
% 5.55/5.76          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 5.55/5.76          | (m1_subset_1 @ (k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41) @ 
% 5.55/5.76             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X43))))),
% 5.55/5.76      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 5.55/5.76  thf('42', plain,
% 5.55/5.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.55/5.76         ((m1_subset_1 @ (k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 5.55/5.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ X0)))
% 5.55/5.76          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 5.55/5.76          | ~ (v1_funct_1 @ X1)
% 5.55/5.76          | ~ (v1_funct_1 @ sk_C))),
% 5.55/5.76      inference('sup-', [status(thm)], ['40', '41'])).
% 5.55/5.76  thf('43', plain, ((v1_funct_1 @ sk_C)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('44', plain,
% 5.55/5.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.55/5.76         ((m1_subset_1 @ (k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 5.55/5.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ X0)))
% 5.55/5.76          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 5.55/5.76          | ~ (v1_funct_1 @ X1))),
% 5.55/5.76      inference('demod', [status(thm)], ['42', '43'])).
% 5.55/5.76  thf('45', plain,
% 5.55/5.76      ((~ (v1_funct_1 @ sk_D)
% 5.55/5.76        | (m1_subset_1 @ 
% 5.55/5.76           (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D) @ 
% 5.55/5.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_A_1))))),
% 5.55/5.76      inference('sup-', [status(thm)], ['39', '44'])).
% 5.55/5.76  thf('46', plain, ((v1_funct_1 @ sk_D)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('47', plain,
% 5.55/5.76      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 5.55/5.76         = (k5_relat_1 @ sk_C @ sk_D))),
% 5.55/5.76      inference('demod', [status(thm)], ['17', '18'])).
% 5.55/5.76  thf('48', plain,
% 5.55/5.76      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 5.55/5.76        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_A_1)))),
% 5.55/5.76      inference('demod', [status(thm)], ['45', '46', '47'])).
% 5.55/5.76  thf(redefinition_r2_relset_1, axiom,
% 5.55/5.76    (![A:$i,B:$i,C:$i,D:$i]:
% 5.55/5.76     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.55/5.76         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.55/5.76       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 5.55/5.76  thf('49', plain,
% 5.55/5.76      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 5.55/5.76         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 5.55/5.76          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 5.55/5.76          | ((X34) = (X37))
% 5.55/5.76          | ~ (r2_relset_1 @ X35 @ X36 @ X34 @ X37))),
% 5.55/5.76      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 5.55/5.76  thf('50', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         (~ (r2_relset_1 @ sk_A_1 @ sk_A_1 @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 5.55/5.76          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 5.55/5.76          | ~ (m1_subset_1 @ X0 @ 
% 5.55/5.76               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_A_1))))),
% 5.55/5.76      inference('sup-', [status(thm)], ['48', '49'])).
% 5.55/5.76  thf('51', plain,
% 5.55/5.76      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A_1) @ 
% 5.55/5.76           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_A_1)))
% 5.55/5.76        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A_1)))),
% 5.55/5.76      inference('sup-', [status(thm)], ['38', '50'])).
% 5.55/5.76  thf(dt_k6_partfun1, axiom,
% 5.55/5.76    (![A:$i]:
% 5.55/5.76     ( ( m1_subset_1 @
% 5.55/5.76         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 5.55/5.76       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 5.55/5.76  thf('52', plain,
% 5.55/5.76      (![X45 : $i]:
% 5.55/5.76         (m1_subset_1 @ (k6_partfun1 @ X45) @ 
% 5.55/5.76          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X45)))),
% 5.55/5.76      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 5.55/5.76  thf('53', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A_1))),
% 5.55/5.76      inference('demod', [status(thm)], ['51', '52'])).
% 5.55/5.76  thf('54', plain,
% 5.55/5.76      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 5.55/5.76         = (k6_partfun1 @ sk_A_1))),
% 5.55/5.76      inference('demod', [status(thm)], ['37', '53'])).
% 5.55/5.76  thf('55', plain,
% 5.55/5.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf(t30_funct_2, axiom,
% 5.55/5.76    (![A:$i,B:$i,C:$i,D:$i]:
% 5.55/5.76     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.55/5.76         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 5.55/5.76       ( ![E:$i]:
% 5.55/5.76         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 5.55/5.76             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 5.55/5.76           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 5.55/5.76               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 5.55/5.76             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 5.55/5.76               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 5.55/5.76  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 5.55/5.76  thf(zf_stmt_2, axiom,
% 5.55/5.76    (![C:$i,B:$i]:
% 5.55/5.76     ( ( zip_tseitin_1 @ C @ B ) =>
% 5.55/5.76       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 5.55/5.76  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 5.55/5.76  thf(zf_stmt_4, axiom,
% 5.55/5.76    (![E:$i,D:$i]:
% 5.55/5.76     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 5.55/5.76  thf(zf_stmt_5, axiom,
% 5.55/5.76    (![A:$i,B:$i,C:$i,D:$i]:
% 5.55/5.76     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 5.55/5.76         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.55/5.76       ( ![E:$i]:
% 5.55/5.76         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 5.55/5.76             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 5.55/5.76           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 5.55/5.76               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 5.55/5.76             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 5.55/5.76  thf('56', plain,
% 5.55/5.76      (![X61 : $i, X62 : $i, X63 : $i, X64 : $i, X65 : $i]:
% 5.55/5.76         (~ (v1_funct_1 @ X61)
% 5.55/5.76          | ~ (v1_funct_2 @ X61 @ X62 @ X63)
% 5.55/5.76          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X62 @ X63)))
% 5.55/5.76          | (zip_tseitin_0 @ X61 @ X64)
% 5.55/5.76          | ~ (v2_funct_1 @ (k1_partfun1 @ X65 @ X62 @ X62 @ X63 @ X64 @ X61))
% 5.55/5.76          | (zip_tseitin_1 @ X63 @ X62)
% 5.55/5.76          | ((k2_relset_1 @ X65 @ X62 @ X64) != (X62))
% 5.55/5.76          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X65 @ X62)))
% 5.55/5.76          | ~ (v1_funct_2 @ X64 @ X65 @ X62)
% 5.55/5.76          | ~ (v1_funct_1 @ X64))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.55/5.76  thf('57', plain,
% 5.55/5.76      (![X0 : $i, X1 : $i]:
% 5.55/5.76         (~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 5.55/5.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 5.55/5.76          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 5.55/5.76          | (zip_tseitin_1 @ sk_A_1 @ sk_B)
% 5.55/5.76          | ~ (v2_funct_1 @ 
% 5.55/5.76               (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A_1 @ X0 @ sk_D))
% 5.55/5.76          | (zip_tseitin_0 @ sk_D @ X0)
% 5.55/5.76          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A_1)
% 5.55/5.76          | ~ (v1_funct_1 @ sk_D))),
% 5.55/5.76      inference('sup-', [status(thm)], ['55', '56'])).
% 5.55/5.76  thf('58', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A_1)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('59', plain, ((v1_funct_1 @ sk_D)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('60', plain,
% 5.55/5.76      (![X0 : $i, X1 : $i]:
% 5.55/5.76         (~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 5.55/5.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 5.55/5.76          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 5.55/5.76          | (zip_tseitin_1 @ sk_A_1 @ sk_B)
% 5.55/5.76          | ~ (v2_funct_1 @ 
% 5.55/5.76               (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A_1 @ X0 @ sk_D))
% 5.55/5.76          | (zip_tseitin_0 @ sk_D @ X0))),
% 5.55/5.76      inference('demod', [status(thm)], ['57', '58', '59'])).
% 5.55/5.76  thf('61', plain,
% 5.55/5.76      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A_1))
% 5.55/5.76        | (zip_tseitin_0 @ sk_D @ sk_C)
% 5.55/5.76        | (zip_tseitin_1 @ sk_A_1 @ sk_B)
% 5.55/5.76        | ((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) != (sk_B))
% 5.55/5.76        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))
% 5.55/5.76        | ~ (v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)
% 5.55/5.76        | ~ (v1_funct_1 @ sk_C))),
% 5.55/5.76      inference('sup-', [status(thm)], ['54', '60'])).
% 5.55/5.76  thf(fc4_funct_1, axiom,
% 5.55/5.76    (![A:$i]:
% 5.55/5.76     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 5.55/5.76       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 5.55/5.76  thf('62', plain, (![X20 : $i]: (v2_funct_1 @ (k6_relat_1 @ X20))),
% 5.55/5.76      inference('cnf', [status(esa)], [fc4_funct_1])).
% 5.55/5.76  thf(redefinition_k6_partfun1, axiom,
% 5.55/5.76    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 5.55/5.76  thf('63', plain, (![X52 : $i]: ((k6_partfun1 @ X52) = (k6_relat_1 @ X52))),
% 5.55/5.76      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.55/5.76  thf('64', plain, (![X20 : $i]: (v2_funct_1 @ (k6_partfun1 @ X20))),
% 5.55/5.76      inference('demod', [status(thm)], ['62', '63'])).
% 5.55/5.76  thf('65', plain, (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (sk_B))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('66', plain,
% 5.55/5.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('67', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('68', plain, ((v1_funct_1 @ sk_C)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('69', plain,
% 5.55/5.76      (((zip_tseitin_0 @ sk_D @ sk_C)
% 5.55/5.76        | (zip_tseitin_1 @ sk_A_1 @ sk_B)
% 5.55/5.76        | ((sk_B) != (sk_B)))),
% 5.55/5.76      inference('demod', [status(thm)], ['61', '64', '65', '66', '67', '68'])).
% 5.55/5.76  thf('70', plain,
% 5.55/5.76      (((zip_tseitin_1 @ sk_A_1 @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 5.55/5.76      inference('simplify', [status(thm)], ['69'])).
% 5.55/5.76  thf('71', plain,
% 5.55/5.76      (![X59 : $i, X60 : $i]:
% 5.55/5.76         (((X59) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X59 @ X60))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.55/5.76  thf('72', plain,
% 5.55/5.76      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A_1) = (k1_xboole_0)))),
% 5.55/5.76      inference('sup-', [status(thm)], ['70', '71'])).
% 5.55/5.76  thf('73', plain, (((sk_A_1) != (k1_xboole_0))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('74', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 5.55/5.76      inference('simplify_reflect-', [status(thm)], ['72', '73'])).
% 5.55/5.76  thf('75', plain,
% 5.55/5.76      (![X57 : $i, X58 : $i]:
% 5.55/5.76         ((v2_funct_1 @ X58) | ~ (zip_tseitin_0 @ X58 @ X57))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_4])).
% 5.55/5.76  thf('76', plain, ((v2_funct_1 @ sk_D)),
% 5.55/5.76      inference('sup-', [status(thm)], ['74', '75'])).
% 5.55/5.76  thf('77', plain,
% 5.55/5.76      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 5.55/5.76      inference('demod', [status(thm)], ['36', '76'])).
% 5.55/5.76  thf('78', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A_1))),
% 5.55/5.76      inference('demod', [status(thm)], ['51', '52'])).
% 5.55/5.76  thf(t64_funct_1, axiom,
% 5.55/5.76    (![A:$i]:
% 5.55/5.76     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.55/5.76       ( ![B:$i]:
% 5.55/5.76         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 5.55/5.76           ( ( ( v2_funct_1 @ A ) & 
% 5.55/5.76               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 5.55/5.76               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 5.55/5.76             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 5.55/5.76  thf('79', plain,
% 5.55/5.76      (![X23 : $i, X24 : $i]:
% 5.55/5.76         (~ (v1_relat_1 @ X23)
% 5.55/5.76          | ~ (v1_funct_1 @ X23)
% 5.55/5.76          | ((X23) = (k2_funct_1 @ X24))
% 5.55/5.76          | ((k5_relat_1 @ X23 @ X24) != (k6_relat_1 @ (k2_relat_1 @ X24)))
% 5.55/5.76          | ((k2_relat_1 @ X23) != (k1_relat_1 @ X24))
% 5.55/5.76          | ~ (v2_funct_1 @ X24)
% 5.55/5.76          | ~ (v1_funct_1 @ X24)
% 5.55/5.76          | ~ (v1_relat_1 @ X24))),
% 5.55/5.76      inference('cnf', [status(esa)], [t64_funct_1])).
% 5.55/5.76  thf('80', plain, (![X52 : $i]: ((k6_partfun1 @ X52) = (k6_relat_1 @ X52))),
% 5.55/5.76      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.55/5.76  thf('81', plain,
% 5.55/5.76      (![X23 : $i, X24 : $i]:
% 5.55/5.76         (~ (v1_relat_1 @ X23)
% 5.55/5.76          | ~ (v1_funct_1 @ X23)
% 5.55/5.76          | ((X23) = (k2_funct_1 @ X24))
% 5.55/5.76          | ((k5_relat_1 @ X23 @ X24) != (k6_partfun1 @ (k2_relat_1 @ X24)))
% 5.55/5.76          | ((k2_relat_1 @ X23) != (k1_relat_1 @ X24))
% 5.55/5.76          | ~ (v2_funct_1 @ X24)
% 5.55/5.76          | ~ (v1_funct_1 @ X24)
% 5.55/5.76          | ~ (v1_relat_1 @ X24))),
% 5.55/5.76      inference('demod', [status(thm)], ['79', '80'])).
% 5.55/5.76  thf('82', plain,
% 5.55/5.76      ((((k6_partfun1 @ sk_A_1) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 5.55/5.76        | ~ (v1_relat_1 @ sk_D)
% 5.55/5.76        | ~ (v1_funct_1 @ sk_D)
% 5.55/5.76        | ~ (v2_funct_1 @ sk_D)
% 5.55/5.76        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 5.55/5.76        | ((sk_C) = (k2_funct_1 @ sk_D))
% 5.55/5.76        | ~ (v1_funct_1 @ sk_C)
% 5.55/5.76        | ~ (v1_relat_1 @ sk_C))),
% 5.55/5.76      inference('sup-', [status(thm)], ['78', '81'])).
% 5.55/5.76  thf('83', plain, (((k2_relat_1 @ sk_D) = (sk_A_1))),
% 5.55/5.76      inference('demod', [status(thm)], ['26', '29', '30', '31', '32', '33'])).
% 5.55/5.76  thf('84', plain,
% 5.55/5.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf(cc2_relat_1, axiom,
% 5.55/5.76    (![A:$i]:
% 5.55/5.76     ( ( v1_relat_1 @ A ) =>
% 5.55/5.76       ( ![B:$i]:
% 5.55/5.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 5.55/5.76  thf('85', plain,
% 5.55/5.76      (![X4 : $i, X5 : $i]:
% 5.55/5.76         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 5.55/5.76          | (v1_relat_1 @ X4)
% 5.55/5.76          | ~ (v1_relat_1 @ X5))),
% 5.55/5.76      inference('cnf', [status(esa)], [cc2_relat_1])).
% 5.55/5.76  thf('86', plain,
% 5.55/5.76      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)) | (v1_relat_1 @ sk_D))),
% 5.55/5.76      inference('sup-', [status(thm)], ['84', '85'])).
% 5.55/5.76  thf(fc6_relat_1, axiom,
% 5.55/5.76    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 5.55/5.76  thf('87', plain,
% 5.55/5.76      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 5.55/5.76      inference('cnf', [status(esa)], [fc6_relat_1])).
% 5.55/5.76  thf('88', plain, ((v1_relat_1 @ sk_D)),
% 5.55/5.76      inference('demod', [status(thm)], ['86', '87'])).
% 5.55/5.76  thf('89', plain, ((v1_funct_1 @ sk_D)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('90', plain,
% 5.55/5.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('91', plain,
% 5.55/5.76      (![X31 : $i, X32 : $i, X33 : $i]:
% 5.55/5.76         (((k2_relset_1 @ X32 @ X33 @ X31) = (k2_relat_1 @ X31))
% 5.55/5.76          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 5.55/5.76      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 5.55/5.76  thf('92', plain,
% 5.55/5.76      (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 5.55/5.76      inference('sup-', [status(thm)], ['90', '91'])).
% 5.55/5.76  thf('93', plain, (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (sk_B))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('94', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 5.55/5.76      inference('sup+', [status(thm)], ['92', '93'])).
% 5.55/5.76  thf('95', plain, ((v1_funct_1 @ sk_C)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('96', plain,
% 5.55/5.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('97', plain,
% 5.55/5.76      (![X4 : $i, X5 : $i]:
% 5.55/5.76         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 5.55/5.76          | (v1_relat_1 @ X4)
% 5.55/5.76          | ~ (v1_relat_1 @ X5))),
% 5.55/5.76      inference('cnf', [status(esa)], [cc2_relat_1])).
% 5.55/5.76  thf('98', plain,
% 5.55/5.76      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)) | (v1_relat_1 @ sk_C))),
% 5.55/5.76      inference('sup-', [status(thm)], ['96', '97'])).
% 5.55/5.76  thf('99', plain,
% 5.55/5.76      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 5.55/5.76      inference('cnf', [status(esa)], [fc6_relat_1])).
% 5.55/5.76  thf('100', plain, ((v1_relat_1 @ sk_C)),
% 5.55/5.76      inference('demod', [status(thm)], ['98', '99'])).
% 5.55/5.76  thf('101', plain,
% 5.55/5.76      ((((k6_partfun1 @ sk_A_1) != (k6_partfun1 @ sk_A_1))
% 5.55/5.76        | ~ (v2_funct_1 @ sk_D)
% 5.55/5.76        | ((sk_B) != (k1_relat_1 @ sk_D))
% 5.55/5.76        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 5.55/5.76      inference('demod', [status(thm)],
% 5.55/5.76                ['82', '83', '88', '89', '94', '95', '100'])).
% 5.55/5.76  thf('102', plain,
% 5.55/5.76      ((((sk_C) = (k2_funct_1 @ sk_D))
% 5.55/5.76        | ((sk_B) != (k1_relat_1 @ sk_D))
% 5.55/5.76        | ~ (v2_funct_1 @ sk_D))),
% 5.55/5.76      inference('simplify', [status(thm)], ['101'])).
% 5.55/5.76  thf('103', plain, ((v2_funct_1 @ sk_D)),
% 5.55/5.76      inference('sup-', [status(thm)], ['74', '75'])).
% 5.55/5.76  thf('104', plain,
% 5.55/5.76      ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (k1_relat_1 @ sk_D)))),
% 5.55/5.76      inference('demod', [status(thm)], ['102', '103'])).
% 5.55/5.76  thf(dt_k2_funct_1, axiom,
% 5.55/5.76    (![A:$i]:
% 5.55/5.76     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.55/5.76       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 5.55/5.76         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 5.55/5.76  thf('105', plain,
% 5.55/5.76      (![X16 : $i]:
% 5.55/5.76         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 5.55/5.76          | ~ (v1_funct_1 @ X16)
% 5.55/5.76          | ~ (v1_relat_1 @ X16))),
% 5.55/5.76      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 5.55/5.76  thf('106', plain,
% 5.55/5.76      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 5.55/5.76      inference('demod', [status(thm)], ['36', '76'])).
% 5.55/5.76  thf(t45_relat_1, axiom,
% 5.55/5.76    (![A:$i]:
% 5.55/5.76     ( ( v1_relat_1 @ A ) =>
% 5.55/5.76       ( ![B:$i]:
% 5.55/5.76         ( ( v1_relat_1 @ B ) =>
% 5.55/5.76           ( r1_tarski @
% 5.55/5.76             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 5.55/5.76  thf('107', plain,
% 5.55/5.76      (![X10 : $i, X11 : $i]:
% 5.55/5.76         (~ (v1_relat_1 @ X10)
% 5.55/5.76          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X11 @ X10)) @ 
% 5.55/5.76             (k2_relat_1 @ X10))
% 5.55/5.76          | ~ (v1_relat_1 @ X11))),
% 5.55/5.76      inference('cnf', [status(esa)], [t45_relat_1])).
% 5.55/5.76  thf(d10_xboole_0, axiom,
% 5.55/5.76    (![A:$i,B:$i]:
% 5.55/5.76     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.55/5.76  thf('108', plain,
% 5.55/5.76      (![X1 : $i, X3 : $i]:
% 5.55/5.76         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 5.55/5.76      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.55/5.76  thf('109', plain,
% 5.55/5.76      (![X0 : $i, X1 : $i]:
% 5.55/5.76         (~ (v1_relat_1 @ X1)
% 5.55/5.76          | ~ (v1_relat_1 @ X0)
% 5.55/5.76          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 5.55/5.76               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 5.55/5.76          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 5.55/5.76      inference('sup-', [status(thm)], ['107', '108'])).
% 5.55/5.76  thf('110', plain,
% 5.55/5.76      ((~ (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_D)) @ 
% 5.55/5.76           (k2_relat_1 @ (k6_partfun1 @ sk_B)))
% 5.55/5.76        | ((k2_relat_1 @ (k2_funct_1 @ sk_D))
% 5.55/5.76            = (k2_relat_1 @ (k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D))))
% 5.55/5.76        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D))
% 5.55/5.76        | ~ (v1_relat_1 @ sk_D))),
% 5.55/5.76      inference('sup-', [status(thm)], ['106', '109'])).
% 5.55/5.76  thf(fc6_funct_1, axiom,
% 5.55/5.76    (![A:$i]:
% 5.55/5.76     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 5.55/5.76       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 5.55/5.76         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 5.55/5.76         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 5.55/5.76  thf('111', plain,
% 5.55/5.76      (![X21 : $i]:
% 5.55/5.76         ((v2_funct_1 @ (k2_funct_1 @ X21))
% 5.55/5.76          | ~ (v2_funct_1 @ X21)
% 5.55/5.76          | ~ (v1_funct_1 @ X21)
% 5.55/5.76          | ~ (v1_relat_1 @ X21))),
% 5.55/5.76      inference('cnf', [status(esa)], [fc6_funct_1])).
% 5.55/5.76  thf('112', plain,
% 5.55/5.76      (![X16 : $i]:
% 5.55/5.76         ((v1_funct_1 @ (k2_funct_1 @ X16))
% 5.55/5.76          | ~ (v1_funct_1 @ X16)
% 5.55/5.76          | ~ (v1_relat_1 @ X16))),
% 5.55/5.76      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 5.55/5.76  thf('113', plain,
% 5.55/5.76      (![X16 : $i]:
% 5.55/5.76         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 5.55/5.76          | ~ (v1_funct_1 @ X16)
% 5.55/5.76          | ~ (v1_relat_1 @ X16))),
% 5.55/5.76      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 5.55/5.76  thf('114', plain,
% 5.55/5.76      (![X21 : $i]:
% 5.55/5.76         ((v2_funct_1 @ (k2_funct_1 @ X21))
% 5.55/5.76          | ~ (v2_funct_1 @ X21)
% 5.55/5.76          | ~ (v1_funct_1 @ X21)
% 5.55/5.76          | ~ (v1_relat_1 @ X21))),
% 5.55/5.76      inference('cnf', [status(esa)], [fc6_funct_1])).
% 5.55/5.76  thf('115', plain,
% 5.55/5.76      (![X16 : $i]:
% 5.55/5.76         ((v1_funct_1 @ (k2_funct_1 @ X16))
% 5.55/5.76          | ~ (v1_funct_1 @ X16)
% 5.55/5.76          | ~ (v1_relat_1 @ X16))),
% 5.55/5.76      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 5.55/5.76  thf('116', plain,
% 5.55/5.76      (![X16 : $i]:
% 5.55/5.76         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 5.55/5.76          | ~ (v1_funct_1 @ X16)
% 5.55/5.76          | ~ (v1_relat_1 @ X16))),
% 5.55/5.76      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 5.55/5.76  thf(t55_funct_1, axiom,
% 5.55/5.76    (![A:$i]:
% 5.55/5.76     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.55/5.76       ( ( v2_funct_1 @ A ) =>
% 5.55/5.76         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 5.55/5.76           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 5.55/5.76  thf('117', plain,
% 5.55/5.76      (![X22 : $i]:
% 5.55/5.76         (~ (v2_funct_1 @ X22)
% 5.55/5.76          | ((k1_relat_1 @ X22) = (k2_relat_1 @ (k2_funct_1 @ X22)))
% 5.55/5.76          | ~ (v1_funct_1 @ X22)
% 5.55/5.76          | ~ (v1_relat_1 @ X22))),
% 5.55/5.76      inference('cnf', [status(esa)], [t55_funct_1])).
% 5.55/5.76  thf('118', plain,
% 5.55/5.76      (![X22 : $i]:
% 5.55/5.76         (~ (v2_funct_1 @ X22)
% 5.55/5.76          | ((k2_relat_1 @ X22) = (k1_relat_1 @ (k2_funct_1 @ X22)))
% 5.55/5.76          | ~ (v1_funct_1 @ X22)
% 5.55/5.76          | ~ (v1_relat_1 @ X22))),
% 5.55/5.76      inference('cnf', [status(esa)], [t55_funct_1])).
% 5.55/5.76  thf('119', plain,
% 5.55/5.76      (![X16 : $i]:
% 5.55/5.76         ((v1_funct_1 @ (k2_funct_1 @ X16))
% 5.55/5.76          | ~ (v1_funct_1 @ X16)
% 5.55/5.76          | ~ (v1_relat_1 @ X16))),
% 5.55/5.76      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 5.55/5.76  thf('120', plain,
% 5.55/5.76      (![X16 : $i]:
% 5.55/5.76         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 5.55/5.76          | ~ (v1_funct_1 @ X16)
% 5.55/5.76          | ~ (v1_relat_1 @ X16))),
% 5.55/5.76      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 5.55/5.76  thf('121', plain,
% 5.55/5.76      (![X16 : $i]:
% 5.55/5.76         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 5.55/5.76          | ~ (v1_funct_1 @ X16)
% 5.55/5.76          | ~ (v1_relat_1 @ X16))),
% 5.55/5.76      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 5.55/5.76  thf('122', plain,
% 5.55/5.76      (![X21 : $i]:
% 5.55/5.76         ((v2_funct_1 @ (k2_funct_1 @ X21))
% 5.55/5.76          | ~ (v2_funct_1 @ X21)
% 5.55/5.76          | ~ (v1_funct_1 @ X21)
% 5.55/5.76          | ~ (v1_relat_1 @ X21))),
% 5.55/5.76      inference('cnf', [status(esa)], [fc6_funct_1])).
% 5.55/5.76  thf('123', plain,
% 5.55/5.76      (![X16 : $i]:
% 5.55/5.76         ((v1_funct_1 @ (k2_funct_1 @ X16))
% 5.55/5.76          | ~ (v1_funct_1 @ X16)
% 5.55/5.76          | ~ (v1_relat_1 @ X16))),
% 5.55/5.76      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 5.55/5.76  thf('124', plain,
% 5.55/5.76      (![X16 : $i]:
% 5.55/5.76         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 5.55/5.76          | ~ (v1_funct_1 @ X16)
% 5.55/5.76          | ~ (v1_relat_1 @ X16))),
% 5.55/5.76      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 5.55/5.76  thf('125', plain,
% 5.55/5.76      (![X22 : $i]:
% 5.55/5.76         (~ (v2_funct_1 @ X22)
% 5.55/5.76          | ((k1_relat_1 @ X22) = (k2_relat_1 @ (k2_funct_1 @ X22)))
% 5.55/5.76          | ~ (v1_funct_1 @ X22)
% 5.55/5.76          | ~ (v1_relat_1 @ X22))),
% 5.55/5.76      inference('cnf', [status(esa)], [t55_funct_1])).
% 5.55/5.76  thf('126', plain,
% 5.55/5.76      (![X16 : $i]:
% 5.55/5.76         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 5.55/5.76          | ~ (v1_funct_1 @ X16)
% 5.55/5.76          | ~ (v1_relat_1 @ X16))),
% 5.55/5.76      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 5.55/5.76  thf('127', plain,
% 5.55/5.76      (![X22 : $i]:
% 5.55/5.76         (~ (v2_funct_1 @ X22)
% 5.55/5.76          | ((k2_relat_1 @ X22) = (k1_relat_1 @ (k2_funct_1 @ X22)))
% 5.55/5.76          | ~ (v1_funct_1 @ X22)
% 5.55/5.76          | ~ (v1_relat_1 @ X22))),
% 5.55/5.76      inference('cnf', [status(esa)], [t55_funct_1])).
% 5.55/5.76  thf('128', plain,
% 5.55/5.76      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 5.55/5.76      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.55/5.76  thf('129', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 5.55/5.76      inference('simplify', [status(thm)], ['128'])).
% 5.55/5.76  thf(d18_relat_1, axiom,
% 5.55/5.76    (![A:$i,B:$i]:
% 5.55/5.76     ( ( v1_relat_1 @ B ) =>
% 5.55/5.76       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 5.55/5.76  thf('130', plain,
% 5.55/5.76      (![X6 : $i, X7 : $i]:
% 5.55/5.76         (~ (r1_tarski @ (k1_relat_1 @ X6) @ X7)
% 5.55/5.76          | (v4_relat_1 @ X6 @ X7)
% 5.55/5.76          | ~ (v1_relat_1 @ X6))),
% 5.55/5.76      inference('cnf', [status(esa)], [d18_relat_1])).
% 5.55/5.76  thf('131', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 5.55/5.76      inference('sup-', [status(thm)], ['129', '130'])).
% 5.55/5.76  thf('132', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 5.55/5.76          | ~ (v1_relat_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 5.55/5.76      inference('sup+', [status(thm)], ['127', '131'])).
% 5.55/5.76  thf('133', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         (~ (v1_relat_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ X0)
% 5.55/5.76          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 5.55/5.76      inference('sup-', [status(thm)], ['126', '132'])).
% 5.55/5.76  thf('134', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ X0))),
% 5.55/5.76      inference('simplify', [status(thm)], ['133'])).
% 5.55/5.76  thf('135', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 5.55/5.76          | ~ (v1_relat_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 5.55/5.76          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 5.55/5.76          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 5.55/5.76      inference('sup+', [status(thm)], ['125', '134'])).
% 5.55/5.76  thf('136', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         (~ (v1_relat_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 5.55/5.76          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ X0)
% 5.55/5.76          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 5.55/5.76      inference('sup-', [status(thm)], ['124', '135'])).
% 5.55/5.76  thf('137', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 5.55/5.76          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ X0))),
% 5.55/5.76      inference('simplify', [status(thm)], ['136'])).
% 5.55/5.76  thf('138', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         (~ (v1_relat_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 5.55/5.76      inference('sup-', [status(thm)], ['123', '137'])).
% 5.55/5.76  thf('139', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ X0))),
% 5.55/5.76      inference('simplify', [status(thm)], ['138'])).
% 5.55/5.76  thf('140', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         (~ (v1_relat_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 5.55/5.76      inference('sup-', [status(thm)], ['122', '139'])).
% 5.55/5.76  thf('141', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ X0))),
% 5.55/5.76      inference('simplify', [status(thm)], ['140'])).
% 5.55/5.76  thf('142', plain,
% 5.55/5.76      (![X6 : $i, X7 : $i]:
% 5.55/5.76         (~ (v4_relat_1 @ X6 @ X7)
% 5.55/5.76          | (r1_tarski @ (k1_relat_1 @ X6) @ X7)
% 5.55/5.76          | ~ (v1_relat_1 @ X6))),
% 5.55/5.76      inference('cnf', [status(esa)], [d18_relat_1])).
% 5.55/5.76  thf('143', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         (~ (v1_relat_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 5.55/5.76          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 5.55/5.76             (k1_relat_1 @ X0)))),
% 5.55/5.76      inference('sup-', [status(thm)], ['141', '142'])).
% 5.55/5.76  thf('144', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 5.55/5.76          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 5.55/5.76          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 5.55/5.76             (k1_relat_1 @ X0))
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ X0))),
% 5.55/5.76      inference('sup-', [status(thm)], ['121', '143'])).
% 5.55/5.76  thf('145', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         (~ (v1_relat_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 5.55/5.76             (k1_relat_1 @ X0))
% 5.55/5.76          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 5.55/5.76      inference('sup-', [status(thm)], ['120', '144'])).
% 5.55/5.76  thf('146', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 5.55/5.76          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 5.55/5.76             (k1_relat_1 @ X0))
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ X0))),
% 5.55/5.76      inference('simplify', [status(thm)], ['145'])).
% 5.55/5.76  thf('147', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         (~ (v1_relat_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 5.55/5.76             (k1_relat_1 @ X0)))),
% 5.55/5.76      inference('sup-', [status(thm)], ['119', '146'])).
% 5.55/5.76  thf('148', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 5.55/5.76           (k1_relat_1 @ X0))
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ X0))),
% 5.55/5.76      inference('simplify', [status(thm)], ['147'])).
% 5.55/5.76  thf('149', plain,
% 5.55/5.76      (![X1 : $i, X3 : $i]:
% 5.55/5.76         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 5.55/5.76      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.55/5.76  thf('150', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         (~ (v1_relat_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ 
% 5.55/5.76               (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 5.55/5.76          | ((k1_relat_1 @ X0)
% 5.55/5.76              = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 5.55/5.76      inference('sup-', [status(thm)], ['148', '149'])).
% 5.55/5.76  thf('151', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         (~ (r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 5.55/5.76          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 5.55/5.76          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 5.55/5.76          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 5.55/5.76          | ((k1_relat_1 @ X0)
% 5.55/5.76              = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ X0))),
% 5.55/5.76      inference('sup-', [status(thm)], ['118', '150'])).
% 5.55/5.76  thf('152', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         (~ (r1_tarski @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 5.55/5.76          | ~ (v1_relat_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ((k1_relat_1 @ X0)
% 5.55/5.76              = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 5.55/5.76          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 5.55/5.76          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 5.55/5.76          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 5.55/5.76      inference('sup-', [status(thm)], ['117', '151'])).
% 5.55/5.76  thf('153', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 5.55/5.76      inference('simplify', [status(thm)], ['128'])).
% 5.55/5.76  thf('154', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         (~ (v1_relat_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ((k1_relat_1 @ X0)
% 5.55/5.76              = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 5.55/5.76          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 5.55/5.76          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 5.55/5.76          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 5.55/5.76      inference('demod', [status(thm)], ['152', '153'])).
% 5.55/5.76  thf('155', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 5.55/5.76          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 5.55/5.76          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 5.55/5.76          | ((k1_relat_1 @ X0)
% 5.55/5.76              = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ X0))),
% 5.55/5.76      inference('simplify', [status(thm)], ['154'])).
% 5.55/5.76  thf('156', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         (~ (v1_relat_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ((k1_relat_1 @ X0)
% 5.55/5.76              = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 5.55/5.76          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 5.55/5.76          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 5.55/5.76      inference('sup-', [status(thm)], ['116', '155'])).
% 5.55/5.76  thf('157', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 5.55/5.76          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 5.55/5.76          | ((k1_relat_1 @ X0)
% 5.55/5.76              = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ X0))),
% 5.55/5.76      inference('simplify', [status(thm)], ['156'])).
% 5.55/5.76  thf('158', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         (~ (v1_relat_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ((k1_relat_1 @ X0)
% 5.55/5.76              = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 5.55/5.76          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 5.55/5.76      inference('sup-', [status(thm)], ['115', '157'])).
% 5.55/5.76  thf('159', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         (~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 5.55/5.76          | ((k1_relat_1 @ X0)
% 5.55/5.76              = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ X0))),
% 5.55/5.76      inference('simplify', [status(thm)], ['158'])).
% 5.55/5.76  thf('160', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         (~ (v1_relat_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ((k1_relat_1 @ X0)
% 5.55/5.76              = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 5.55/5.76      inference('sup-', [status(thm)], ['114', '159'])).
% 5.55/5.76  thf('161', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         (((k1_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ X0))),
% 5.55/5.76      inference('simplify', [status(thm)], ['160'])).
% 5.55/5.76  thf('162', plain,
% 5.55/5.76      (![X16 : $i]:
% 5.55/5.76         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 5.55/5.76          | ~ (v1_funct_1 @ X16)
% 5.55/5.76          | ~ (v1_relat_1 @ X16))),
% 5.55/5.76      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 5.55/5.76  thf('163', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ X0))),
% 5.55/5.76      inference('simplify', [status(thm)], ['133'])).
% 5.55/5.76  thf('164', plain,
% 5.55/5.76      (![X6 : $i, X7 : $i]:
% 5.55/5.76         (~ (v4_relat_1 @ X6 @ X7)
% 5.55/5.76          | (r1_tarski @ (k1_relat_1 @ X6) @ X7)
% 5.55/5.76          | ~ (v1_relat_1 @ X6))),
% 5.55/5.76      inference('cnf', [status(esa)], [d18_relat_1])).
% 5.55/5.76  thf('165', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         (~ (v1_relat_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 5.55/5.76          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0)))),
% 5.55/5.76      inference('sup-', [status(thm)], ['163', '164'])).
% 5.55/5.76  thf('166', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         (~ (v1_relat_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ X0))),
% 5.55/5.76      inference('sup-', [status(thm)], ['162', '165'])).
% 5.55/5.76  thf('167', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         (~ (v2_funct_1 @ X0)
% 5.55/5.76          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ X0))),
% 5.55/5.76      inference('simplify', [status(thm)], ['166'])).
% 5.55/5.76  thf('168', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         ((r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 5.55/5.76          | ~ (v1_relat_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 5.55/5.76          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 5.55/5.76          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 5.55/5.76      inference('sup+', [status(thm)], ['161', '167'])).
% 5.55/5.76  thf('169', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         (~ (v1_relat_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 5.55/5.76          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ X0)
% 5.55/5.76          | (r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 5.55/5.76      inference('sup-', [status(thm)], ['113', '168'])).
% 5.55/5.76  thf('170', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         ((r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 5.55/5.76          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ X0))),
% 5.55/5.76      inference('simplify', [status(thm)], ['169'])).
% 5.55/5.76  thf('171', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         (~ (v1_relat_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | (r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 5.55/5.76      inference('sup-', [status(thm)], ['112', '170'])).
% 5.55/5.76  thf('172', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         ((r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ X0))),
% 5.55/5.76      inference('simplify', [status(thm)], ['171'])).
% 5.55/5.76  thf('173', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         (~ (v1_relat_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | (r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 5.55/5.76      inference('sup-', [status(thm)], ['111', '172'])).
% 5.55/5.76  thf('174', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         ((r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ X0))),
% 5.55/5.76      inference('simplify', [status(thm)], ['173'])).
% 5.55/5.76  thf(t78_relat_1, axiom,
% 5.55/5.76    (![A:$i]:
% 5.55/5.76     ( ( v1_relat_1 @ A ) =>
% 5.55/5.76       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 5.55/5.76  thf('175', plain,
% 5.55/5.76      (![X14 : $i]:
% 5.55/5.76         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X14)) @ X14) = (X14))
% 5.55/5.76          | ~ (v1_relat_1 @ X14))),
% 5.55/5.76      inference('cnf', [status(esa)], [t78_relat_1])).
% 5.55/5.76  thf('176', plain, (![X52 : $i]: ((k6_partfun1 @ X52) = (k6_relat_1 @ X52))),
% 5.55/5.76      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.55/5.76  thf('177', plain,
% 5.55/5.76      (![X14 : $i]:
% 5.55/5.76         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X14)) @ X14) = (X14))
% 5.55/5.76          | ~ (v1_relat_1 @ X14))),
% 5.55/5.76      inference('demod', [status(thm)], ['175', '176'])).
% 5.55/5.76  thf('178', plain,
% 5.55/5.76      (![X14 : $i]:
% 5.55/5.76         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X14)) @ X14) = (X14))
% 5.55/5.76          | ~ (v1_relat_1 @ X14))),
% 5.55/5.76      inference('demod', [status(thm)], ['175', '176'])).
% 5.55/5.76  thf('179', plain,
% 5.55/5.76      (![X14 : $i]:
% 5.55/5.76         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X14)) @ X14) = (X14))
% 5.55/5.76          | ~ (v1_relat_1 @ X14))),
% 5.55/5.76      inference('demod', [status(thm)], ['175', '176'])).
% 5.55/5.76  thf('180', plain, (((k2_relat_1 @ sk_D) = (sk_A_1))),
% 5.55/5.76      inference('demod', [status(thm)], ['26', '29', '30', '31', '32', '33'])).
% 5.55/5.76  thf('181', plain,
% 5.55/5.76      (![X0 : $i, X1 : $i]:
% 5.55/5.76         (~ (v1_relat_1 @ X1)
% 5.55/5.76          | ~ (v1_relat_1 @ X0)
% 5.55/5.76          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 5.55/5.76               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 5.55/5.76          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 5.55/5.76      inference('sup-', [status(thm)], ['107', '108'])).
% 5.55/5.76  thf('182', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         (~ (r1_tarski @ sk_A_1 @ (k2_relat_1 @ (k5_relat_1 @ X0 @ sk_D)))
% 5.55/5.76          | ((k2_relat_1 @ sk_D) = (k2_relat_1 @ (k5_relat_1 @ X0 @ sk_D)))
% 5.55/5.76          | ~ (v1_relat_1 @ sk_D)
% 5.55/5.76          | ~ (v1_relat_1 @ X0))),
% 5.55/5.76      inference('sup-', [status(thm)], ['180', '181'])).
% 5.55/5.76  thf('183', plain, (((k2_relat_1 @ sk_D) = (sk_A_1))),
% 5.55/5.76      inference('demod', [status(thm)], ['26', '29', '30', '31', '32', '33'])).
% 5.55/5.76  thf('184', plain, ((v1_relat_1 @ sk_D)),
% 5.55/5.76      inference('demod', [status(thm)], ['86', '87'])).
% 5.55/5.76  thf('185', plain,
% 5.55/5.76      (![X0 : $i]:
% 5.55/5.76         (~ (r1_tarski @ sk_A_1 @ (k2_relat_1 @ (k5_relat_1 @ X0 @ sk_D)))
% 5.55/5.76          | ((sk_A_1) = (k2_relat_1 @ (k5_relat_1 @ X0 @ sk_D)))
% 5.55/5.76          | ~ (v1_relat_1 @ X0))),
% 5.55/5.76      inference('demod', [status(thm)], ['182', '183', '184'])).
% 5.55/5.76  thf('186', plain,
% 5.55/5.76      ((~ (r1_tarski @ sk_A_1 @ (k2_relat_1 @ sk_D))
% 5.55/5.76        | ~ (v1_relat_1 @ sk_D)
% 5.55/5.76        | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)))
% 5.55/5.76        | ((sk_A_1)
% 5.55/5.76            = (k2_relat_1 @ 
% 5.55/5.76               (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ sk_D))))),
% 5.55/5.76      inference('sup-', [status(thm)], ['179', '185'])).
% 5.55/5.76  thf('187', plain, (((k2_relat_1 @ sk_D) = (sk_A_1))),
% 5.55/5.76      inference('demod', [status(thm)], ['26', '29', '30', '31', '32', '33'])).
% 5.55/5.76  thf('188', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 5.55/5.76      inference('simplify', [status(thm)], ['128'])).
% 5.55/5.76  thf('189', plain, ((v1_relat_1 @ sk_D)),
% 5.55/5.76      inference('demod', [status(thm)], ['86', '87'])).
% 5.55/5.76  thf(fc3_funct_1, axiom,
% 5.55/5.76    (![A:$i]:
% 5.55/5.76     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 5.55/5.76       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 5.55/5.76  thf('190', plain, (![X17 : $i]: (v1_relat_1 @ (k6_relat_1 @ X17))),
% 5.55/5.76      inference('cnf', [status(esa)], [fc3_funct_1])).
% 5.55/5.76  thf('191', plain, (![X52 : $i]: ((k6_partfun1 @ X52) = (k6_relat_1 @ X52))),
% 5.55/5.76      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.55/5.76  thf('192', plain, (![X17 : $i]: (v1_relat_1 @ (k6_partfun1 @ X17))),
% 5.55/5.76      inference('demod', [status(thm)], ['190', '191'])).
% 5.55/5.76  thf('193', plain,
% 5.55/5.76      (((sk_A_1)
% 5.55/5.76         = (k2_relat_1 @ 
% 5.55/5.76            (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ sk_D)))),
% 5.55/5.76      inference('demod', [status(thm)], ['186', '187', '188', '189', '192'])).
% 5.55/5.76  thf(t80_relat_1, axiom,
% 5.55/5.76    (![A:$i]:
% 5.55/5.76     ( ( v1_relat_1 @ A ) =>
% 5.55/5.76       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 5.55/5.76  thf('194', plain,
% 5.55/5.76      (![X15 : $i]:
% 5.55/5.76         (((k5_relat_1 @ X15 @ (k6_relat_1 @ (k2_relat_1 @ X15))) = (X15))
% 5.55/5.76          | ~ (v1_relat_1 @ X15))),
% 5.55/5.76      inference('cnf', [status(esa)], [t80_relat_1])).
% 5.55/5.76  thf('195', plain, (![X52 : $i]: ((k6_partfun1 @ X52) = (k6_relat_1 @ X52))),
% 5.55/5.76      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.55/5.76  thf('196', plain,
% 5.55/5.76      (![X15 : $i]:
% 5.55/5.76         (((k5_relat_1 @ X15 @ (k6_partfun1 @ (k2_relat_1 @ X15))) = (X15))
% 5.55/5.76          | ~ (v1_relat_1 @ X15))),
% 5.55/5.76      inference('demod', [status(thm)], ['194', '195'])).
% 5.55/5.76  thf('197', plain,
% 5.55/5.76      ((((k5_relat_1 @ 
% 5.55/5.76          (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ sk_D) @ 
% 5.55/5.76          (k6_partfun1 @ sk_A_1))
% 5.55/5.76          = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ sk_D))
% 5.55/5.76        | ~ (v1_relat_1 @ 
% 5.55/5.76             (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ sk_D)))),
% 5.55/5.76      inference('sup+', [status(thm)], ['193', '196'])).
% 5.55/5.76  thf('198', plain,
% 5.55/5.76      ((~ (v1_relat_1 @ sk_D)
% 5.55/5.76        | ~ (v1_relat_1 @ sk_D)
% 5.55/5.76        | ((k5_relat_1 @ 
% 5.55/5.76            (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ sk_D) @ 
% 5.55/5.76            (k6_partfun1 @ sk_A_1))
% 5.55/5.76            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ sk_D)))),
% 5.55/5.76      inference('sup-', [status(thm)], ['178', '197'])).
% 5.55/5.76  thf('199', plain, ((v1_relat_1 @ sk_D)),
% 5.55/5.76      inference('demod', [status(thm)], ['86', '87'])).
% 5.55/5.76  thf('200', plain, ((v1_relat_1 @ sk_D)),
% 5.55/5.76      inference('demod', [status(thm)], ['86', '87'])).
% 5.55/5.76  thf('201', plain,
% 5.55/5.76      (((k5_relat_1 @ 
% 5.55/5.76         (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ sk_D) @ 
% 5.55/5.76         (k6_partfun1 @ sk_A_1))
% 5.55/5.76         = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ sk_D))),
% 5.55/5.76      inference('demod', [status(thm)], ['198', '199', '200'])).
% 5.55/5.76  thf('202', plain,
% 5.55/5.76      ((((k5_relat_1 @ sk_D @ (k6_partfun1 @ sk_A_1))
% 5.55/5.76          = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ sk_D))
% 5.55/5.76        | ~ (v1_relat_1 @ sk_D))),
% 5.55/5.76      inference('sup+', [status(thm)], ['177', '201'])).
% 5.55/5.76  thf('203', plain, (((k2_relat_1 @ sk_D) = (sk_A_1))),
% 5.55/5.76      inference('demod', [status(thm)], ['26', '29', '30', '31', '32', '33'])).
% 5.55/5.76  thf('204', plain,
% 5.55/5.76      (![X15 : $i]:
% 5.55/5.76         (((k5_relat_1 @ X15 @ (k6_partfun1 @ (k2_relat_1 @ X15))) = (X15))
% 5.55/5.76          | ~ (v1_relat_1 @ X15))),
% 5.55/5.76      inference('demod', [status(thm)], ['194', '195'])).
% 5.55/5.76  thf('205', plain,
% 5.55/5.76      ((((k5_relat_1 @ sk_D @ (k6_partfun1 @ sk_A_1)) = (sk_D))
% 5.55/5.76        | ~ (v1_relat_1 @ sk_D))),
% 5.55/5.76      inference('sup+', [status(thm)], ['203', '204'])).
% 5.55/5.76  thf('206', plain, ((v1_relat_1 @ sk_D)),
% 5.55/5.76      inference('demod', [status(thm)], ['86', '87'])).
% 5.55/5.76  thf('207', plain, (((k5_relat_1 @ sk_D @ (k6_partfun1 @ sk_A_1)) = (sk_D))),
% 5.55/5.76      inference('demod', [status(thm)], ['205', '206'])).
% 5.55/5.76  thf('208', plain, ((v1_relat_1 @ sk_D)),
% 5.55/5.76      inference('demod', [status(thm)], ['86', '87'])).
% 5.55/5.76  thf('209', plain,
% 5.55/5.76      (((sk_D) = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ sk_D))),
% 5.55/5.76      inference('demod', [status(thm)], ['202', '207', '208'])).
% 5.55/5.76  thf('210', plain,
% 5.55/5.76      (![X16 : $i]:
% 5.55/5.76         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 5.55/5.76          | ~ (v1_funct_1 @ X16)
% 5.55/5.76          | ~ (v1_relat_1 @ X16))),
% 5.55/5.76      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 5.55/5.76  thf(t67_funct_1, axiom,
% 5.55/5.76    (![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 5.55/5.76  thf('211', plain,
% 5.55/5.76      (![X27 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X27)) = (k6_relat_1 @ X27))),
% 5.55/5.76      inference('cnf', [status(esa)], [t67_funct_1])).
% 5.55/5.76  thf('212', plain, (![X52 : $i]: ((k6_partfun1 @ X52) = (k6_relat_1 @ X52))),
% 5.55/5.76      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.55/5.76  thf('213', plain, (![X52 : $i]: ((k6_partfun1 @ X52) = (k6_relat_1 @ X52))),
% 5.55/5.76      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.55/5.76  thf('214', plain,
% 5.55/5.76      (![X27 : $i]: ((k2_funct_1 @ (k6_partfun1 @ X27)) = (k6_partfun1 @ X27))),
% 5.55/5.76      inference('demod', [status(thm)], ['211', '212', '213'])).
% 5.55/5.76  thf(t66_funct_1, axiom,
% 5.55/5.76    (![A:$i]:
% 5.55/5.76     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.55/5.76       ( ![B:$i]:
% 5.55/5.76         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 5.55/5.76           ( ( ( v2_funct_1 @ A ) & ( v2_funct_1 @ B ) ) =>
% 5.55/5.76             ( ( k2_funct_1 @ ( k5_relat_1 @ A @ B ) ) =
% 5.55/5.76               ( k5_relat_1 @ ( k2_funct_1 @ B ) @ ( k2_funct_1 @ A ) ) ) ) ) ) ))).
% 5.55/5.76  thf('215', plain,
% 5.55/5.76      (![X25 : $i, X26 : $i]:
% 5.55/5.76         (~ (v1_relat_1 @ X25)
% 5.55/5.76          | ~ (v1_funct_1 @ X25)
% 5.55/5.76          | ((k2_funct_1 @ (k5_relat_1 @ X26 @ X25))
% 5.55/5.76              = (k5_relat_1 @ (k2_funct_1 @ X25) @ (k2_funct_1 @ X26)))
% 5.55/5.76          | ~ (v2_funct_1 @ X25)
% 5.55/5.76          | ~ (v2_funct_1 @ X26)
% 5.55/5.76          | ~ (v1_funct_1 @ X26)
% 5.55/5.76          | ~ (v1_relat_1 @ X26))),
% 5.55/5.76      inference('cnf', [status(esa)], [t66_funct_1])).
% 5.55/5.76  thf('216', plain,
% 5.55/5.76      (![X10 : $i, X11 : $i]:
% 5.55/5.76         (~ (v1_relat_1 @ X10)
% 5.55/5.76          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X11 @ X10)) @ 
% 5.55/5.76             (k2_relat_1 @ X10))
% 5.55/5.76          | ~ (v1_relat_1 @ X11))),
% 5.55/5.76      inference('cnf', [status(esa)], [t45_relat_1])).
% 5.55/5.76  thf(t71_relat_1, axiom,
% 5.55/5.76    (![A:$i]:
% 5.55/5.76     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 5.55/5.76       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 5.55/5.76  thf('217', plain, (![X12 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 5.55/5.76      inference('cnf', [status(esa)], [t71_relat_1])).
% 5.55/5.76  thf('218', plain, (![X52 : $i]: ((k6_partfun1 @ X52) = (k6_relat_1 @ X52))),
% 5.55/5.76      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.55/5.76  thf('219', plain,
% 5.55/5.76      (![X12 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X12)) = (X12))),
% 5.55/5.76      inference('demod', [status(thm)], ['217', '218'])).
% 5.55/5.76  thf('220', plain,
% 5.55/5.76      (![X6 : $i, X7 : $i]:
% 5.55/5.76         (~ (r1_tarski @ (k1_relat_1 @ X6) @ X7)
% 5.55/5.76          | (v4_relat_1 @ X6 @ X7)
% 5.55/5.76          | ~ (v1_relat_1 @ X6))),
% 5.55/5.76      inference('cnf', [status(esa)], [d18_relat_1])).
% 5.55/5.76  thf('221', plain,
% 5.55/5.76      (![X0 : $i, X1 : $i]:
% 5.55/5.76         (~ (r1_tarski @ X0 @ X1)
% 5.55/5.76          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 5.55/5.76          | (v4_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 5.55/5.76      inference('sup-', [status(thm)], ['219', '220'])).
% 5.55/5.76  thf('222', plain, (![X17 : $i]: (v1_relat_1 @ (k6_partfun1 @ X17))),
% 5.55/5.76      inference('demod', [status(thm)], ['190', '191'])).
% 5.55/5.76  thf('223', plain,
% 5.55/5.76      (![X0 : $i, X1 : $i]:
% 5.55/5.76         (~ (r1_tarski @ X0 @ X1) | (v4_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 5.55/5.76      inference('demod', [status(thm)], ['221', '222'])).
% 5.55/5.76  thf('224', plain,
% 5.55/5.76      (![X0 : $i, X1 : $i]:
% 5.55/5.76         (~ (v1_relat_1 @ X1)
% 5.55/5.76          | ~ (v1_relat_1 @ X0)
% 5.55/5.76          | (v4_relat_1 @ 
% 5.55/5.76             (k6_partfun1 @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))) @ 
% 5.55/5.76             (k2_relat_1 @ X0)))),
% 5.55/5.76      inference('sup-', [status(thm)], ['216', '223'])).
% 5.55/5.76  thf('225', plain,
% 5.55/5.76      (![X0 : $i, X1 : $i]:
% 5.55/5.76         ((v4_relat_1 @ 
% 5.55/5.76           (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ (k5_relat_1 @ X1 @ X0)))) @ 
% 5.55/5.76           (k2_relat_1 @ (k2_funct_1 @ X1)))
% 5.55/5.76          | ~ (v1_relat_1 @ X1)
% 5.55/5.76          | ~ (v1_funct_1 @ X1)
% 5.55/5.76          | ~ (v2_funct_1 @ X1)
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ (k2_funct_1 @ X1))
% 5.55/5.76          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 5.55/5.76      inference('sup+', [status(thm)], ['215', '224'])).
% 5.55/5.76  thf('226', plain,
% 5.55/5.76      (![X0 : $i, X1 : $i]:
% 5.55/5.76         (~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 5.55/5.76          | ~ (v1_relat_1 @ (k2_funct_1 @ X1))
% 5.55/5.76          | ~ (v1_relat_1 @ X1)
% 5.55/5.76          | ~ (v1_funct_1 @ X1)
% 5.55/5.76          | ~ (v2_funct_1 @ X1)
% 5.55/5.76          | ~ (v2_funct_1 @ (k6_partfun1 @ X0))
% 5.55/5.76          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 5.55/5.76          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 5.55/5.76          | (v4_relat_1 @ 
% 5.55/5.76             (k6_partfun1 @ 
% 5.55/5.76              (k2_relat_1 @ 
% 5.55/5.76               (k2_funct_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1)))) @ 
% 5.55/5.76             (k2_relat_1 @ (k2_funct_1 @ (k6_partfun1 @ X0)))))),
% 5.55/5.76      inference('sup-', [status(thm)], ['214', '225'])).
% 5.55/5.76  thf('227', plain, (![X17 : $i]: (v1_relat_1 @ (k6_partfun1 @ X17))),
% 5.55/5.76      inference('demod', [status(thm)], ['190', '191'])).
% 5.55/5.76  thf('228', plain, (![X20 : $i]: (v2_funct_1 @ (k6_partfun1 @ X20))),
% 5.55/5.76      inference('demod', [status(thm)], ['62', '63'])).
% 5.55/5.76  thf('229', plain, (![X18 : $i]: (v1_funct_1 @ (k6_relat_1 @ X18))),
% 5.55/5.76      inference('cnf', [status(esa)], [fc3_funct_1])).
% 5.55/5.76  thf('230', plain, (![X52 : $i]: ((k6_partfun1 @ X52) = (k6_relat_1 @ X52))),
% 5.55/5.76      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.55/5.76  thf('231', plain, (![X18 : $i]: (v1_funct_1 @ (k6_partfun1 @ X18))),
% 5.55/5.76      inference('demod', [status(thm)], ['229', '230'])).
% 5.55/5.76  thf('232', plain, (![X17 : $i]: (v1_relat_1 @ (k6_partfun1 @ X17))),
% 5.55/5.76      inference('demod', [status(thm)], ['190', '191'])).
% 5.55/5.76  thf('233', plain,
% 5.55/5.76      (![X27 : $i]: ((k2_funct_1 @ (k6_partfun1 @ X27)) = (k6_partfun1 @ X27))),
% 5.55/5.76      inference('demod', [status(thm)], ['211', '212', '213'])).
% 5.55/5.76  thf('234', plain, (![X13 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 5.55/5.76      inference('cnf', [status(esa)], [t71_relat_1])).
% 5.55/5.76  thf('235', plain, (![X52 : $i]: ((k6_partfun1 @ X52) = (k6_relat_1 @ X52))),
% 5.55/5.76      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.55/5.76  thf('236', plain,
% 5.55/5.76      (![X13 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X13)) = (X13))),
% 5.55/5.76      inference('demod', [status(thm)], ['234', '235'])).
% 5.55/5.76  thf('237', plain,
% 5.55/5.76      (![X0 : $i, X1 : $i]:
% 5.55/5.76         (~ (v1_relat_1 @ (k2_funct_1 @ X1))
% 5.55/5.76          | ~ (v1_relat_1 @ X1)
% 5.55/5.76          | ~ (v1_funct_1 @ X1)
% 5.55/5.76          | ~ (v2_funct_1 @ X1)
% 5.55/5.76          | (v4_relat_1 @ 
% 5.55/5.76             (k6_partfun1 @ 
% 5.55/5.76              (k2_relat_1 @ 
% 5.55/5.76               (k2_funct_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1)))) @ 
% 5.55/5.76             X0))),
% 5.55/5.76      inference('demod', [status(thm)],
% 5.55/5.76                ['226', '227', '228', '231', '232', '233', '236'])).
% 5.55/5.76  thf('238', plain,
% 5.55/5.76      (![X0 : $i, X1 : $i]:
% 5.55/5.76         (~ (v1_relat_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | (v4_relat_1 @ 
% 5.55/5.76             (k6_partfun1 @ 
% 5.55/5.76              (k2_relat_1 @ 
% 5.55/5.76               (k2_funct_1 @ (k5_relat_1 @ (k6_partfun1 @ X1) @ X0)))) @ 
% 5.55/5.76             X1)
% 5.55/5.76          | ~ (v2_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ X0))),
% 5.55/5.76      inference('sup-', [status(thm)], ['210', '237'])).
% 5.55/5.76  thf('239', plain,
% 5.55/5.76      (![X0 : $i, X1 : $i]:
% 5.55/5.76         (~ (v2_funct_1 @ X0)
% 5.55/5.76          | (v4_relat_1 @ 
% 5.55/5.76             (k6_partfun1 @ 
% 5.55/5.76              (k2_relat_1 @ 
% 5.55/5.76               (k2_funct_1 @ (k5_relat_1 @ (k6_partfun1 @ X1) @ X0)))) @ 
% 5.55/5.76             X1)
% 5.55/5.76          | ~ (v1_funct_1 @ X0)
% 5.55/5.76          | ~ (v1_relat_1 @ X0))),
% 5.55/5.76      inference('simplify', [status(thm)], ['238'])).
% 5.55/5.76  thf('240', plain,
% 5.55/5.76      (![X6 : $i, X7 : $i]:
% 5.55/5.76         (~ (v4_relat_1 @ X6 @ X7)
% 5.55/5.76          | (r1_tarski @ (k1_relat_1 @ X6) @ X7)
% 5.55/5.76          | ~ (v1_relat_1 @ X6))),
% 5.55/5.76      inference('cnf', [status(esa)], [d18_relat_1])).
% 5.55/5.76  thf('241', plain,
% 5.55/5.76      (![X0 : $i, X1 : $i]:
% 5.55/5.76         (~ (v1_relat_1 @ X1)
% 5.55/5.76          | ~ (v1_funct_1 @ X1)
% 5.55/5.76          | ~ (v2_funct_1 @ X1)
% 5.55/5.76          | ~ (v1_relat_1 @ 
% 5.55/5.76               (k6_partfun1 @ 
% 5.55/5.76                (k2_relat_1 @ 
% 5.55/5.76                 (k2_funct_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1)))))
% 5.55/5.76          | (r1_tarski @ 
% 5.55/5.76             (k1_relat_1 @ 
% 5.55/5.76              (k6_partfun1 @ 
% 5.55/5.76               (k2_relat_1 @ 
% 5.55/5.76                (k2_funct_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))))) @ 
% 5.55/5.76             X0))),
% 5.55/5.76      inference('sup-', [status(thm)], ['239', '240'])).
% 5.55/5.76  thf('242', plain, (![X17 : $i]: (v1_relat_1 @ (k6_partfun1 @ X17))),
% 5.55/5.76      inference('demod', [status(thm)], ['190', '191'])).
% 5.55/5.76  thf('243', plain,
% 5.55/5.76      (![X12 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X12)) = (X12))),
% 5.55/5.76      inference('demod', [status(thm)], ['217', '218'])).
% 5.55/5.76  thf('244', plain,
% 5.55/5.76      (![X0 : $i, X1 : $i]:
% 5.55/5.76         (~ (v1_relat_1 @ X1)
% 5.55/5.76          | ~ (v1_funct_1 @ X1)
% 5.55/5.76          | ~ (v2_funct_1 @ X1)
% 5.55/5.76          | (r1_tarski @ 
% 5.55/5.76             (k2_relat_1 @ 
% 5.55/5.76              (k2_funct_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))) @ 
% 5.55/5.76             X0))),
% 5.55/5.76      inference('demod', [status(thm)], ['241', '242', '243'])).
% 5.55/5.76  thf('245', plain,
% 5.55/5.76      (![X1 : $i, X3 : $i]:
% 5.55/5.76         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 5.55/5.76      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.55/5.76  thf('246', plain,
% 5.55/5.76      (![X0 : $i, X1 : $i]:
% 5.55/5.76         (~ (v2_funct_1 @ X1)
% 5.55/5.76          | ~ (v1_funct_1 @ X1)
% 5.55/5.76          | ~ (v1_relat_1 @ X1)
% 5.55/5.76          | ~ (r1_tarski @ X0 @ 
% 5.55/5.76               (k2_relat_1 @ 
% 5.55/5.76                (k2_funct_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))))
% 5.55/5.76          | ((X0)
% 5.55/5.76              = (k2_relat_1 @ 
% 5.55/5.76                 (k2_funct_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1)))))),
% 5.55/5.76      inference('sup-', [status(thm)], ['244', '245'])).
% 5.55/5.76  thf('247', plain,
% 5.55/5.76      ((~ (r1_tarski @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ (k2_funct_1 @ sk_D)))
% 5.55/5.76        | ((k1_relat_1 @ sk_D)
% 5.55/5.76            = (k2_relat_1 @ 
% 5.55/5.76               (k2_funct_1 @ 
% 5.55/5.76                (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ sk_D))))
% 5.55/5.76        | ~ (v1_relat_1 @ sk_D)
% 5.55/5.76        | ~ (v1_funct_1 @ sk_D)
% 5.55/5.76        | ~ (v2_funct_1 @ sk_D))),
% 5.55/5.76      inference('sup-', [status(thm)], ['209', '246'])).
% 5.55/5.76  thf('248', plain,
% 5.55/5.76      (((sk_D) = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ sk_D))),
% 5.55/5.76      inference('demod', [status(thm)], ['202', '207', '208'])).
% 5.55/5.76  thf('249', plain, ((v1_relat_1 @ sk_D)),
% 5.55/5.76      inference('demod', [status(thm)], ['86', '87'])).
% 5.55/5.76  thf('250', plain, ((v1_funct_1 @ sk_D)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('251', plain,
% 5.55/5.76      ((~ (r1_tarski @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ (k2_funct_1 @ sk_D)))
% 5.55/5.76        | ((k1_relat_1 @ sk_D) = (k2_relat_1 @ (k2_funct_1 @ sk_D)))
% 5.55/5.76        | ~ (v2_funct_1 @ sk_D))),
% 5.55/5.76      inference('demod', [status(thm)], ['247', '248', '249', '250'])).
% 5.55/5.76  thf('252', plain,
% 5.55/5.76      ((~ (v1_relat_1 @ sk_D)
% 5.55/5.76        | ~ (v1_funct_1 @ sk_D)
% 5.55/5.76        | ~ (v2_funct_1 @ sk_D)
% 5.55/5.76        | ~ (v2_funct_1 @ sk_D)
% 5.55/5.76        | ((k1_relat_1 @ sk_D) = (k2_relat_1 @ (k2_funct_1 @ sk_D))))),
% 5.55/5.76      inference('sup-', [status(thm)], ['174', '251'])).
% 5.55/5.76  thf('253', plain, ((v1_relat_1 @ sk_D)),
% 5.55/5.76      inference('demod', [status(thm)], ['86', '87'])).
% 5.55/5.76  thf('254', plain, ((v1_funct_1 @ sk_D)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('255', plain,
% 5.55/5.76      ((~ (v2_funct_1 @ sk_D)
% 5.55/5.76        | ~ (v2_funct_1 @ sk_D)
% 5.55/5.76        | ((k1_relat_1 @ sk_D) = (k2_relat_1 @ (k2_funct_1 @ sk_D))))),
% 5.55/5.76      inference('demod', [status(thm)], ['252', '253', '254'])).
% 5.55/5.76  thf('256', plain,
% 5.55/5.76      ((((k1_relat_1 @ sk_D) = (k2_relat_1 @ (k2_funct_1 @ sk_D)))
% 5.55/5.76        | ~ (v2_funct_1 @ sk_D))),
% 5.55/5.76      inference('simplify', [status(thm)], ['255'])).
% 5.55/5.76  thf('257', plain, ((v2_funct_1 @ sk_D)),
% 5.55/5.76      inference('sup-', [status(thm)], ['74', '75'])).
% 5.55/5.76  thf('258', plain,
% 5.55/5.76      (((k1_relat_1 @ sk_D) = (k2_relat_1 @ (k2_funct_1 @ sk_D)))),
% 5.55/5.76      inference('demod', [status(thm)], ['256', '257'])).
% 5.55/5.76  thf('259', plain,
% 5.55/5.76      (![X13 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X13)) = (X13))),
% 5.55/5.76      inference('demod', [status(thm)], ['234', '235'])).
% 5.55/5.76  thf('260', plain,
% 5.55/5.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf(cc2_relset_1, axiom,
% 5.55/5.76    (![A:$i,B:$i,C:$i]:
% 5.55/5.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.55/5.76       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 5.55/5.76  thf('261', plain,
% 5.55/5.76      (![X28 : $i, X29 : $i, X30 : $i]:
% 5.55/5.76         ((v4_relat_1 @ X28 @ X29)
% 5.55/5.76          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 5.55/5.76      inference('cnf', [status(esa)], [cc2_relset_1])).
% 5.55/5.76  thf('262', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 5.55/5.76      inference('sup-', [status(thm)], ['260', '261'])).
% 5.55/5.76  thf('263', plain,
% 5.55/5.76      (![X6 : $i, X7 : $i]:
% 5.55/5.76         (~ (v4_relat_1 @ X6 @ X7)
% 5.55/5.76          | (r1_tarski @ (k1_relat_1 @ X6) @ X7)
% 5.55/5.76          | ~ (v1_relat_1 @ X6))),
% 5.55/5.76      inference('cnf', [status(esa)], [d18_relat_1])).
% 5.55/5.76  thf('264', plain,
% 5.55/5.76      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B))),
% 5.55/5.76      inference('sup-', [status(thm)], ['262', '263'])).
% 5.55/5.76  thf('265', plain, ((v1_relat_1 @ sk_D)),
% 5.55/5.76      inference('demod', [status(thm)], ['86', '87'])).
% 5.55/5.76  thf('266', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 5.55/5.76      inference('demod', [status(thm)], ['264', '265'])).
% 5.55/5.76  thf('267', plain,
% 5.55/5.76      (((k1_relat_1 @ sk_D) = (k2_relat_1 @ (k2_funct_1 @ sk_D)))),
% 5.55/5.76      inference('demod', [status(thm)], ['256', '257'])).
% 5.55/5.76  thf('268', plain,
% 5.55/5.76      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 5.55/5.76      inference('demod', [status(thm)], ['36', '76'])).
% 5.55/5.76  thf('269', plain,
% 5.55/5.76      (![X13 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X13)) = (X13))),
% 5.55/5.76      inference('demod', [status(thm)], ['234', '235'])).
% 5.55/5.76  thf('270', plain, ((v1_relat_1 @ sk_D)),
% 5.55/5.76      inference('demod', [status(thm)], ['86', '87'])).
% 5.55/5.76  thf('271', plain,
% 5.55/5.76      ((((k1_relat_1 @ sk_D) = (sk_B)) | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D)))),
% 5.55/5.76      inference('demod', [status(thm)],
% 5.55/5.76                ['110', '258', '259', '266', '267', '268', '269', '270'])).
% 5.55/5.76  thf('272', plain,
% 5.55/5.76      ((~ (v1_relat_1 @ sk_D)
% 5.55/5.76        | ~ (v1_funct_1 @ sk_D)
% 5.55/5.76        | ((k1_relat_1 @ sk_D) = (sk_B)))),
% 5.55/5.76      inference('sup-', [status(thm)], ['105', '271'])).
% 5.55/5.76  thf('273', plain, ((v1_relat_1 @ sk_D)),
% 5.55/5.76      inference('demod', [status(thm)], ['86', '87'])).
% 5.55/5.76  thf('274', plain, ((v1_funct_1 @ sk_D)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('275', plain, (((k1_relat_1 @ sk_D) = (sk_B))),
% 5.55/5.76      inference('demod', [status(thm)], ['272', '273', '274'])).
% 5.55/5.76  thf('276', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (sk_B)))),
% 5.55/5.76      inference('demod', [status(thm)], ['104', '275'])).
% 5.55/5.76  thf('277', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 5.55/5.76      inference('simplify', [status(thm)], ['276'])).
% 5.55/5.76  thf('278', plain, (((k5_relat_1 @ sk_D @ sk_C) = (k6_partfun1 @ sk_B))),
% 5.55/5.76      inference('demod', [status(thm)], ['77', '277'])).
% 5.55/5.76  thf('279', plain,
% 5.55/5.76      (![X23 : $i, X24 : $i]:
% 5.55/5.76         (~ (v1_relat_1 @ X23)
% 5.55/5.76          | ~ (v1_funct_1 @ X23)
% 5.55/5.76          | ((X23) = (k2_funct_1 @ X24))
% 5.55/5.76          | ((k5_relat_1 @ X23 @ X24) != (k6_partfun1 @ (k2_relat_1 @ X24)))
% 5.55/5.76          | ((k2_relat_1 @ X23) != (k1_relat_1 @ X24))
% 5.55/5.76          | ~ (v2_funct_1 @ X24)
% 5.55/5.76          | ~ (v1_funct_1 @ X24)
% 5.55/5.76          | ~ (v1_relat_1 @ X24))),
% 5.55/5.76      inference('demod', [status(thm)], ['79', '80'])).
% 5.55/5.76  thf('280', plain,
% 5.55/5.76      ((((k6_partfun1 @ sk_B) != (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 5.55/5.76        | ~ (v1_relat_1 @ sk_C)
% 5.55/5.76        | ~ (v1_funct_1 @ sk_C)
% 5.55/5.76        | ~ (v2_funct_1 @ sk_C)
% 5.55/5.76        | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ sk_C))
% 5.55/5.76        | ((sk_D) = (k2_funct_1 @ sk_C))
% 5.55/5.76        | ~ (v1_funct_1 @ sk_D)
% 5.55/5.76        | ~ (v1_relat_1 @ sk_D))),
% 5.55/5.76      inference('sup-', [status(thm)], ['278', '279'])).
% 5.55/5.76  thf('281', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 5.55/5.76      inference('sup+', [status(thm)], ['92', '93'])).
% 5.55/5.76  thf('282', plain, ((v1_relat_1 @ sk_C)),
% 5.55/5.76      inference('demod', [status(thm)], ['98', '99'])).
% 5.55/5.76  thf('283', plain, ((v1_funct_1 @ sk_C)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('284', plain, ((v2_funct_1 @ sk_C)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('285', plain, (((k2_relat_1 @ sk_D) = (sk_A_1))),
% 5.55/5.76      inference('demod', [status(thm)], ['26', '29', '30', '31', '32', '33'])).
% 5.55/5.76  thf('286', plain,
% 5.55/5.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('287', plain,
% 5.55/5.76      (![X28 : $i, X29 : $i, X30 : $i]:
% 5.55/5.76         ((v4_relat_1 @ X28 @ X29)
% 5.55/5.76          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 5.55/5.76      inference('cnf', [status(esa)], [cc2_relset_1])).
% 5.55/5.76  thf('288', plain, ((v4_relat_1 @ sk_C @ sk_A_1)),
% 5.55/5.76      inference('sup-', [status(thm)], ['286', '287'])).
% 5.55/5.76  thf('289', plain,
% 5.55/5.76      (![X6 : $i, X7 : $i]:
% 5.55/5.76         (~ (v4_relat_1 @ X6 @ X7)
% 5.55/5.76          | (r1_tarski @ (k1_relat_1 @ X6) @ X7)
% 5.55/5.76          | ~ (v1_relat_1 @ X6))),
% 5.55/5.76      inference('cnf', [status(esa)], [d18_relat_1])).
% 5.55/5.76  thf('290', plain,
% 5.55/5.76      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A_1))),
% 5.55/5.76      inference('sup-', [status(thm)], ['288', '289'])).
% 5.55/5.76  thf('291', plain, ((v1_relat_1 @ sk_C)),
% 5.55/5.76      inference('demod', [status(thm)], ['98', '99'])).
% 5.55/5.76  thf('292', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A_1)),
% 5.55/5.76      inference('demod', [status(thm)], ['290', '291'])).
% 5.55/5.76  thf('293', plain,
% 5.55/5.76      (![X1 : $i, X3 : $i]:
% 5.55/5.76         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 5.55/5.76      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.55/5.76  thf('294', plain,
% 5.55/5.76      ((~ (r1_tarski @ sk_A_1 @ (k1_relat_1 @ sk_C))
% 5.55/5.76        | ((sk_A_1) = (k1_relat_1 @ sk_C)))),
% 5.55/5.76      inference('sup-', [status(thm)], ['292', '293'])).
% 5.55/5.76  thf('295', plain,
% 5.55/5.76      (![X22 : $i]:
% 5.55/5.76         (~ (v2_funct_1 @ X22)
% 5.55/5.76          | ((k1_relat_1 @ X22) = (k2_relat_1 @ (k2_funct_1 @ X22)))
% 5.55/5.76          | ~ (v1_funct_1 @ X22)
% 5.55/5.76          | ~ (v1_relat_1 @ X22))),
% 5.55/5.76      inference('cnf', [status(esa)], [t55_funct_1])).
% 5.55/5.76  thf('296', plain,
% 5.55/5.76      (![X16 : $i]:
% 5.55/5.76         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 5.55/5.76          | ~ (v1_funct_1 @ X16)
% 5.55/5.76          | ~ (v1_relat_1 @ X16))),
% 5.55/5.76      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 5.55/5.76  thf('297', plain,
% 5.55/5.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('298', plain,
% 5.55/5.76      (![X66 : $i, X67 : $i, X68 : $i]:
% 5.55/5.76         (((X66) = (k1_xboole_0))
% 5.55/5.76          | ~ (v1_funct_1 @ X67)
% 5.55/5.76          | ~ (v1_funct_2 @ X67 @ X68 @ X66)
% 5.55/5.76          | ~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X68 @ X66)))
% 5.55/5.76          | ((k5_relat_1 @ X67 @ (k2_funct_1 @ X67)) = (k6_partfun1 @ X68))
% 5.55/5.76          | ~ (v2_funct_1 @ X67)
% 5.55/5.76          | ((k2_relset_1 @ X68 @ X66 @ X67) != (X66)))),
% 5.55/5.76      inference('cnf', [status(esa)], [t35_funct_2])).
% 5.55/5.76  thf('299', plain,
% 5.55/5.76      ((((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) != (sk_B))
% 5.55/5.76        | ~ (v2_funct_1 @ sk_C)
% 5.55/5.76        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A_1))
% 5.55/5.76        | ~ (v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)
% 5.55/5.76        | ~ (v1_funct_1 @ sk_C)
% 5.55/5.76        | ((sk_B) = (k1_xboole_0)))),
% 5.55/5.76      inference('sup-', [status(thm)], ['297', '298'])).
% 5.55/5.76  thf('300', plain, (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (sk_B))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('301', plain, ((v2_funct_1 @ sk_C)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('302', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('303', plain, ((v1_funct_1 @ sk_C)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('304', plain,
% 5.55/5.76      ((((sk_B) != (sk_B))
% 5.55/5.76        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A_1))
% 5.55/5.76        | ((sk_B) = (k1_xboole_0)))),
% 5.55/5.76      inference('demod', [status(thm)], ['299', '300', '301', '302', '303'])).
% 5.55/5.76  thf('305', plain,
% 5.55/5.76      ((((sk_B) = (k1_xboole_0))
% 5.55/5.76        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A_1)))),
% 5.55/5.76      inference('simplify', [status(thm)], ['304'])).
% 5.55/5.76  thf('306', plain, (((sk_B) != (k1_xboole_0))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('307', plain,
% 5.55/5.76      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A_1))),
% 5.55/5.76      inference('simplify_reflect-', [status(thm)], ['305', '306'])).
% 5.55/5.76  thf('308', plain,
% 5.55/5.76      (![X10 : $i, X11 : $i]:
% 5.55/5.76         (~ (v1_relat_1 @ X10)
% 5.55/5.76          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X11 @ X10)) @ 
% 5.55/5.76             (k2_relat_1 @ X10))
% 5.55/5.76          | ~ (v1_relat_1 @ X11))),
% 5.55/5.76      inference('cnf', [status(esa)], [t45_relat_1])).
% 5.55/5.76  thf('309', plain,
% 5.55/5.76      (((r1_tarski @ (k2_relat_1 @ (k6_partfun1 @ sk_A_1)) @ 
% 5.55/5.76         (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 5.55/5.76        | ~ (v1_relat_1 @ sk_C)
% 5.55/5.76        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 5.55/5.76      inference('sup+', [status(thm)], ['307', '308'])).
% 5.55/5.76  thf('310', plain,
% 5.55/5.76      (![X13 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X13)) = (X13))),
% 5.55/5.76      inference('demod', [status(thm)], ['234', '235'])).
% 5.55/5.76  thf('311', plain, ((v1_relat_1 @ sk_C)),
% 5.55/5.76      inference('demod', [status(thm)], ['98', '99'])).
% 5.55/5.76  thf('312', plain,
% 5.55/5.76      (((r1_tarski @ sk_A_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 5.55/5.76        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 5.55/5.76      inference('demod', [status(thm)], ['309', '310', '311'])).
% 5.55/5.76  thf('313', plain,
% 5.55/5.76      ((~ (v1_relat_1 @ sk_C)
% 5.55/5.76        | ~ (v1_funct_1 @ sk_C)
% 5.55/5.76        | (r1_tarski @ sk_A_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 5.55/5.76      inference('sup-', [status(thm)], ['296', '312'])).
% 5.55/5.76  thf('314', plain, ((v1_relat_1 @ sk_C)),
% 5.55/5.76      inference('demod', [status(thm)], ['98', '99'])).
% 5.55/5.76  thf('315', plain, ((v1_funct_1 @ sk_C)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('316', plain,
% 5.55/5.76      ((r1_tarski @ sk_A_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 5.55/5.76      inference('demod', [status(thm)], ['313', '314', '315'])).
% 5.55/5.76  thf('317', plain,
% 5.55/5.76      (((r1_tarski @ sk_A_1 @ (k1_relat_1 @ sk_C))
% 5.55/5.76        | ~ (v1_relat_1 @ sk_C)
% 5.55/5.76        | ~ (v1_funct_1 @ sk_C)
% 5.55/5.76        | ~ (v2_funct_1 @ sk_C))),
% 5.55/5.76      inference('sup+', [status(thm)], ['295', '316'])).
% 5.55/5.76  thf('318', plain, ((v1_relat_1 @ sk_C)),
% 5.55/5.76      inference('demod', [status(thm)], ['98', '99'])).
% 5.55/5.76  thf('319', plain, ((v1_funct_1 @ sk_C)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('320', plain, ((v2_funct_1 @ sk_C)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('321', plain, ((r1_tarski @ sk_A_1 @ (k1_relat_1 @ sk_C))),
% 5.55/5.76      inference('demod', [status(thm)], ['317', '318', '319', '320'])).
% 5.55/5.76  thf('322', plain, (((sk_A_1) = (k1_relat_1 @ sk_C))),
% 5.55/5.76      inference('demod', [status(thm)], ['294', '321'])).
% 5.55/5.76  thf('323', plain, ((v1_funct_1 @ sk_D)),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('324', plain, ((v1_relat_1 @ sk_D)),
% 5.55/5.76      inference('demod', [status(thm)], ['86', '87'])).
% 5.55/5.76  thf('325', plain,
% 5.55/5.76      ((((k6_partfun1 @ sk_B) != (k6_partfun1 @ sk_B))
% 5.55/5.76        | ((sk_A_1) != (sk_A_1))
% 5.55/5.76        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 5.55/5.76      inference('demod', [status(thm)],
% 5.55/5.76                ['280', '281', '282', '283', '284', '285', '322', '323', '324'])).
% 5.55/5.76  thf('326', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 5.55/5.76      inference('simplify', [status(thm)], ['325'])).
% 5.55/5.76  thf('327', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 5.55/5.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.55/5.76  thf('328', plain, ($false),
% 5.55/5.76      inference('simplify_reflect-', [status(thm)], ['326', '327'])).
% 5.55/5.76  
% 5.55/5.76  % SZS output end Refutation
% 5.55/5.76  
% 5.55/5.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

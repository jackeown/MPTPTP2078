%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ha3Qmg65QZ

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:00 EST 2020

% Result     : Theorem 0.84s
% Output     : Refutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 690 expanded)
%              Number of leaves         :   45 ( 226 expanded)
%              Depth                    :   19
%              Number of atoms          : 1772 (16982 expanded)
%              Number of equality atoms :  129 (1151 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

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
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( X45 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X45 ) ) )
      | ( ( k5_relat_1 @ X46 @ ( k2_funct_1 @ X46 ) )
        = ( k6_partfun1 @ X47 ) )
      | ~ ( v2_funct_1 @ X46 )
      | ( ( k2_relset_1 @ X47 @ X45 @ X46 )
       != X45 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( X45 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X45 ) ) )
      | ( ( k5_relat_1 @ X46 @ ( k2_funct_1 @ X46 ) )
        = ( k6_relat_1 @ X47 ) )
      | ~ ( v2_funct_1 @ X46 )
      | ( ( k2_relset_1 @ X47 @ X45 @ X46 )
       != X45 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('7',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','7','8','9'])).

thf('11',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('13',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('15',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
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

thf('18',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('25',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( X14 = X17 )
      | ~ ( r2_relset_1 @ X15 @ X16 @ X14 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','26'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('28',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('29',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('30',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,(
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

thf('33',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( r2_relset_1 @ X42 @ X42 @ ( k1_partfun1 @ X42 @ X43 @ X43 @ X42 @ X41 @ X44 ) @ ( k6_partfun1 @ X42 ) )
      | ( ( k2_relset_1 @ X43 @ X42 @ X44 )
        = X42 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X43 @ X42 )
      | ~ ( v1_funct_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('34',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('35',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( r2_relset_1 @ X42 @ X42 @ ( k1_partfun1 @ X42 @ X43 @ X43 @ X42 @ X41 @ X44 ) @ ( k6_relat_1 @ X42 ) )
      | ( ( k2_relset_1 @ X43 @ X42 @ X44 )
        = X42 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X43 @ X42 )
      | ~ ( v1_funct_1 @ X44 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['31','39'])).

thf('41',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('42',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( r2_relset_1 @ X15 @ X16 @ X14 @ X17 )
      | ( X14 != X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('43',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_relset_1 @ X15 @ X16 @ X17 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('46',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['40','44','45','46','47','48'])).

thf('50',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','49'])).

thf('51',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
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

thf('54',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( ( k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37 )
        = ( k5_relat_1 @ X34 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('61',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf(t48_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) ) )
           => ( ( v2_funct_1 @ B )
              & ( v2_funct_1 @ A ) ) ) ) ) )).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X1 )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ X1 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('63',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('64',plain,(
    ! [X2: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('66',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('67',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('71',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('75',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ( X20
        = ( k1_relset_1 @ X20 @ X21 @ X22 ) )
      | ~ ( zip_tseitin_1 @ X22 @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('76',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('77',plain,(
    ! [X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('78',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('79',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X24 )
      | ( zip_tseitin_1 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('80',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('85',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('86',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['76','83','86'])).

thf('88',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('91',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( sk_B != sk_B )
    | ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['63','64','67','68','73','87','88','91'])).

thf('93',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['51','93'])).

thf('95',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['58','59','60'])).

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

thf('96',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ( X3
        = ( k2_funct_1 @ X4 ) )
      | ( ( k5_relat_1 @ X3 @ X4 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X4 ) ) )
      | ( ( k2_relat_1 @ X3 )
       != ( k1_relat_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('97',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['40','44','45','46','47','48'])).

thf('99',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['65','66'])).

thf('100',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['71','72'])).

thf('102',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['76','83','86'])).

thf('103',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['89','90'])).

thf('105',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B != sk_B )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['97','98','99','100','101','102','103','104'])).

thf('106',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['92'])).

thf('108',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k5_relat_1 @ sk_D @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['94','108'])).

thf('110',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ( X3
        = ( k2_funct_1 @ X4 ) )
      | ( ( k5_relat_1 @ X3 @ X4 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X4 ) ) )
      | ( ( k2_relat_1 @ X3 )
       != ( k1_relat_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('111',plain,
    ( ( ( k6_relat_1 @ sk_B )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_D )
     != ( k1_relat_1 @ sk_C ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['71','72'])).

thf('113',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['89','90'])).

thf('114',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['40','44','45','46','47','48'])).

thf('117',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ( X20
        = ( k1_relset_1 @ X20 @ X21 @ X22 ) )
      | ~ ( zip_tseitin_1 @ X22 @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('119',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('121',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X24 )
      | ( zip_tseitin_1 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('123',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['120','123'])).

thf('125',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['124','125'])).

thf('127',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('129',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['119','126','129'])).

thf('131',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['65','66'])).

thf('133',plain,
    ( ( ( k6_relat_1 @ sk_B )
     != ( k6_relat_1 @ sk_B ) )
    | ( sk_A != sk_A )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['111','112','113','114','115','116','130','131','132'])).

thf('134',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['134','135'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ha3Qmg65QZ
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:43:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.84/1.07  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.84/1.07  % Solved by: fo/fo7.sh
% 0.84/1.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.84/1.07  % done 430 iterations in 0.640s
% 0.84/1.07  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.84/1.07  % SZS output start Refutation
% 0.84/1.07  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.84/1.07  thf(sk_C_type, type, sk_C: $i).
% 0.84/1.07  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.84/1.07  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.84/1.07  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.84/1.07  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.84/1.07  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.84/1.07  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.84/1.07  thf(sk_A_type, type, sk_A: $i).
% 0.84/1.07  thf(sk_B_type, type, sk_B: $i).
% 0.84/1.07  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.84/1.07  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.84/1.07  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.84/1.07  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.84/1.07  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.84/1.07  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.84/1.07  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.84/1.07  thf(sk_D_type, type, sk_D: $i).
% 0.84/1.07  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.84/1.07  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.84/1.07  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.84/1.07  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.84/1.07  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.84/1.07  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.84/1.07  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.84/1.07  thf(t36_funct_2, conjecture,
% 0.84/1.07    (![A:$i,B:$i,C:$i]:
% 0.84/1.07     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.84/1.07         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.84/1.07       ( ![D:$i]:
% 0.84/1.07         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.84/1.07             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.84/1.07           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.84/1.07               ( r2_relset_1 @
% 0.84/1.07                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.84/1.07                 ( k6_partfun1 @ A ) ) & 
% 0.84/1.07               ( v2_funct_1 @ C ) ) =>
% 0.84/1.07             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.84/1.07               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.84/1.07  thf(zf_stmt_0, negated_conjecture,
% 0.84/1.07    (~( ![A:$i,B:$i,C:$i]:
% 0.84/1.07        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.84/1.07            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.84/1.07          ( ![D:$i]:
% 0.84/1.07            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.84/1.07                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.84/1.07              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.84/1.07                  ( r2_relset_1 @
% 0.84/1.07                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.84/1.07                    ( k6_partfun1 @ A ) ) & 
% 0.84/1.07                  ( v2_funct_1 @ C ) ) =>
% 0.84/1.07                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.84/1.07                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.84/1.07    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.84/1.07  thf('0', plain,
% 0.84/1.07      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf(t35_funct_2, axiom,
% 0.84/1.07    (![A:$i,B:$i,C:$i]:
% 0.84/1.07     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.84/1.07         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.84/1.07       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.84/1.07         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.84/1.07           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.84/1.07             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.84/1.07  thf('1', plain,
% 0.84/1.07      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.84/1.07         (((X45) = (k1_xboole_0))
% 0.84/1.07          | ~ (v1_funct_1 @ X46)
% 0.84/1.07          | ~ (v1_funct_2 @ X46 @ X47 @ X45)
% 0.84/1.07          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X45)))
% 0.84/1.07          | ((k5_relat_1 @ X46 @ (k2_funct_1 @ X46)) = (k6_partfun1 @ X47))
% 0.84/1.07          | ~ (v2_funct_1 @ X46)
% 0.84/1.07          | ((k2_relset_1 @ X47 @ X45 @ X46) != (X45)))),
% 0.84/1.07      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.84/1.07  thf(redefinition_k6_partfun1, axiom,
% 0.84/1.07    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.84/1.07  thf('2', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 0.84/1.07      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.84/1.07  thf('3', plain,
% 0.84/1.07      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.84/1.07         (((X45) = (k1_xboole_0))
% 0.84/1.07          | ~ (v1_funct_1 @ X46)
% 0.84/1.07          | ~ (v1_funct_2 @ X46 @ X47 @ X45)
% 0.84/1.07          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X45)))
% 0.84/1.07          | ((k5_relat_1 @ X46 @ (k2_funct_1 @ X46)) = (k6_relat_1 @ X47))
% 0.84/1.07          | ~ (v2_funct_1 @ X46)
% 0.84/1.07          | ((k2_relset_1 @ X47 @ X45 @ X46) != (X45)))),
% 0.84/1.07      inference('demod', [status(thm)], ['1', '2'])).
% 0.84/1.07  thf('4', plain,
% 0.84/1.07      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 0.84/1.07        | ~ (v2_funct_1 @ sk_D)
% 0.84/1.07        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 0.84/1.07        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.84/1.07        | ~ (v1_funct_1 @ sk_D)
% 0.84/1.07        | ((sk_A) = (k1_xboole_0)))),
% 0.84/1.07      inference('sup-', [status(thm)], ['0', '3'])).
% 0.84/1.07  thf('5', plain,
% 0.84/1.07      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf(redefinition_k2_relset_1, axiom,
% 0.84/1.07    (![A:$i,B:$i,C:$i]:
% 0.84/1.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.84/1.07       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.84/1.07  thf('6', plain,
% 0.84/1.07      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.84/1.07         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 0.84/1.07          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.84/1.07      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.84/1.07  thf('7', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.84/1.07      inference('sup-', [status(thm)], ['5', '6'])).
% 0.84/1.07  thf('8', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('10', plain,
% 0.84/1.07      ((((k2_relat_1 @ sk_D) != (sk_A))
% 0.84/1.07        | ~ (v2_funct_1 @ sk_D)
% 0.84/1.07        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 0.84/1.07        | ((sk_A) = (k1_xboole_0)))),
% 0.84/1.07      inference('demod', [status(thm)], ['4', '7', '8', '9'])).
% 0.84/1.07  thf('11', plain, (((sk_A) != (k1_xboole_0))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('12', plain,
% 0.84/1.07      ((((k2_relat_1 @ sk_D) != (sk_A))
% 0.84/1.07        | ~ (v2_funct_1 @ sk_D)
% 0.84/1.07        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B)))),
% 0.84/1.07      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.84/1.07  thf('13', plain,
% 0.84/1.07      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.84/1.07        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.84/1.07        (k6_partfun1 @ sk_A))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('14', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 0.84/1.07      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.84/1.07  thf('15', plain,
% 0.84/1.07      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.84/1.07        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.84/1.07        (k6_relat_1 @ sk_A))),
% 0.84/1.07      inference('demod', [status(thm)], ['13', '14'])).
% 0.84/1.07  thf('16', plain,
% 0.84/1.07      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('17', plain,
% 0.84/1.07      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf(dt_k1_partfun1, axiom,
% 0.84/1.07    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.84/1.07     ( ( ( v1_funct_1 @ E ) & 
% 0.84/1.07         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.84/1.07         ( v1_funct_1 @ F ) & 
% 0.84/1.07         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.84/1.07       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.84/1.07         ( m1_subset_1 @
% 0.84/1.07           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.84/1.07           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.84/1.07  thf('18', plain,
% 0.84/1.07      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.84/1.07         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.84/1.07          | ~ (v1_funct_1 @ X26)
% 0.84/1.07          | ~ (v1_funct_1 @ X29)
% 0.84/1.07          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.84/1.07          | (m1_subset_1 @ (k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29) @ 
% 0.84/1.07             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X31))))),
% 0.84/1.07      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.84/1.07  thf('19', plain,
% 0.84/1.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.07         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.84/1.07           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.84/1.07          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.84/1.07          | ~ (v1_funct_1 @ X1)
% 0.84/1.07          | ~ (v1_funct_1 @ sk_C))),
% 0.84/1.07      inference('sup-', [status(thm)], ['17', '18'])).
% 0.84/1.07  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('21', plain,
% 0.84/1.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.07         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.84/1.07           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.84/1.07          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.84/1.07          | ~ (v1_funct_1 @ X1))),
% 0.84/1.07      inference('demod', [status(thm)], ['19', '20'])).
% 0.84/1.07  thf('22', plain,
% 0.84/1.07      ((~ (v1_funct_1 @ sk_D)
% 0.84/1.07        | (m1_subset_1 @ 
% 0.84/1.07           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.84/1.07           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.84/1.07      inference('sup-', [status(thm)], ['16', '21'])).
% 0.84/1.07  thf('23', plain, ((v1_funct_1 @ sk_D)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('24', plain,
% 0.84/1.07      ((m1_subset_1 @ 
% 0.84/1.07        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.84/1.07        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.84/1.07      inference('demod', [status(thm)], ['22', '23'])).
% 0.84/1.07  thf(redefinition_r2_relset_1, axiom,
% 0.84/1.07    (![A:$i,B:$i,C:$i,D:$i]:
% 0.84/1.07     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.84/1.07         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.84/1.07       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.84/1.07  thf('25', plain,
% 0.84/1.07      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.84/1.07         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.84/1.07          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.84/1.07          | ((X14) = (X17))
% 0.84/1.07          | ~ (r2_relset_1 @ X15 @ X16 @ X14 @ X17))),
% 0.84/1.07      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.84/1.07  thf('26', plain,
% 0.84/1.07      (![X0 : $i]:
% 0.84/1.07         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.84/1.07             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.84/1.07          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.84/1.07          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.84/1.07      inference('sup-', [status(thm)], ['24', '25'])).
% 0.84/1.07  thf('27', plain,
% 0.84/1.07      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 0.84/1.07           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.84/1.07        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.84/1.07            = (k6_relat_1 @ sk_A)))),
% 0.84/1.07      inference('sup-', [status(thm)], ['15', '26'])).
% 0.84/1.07  thf(dt_k6_partfun1, axiom,
% 0.84/1.07    (![A:$i]:
% 0.84/1.07     ( ( m1_subset_1 @
% 0.84/1.07         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.84/1.07       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.84/1.07  thf('28', plain,
% 0.84/1.07      (![X33 : $i]:
% 0.84/1.07         (m1_subset_1 @ (k6_partfun1 @ X33) @ 
% 0.84/1.07          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 0.84/1.07      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.84/1.07  thf('29', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 0.84/1.07      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.84/1.07  thf('30', plain,
% 0.84/1.07      (![X33 : $i]:
% 0.84/1.07         (m1_subset_1 @ (k6_relat_1 @ X33) @ 
% 0.84/1.07          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 0.84/1.07      inference('demod', [status(thm)], ['28', '29'])).
% 0.84/1.07  thf('31', plain,
% 0.84/1.07      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.84/1.07         = (k6_relat_1 @ sk_A))),
% 0.84/1.07      inference('demod', [status(thm)], ['27', '30'])).
% 0.84/1.07  thf('32', plain,
% 0.84/1.07      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf(t24_funct_2, axiom,
% 0.84/1.07    (![A:$i,B:$i,C:$i]:
% 0.84/1.07     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.84/1.07         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.84/1.07       ( ![D:$i]:
% 0.84/1.07         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.84/1.07             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.84/1.07           ( ( r2_relset_1 @
% 0.84/1.07               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.84/1.07               ( k6_partfun1 @ B ) ) =>
% 0.84/1.07             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.84/1.07  thf('33', plain,
% 0.84/1.07      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.84/1.07         (~ (v1_funct_1 @ X41)
% 0.84/1.07          | ~ (v1_funct_2 @ X41 @ X42 @ X43)
% 0.84/1.07          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 0.84/1.07          | ~ (r2_relset_1 @ X42 @ X42 @ 
% 0.84/1.07               (k1_partfun1 @ X42 @ X43 @ X43 @ X42 @ X41 @ X44) @ 
% 0.84/1.07               (k6_partfun1 @ X42))
% 0.84/1.07          | ((k2_relset_1 @ X43 @ X42 @ X44) = (X42))
% 0.84/1.07          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42)))
% 0.84/1.07          | ~ (v1_funct_2 @ X44 @ X43 @ X42)
% 0.84/1.07          | ~ (v1_funct_1 @ X44))),
% 0.84/1.07      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.84/1.07  thf('34', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 0.84/1.07      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.84/1.07  thf('35', plain,
% 0.84/1.07      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.84/1.07         (~ (v1_funct_1 @ X41)
% 0.84/1.07          | ~ (v1_funct_2 @ X41 @ X42 @ X43)
% 0.84/1.07          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 0.84/1.07          | ~ (r2_relset_1 @ X42 @ X42 @ 
% 0.84/1.07               (k1_partfun1 @ X42 @ X43 @ X43 @ X42 @ X41 @ X44) @ 
% 0.84/1.07               (k6_relat_1 @ X42))
% 0.84/1.07          | ((k2_relset_1 @ X43 @ X42 @ X44) = (X42))
% 0.84/1.07          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42)))
% 0.84/1.07          | ~ (v1_funct_2 @ X44 @ X43 @ X42)
% 0.84/1.07          | ~ (v1_funct_1 @ X44))),
% 0.84/1.07      inference('demod', [status(thm)], ['33', '34'])).
% 0.84/1.07  thf('36', plain,
% 0.84/1.07      (![X0 : $i]:
% 0.84/1.07         (~ (v1_funct_1 @ X0)
% 0.84/1.07          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.84/1.07          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.84/1.07          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.84/1.07          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.84/1.07               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.84/1.07               (k6_relat_1 @ sk_A))
% 0.84/1.07          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.84/1.07          | ~ (v1_funct_1 @ sk_C))),
% 0.84/1.07      inference('sup-', [status(thm)], ['32', '35'])).
% 0.84/1.07  thf('37', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('38', plain, ((v1_funct_1 @ sk_C)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('39', plain,
% 0.84/1.07      (![X0 : $i]:
% 0.84/1.07         (~ (v1_funct_1 @ X0)
% 0.84/1.07          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.84/1.07          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.84/1.07          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.84/1.07          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.84/1.07               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.84/1.07               (k6_relat_1 @ sk_A)))),
% 0.84/1.07      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.84/1.07  thf('40', plain,
% 0.84/1.07      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 0.84/1.07           (k6_relat_1 @ sk_A))
% 0.84/1.07        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.84/1.07        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.84/1.07        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.84/1.07        | ~ (v1_funct_1 @ sk_D))),
% 0.84/1.07      inference('sup-', [status(thm)], ['31', '39'])).
% 0.84/1.07  thf('41', plain,
% 0.84/1.07      (![X33 : $i]:
% 0.84/1.07         (m1_subset_1 @ (k6_relat_1 @ X33) @ 
% 0.84/1.07          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 0.84/1.07      inference('demod', [status(thm)], ['28', '29'])).
% 0.84/1.07  thf('42', plain,
% 0.84/1.07      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.84/1.07         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.84/1.07          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.84/1.07          | (r2_relset_1 @ X15 @ X16 @ X14 @ X17)
% 0.84/1.07          | ((X14) != (X17)))),
% 0.84/1.07      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.84/1.07  thf('43', plain,
% 0.84/1.07      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.84/1.07         ((r2_relset_1 @ X15 @ X16 @ X17 @ X17)
% 0.84/1.07          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.84/1.07      inference('simplify', [status(thm)], ['42'])).
% 0.84/1.07  thf('44', plain,
% 0.84/1.07      (![X0 : $i]:
% 0.84/1.07         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.84/1.07      inference('sup-', [status(thm)], ['41', '43'])).
% 0.84/1.07  thf('45', plain,
% 0.84/1.07      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.84/1.07      inference('sup-', [status(thm)], ['5', '6'])).
% 0.84/1.07  thf('46', plain,
% 0.84/1.07      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('47', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('48', plain, ((v1_funct_1 @ sk_D)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('49', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.84/1.07      inference('demod', [status(thm)], ['40', '44', '45', '46', '47', '48'])).
% 0.84/1.07  thf('50', plain,
% 0.84/1.07      ((((sk_A) != (sk_A))
% 0.84/1.07        | ~ (v2_funct_1 @ sk_D)
% 0.84/1.07        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B)))),
% 0.84/1.07      inference('demod', [status(thm)], ['12', '49'])).
% 0.84/1.07  thf('51', plain,
% 0.84/1.07      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 0.84/1.07        | ~ (v2_funct_1 @ sk_D))),
% 0.84/1.07      inference('simplify', [status(thm)], ['50'])).
% 0.84/1.07  thf('52', plain,
% 0.84/1.07      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('53', plain,
% 0.84/1.07      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf(redefinition_k1_partfun1, axiom,
% 0.84/1.07    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.84/1.07     ( ( ( v1_funct_1 @ E ) & 
% 0.84/1.07         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.84/1.07         ( v1_funct_1 @ F ) & 
% 0.84/1.07         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.84/1.07       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.84/1.07  thf('54', plain,
% 0.84/1.07      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.84/1.07         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.84/1.07          | ~ (v1_funct_1 @ X34)
% 0.84/1.07          | ~ (v1_funct_1 @ X37)
% 0.84/1.07          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.84/1.07          | ((k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37)
% 0.84/1.07              = (k5_relat_1 @ X34 @ X37)))),
% 0.84/1.07      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.84/1.07  thf('55', plain,
% 0.84/1.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.07         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.84/1.07            = (k5_relat_1 @ sk_C @ X0))
% 0.84/1.07          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.84/1.07          | ~ (v1_funct_1 @ X0)
% 0.84/1.07          | ~ (v1_funct_1 @ sk_C))),
% 0.84/1.07      inference('sup-', [status(thm)], ['53', '54'])).
% 0.84/1.07  thf('56', plain, ((v1_funct_1 @ sk_C)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('57', plain,
% 0.84/1.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.07         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.84/1.07            = (k5_relat_1 @ sk_C @ X0))
% 0.84/1.07          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.84/1.07          | ~ (v1_funct_1 @ X0))),
% 0.84/1.07      inference('demod', [status(thm)], ['55', '56'])).
% 0.84/1.07  thf('58', plain,
% 0.84/1.07      ((~ (v1_funct_1 @ sk_D)
% 0.84/1.07        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.84/1.07            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.84/1.07      inference('sup-', [status(thm)], ['52', '57'])).
% 0.84/1.07  thf('59', plain, ((v1_funct_1 @ sk_D)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('60', plain,
% 0.84/1.07      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.84/1.07         = (k6_relat_1 @ sk_A))),
% 0.84/1.07      inference('demod', [status(thm)], ['27', '30'])).
% 0.84/1.07  thf('61', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.84/1.07      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.84/1.07  thf(t48_funct_1, axiom,
% 0.84/1.07    (![A:$i]:
% 0.84/1.07     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.84/1.07       ( ![B:$i]:
% 0.84/1.07         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.84/1.07           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.84/1.07               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.84/1.07             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.84/1.07  thf('62', plain,
% 0.84/1.07      (![X0 : $i, X1 : $i]:
% 0.84/1.07         (~ (v1_relat_1 @ X0)
% 0.84/1.07          | ~ (v1_funct_1 @ X0)
% 0.84/1.07          | (v2_funct_1 @ X1)
% 0.84/1.07          | ((k2_relat_1 @ X0) != (k1_relat_1 @ X1))
% 0.84/1.07          | ~ (v2_funct_1 @ (k5_relat_1 @ X0 @ X1))
% 0.84/1.07          | ~ (v1_funct_1 @ X1)
% 0.84/1.07          | ~ (v1_relat_1 @ X1))),
% 0.84/1.07      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.84/1.07  thf('63', plain,
% 0.84/1.07      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 0.84/1.07        | ~ (v1_relat_1 @ sk_D)
% 0.84/1.07        | ~ (v1_funct_1 @ sk_D)
% 0.84/1.07        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.84/1.07        | (v2_funct_1 @ sk_D)
% 0.84/1.07        | ~ (v1_funct_1 @ sk_C)
% 0.84/1.07        | ~ (v1_relat_1 @ sk_C))),
% 0.84/1.07      inference('sup-', [status(thm)], ['61', '62'])).
% 0.84/1.07  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 0.84/1.07  thf('64', plain, (![X2 : $i]: (v2_funct_1 @ (k6_relat_1 @ X2))),
% 0.84/1.07      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.84/1.07  thf('65', plain,
% 0.84/1.07      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf(cc1_relset_1, axiom,
% 0.84/1.07    (![A:$i,B:$i,C:$i]:
% 0.84/1.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.84/1.07       ( v1_relat_1 @ C ) ))).
% 0.84/1.07  thf('66', plain,
% 0.84/1.07      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.84/1.07         ((v1_relat_1 @ X5)
% 0.84/1.07          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.84/1.07      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.84/1.07  thf('67', plain, ((v1_relat_1 @ sk_D)),
% 0.84/1.07      inference('sup-', [status(thm)], ['65', '66'])).
% 0.84/1.07  thf('68', plain, ((v1_funct_1 @ sk_D)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('69', plain,
% 0.84/1.07      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('70', plain,
% 0.84/1.07      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.84/1.07         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 0.84/1.07          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.84/1.07      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.84/1.07  thf('71', plain,
% 0.84/1.07      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.84/1.07      inference('sup-', [status(thm)], ['69', '70'])).
% 0.84/1.07  thf('72', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('73', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.84/1.07      inference('sup+', [status(thm)], ['71', '72'])).
% 0.84/1.07  thf('74', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf(d1_funct_2, axiom,
% 0.84/1.07    (![A:$i,B:$i,C:$i]:
% 0.84/1.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.84/1.07       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.84/1.07           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.84/1.07             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.84/1.07         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.84/1.07           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.84/1.07             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.84/1.07  thf(zf_stmt_1, axiom,
% 0.84/1.07    (![C:$i,B:$i,A:$i]:
% 0.84/1.07     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.84/1.07       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.84/1.07  thf('75', plain,
% 0.84/1.07      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.84/1.07         (~ (v1_funct_2 @ X22 @ X20 @ X21)
% 0.84/1.07          | ((X20) = (k1_relset_1 @ X20 @ X21 @ X22))
% 0.84/1.07          | ~ (zip_tseitin_1 @ X22 @ X21 @ X20))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.84/1.07  thf('76', plain,
% 0.84/1.07      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 0.84/1.07        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 0.84/1.07      inference('sup-', [status(thm)], ['74', '75'])).
% 0.84/1.07  thf(zf_stmt_2, axiom,
% 0.84/1.07    (![B:$i,A:$i]:
% 0.84/1.07     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.84/1.07       ( zip_tseitin_0 @ B @ A ) ))).
% 0.84/1.07  thf('77', plain,
% 0.84/1.07      (![X18 : $i, X19 : $i]:
% 0.84/1.07         ((zip_tseitin_0 @ X18 @ X19) | ((X18) = (k1_xboole_0)))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.84/1.07  thf('78', plain,
% 0.84/1.07      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.84/1.07  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.84/1.07  thf(zf_stmt_5, axiom,
% 0.84/1.07    (![A:$i,B:$i,C:$i]:
% 0.84/1.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.84/1.07       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.84/1.07         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.84/1.07           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.84/1.07             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.84/1.07  thf('79', plain,
% 0.84/1.07      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.84/1.07         (~ (zip_tseitin_0 @ X23 @ X24)
% 0.84/1.07          | (zip_tseitin_1 @ X25 @ X23 @ X24)
% 0.84/1.07          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23))))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.84/1.07  thf('80', plain,
% 0.84/1.07      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 0.84/1.07      inference('sup-', [status(thm)], ['78', '79'])).
% 0.84/1.07  thf('81', plain,
% 0.84/1.07      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 0.84/1.07      inference('sup-', [status(thm)], ['77', '80'])).
% 0.84/1.07  thf('82', plain, (((sk_A) != (k1_xboole_0))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('83', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 0.84/1.07      inference('simplify_reflect-', [status(thm)], ['81', '82'])).
% 0.84/1.07  thf('84', plain,
% 0.84/1.07      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf(redefinition_k1_relset_1, axiom,
% 0.84/1.07    (![A:$i,B:$i,C:$i]:
% 0.84/1.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.84/1.07       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.84/1.07  thf('85', plain,
% 0.84/1.07      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.84/1.07         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 0.84/1.07          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.84/1.07      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.84/1.07  thf('86', plain,
% 0.84/1.07      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.84/1.07      inference('sup-', [status(thm)], ['84', '85'])).
% 0.84/1.07  thf('87', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.84/1.07      inference('demod', [status(thm)], ['76', '83', '86'])).
% 0.84/1.07  thf('88', plain, ((v1_funct_1 @ sk_C)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('89', plain,
% 0.84/1.07      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('90', plain,
% 0.84/1.07      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.84/1.07         ((v1_relat_1 @ X5)
% 0.84/1.07          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.84/1.07      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.84/1.07  thf('91', plain, ((v1_relat_1 @ sk_C)),
% 0.84/1.07      inference('sup-', [status(thm)], ['89', '90'])).
% 0.84/1.07  thf('92', plain, ((((sk_B) != (sk_B)) | (v2_funct_1 @ sk_D))),
% 0.84/1.07      inference('demod', [status(thm)],
% 0.84/1.07                ['63', '64', '67', '68', '73', '87', '88', '91'])).
% 0.84/1.07  thf('93', plain, ((v2_funct_1 @ sk_D)),
% 0.84/1.07      inference('simplify', [status(thm)], ['92'])).
% 0.84/1.07  thf('94', plain,
% 0.84/1.07      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 0.84/1.07      inference('demod', [status(thm)], ['51', '93'])).
% 0.84/1.07  thf('95', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.84/1.07      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.84/1.07  thf(t64_funct_1, axiom,
% 0.84/1.07    (![A:$i]:
% 0.84/1.07     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.84/1.07       ( ![B:$i]:
% 0.84/1.07         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.84/1.07           ( ( ( v2_funct_1 @ A ) & 
% 0.84/1.07               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.84/1.07               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.84/1.07             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.84/1.07  thf('96', plain,
% 0.84/1.07      (![X3 : $i, X4 : $i]:
% 0.84/1.07         (~ (v1_relat_1 @ X3)
% 0.84/1.07          | ~ (v1_funct_1 @ X3)
% 0.84/1.07          | ((X3) = (k2_funct_1 @ X4))
% 0.84/1.07          | ((k5_relat_1 @ X3 @ X4) != (k6_relat_1 @ (k2_relat_1 @ X4)))
% 0.84/1.07          | ((k2_relat_1 @ X3) != (k1_relat_1 @ X4))
% 0.84/1.07          | ~ (v2_funct_1 @ X4)
% 0.84/1.07          | ~ (v1_funct_1 @ X4)
% 0.84/1.07          | ~ (v1_relat_1 @ X4))),
% 0.84/1.07      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.84/1.07  thf('97', plain,
% 0.84/1.07      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ (k2_relat_1 @ sk_D)))
% 0.84/1.07        | ~ (v1_relat_1 @ sk_D)
% 0.84/1.07        | ~ (v1_funct_1 @ sk_D)
% 0.84/1.07        | ~ (v2_funct_1 @ sk_D)
% 0.84/1.07        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.84/1.07        | ((sk_C) = (k2_funct_1 @ sk_D))
% 0.84/1.07        | ~ (v1_funct_1 @ sk_C)
% 0.84/1.07        | ~ (v1_relat_1 @ sk_C))),
% 0.84/1.07      inference('sup-', [status(thm)], ['95', '96'])).
% 0.84/1.07  thf('98', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.84/1.07      inference('demod', [status(thm)], ['40', '44', '45', '46', '47', '48'])).
% 0.84/1.07  thf('99', plain, ((v1_relat_1 @ sk_D)),
% 0.84/1.07      inference('sup-', [status(thm)], ['65', '66'])).
% 0.84/1.07  thf('100', plain, ((v1_funct_1 @ sk_D)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('101', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.84/1.07      inference('sup+', [status(thm)], ['71', '72'])).
% 0.84/1.07  thf('102', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.84/1.07      inference('demod', [status(thm)], ['76', '83', '86'])).
% 0.84/1.07  thf('103', plain, ((v1_funct_1 @ sk_C)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('104', plain, ((v1_relat_1 @ sk_C)),
% 0.84/1.07      inference('sup-', [status(thm)], ['89', '90'])).
% 0.84/1.07  thf('105', plain,
% 0.84/1.07      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ sk_A))
% 0.84/1.07        | ~ (v2_funct_1 @ sk_D)
% 0.84/1.07        | ((sk_B) != (sk_B))
% 0.84/1.07        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 0.84/1.07      inference('demod', [status(thm)],
% 0.84/1.07                ['97', '98', '99', '100', '101', '102', '103', '104'])).
% 0.84/1.07  thf('106', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 0.84/1.07      inference('simplify', [status(thm)], ['105'])).
% 0.84/1.07  thf('107', plain, ((v2_funct_1 @ sk_D)),
% 0.84/1.07      inference('simplify', [status(thm)], ['92'])).
% 0.84/1.07  thf('108', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.84/1.07      inference('demod', [status(thm)], ['106', '107'])).
% 0.84/1.07  thf('109', plain, (((k5_relat_1 @ sk_D @ sk_C) = (k6_relat_1 @ sk_B))),
% 0.84/1.07      inference('demod', [status(thm)], ['94', '108'])).
% 0.84/1.07  thf('110', plain,
% 0.84/1.07      (![X3 : $i, X4 : $i]:
% 0.84/1.07         (~ (v1_relat_1 @ X3)
% 0.84/1.07          | ~ (v1_funct_1 @ X3)
% 0.84/1.07          | ((X3) = (k2_funct_1 @ X4))
% 0.84/1.07          | ((k5_relat_1 @ X3 @ X4) != (k6_relat_1 @ (k2_relat_1 @ X4)))
% 0.84/1.07          | ((k2_relat_1 @ X3) != (k1_relat_1 @ X4))
% 0.84/1.07          | ~ (v2_funct_1 @ X4)
% 0.84/1.07          | ~ (v1_funct_1 @ X4)
% 0.84/1.07          | ~ (v1_relat_1 @ X4))),
% 0.84/1.07      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.84/1.07  thf('111', plain,
% 0.84/1.07      ((((k6_relat_1 @ sk_B) != (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.84/1.07        | ~ (v1_relat_1 @ sk_C)
% 0.84/1.07        | ~ (v1_funct_1 @ sk_C)
% 0.84/1.07        | ~ (v2_funct_1 @ sk_C)
% 0.84/1.07        | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ sk_C))
% 0.84/1.07        | ((sk_D) = (k2_funct_1 @ sk_C))
% 0.84/1.07        | ~ (v1_funct_1 @ sk_D)
% 0.84/1.07        | ~ (v1_relat_1 @ sk_D))),
% 0.84/1.07      inference('sup-', [status(thm)], ['109', '110'])).
% 0.84/1.07  thf('112', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.84/1.07      inference('sup+', [status(thm)], ['71', '72'])).
% 0.84/1.07  thf('113', plain, ((v1_relat_1 @ sk_C)),
% 0.84/1.07      inference('sup-', [status(thm)], ['89', '90'])).
% 0.84/1.07  thf('114', plain, ((v1_funct_1 @ sk_C)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('115', plain, ((v2_funct_1 @ sk_C)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('116', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.84/1.07      inference('demod', [status(thm)], ['40', '44', '45', '46', '47', '48'])).
% 0.84/1.07  thf('117', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('118', plain,
% 0.84/1.07      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.84/1.07         (~ (v1_funct_2 @ X22 @ X20 @ X21)
% 0.84/1.07          | ((X20) = (k1_relset_1 @ X20 @ X21 @ X22))
% 0.84/1.07          | ~ (zip_tseitin_1 @ X22 @ X21 @ X20))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.84/1.07  thf('119', plain,
% 0.84/1.07      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.84/1.07        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.84/1.07      inference('sup-', [status(thm)], ['117', '118'])).
% 0.84/1.07  thf('120', plain,
% 0.84/1.07      (![X18 : $i, X19 : $i]:
% 0.84/1.07         ((zip_tseitin_0 @ X18 @ X19) | ((X18) = (k1_xboole_0)))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.84/1.07  thf('121', plain,
% 0.84/1.07      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('122', plain,
% 0.84/1.07      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.84/1.07         (~ (zip_tseitin_0 @ X23 @ X24)
% 0.84/1.07          | (zip_tseitin_1 @ X25 @ X23 @ X24)
% 0.84/1.07          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23))))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.84/1.07  thf('123', plain,
% 0.84/1.07      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.84/1.07      inference('sup-', [status(thm)], ['121', '122'])).
% 0.84/1.07  thf('124', plain,
% 0.84/1.07      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.84/1.07      inference('sup-', [status(thm)], ['120', '123'])).
% 0.84/1.07  thf('125', plain, (((sk_B) != (k1_xboole_0))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('126', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.84/1.07      inference('simplify_reflect-', [status(thm)], ['124', '125'])).
% 0.84/1.07  thf('127', plain,
% 0.84/1.07      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('128', plain,
% 0.84/1.07      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.84/1.07         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 0.84/1.07          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.84/1.07      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.84/1.07  thf('129', plain,
% 0.84/1.07      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.84/1.07      inference('sup-', [status(thm)], ['127', '128'])).
% 0.84/1.07  thf('130', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.84/1.07      inference('demod', [status(thm)], ['119', '126', '129'])).
% 0.84/1.07  thf('131', plain, ((v1_funct_1 @ sk_D)),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('132', plain, ((v1_relat_1 @ sk_D)),
% 0.84/1.07      inference('sup-', [status(thm)], ['65', '66'])).
% 0.84/1.07  thf('133', plain,
% 0.84/1.07      ((((k6_relat_1 @ sk_B) != (k6_relat_1 @ sk_B))
% 0.84/1.07        | ((sk_A) != (sk_A))
% 0.84/1.07        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 0.84/1.07      inference('demod', [status(thm)],
% 0.84/1.07                ['111', '112', '113', '114', '115', '116', '130', '131', '132'])).
% 0.84/1.07  thf('134', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 0.84/1.07      inference('simplify', [status(thm)], ['133'])).
% 0.84/1.07  thf('135', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf('136', plain, ($false),
% 0.84/1.07      inference('simplify_reflect-', [status(thm)], ['134', '135'])).
% 0.84/1.07  
% 0.84/1.07  % SZS output end Refutation
% 0.84/1.07  
% 0.84/1.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

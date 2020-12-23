%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yH1pJWvq9U

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:53 EST 2020

% Result     : Theorem 5.46s
% Output     : Refutation 5.46s
% Verified   : 
% Statistics : Number of formulae       :  262 (1579 expanded)
%              Number of leaves         :   53 ( 492 expanded)
%              Depth                    :   30
%              Number of atoms          : 2559 (39944 expanded)
%              Number of equality atoms :  168 (2571 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X59: $i,X60: $i,X61: $i] :
      ( ( X59 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X60 )
      | ~ ( v1_funct_2 @ X60 @ X61 @ X59 )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X61 @ X59 ) ) )
      | ( ( k5_relat_1 @ X60 @ ( k2_funct_1 @ X60 ) )
        = ( k6_partfun1 @ X61 ) )
      | ~ ( v2_funct_1 @ X60 )
      | ( ( k2_relset_1 @ X61 @ X59 @ X60 )
       != X59 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ( X59 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X60 )
      | ~ ( v1_funct_2 @ X60 @ X61 @ X59 )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X61 @ X59 ) ) )
      | ( ( k5_relat_1 @ X60 @ ( k2_funct_1 @ X60 ) )
        = ( k6_relat_1 @ X61 ) )
      | ~ ( v2_funct_1 @ X60 )
      | ( ( k2_relset_1 @ X61 @ X59 @ X60 )
       != X59 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
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
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X33 ) ) ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( X24 = X27 )
      | ~ ( r2_relset_1 @ X25 @ X26 @ X24 @ X27 ) ) ),
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
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('29',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('30',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
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

thf('34',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('35',plain,(
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
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('42',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( r2_relset_1 @ X25 @ X26 @ X24 @ X27 )
      | ( X24 != X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('43',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_relset_1 @ X25 @ X26 @ X27 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
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

thf('52',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('53',plain,(
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

thf('54',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_2 @ X51 @ X52 @ X53 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) )
      | ( zip_tseitin_0 @ X51 @ X54 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X55 @ X52 @ X52 @ X53 @ X54 @ X51 ) )
      | ( zip_tseitin_1 @ X53 @ X52 )
      | ( ( k2_relset_1 @ X55 @ X52 @ X54 )
       != X52 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X52 ) ) )
      | ~ ( v1_funct_2 @ X54 @ X55 @ X52 )
      | ~ ( v1_funct_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('55',plain,(
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
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['52','58'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('60',plain,(
    ! [X11: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('61',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['59','60','61','62','63','64'])).

thf('66',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X49: $i,X50: $i] :
      ( ( X49 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('68',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X47: $i,X48: $i] :
      ( ( v2_funct_1 @ X48 )
      | ~ ( zip_tseitin_0 @ X48 @ X47 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('72',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['51','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
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

thf('76',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( ( k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39 )
        = ( k5_relat_1 @ X36 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['74','79'])).

thf('81',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('83',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['80','81','82'])).

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

thf('84',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( X13
        = ( k2_funct_1 @ X14 ) )
      | ( ( k5_relat_1 @ X13 @ X14 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X14 ) ) )
      | ( ( k2_relat_1 @ X13 )
       != ( k1_relat_1 @ X14 ) )
      | ~ ( v2_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('85',plain,
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
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['40','44','45','46','47','48'])).

thf('87',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('89',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('90',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('91',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('95',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('101',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('103',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['85','86','91','92','97','98','103'])).

thf('105',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['70','71'])).

thf('107',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('108',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k1_relat_1 @ X12 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('109',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf('110',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ~ ( v2_funct_1 @ X56 )
      | ( ( k2_relset_1 @ X58 @ X57 @ X56 )
       != X57 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X56 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X58 ) ) )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X57 ) ) )
      | ~ ( v1_funct_2 @ X56 @ X58 @ X57 )
      | ~ ( v1_funct_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('111',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('115',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['111','112','113','114'])).

thf('116',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['40','44','45','46','47','48'])).

thf('117',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ~ ( v2_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['70','71'])).

thf('120',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('121',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v4_relat_1 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('122',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_D ) @ sk_A ),
    inference('sup-',[status(thm)],['120','121'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('123',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v4_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('124',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_D ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('126',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('127',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_D ) ) @ sk_A ),
    inference(demod,[status(thm)],['124','127'])).

thf('129',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['40','44','45','46','47','48'])).

thf(t47_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('130',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X6 @ X7 ) )
        = ( k2_relat_1 @ X7 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X7 ) @ ( k2_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['89','90'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['128','133'])).

thf('135',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['51','72'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('136',plain,(
    ! [X9: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('137',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('138',plain,
    ( sk_B
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['134','135','136','137'])).

thf('139',plain,
    ( ( sk_B
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['108','138'])).

thf('140',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['89','90'])).

thf('141',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['70','71'])).

thf('143',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['139','140','141','142'])).

thf('144',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['107','143'])).

thf('145',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,
    ( ( k5_relat_1 @ sk_D @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['73','145'])).

thf('147',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( X13
        = ( k2_funct_1 @ X14 ) )
      | ( ( k5_relat_1 @ X13 @ X14 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X14 ) ) )
      | ( ( k2_relat_1 @ X13 )
       != ( k1_relat_1 @ X14 ) )
      | ~ ( v2_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('148',plain,
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
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['95','96'])).

thf('150',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['101','102'])).

thf('151',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['40','44','45','46','47','48'])).

thf('154',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k1_relat_1 @ X12 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('155',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ~ ( v2_funct_1 @ X56 )
      | ( ( k2_relset_1 @ X58 @ X57 @ X56 )
       != X57 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X56 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X58 ) ) )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X57 ) ) )
      | ~ ( v1_funct_2 @ X56 @ X58 @ X57 )
      | ~ ( v1_funct_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('157',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['157','158','159','160','161'])).

thf('163',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('165',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('167',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v4_relat_1 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('168',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v4_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('170',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('172',plain,(
    ! [X8: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('173',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['170','171','172'])).

thf('174',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_relat_1 @ X12 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('175',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X6 @ X7 ) )
        = ( k2_relat_1 @ X7 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X7 ) @ ( k2_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['173','176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['177'])).

thf('179',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['165','178'])).

thf('180',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['101','102'])).

thf('181',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['179','180','181','182'])).

thf('184',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ( X59 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X60 )
      | ~ ( v1_funct_2 @ X60 @ X61 @ X59 )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X61 @ X59 ) ) )
      | ( ( k5_relat_1 @ X60 @ ( k2_funct_1 @ X60 ) )
        = ( k6_relat_1 @ X61 ) )
      | ~ ( v2_funct_1 @ X60 )
      | ( ( k2_relset_1 @ X61 @ X59 @ X60 )
       != X59 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('186',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['186','187','188','189','190'])).

thf('192',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['191'])).

thf('193',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['192','193'])).

thf('195',plain,(
    ! [X9: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('196',plain,
    ( sk_A
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['183','194','195'])).

thf('197',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['154','196'])).

thf('198',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['101','102'])).

thf('199',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['197','198','199','200'])).

thf('202',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['89','90'])).

thf('204',plain,
    ( ( ( k6_relat_1 @ sk_B )
     != ( k6_relat_1 @ sk_B ) )
    | ( sk_A != sk_A )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['148','149','150','151','152','153','201','202','203'])).

thf('205',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['204'])).

thf('206',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['205','206'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yH1pJWvq9U
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:45:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 5.46/5.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.46/5.67  % Solved by: fo/fo7.sh
% 5.46/5.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.46/5.67  % done 1736 iterations in 5.211s
% 5.46/5.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.46/5.67  % SZS output start Refutation
% 5.46/5.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.46/5.67  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 5.46/5.67  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 5.46/5.67  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 5.46/5.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 5.46/5.67  thf(sk_A_type, type, sk_A: $i).
% 5.46/5.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.46/5.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.46/5.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 5.46/5.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.46/5.67  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 5.46/5.67  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 5.46/5.67  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 5.46/5.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 5.46/5.67  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 5.46/5.67  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 5.46/5.67  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 5.46/5.67  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 5.46/5.67  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 5.46/5.67  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 5.46/5.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 5.46/5.67  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 5.46/5.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.46/5.67  thf(sk_D_type, type, sk_D: $i).
% 5.46/5.67  thf(sk_C_type, type, sk_C: $i).
% 5.46/5.67  thf(sk_B_type, type, sk_B: $i).
% 5.46/5.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.46/5.67  thf(t36_funct_2, conjecture,
% 5.46/5.67    (![A:$i,B:$i,C:$i]:
% 5.46/5.67     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.46/5.67         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.46/5.67       ( ![D:$i]:
% 5.46/5.67         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 5.46/5.67             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 5.46/5.67           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 5.46/5.67               ( r2_relset_1 @
% 5.46/5.67                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 5.46/5.67                 ( k6_partfun1 @ A ) ) & 
% 5.46/5.67               ( v2_funct_1 @ C ) ) =>
% 5.46/5.67             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 5.46/5.67               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 5.46/5.67  thf(zf_stmt_0, negated_conjecture,
% 5.46/5.67    (~( ![A:$i,B:$i,C:$i]:
% 5.46/5.67        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.46/5.67            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.46/5.67          ( ![D:$i]:
% 5.46/5.67            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 5.46/5.67                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 5.46/5.67              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 5.46/5.67                  ( r2_relset_1 @
% 5.46/5.67                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 5.46/5.67                    ( k6_partfun1 @ A ) ) & 
% 5.46/5.67                  ( v2_funct_1 @ C ) ) =>
% 5.46/5.67                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 5.46/5.67                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 5.46/5.67    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 5.46/5.67  thf('0', plain,
% 5.46/5.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf(t35_funct_2, axiom,
% 5.46/5.67    (![A:$i,B:$i,C:$i]:
% 5.46/5.67     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.46/5.67         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.46/5.67       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 5.46/5.67         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 5.46/5.67           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 5.46/5.67             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 5.46/5.67  thf('1', plain,
% 5.46/5.67      (![X59 : $i, X60 : $i, X61 : $i]:
% 5.46/5.67         (((X59) = (k1_xboole_0))
% 5.46/5.67          | ~ (v1_funct_1 @ X60)
% 5.46/5.67          | ~ (v1_funct_2 @ X60 @ X61 @ X59)
% 5.46/5.67          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X61 @ X59)))
% 5.46/5.67          | ((k5_relat_1 @ X60 @ (k2_funct_1 @ X60)) = (k6_partfun1 @ X61))
% 5.46/5.67          | ~ (v2_funct_1 @ X60)
% 5.46/5.67          | ((k2_relset_1 @ X61 @ X59 @ X60) != (X59)))),
% 5.46/5.67      inference('cnf', [status(esa)], [t35_funct_2])).
% 5.46/5.67  thf(redefinition_k6_partfun1, axiom,
% 5.46/5.67    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 5.46/5.67  thf('2', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 5.46/5.67      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.46/5.67  thf('3', plain,
% 5.46/5.67      (![X59 : $i, X60 : $i, X61 : $i]:
% 5.46/5.67         (((X59) = (k1_xboole_0))
% 5.46/5.67          | ~ (v1_funct_1 @ X60)
% 5.46/5.67          | ~ (v1_funct_2 @ X60 @ X61 @ X59)
% 5.46/5.67          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X61 @ X59)))
% 5.46/5.67          | ((k5_relat_1 @ X60 @ (k2_funct_1 @ X60)) = (k6_relat_1 @ X61))
% 5.46/5.67          | ~ (v2_funct_1 @ X60)
% 5.46/5.67          | ((k2_relset_1 @ X61 @ X59 @ X60) != (X59)))),
% 5.46/5.67      inference('demod', [status(thm)], ['1', '2'])).
% 5.46/5.67  thf('4', plain,
% 5.46/5.67      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 5.46/5.67        | ~ (v2_funct_1 @ sk_D)
% 5.46/5.67        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 5.46/5.67        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 5.46/5.67        | ~ (v1_funct_1 @ sk_D)
% 5.46/5.67        | ((sk_A) = (k1_xboole_0)))),
% 5.46/5.67      inference('sup-', [status(thm)], ['0', '3'])).
% 5.46/5.67  thf('5', plain,
% 5.46/5.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf(redefinition_k2_relset_1, axiom,
% 5.46/5.67    (![A:$i,B:$i,C:$i]:
% 5.46/5.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.46/5.67       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 5.46/5.67  thf('6', plain,
% 5.46/5.67      (![X21 : $i, X22 : $i, X23 : $i]:
% 5.46/5.67         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 5.46/5.67          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 5.46/5.67      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 5.46/5.67  thf('7', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 5.46/5.67      inference('sup-', [status(thm)], ['5', '6'])).
% 5.46/5.67  thf('8', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('10', plain,
% 5.46/5.67      ((((k2_relat_1 @ sk_D) != (sk_A))
% 5.46/5.67        | ~ (v2_funct_1 @ sk_D)
% 5.46/5.67        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 5.46/5.67        | ((sk_A) = (k1_xboole_0)))),
% 5.46/5.67      inference('demod', [status(thm)], ['4', '7', '8', '9'])).
% 5.46/5.67  thf('11', plain, (((sk_A) != (k1_xboole_0))),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('12', plain,
% 5.46/5.67      ((((k2_relat_1 @ sk_D) != (sk_A))
% 5.46/5.67        | ~ (v2_funct_1 @ sk_D)
% 5.46/5.67        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B)))),
% 5.46/5.67      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 5.46/5.67  thf('13', plain,
% 5.46/5.67      ((r2_relset_1 @ sk_A @ sk_A @ 
% 5.46/5.67        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 5.46/5.67        (k6_partfun1 @ sk_A))),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('14', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 5.46/5.67      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.46/5.67  thf('15', plain,
% 5.46/5.67      ((r2_relset_1 @ sk_A @ sk_A @ 
% 5.46/5.67        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 5.46/5.67        (k6_relat_1 @ sk_A))),
% 5.46/5.67      inference('demod', [status(thm)], ['13', '14'])).
% 5.46/5.67  thf('16', plain,
% 5.46/5.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('17', plain,
% 5.46/5.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf(dt_k1_partfun1, axiom,
% 5.46/5.67    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 5.46/5.67     ( ( ( v1_funct_1 @ E ) & 
% 5.46/5.67         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.46/5.67         ( v1_funct_1 @ F ) & 
% 5.46/5.67         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 5.46/5.67       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 5.46/5.67         ( m1_subset_1 @
% 5.46/5.67           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 5.46/5.67           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 5.46/5.67  thf('18', plain,
% 5.46/5.67      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 5.46/5.67         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 5.46/5.67          | ~ (v1_funct_1 @ X28)
% 5.46/5.67          | ~ (v1_funct_1 @ X31)
% 5.46/5.67          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 5.46/5.67          | (m1_subset_1 @ (k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31) @ 
% 5.46/5.67             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X33))))),
% 5.46/5.67      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 5.46/5.67  thf('19', plain,
% 5.46/5.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.46/5.67         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 5.46/5.67           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 5.46/5.67          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 5.46/5.67          | ~ (v1_funct_1 @ X1)
% 5.46/5.67          | ~ (v1_funct_1 @ sk_C))),
% 5.46/5.67      inference('sup-', [status(thm)], ['17', '18'])).
% 5.46/5.67  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('21', plain,
% 5.46/5.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.46/5.67         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 5.46/5.67           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 5.46/5.67          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 5.46/5.67          | ~ (v1_funct_1 @ X1))),
% 5.46/5.67      inference('demod', [status(thm)], ['19', '20'])).
% 5.46/5.67  thf('22', plain,
% 5.46/5.67      ((~ (v1_funct_1 @ sk_D)
% 5.46/5.67        | (m1_subset_1 @ 
% 5.46/5.67           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 5.46/5.67           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 5.46/5.67      inference('sup-', [status(thm)], ['16', '21'])).
% 5.46/5.67  thf('23', plain, ((v1_funct_1 @ sk_D)),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('24', plain,
% 5.46/5.67      ((m1_subset_1 @ 
% 5.46/5.67        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 5.46/5.67        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.46/5.67      inference('demod', [status(thm)], ['22', '23'])).
% 5.46/5.67  thf(redefinition_r2_relset_1, axiom,
% 5.46/5.67    (![A:$i,B:$i,C:$i,D:$i]:
% 5.46/5.67     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.46/5.67         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.46/5.67       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 5.46/5.67  thf('25', plain,
% 5.46/5.67      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 5.46/5.67         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 5.46/5.67          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 5.46/5.67          | ((X24) = (X27))
% 5.46/5.67          | ~ (r2_relset_1 @ X25 @ X26 @ X24 @ X27))),
% 5.46/5.67      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 5.46/5.67  thf('26', plain,
% 5.46/5.67      (![X0 : $i]:
% 5.46/5.67         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 5.46/5.67             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 5.46/5.67          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 5.46/5.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 5.46/5.67      inference('sup-', [status(thm)], ['24', '25'])).
% 5.46/5.67  thf('27', plain,
% 5.46/5.67      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 5.46/5.67           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 5.46/5.67        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 5.46/5.67            = (k6_relat_1 @ sk_A)))),
% 5.46/5.67      inference('sup-', [status(thm)], ['15', '26'])).
% 5.46/5.67  thf(dt_k6_partfun1, axiom,
% 5.46/5.67    (![A:$i]:
% 5.46/5.67     ( ( m1_subset_1 @
% 5.46/5.67         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 5.46/5.67       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 5.46/5.67  thf('28', plain,
% 5.46/5.67      (![X35 : $i]:
% 5.46/5.67         (m1_subset_1 @ (k6_partfun1 @ X35) @ 
% 5.46/5.67          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 5.46/5.67      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 5.46/5.67  thf('29', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 5.46/5.67      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.46/5.67  thf('30', plain,
% 5.46/5.67      (![X35 : $i]:
% 5.46/5.67         (m1_subset_1 @ (k6_relat_1 @ X35) @ 
% 5.46/5.67          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 5.46/5.67      inference('demod', [status(thm)], ['28', '29'])).
% 5.46/5.67  thf('31', plain,
% 5.46/5.67      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 5.46/5.67         = (k6_relat_1 @ sk_A))),
% 5.46/5.67      inference('demod', [status(thm)], ['27', '30'])).
% 5.46/5.67  thf('32', plain,
% 5.46/5.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf(t24_funct_2, axiom,
% 5.46/5.67    (![A:$i,B:$i,C:$i]:
% 5.46/5.67     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.46/5.67         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.46/5.67       ( ![D:$i]:
% 5.46/5.67         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 5.46/5.67             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 5.46/5.67           ( ( r2_relset_1 @
% 5.46/5.67               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 5.46/5.67               ( k6_partfun1 @ B ) ) =>
% 5.46/5.67             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 5.46/5.67  thf('33', plain,
% 5.46/5.67      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 5.46/5.67         (~ (v1_funct_1 @ X43)
% 5.46/5.67          | ~ (v1_funct_2 @ X43 @ X44 @ X45)
% 5.46/5.67          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 5.46/5.67          | ~ (r2_relset_1 @ X44 @ X44 @ 
% 5.46/5.67               (k1_partfun1 @ X44 @ X45 @ X45 @ X44 @ X43 @ X46) @ 
% 5.46/5.67               (k6_partfun1 @ X44))
% 5.46/5.67          | ((k2_relset_1 @ X45 @ X44 @ X46) = (X44))
% 5.46/5.67          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 5.46/5.67          | ~ (v1_funct_2 @ X46 @ X45 @ X44)
% 5.46/5.67          | ~ (v1_funct_1 @ X46))),
% 5.46/5.67      inference('cnf', [status(esa)], [t24_funct_2])).
% 5.46/5.67  thf('34', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 5.46/5.67      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.46/5.67  thf('35', plain,
% 5.46/5.67      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 5.46/5.67         (~ (v1_funct_1 @ X43)
% 5.46/5.67          | ~ (v1_funct_2 @ X43 @ X44 @ X45)
% 5.46/5.67          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 5.46/5.67          | ~ (r2_relset_1 @ X44 @ X44 @ 
% 5.46/5.67               (k1_partfun1 @ X44 @ X45 @ X45 @ X44 @ X43 @ X46) @ 
% 5.46/5.67               (k6_relat_1 @ X44))
% 5.46/5.67          | ((k2_relset_1 @ X45 @ X44 @ X46) = (X44))
% 5.46/5.67          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 5.46/5.67          | ~ (v1_funct_2 @ X46 @ X45 @ X44)
% 5.46/5.67          | ~ (v1_funct_1 @ X46))),
% 5.46/5.67      inference('demod', [status(thm)], ['33', '34'])).
% 5.46/5.67  thf('36', plain,
% 5.46/5.67      (![X0 : $i]:
% 5.46/5.67         (~ (v1_funct_1 @ X0)
% 5.46/5.67          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 5.46/5.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 5.46/5.67          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 5.46/5.67          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 5.46/5.67               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 5.46/5.67               (k6_relat_1 @ sk_A))
% 5.46/5.67          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 5.46/5.67          | ~ (v1_funct_1 @ sk_C))),
% 5.46/5.67      inference('sup-', [status(thm)], ['32', '35'])).
% 5.46/5.67  thf('37', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('38', plain, ((v1_funct_1 @ sk_C)),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('39', plain,
% 5.46/5.67      (![X0 : $i]:
% 5.46/5.67         (~ (v1_funct_1 @ X0)
% 5.46/5.67          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 5.46/5.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 5.46/5.67          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 5.46/5.67          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 5.46/5.67               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 5.46/5.67               (k6_relat_1 @ sk_A)))),
% 5.46/5.67      inference('demod', [status(thm)], ['36', '37', '38'])).
% 5.46/5.67  thf('40', plain,
% 5.46/5.67      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 5.46/5.67           (k6_relat_1 @ sk_A))
% 5.46/5.67        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 5.46/5.67        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 5.46/5.67        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 5.46/5.67        | ~ (v1_funct_1 @ sk_D))),
% 5.46/5.67      inference('sup-', [status(thm)], ['31', '39'])).
% 5.46/5.67  thf('41', plain,
% 5.46/5.67      (![X35 : $i]:
% 5.46/5.67         (m1_subset_1 @ (k6_relat_1 @ X35) @ 
% 5.46/5.67          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 5.46/5.67      inference('demod', [status(thm)], ['28', '29'])).
% 5.46/5.67  thf('42', plain,
% 5.46/5.67      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 5.46/5.67         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 5.46/5.67          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 5.46/5.67          | (r2_relset_1 @ X25 @ X26 @ X24 @ X27)
% 5.46/5.67          | ((X24) != (X27)))),
% 5.46/5.67      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 5.46/5.67  thf('43', plain,
% 5.46/5.67      (![X25 : $i, X26 : $i, X27 : $i]:
% 5.46/5.67         ((r2_relset_1 @ X25 @ X26 @ X27 @ X27)
% 5.46/5.67          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 5.46/5.67      inference('simplify', [status(thm)], ['42'])).
% 5.46/5.67  thf('44', plain,
% 5.46/5.67      (![X0 : $i]:
% 5.46/5.67         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 5.46/5.67      inference('sup-', [status(thm)], ['41', '43'])).
% 5.46/5.67  thf('45', plain,
% 5.46/5.67      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 5.46/5.67      inference('sup-', [status(thm)], ['5', '6'])).
% 5.46/5.67  thf('46', plain,
% 5.46/5.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('47', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('48', plain, ((v1_funct_1 @ sk_D)),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('49', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 5.46/5.67      inference('demod', [status(thm)], ['40', '44', '45', '46', '47', '48'])).
% 5.46/5.67  thf('50', plain,
% 5.46/5.67      ((((sk_A) != (sk_A))
% 5.46/5.67        | ~ (v2_funct_1 @ sk_D)
% 5.46/5.67        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B)))),
% 5.46/5.67      inference('demod', [status(thm)], ['12', '49'])).
% 5.46/5.67  thf('51', plain,
% 5.46/5.67      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 5.46/5.67        | ~ (v2_funct_1 @ sk_D))),
% 5.46/5.67      inference('simplify', [status(thm)], ['50'])).
% 5.46/5.67  thf('52', plain,
% 5.46/5.67      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 5.46/5.67         = (k6_relat_1 @ sk_A))),
% 5.46/5.67      inference('demod', [status(thm)], ['27', '30'])).
% 5.46/5.67  thf('53', plain,
% 5.46/5.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf(t30_funct_2, axiom,
% 5.46/5.67    (![A:$i,B:$i,C:$i,D:$i]:
% 5.46/5.67     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.46/5.67         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 5.46/5.67       ( ![E:$i]:
% 5.46/5.67         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 5.46/5.67             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 5.46/5.67           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 5.46/5.67               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 5.46/5.67             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 5.46/5.67               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 5.46/5.67  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 5.46/5.67  thf(zf_stmt_2, axiom,
% 5.46/5.67    (![C:$i,B:$i]:
% 5.46/5.67     ( ( zip_tseitin_1 @ C @ B ) =>
% 5.46/5.67       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 5.46/5.67  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 5.46/5.67  thf(zf_stmt_4, axiom,
% 5.46/5.67    (![E:$i,D:$i]:
% 5.46/5.67     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 5.46/5.67  thf(zf_stmt_5, axiom,
% 5.46/5.67    (![A:$i,B:$i,C:$i,D:$i]:
% 5.46/5.67     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 5.46/5.67         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.46/5.67       ( ![E:$i]:
% 5.46/5.67         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 5.46/5.67             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 5.46/5.67           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 5.46/5.67               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 5.46/5.67             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 5.46/5.67  thf('54', plain,
% 5.46/5.67      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 5.46/5.67         (~ (v1_funct_1 @ X51)
% 5.46/5.67          | ~ (v1_funct_2 @ X51 @ X52 @ X53)
% 5.46/5.67          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53)))
% 5.46/5.67          | (zip_tseitin_0 @ X51 @ X54)
% 5.46/5.67          | ~ (v2_funct_1 @ (k1_partfun1 @ X55 @ X52 @ X52 @ X53 @ X54 @ X51))
% 5.46/5.67          | (zip_tseitin_1 @ X53 @ X52)
% 5.46/5.67          | ((k2_relset_1 @ X55 @ X52 @ X54) != (X52))
% 5.46/5.67          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X52)))
% 5.46/5.67          | ~ (v1_funct_2 @ X54 @ X55 @ X52)
% 5.46/5.67          | ~ (v1_funct_1 @ X54))),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.46/5.67  thf('55', plain,
% 5.46/5.67      (![X0 : $i, X1 : $i]:
% 5.46/5.67         (~ (v1_funct_1 @ X0)
% 5.46/5.67          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 5.46/5.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 5.46/5.67          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 5.46/5.67          | (zip_tseitin_1 @ sk_A @ sk_B)
% 5.46/5.67          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 5.46/5.67          | (zip_tseitin_0 @ sk_D @ X0)
% 5.46/5.67          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 5.46/5.67          | ~ (v1_funct_1 @ sk_D))),
% 5.46/5.67      inference('sup-', [status(thm)], ['53', '54'])).
% 5.46/5.67  thf('56', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('57', plain, ((v1_funct_1 @ sk_D)),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('58', plain,
% 5.46/5.67      (![X0 : $i, X1 : $i]:
% 5.46/5.67         (~ (v1_funct_1 @ X0)
% 5.46/5.67          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 5.46/5.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 5.46/5.67          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 5.46/5.67          | (zip_tseitin_1 @ sk_A @ sk_B)
% 5.46/5.67          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 5.46/5.67          | (zip_tseitin_0 @ sk_D @ X0))),
% 5.46/5.67      inference('demod', [status(thm)], ['55', '56', '57'])).
% 5.46/5.67  thf('59', plain,
% 5.46/5.67      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 5.46/5.67        | (zip_tseitin_0 @ sk_D @ sk_C)
% 5.46/5.67        | (zip_tseitin_1 @ sk_A @ sk_B)
% 5.46/5.67        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 5.46/5.67        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 5.46/5.67        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 5.46/5.67        | ~ (v1_funct_1 @ sk_C))),
% 5.46/5.67      inference('sup-', [status(thm)], ['52', '58'])).
% 5.46/5.67  thf(fc4_funct_1, axiom,
% 5.46/5.67    (![A:$i]:
% 5.46/5.67     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 5.46/5.67       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 5.46/5.67  thf('60', plain, (![X11 : $i]: (v2_funct_1 @ (k6_relat_1 @ X11))),
% 5.46/5.67      inference('cnf', [status(esa)], [fc4_funct_1])).
% 5.46/5.67  thf('61', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('62', plain,
% 5.46/5.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('63', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('65', plain,
% 5.46/5.67      (((zip_tseitin_0 @ sk_D @ sk_C)
% 5.46/5.67        | (zip_tseitin_1 @ sk_A @ sk_B)
% 5.46/5.67        | ((sk_B) != (sk_B)))),
% 5.46/5.67      inference('demod', [status(thm)], ['59', '60', '61', '62', '63', '64'])).
% 5.46/5.67  thf('66', plain,
% 5.46/5.67      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 5.46/5.67      inference('simplify', [status(thm)], ['65'])).
% 5.46/5.67  thf('67', plain,
% 5.46/5.67      (![X49 : $i, X50 : $i]:
% 5.46/5.67         (((X49) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X49 @ X50))),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.46/5.67  thf('68', plain,
% 5.46/5.67      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 5.46/5.67      inference('sup-', [status(thm)], ['66', '67'])).
% 5.46/5.67  thf('69', plain, (((sk_A) != (k1_xboole_0))),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('70', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 5.46/5.67      inference('simplify_reflect-', [status(thm)], ['68', '69'])).
% 5.46/5.67  thf('71', plain,
% 5.46/5.67      (![X47 : $i, X48 : $i]:
% 5.46/5.67         ((v2_funct_1 @ X48) | ~ (zip_tseitin_0 @ X48 @ X47))),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_4])).
% 5.46/5.67  thf('72', plain, ((v2_funct_1 @ sk_D)),
% 5.46/5.67      inference('sup-', [status(thm)], ['70', '71'])).
% 5.46/5.67  thf('73', plain,
% 5.46/5.67      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 5.46/5.67      inference('demod', [status(thm)], ['51', '72'])).
% 5.46/5.67  thf('74', plain,
% 5.46/5.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('75', plain,
% 5.46/5.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf(redefinition_k1_partfun1, axiom,
% 5.46/5.67    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 5.46/5.67     ( ( ( v1_funct_1 @ E ) & 
% 5.46/5.67         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.46/5.67         ( v1_funct_1 @ F ) & 
% 5.46/5.67         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 5.46/5.67       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 5.46/5.67  thf('76', plain,
% 5.46/5.67      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 5.46/5.67         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 5.46/5.67          | ~ (v1_funct_1 @ X36)
% 5.46/5.67          | ~ (v1_funct_1 @ X39)
% 5.46/5.67          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 5.46/5.67          | ((k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39)
% 5.46/5.67              = (k5_relat_1 @ X36 @ X39)))),
% 5.46/5.67      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 5.46/5.67  thf('77', plain,
% 5.46/5.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.46/5.67         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 5.46/5.67            = (k5_relat_1 @ sk_C @ X0))
% 5.46/5.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 5.46/5.67          | ~ (v1_funct_1 @ X0)
% 5.46/5.67          | ~ (v1_funct_1 @ sk_C))),
% 5.46/5.67      inference('sup-', [status(thm)], ['75', '76'])).
% 5.46/5.67  thf('78', plain, ((v1_funct_1 @ sk_C)),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('79', plain,
% 5.46/5.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.46/5.67         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 5.46/5.67            = (k5_relat_1 @ sk_C @ X0))
% 5.46/5.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 5.46/5.67          | ~ (v1_funct_1 @ X0))),
% 5.46/5.67      inference('demod', [status(thm)], ['77', '78'])).
% 5.46/5.67  thf('80', plain,
% 5.46/5.67      ((~ (v1_funct_1 @ sk_D)
% 5.46/5.67        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 5.46/5.67            = (k5_relat_1 @ sk_C @ sk_D)))),
% 5.46/5.67      inference('sup-', [status(thm)], ['74', '79'])).
% 5.46/5.67  thf('81', plain, ((v1_funct_1 @ sk_D)),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('82', plain,
% 5.46/5.67      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 5.46/5.67         = (k6_relat_1 @ sk_A))),
% 5.46/5.67      inference('demod', [status(thm)], ['27', '30'])).
% 5.46/5.67  thf('83', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 5.46/5.67      inference('demod', [status(thm)], ['80', '81', '82'])).
% 5.46/5.67  thf(t64_funct_1, axiom,
% 5.46/5.67    (![A:$i]:
% 5.46/5.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.46/5.67       ( ![B:$i]:
% 5.46/5.67         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 5.46/5.67           ( ( ( v2_funct_1 @ A ) & 
% 5.46/5.67               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 5.46/5.67               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 5.46/5.67             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 5.46/5.67  thf('84', plain,
% 5.46/5.67      (![X13 : $i, X14 : $i]:
% 5.46/5.67         (~ (v1_relat_1 @ X13)
% 5.46/5.67          | ~ (v1_funct_1 @ X13)
% 5.46/5.67          | ((X13) = (k2_funct_1 @ X14))
% 5.46/5.67          | ((k5_relat_1 @ X13 @ X14) != (k6_relat_1 @ (k2_relat_1 @ X14)))
% 5.46/5.67          | ((k2_relat_1 @ X13) != (k1_relat_1 @ X14))
% 5.46/5.67          | ~ (v2_funct_1 @ X14)
% 5.46/5.67          | ~ (v1_funct_1 @ X14)
% 5.46/5.67          | ~ (v1_relat_1 @ X14))),
% 5.46/5.67      inference('cnf', [status(esa)], [t64_funct_1])).
% 5.46/5.67  thf('85', plain,
% 5.46/5.67      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ (k2_relat_1 @ sk_D)))
% 5.46/5.67        | ~ (v1_relat_1 @ sk_D)
% 5.46/5.67        | ~ (v1_funct_1 @ sk_D)
% 5.46/5.67        | ~ (v2_funct_1 @ sk_D)
% 5.46/5.67        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 5.46/5.67        | ((sk_C) = (k2_funct_1 @ sk_D))
% 5.46/5.67        | ~ (v1_funct_1 @ sk_C)
% 5.46/5.67        | ~ (v1_relat_1 @ sk_C))),
% 5.46/5.67      inference('sup-', [status(thm)], ['83', '84'])).
% 5.46/5.67  thf('86', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 5.46/5.67      inference('demod', [status(thm)], ['40', '44', '45', '46', '47', '48'])).
% 5.46/5.67  thf('87', plain,
% 5.46/5.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf(cc2_relat_1, axiom,
% 5.46/5.67    (![A:$i]:
% 5.46/5.67     ( ( v1_relat_1 @ A ) =>
% 5.46/5.67       ( ![B:$i]:
% 5.46/5.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 5.46/5.67  thf('88', plain,
% 5.46/5.67      (![X0 : $i, X1 : $i]:
% 5.46/5.67         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 5.46/5.67          | (v1_relat_1 @ X0)
% 5.46/5.67          | ~ (v1_relat_1 @ X1))),
% 5.46/5.67      inference('cnf', [status(esa)], [cc2_relat_1])).
% 5.46/5.67  thf('89', plain,
% 5.46/5.67      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 5.46/5.67      inference('sup-', [status(thm)], ['87', '88'])).
% 5.46/5.67  thf(fc6_relat_1, axiom,
% 5.46/5.67    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 5.46/5.67  thf('90', plain,
% 5.46/5.67      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 5.46/5.67      inference('cnf', [status(esa)], [fc6_relat_1])).
% 5.46/5.67  thf('91', plain, ((v1_relat_1 @ sk_D)),
% 5.46/5.67      inference('demod', [status(thm)], ['89', '90'])).
% 5.46/5.67  thf('92', plain, ((v1_funct_1 @ sk_D)),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('93', plain,
% 5.46/5.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('94', plain,
% 5.46/5.67      (![X21 : $i, X22 : $i, X23 : $i]:
% 5.46/5.67         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 5.46/5.67          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 5.46/5.67      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 5.46/5.67  thf('95', plain,
% 5.46/5.67      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 5.46/5.67      inference('sup-', [status(thm)], ['93', '94'])).
% 5.46/5.67  thf('96', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('97', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 5.46/5.67      inference('sup+', [status(thm)], ['95', '96'])).
% 5.46/5.67  thf('98', plain, ((v1_funct_1 @ sk_C)),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('99', plain,
% 5.46/5.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('100', plain,
% 5.46/5.67      (![X0 : $i, X1 : $i]:
% 5.46/5.67         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 5.46/5.67          | (v1_relat_1 @ X0)
% 5.46/5.67          | ~ (v1_relat_1 @ X1))),
% 5.46/5.67      inference('cnf', [status(esa)], [cc2_relat_1])).
% 5.46/5.67  thf('101', plain,
% 5.46/5.67      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 5.46/5.67      inference('sup-', [status(thm)], ['99', '100'])).
% 5.46/5.67  thf('102', plain,
% 5.46/5.67      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 5.46/5.67      inference('cnf', [status(esa)], [fc6_relat_1])).
% 5.46/5.67  thf('103', plain, ((v1_relat_1 @ sk_C)),
% 5.46/5.67      inference('demod', [status(thm)], ['101', '102'])).
% 5.46/5.67  thf('104', plain,
% 5.46/5.67      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ sk_A))
% 5.46/5.67        | ~ (v2_funct_1 @ sk_D)
% 5.46/5.67        | ((sk_B) != (k1_relat_1 @ sk_D))
% 5.46/5.67        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 5.46/5.67      inference('demod', [status(thm)],
% 5.46/5.67                ['85', '86', '91', '92', '97', '98', '103'])).
% 5.46/5.67  thf('105', plain,
% 5.46/5.67      ((((sk_C) = (k2_funct_1 @ sk_D))
% 5.46/5.67        | ((sk_B) != (k1_relat_1 @ sk_D))
% 5.46/5.67        | ~ (v2_funct_1 @ sk_D))),
% 5.46/5.67      inference('simplify', [status(thm)], ['104'])).
% 5.46/5.67  thf('106', plain, ((v2_funct_1 @ sk_D)),
% 5.46/5.67      inference('sup-', [status(thm)], ['70', '71'])).
% 5.46/5.67  thf('107', plain,
% 5.46/5.67      ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (k1_relat_1 @ sk_D)))),
% 5.46/5.67      inference('demod', [status(thm)], ['105', '106'])).
% 5.46/5.67  thf(t55_funct_1, axiom,
% 5.46/5.67    (![A:$i]:
% 5.46/5.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.46/5.67       ( ( v2_funct_1 @ A ) =>
% 5.46/5.67         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 5.46/5.67           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 5.46/5.67  thf('108', plain,
% 5.46/5.67      (![X12 : $i]:
% 5.46/5.67         (~ (v2_funct_1 @ X12)
% 5.46/5.67          | ((k1_relat_1 @ X12) = (k2_relat_1 @ (k2_funct_1 @ X12)))
% 5.46/5.67          | ~ (v1_funct_1 @ X12)
% 5.46/5.67          | ~ (v1_relat_1 @ X12))),
% 5.46/5.67      inference('cnf', [status(esa)], [t55_funct_1])).
% 5.46/5.67  thf('109', plain,
% 5.46/5.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf(t31_funct_2, axiom,
% 5.46/5.67    (![A:$i,B:$i,C:$i]:
% 5.46/5.67     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.46/5.67         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.46/5.67       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 5.46/5.67         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 5.46/5.67           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 5.46/5.67           ( m1_subset_1 @
% 5.46/5.67             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 5.46/5.67  thf('110', plain,
% 5.46/5.67      (![X56 : $i, X57 : $i, X58 : $i]:
% 5.46/5.67         (~ (v2_funct_1 @ X56)
% 5.46/5.67          | ((k2_relset_1 @ X58 @ X57 @ X56) != (X57))
% 5.46/5.67          | (m1_subset_1 @ (k2_funct_1 @ X56) @ 
% 5.46/5.67             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X58)))
% 5.46/5.67          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X57)))
% 5.46/5.67          | ~ (v1_funct_2 @ X56 @ X58 @ X57)
% 5.46/5.67          | ~ (v1_funct_1 @ X56))),
% 5.46/5.67      inference('cnf', [status(esa)], [t31_funct_2])).
% 5.46/5.67  thf('111', plain,
% 5.46/5.67      ((~ (v1_funct_1 @ sk_D)
% 5.46/5.67        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 5.46/5.67        | (m1_subset_1 @ (k2_funct_1 @ sk_D) @ 
% 5.46/5.67           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 5.46/5.67        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 5.46/5.67        | ~ (v2_funct_1 @ sk_D))),
% 5.46/5.67      inference('sup-', [status(thm)], ['109', '110'])).
% 5.46/5.67  thf('112', plain, ((v1_funct_1 @ sk_D)),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('113', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('114', plain,
% 5.46/5.67      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 5.46/5.67      inference('sup-', [status(thm)], ['5', '6'])).
% 5.46/5.67  thf('115', plain,
% 5.46/5.67      (((m1_subset_1 @ (k2_funct_1 @ sk_D) @ 
% 5.46/5.67         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 5.46/5.67        | ((k2_relat_1 @ sk_D) != (sk_A))
% 5.46/5.67        | ~ (v2_funct_1 @ sk_D))),
% 5.46/5.67      inference('demod', [status(thm)], ['111', '112', '113', '114'])).
% 5.46/5.67  thf('116', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 5.46/5.67      inference('demod', [status(thm)], ['40', '44', '45', '46', '47', '48'])).
% 5.46/5.67  thf('117', plain,
% 5.46/5.67      (((m1_subset_1 @ (k2_funct_1 @ sk_D) @ 
% 5.46/5.67         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 5.46/5.67        | ((sk_A) != (sk_A))
% 5.46/5.67        | ~ (v2_funct_1 @ sk_D))),
% 5.46/5.67      inference('demod', [status(thm)], ['115', '116'])).
% 5.46/5.67  thf('118', plain,
% 5.46/5.67      ((~ (v2_funct_1 @ sk_D)
% 5.46/5.67        | (m1_subset_1 @ (k2_funct_1 @ sk_D) @ 
% 5.46/5.67           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 5.46/5.67      inference('simplify', [status(thm)], ['117'])).
% 5.46/5.67  thf('119', plain, ((v2_funct_1 @ sk_D)),
% 5.46/5.67      inference('sup-', [status(thm)], ['70', '71'])).
% 5.46/5.67  thf('120', plain,
% 5.46/5.67      ((m1_subset_1 @ (k2_funct_1 @ sk_D) @ 
% 5.46/5.67        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.46/5.67      inference('demod', [status(thm)], ['118', '119'])).
% 5.46/5.67  thf(cc2_relset_1, axiom,
% 5.46/5.67    (![A:$i,B:$i,C:$i]:
% 5.46/5.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.46/5.67       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 5.46/5.67  thf('121', plain,
% 5.46/5.67      (![X18 : $i, X19 : $i, X20 : $i]:
% 5.46/5.67         ((v4_relat_1 @ X18 @ X19)
% 5.46/5.67          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 5.46/5.67      inference('cnf', [status(esa)], [cc2_relset_1])).
% 5.46/5.67  thf('122', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_D) @ sk_A)),
% 5.46/5.67      inference('sup-', [status(thm)], ['120', '121'])).
% 5.46/5.67  thf(d18_relat_1, axiom,
% 5.46/5.67    (![A:$i,B:$i]:
% 5.46/5.67     ( ( v1_relat_1 @ B ) =>
% 5.46/5.67       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 5.46/5.67  thf('123', plain,
% 5.46/5.67      (![X2 : $i, X3 : $i]:
% 5.46/5.67         (~ (v4_relat_1 @ X2 @ X3)
% 5.46/5.67          | (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 5.46/5.67          | ~ (v1_relat_1 @ X2))),
% 5.46/5.67      inference('cnf', [status(esa)], [d18_relat_1])).
% 5.46/5.67  thf('124', plain,
% 5.46/5.67      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_D))
% 5.46/5.67        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_D)) @ sk_A))),
% 5.46/5.67      inference('sup-', [status(thm)], ['122', '123'])).
% 5.46/5.67  thf('125', plain,
% 5.46/5.67      ((m1_subset_1 @ (k2_funct_1 @ sk_D) @ 
% 5.46/5.67        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.46/5.67      inference('demod', [status(thm)], ['118', '119'])).
% 5.46/5.67  thf(cc1_relset_1, axiom,
% 5.46/5.67    (![A:$i,B:$i,C:$i]:
% 5.46/5.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.46/5.67       ( v1_relat_1 @ C ) ))).
% 5.46/5.67  thf('126', plain,
% 5.46/5.67      (![X15 : $i, X16 : $i, X17 : $i]:
% 5.46/5.67         ((v1_relat_1 @ X15)
% 5.46/5.67          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 5.46/5.67      inference('cnf', [status(esa)], [cc1_relset_1])).
% 5.46/5.67  thf('127', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_D))),
% 5.46/5.67      inference('sup-', [status(thm)], ['125', '126'])).
% 5.46/5.67  thf('128', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_D)) @ sk_A)),
% 5.46/5.67      inference('demod', [status(thm)], ['124', '127'])).
% 5.46/5.67  thf('129', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 5.46/5.67      inference('demod', [status(thm)], ['40', '44', '45', '46', '47', '48'])).
% 5.46/5.67  thf(t47_relat_1, axiom,
% 5.46/5.67    (![A:$i]:
% 5.46/5.67     ( ( v1_relat_1 @ A ) =>
% 5.46/5.67       ( ![B:$i]:
% 5.46/5.67         ( ( v1_relat_1 @ B ) =>
% 5.46/5.67           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 5.46/5.67             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 5.46/5.67  thf('130', plain,
% 5.46/5.67      (![X6 : $i, X7 : $i]:
% 5.46/5.67         (~ (v1_relat_1 @ X6)
% 5.46/5.67          | ((k2_relat_1 @ (k5_relat_1 @ X6 @ X7)) = (k2_relat_1 @ X7))
% 5.46/5.67          | ~ (r1_tarski @ (k1_relat_1 @ X7) @ (k2_relat_1 @ X6))
% 5.46/5.67          | ~ (v1_relat_1 @ X7))),
% 5.46/5.67      inference('cnf', [status(esa)], [t47_relat_1])).
% 5.46/5.67  thf('131', plain,
% 5.46/5.67      (![X0 : $i]:
% 5.46/5.67         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 5.46/5.67          | ~ (v1_relat_1 @ X0)
% 5.46/5.67          | ((k2_relat_1 @ (k5_relat_1 @ sk_D @ X0)) = (k2_relat_1 @ X0))
% 5.46/5.67          | ~ (v1_relat_1 @ sk_D))),
% 5.46/5.67      inference('sup-', [status(thm)], ['129', '130'])).
% 5.46/5.67  thf('132', plain, ((v1_relat_1 @ sk_D)),
% 5.46/5.67      inference('demod', [status(thm)], ['89', '90'])).
% 5.46/5.67  thf('133', plain,
% 5.46/5.67      (![X0 : $i]:
% 5.46/5.67         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 5.46/5.67          | ~ (v1_relat_1 @ X0)
% 5.46/5.67          | ((k2_relat_1 @ (k5_relat_1 @ sk_D @ X0)) = (k2_relat_1 @ X0)))),
% 5.46/5.67      inference('demod', [status(thm)], ['131', '132'])).
% 5.46/5.67  thf('134', plain,
% 5.46/5.67      ((((k2_relat_1 @ (k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)))
% 5.46/5.67          = (k2_relat_1 @ (k2_funct_1 @ sk_D)))
% 5.46/5.67        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D)))),
% 5.46/5.67      inference('sup-', [status(thm)], ['128', '133'])).
% 5.46/5.67  thf('135', plain,
% 5.46/5.67      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 5.46/5.67      inference('demod', [status(thm)], ['51', '72'])).
% 5.46/5.67  thf(t71_relat_1, axiom,
% 5.46/5.67    (![A:$i]:
% 5.46/5.67     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 5.46/5.67       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 5.46/5.67  thf('136', plain, (![X9 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 5.46/5.67      inference('cnf', [status(esa)], [t71_relat_1])).
% 5.46/5.67  thf('137', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_D))),
% 5.46/5.67      inference('sup-', [status(thm)], ['125', '126'])).
% 5.46/5.67  thf('138', plain, (((sk_B) = (k2_relat_1 @ (k2_funct_1 @ sk_D)))),
% 5.46/5.67      inference('demod', [status(thm)], ['134', '135', '136', '137'])).
% 5.46/5.67  thf('139', plain,
% 5.46/5.67      ((((sk_B) = (k1_relat_1 @ sk_D))
% 5.46/5.67        | ~ (v1_relat_1 @ sk_D)
% 5.46/5.67        | ~ (v1_funct_1 @ sk_D)
% 5.46/5.67        | ~ (v2_funct_1 @ sk_D))),
% 5.46/5.67      inference('sup+', [status(thm)], ['108', '138'])).
% 5.46/5.67  thf('140', plain, ((v1_relat_1 @ sk_D)),
% 5.46/5.67      inference('demod', [status(thm)], ['89', '90'])).
% 5.46/5.67  thf('141', plain, ((v1_funct_1 @ sk_D)),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('142', plain, ((v2_funct_1 @ sk_D)),
% 5.46/5.67      inference('sup-', [status(thm)], ['70', '71'])).
% 5.46/5.67  thf('143', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 5.46/5.67      inference('demod', [status(thm)], ['139', '140', '141', '142'])).
% 5.46/5.67  thf('144', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (sk_B)))),
% 5.46/5.67      inference('demod', [status(thm)], ['107', '143'])).
% 5.46/5.67  thf('145', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 5.46/5.67      inference('simplify', [status(thm)], ['144'])).
% 5.46/5.67  thf('146', plain, (((k5_relat_1 @ sk_D @ sk_C) = (k6_relat_1 @ sk_B))),
% 5.46/5.67      inference('demod', [status(thm)], ['73', '145'])).
% 5.46/5.67  thf('147', plain,
% 5.46/5.67      (![X13 : $i, X14 : $i]:
% 5.46/5.67         (~ (v1_relat_1 @ X13)
% 5.46/5.67          | ~ (v1_funct_1 @ X13)
% 5.46/5.67          | ((X13) = (k2_funct_1 @ X14))
% 5.46/5.67          | ((k5_relat_1 @ X13 @ X14) != (k6_relat_1 @ (k2_relat_1 @ X14)))
% 5.46/5.67          | ((k2_relat_1 @ X13) != (k1_relat_1 @ X14))
% 5.46/5.67          | ~ (v2_funct_1 @ X14)
% 5.46/5.67          | ~ (v1_funct_1 @ X14)
% 5.46/5.67          | ~ (v1_relat_1 @ X14))),
% 5.46/5.67      inference('cnf', [status(esa)], [t64_funct_1])).
% 5.46/5.67  thf('148', plain,
% 5.46/5.67      ((((k6_relat_1 @ sk_B) != (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 5.46/5.67        | ~ (v1_relat_1 @ sk_C)
% 5.46/5.67        | ~ (v1_funct_1 @ sk_C)
% 5.46/5.67        | ~ (v2_funct_1 @ sk_C)
% 5.46/5.67        | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ sk_C))
% 5.46/5.67        | ((sk_D) = (k2_funct_1 @ sk_C))
% 5.46/5.67        | ~ (v1_funct_1 @ sk_D)
% 5.46/5.67        | ~ (v1_relat_1 @ sk_D))),
% 5.46/5.67      inference('sup-', [status(thm)], ['146', '147'])).
% 5.46/5.67  thf('149', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 5.46/5.67      inference('sup+', [status(thm)], ['95', '96'])).
% 5.46/5.67  thf('150', plain, ((v1_relat_1 @ sk_C)),
% 5.46/5.67      inference('demod', [status(thm)], ['101', '102'])).
% 5.46/5.67  thf('151', plain, ((v1_funct_1 @ sk_C)),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('152', plain, ((v2_funct_1 @ sk_C)),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('153', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 5.46/5.67      inference('demod', [status(thm)], ['40', '44', '45', '46', '47', '48'])).
% 5.46/5.67  thf('154', plain,
% 5.46/5.67      (![X12 : $i]:
% 5.46/5.67         (~ (v2_funct_1 @ X12)
% 5.46/5.67          | ((k1_relat_1 @ X12) = (k2_relat_1 @ (k2_funct_1 @ X12)))
% 5.46/5.67          | ~ (v1_funct_1 @ X12)
% 5.46/5.67          | ~ (v1_relat_1 @ X12))),
% 5.46/5.67      inference('cnf', [status(esa)], [t55_funct_1])).
% 5.46/5.67  thf('155', plain,
% 5.46/5.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('156', plain,
% 5.46/5.67      (![X56 : $i, X57 : $i, X58 : $i]:
% 5.46/5.67         (~ (v2_funct_1 @ X56)
% 5.46/5.67          | ((k2_relset_1 @ X58 @ X57 @ X56) != (X57))
% 5.46/5.67          | (m1_subset_1 @ (k2_funct_1 @ X56) @ 
% 5.46/5.67             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X58)))
% 5.46/5.67          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X57)))
% 5.46/5.67          | ~ (v1_funct_2 @ X56 @ X58 @ X57)
% 5.46/5.67          | ~ (v1_funct_1 @ X56))),
% 5.46/5.67      inference('cnf', [status(esa)], [t31_funct_2])).
% 5.46/5.67  thf('157', plain,
% 5.46/5.67      ((~ (v1_funct_1 @ sk_C)
% 5.46/5.67        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 5.46/5.67        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.46/5.67           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 5.46/5.67        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 5.46/5.67        | ~ (v2_funct_1 @ sk_C))),
% 5.46/5.67      inference('sup-', [status(thm)], ['155', '156'])).
% 5.46/5.67  thf('158', plain, ((v1_funct_1 @ sk_C)),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('159', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('160', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('161', plain, ((v2_funct_1 @ sk_C)),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('162', plain,
% 5.46/5.67      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.46/5.67         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 5.46/5.67        | ((sk_B) != (sk_B)))),
% 5.46/5.67      inference('demod', [status(thm)], ['157', '158', '159', '160', '161'])).
% 5.46/5.67  thf('163', plain,
% 5.46/5.67      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.46/5.67        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 5.46/5.67      inference('simplify', [status(thm)], ['162'])).
% 5.46/5.67  thf('164', plain,
% 5.46/5.67      (![X15 : $i, X16 : $i, X17 : $i]:
% 5.46/5.67         ((v1_relat_1 @ X15)
% 5.46/5.67          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 5.46/5.67      inference('cnf', [status(esa)], [cc1_relset_1])).
% 5.46/5.67  thf('165', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 5.46/5.67      inference('sup-', [status(thm)], ['163', '164'])).
% 5.46/5.67  thf('166', plain,
% 5.46/5.67      (![X35 : $i]:
% 5.46/5.67         (m1_subset_1 @ (k6_relat_1 @ X35) @ 
% 5.46/5.67          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 5.46/5.67      inference('demod', [status(thm)], ['28', '29'])).
% 5.46/5.67  thf('167', plain,
% 5.46/5.67      (![X18 : $i, X19 : $i, X20 : $i]:
% 5.46/5.67         ((v4_relat_1 @ X18 @ X19)
% 5.46/5.67          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 5.46/5.67      inference('cnf', [status(esa)], [cc2_relset_1])).
% 5.46/5.67  thf('168', plain, (![X0 : $i]: (v4_relat_1 @ (k6_relat_1 @ X0) @ X0)),
% 5.46/5.67      inference('sup-', [status(thm)], ['166', '167'])).
% 5.46/5.67  thf('169', plain,
% 5.46/5.67      (![X2 : $i, X3 : $i]:
% 5.46/5.67         (~ (v4_relat_1 @ X2 @ X3)
% 5.46/5.67          | (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 5.46/5.67          | ~ (v1_relat_1 @ X2))),
% 5.46/5.67      inference('cnf', [status(esa)], [d18_relat_1])).
% 5.46/5.67  thf('170', plain,
% 5.46/5.67      (![X0 : $i]:
% 5.46/5.67         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 5.46/5.67          | (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ X0)) @ X0))),
% 5.46/5.67      inference('sup-', [status(thm)], ['168', '169'])).
% 5.46/5.67  thf('171', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 5.46/5.67      inference('cnf', [status(esa)], [fc4_funct_1])).
% 5.46/5.67  thf('172', plain, (![X8 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X8)) = (X8))),
% 5.46/5.67      inference('cnf', [status(esa)], [t71_relat_1])).
% 5.46/5.67  thf('173', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 5.46/5.67      inference('demod', [status(thm)], ['170', '171', '172'])).
% 5.46/5.67  thf('174', plain,
% 5.46/5.67      (![X12 : $i]:
% 5.46/5.67         (~ (v2_funct_1 @ X12)
% 5.46/5.67          | ((k2_relat_1 @ X12) = (k1_relat_1 @ (k2_funct_1 @ X12)))
% 5.46/5.67          | ~ (v1_funct_1 @ X12)
% 5.46/5.67          | ~ (v1_relat_1 @ X12))),
% 5.46/5.67      inference('cnf', [status(esa)], [t55_funct_1])).
% 5.46/5.67  thf('175', plain,
% 5.46/5.67      (![X6 : $i, X7 : $i]:
% 5.46/5.67         (~ (v1_relat_1 @ X6)
% 5.46/5.67          | ((k2_relat_1 @ (k5_relat_1 @ X6 @ X7)) = (k2_relat_1 @ X7))
% 5.46/5.67          | ~ (r1_tarski @ (k1_relat_1 @ X7) @ (k2_relat_1 @ X6))
% 5.46/5.67          | ~ (v1_relat_1 @ X7))),
% 5.46/5.67      inference('cnf', [status(esa)], [t47_relat_1])).
% 5.46/5.67  thf('176', plain,
% 5.46/5.67      (![X0 : $i, X1 : $i]:
% 5.46/5.67         (~ (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X1))
% 5.46/5.67          | ~ (v1_relat_1 @ X0)
% 5.46/5.67          | ~ (v1_funct_1 @ X0)
% 5.46/5.67          | ~ (v2_funct_1 @ X0)
% 5.46/5.67          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 5.46/5.67          | ((k2_relat_1 @ (k5_relat_1 @ X1 @ (k2_funct_1 @ X0)))
% 5.46/5.67              = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 5.46/5.67          | ~ (v1_relat_1 @ X1))),
% 5.46/5.67      inference('sup-', [status(thm)], ['174', '175'])).
% 5.46/5.67  thf('177', plain,
% 5.46/5.67      (![X0 : $i]:
% 5.46/5.67         (~ (v1_relat_1 @ X0)
% 5.46/5.67          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 5.46/5.67              = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 5.46/5.67          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 5.46/5.67          | ~ (v2_funct_1 @ X0)
% 5.46/5.67          | ~ (v1_funct_1 @ X0)
% 5.46/5.67          | ~ (v1_relat_1 @ X0))),
% 5.46/5.67      inference('sup-', [status(thm)], ['173', '176'])).
% 5.46/5.67  thf('178', plain,
% 5.46/5.67      (![X0 : $i]:
% 5.46/5.67         (~ (v1_funct_1 @ X0)
% 5.46/5.67          | ~ (v2_funct_1 @ X0)
% 5.46/5.67          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 5.46/5.67          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 5.46/5.67              = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 5.46/5.67          | ~ (v1_relat_1 @ X0))),
% 5.46/5.67      inference('simplify', [status(thm)], ['177'])).
% 5.46/5.67  thf('179', plain,
% 5.46/5.67      ((~ (v1_relat_1 @ sk_C)
% 5.46/5.67        | ((k2_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 5.46/5.67            = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 5.46/5.67        | ~ (v2_funct_1 @ sk_C)
% 5.46/5.67        | ~ (v1_funct_1 @ sk_C))),
% 5.46/5.67      inference('sup-', [status(thm)], ['165', '178'])).
% 5.46/5.67  thf('180', plain, ((v1_relat_1 @ sk_C)),
% 5.46/5.67      inference('demod', [status(thm)], ['101', '102'])).
% 5.46/5.67  thf('181', plain, ((v2_funct_1 @ sk_C)),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('182', plain, ((v1_funct_1 @ sk_C)),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('183', plain,
% 5.46/5.67      (((k2_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 5.46/5.67         = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 5.46/5.67      inference('demod', [status(thm)], ['179', '180', '181', '182'])).
% 5.46/5.67  thf('184', plain,
% 5.46/5.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('185', plain,
% 5.46/5.67      (![X59 : $i, X60 : $i, X61 : $i]:
% 5.46/5.67         (((X59) = (k1_xboole_0))
% 5.46/5.67          | ~ (v1_funct_1 @ X60)
% 5.46/5.67          | ~ (v1_funct_2 @ X60 @ X61 @ X59)
% 5.46/5.67          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X61 @ X59)))
% 5.46/5.67          | ((k5_relat_1 @ X60 @ (k2_funct_1 @ X60)) = (k6_relat_1 @ X61))
% 5.46/5.67          | ~ (v2_funct_1 @ X60)
% 5.46/5.67          | ((k2_relset_1 @ X61 @ X59 @ X60) != (X59)))),
% 5.46/5.67      inference('demod', [status(thm)], ['1', '2'])).
% 5.46/5.67  thf('186', plain,
% 5.46/5.67      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 5.46/5.67        | ~ (v2_funct_1 @ sk_C)
% 5.46/5.67        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 5.46/5.67        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 5.46/5.67        | ~ (v1_funct_1 @ sk_C)
% 5.46/5.67        | ((sk_B) = (k1_xboole_0)))),
% 5.46/5.67      inference('sup-', [status(thm)], ['184', '185'])).
% 5.46/5.67  thf('187', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('188', plain, ((v2_funct_1 @ sk_C)),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('189', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('190', plain, ((v1_funct_1 @ sk_C)),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('191', plain,
% 5.46/5.67      ((((sk_B) != (sk_B))
% 5.46/5.67        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 5.46/5.67        | ((sk_B) = (k1_xboole_0)))),
% 5.46/5.67      inference('demod', [status(thm)], ['186', '187', '188', '189', '190'])).
% 5.46/5.67  thf('192', plain,
% 5.46/5.67      ((((sk_B) = (k1_xboole_0))
% 5.46/5.67        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A)))),
% 5.46/5.67      inference('simplify', [status(thm)], ['191'])).
% 5.46/5.67  thf('193', plain, (((sk_B) != (k1_xboole_0))),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('194', plain,
% 5.46/5.67      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))),
% 5.46/5.67      inference('simplify_reflect-', [status(thm)], ['192', '193'])).
% 5.46/5.67  thf('195', plain, (![X9 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 5.46/5.67      inference('cnf', [status(esa)], [t71_relat_1])).
% 5.46/5.67  thf('196', plain, (((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 5.46/5.67      inference('demod', [status(thm)], ['183', '194', '195'])).
% 5.46/5.67  thf('197', plain,
% 5.46/5.67      ((((sk_A) = (k1_relat_1 @ sk_C))
% 5.46/5.67        | ~ (v1_relat_1 @ sk_C)
% 5.46/5.67        | ~ (v1_funct_1 @ sk_C)
% 5.46/5.67        | ~ (v2_funct_1 @ sk_C))),
% 5.46/5.67      inference('sup+', [status(thm)], ['154', '196'])).
% 5.46/5.67  thf('198', plain, ((v1_relat_1 @ sk_C)),
% 5.46/5.67      inference('demod', [status(thm)], ['101', '102'])).
% 5.46/5.67  thf('199', plain, ((v1_funct_1 @ sk_C)),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('200', plain, ((v2_funct_1 @ sk_C)),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('201', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 5.46/5.67      inference('demod', [status(thm)], ['197', '198', '199', '200'])).
% 5.46/5.67  thf('202', plain, ((v1_funct_1 @ sk_D)),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('203', plain, ((v1_relat_1 @ sk_D)),
% 5.46/5.67      inference('demod', [status(thm)], ['89', '90'])).
% 5.46/5.67  thf('204', plain,
% 5.46/5.67      ((((k6_relat_1 @ sk_B) != (k6_relat_1 @ sk_B))
% 5.46/5.67        | ((sk_A) != (sk_A))
% 5.46/5.67        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 5.46/5.67      inference('demod', [status(thm)],
% 5.46/5.67                ['148', '149', '150', '151', '152', '153', '201', '202', '203'])).
% 5.46/5.67  thf('205', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 5.46/5.67      inference('simplify', [status(thm)], ['204'])).
% 5.46/5.67  thf('206', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 5.46/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.46/5.67  thf('207', plain, ($false),
% 5.46/5.67      inference('simplify_reflect-', [status(thm)], ['205', '206'])).
% 5.46/5.67  
% 5.46/5.67  % SZS output end Refutation
% 5.46/5.67  
% 5.46/5.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

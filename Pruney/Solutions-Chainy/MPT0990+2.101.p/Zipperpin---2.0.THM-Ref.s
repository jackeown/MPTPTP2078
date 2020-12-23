%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LoywVgfVqG

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:11 EST 2020

% Result     : Theorem 2.17s
% Output     : Refutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :  340 (3284 expanded)
%              Number of leaves         :   56 (1009 expanded)
%              Depth                    :   28
%              Number of atoms          : 3320 (79679 expanded)
%              Number of equality atoms :  235 (5628 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X63: $i] :
      ( ( k6_partfun1 @ X63 )
      = ( k6_relat_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X57: $i,X58: $i,X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X59 ) ) )
      | ~ ( v1_funct_1 @ X57 )
      | ~ ( v1_funct_1 @ X60 )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X61 @ X62 ) ) )
      | ( ( k1_partfun1 @ X58 @ X59 @ X61 @ X62 @ X57 @ X60 )
        = ( k5_relat_1 @ X57 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
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
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( m1_subset_1 @ ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) )).

thf('15',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relset_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('20',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( ( k4_relset_1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40 )
        = ( k5_relat_1 @ X37 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','22'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('24',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ( X43 = X46 )
      | ~ ( r2_relset_1 @ X44 @ X45 @ X43 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','25'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('27',plain,(
    ! [X56: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X56 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('28',plain,(
    ! [X63: $i] :
      ( ( k6_partfun1 @ X63 )
      = ( k6_relat_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('29',plain,(
    ! [X56: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X56 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X56 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('31',plain,(
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

thf('32',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( v1_funct_2 @ X51 @ X49 @ X50 )
      | ( X49
        = ( k1_relset_1 @ X49 @ X50 @ X51 ) )
      | ~ ( zip_tseitin_1 @ X51 @ X50 @ X49 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('33',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('34',plain,(
    ! [X47: $i,X48: $i] :
      ( ( zip_tseitin_0 @ X47 @ X48 )
      | ( X47 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('35',plain,(
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

thf('36',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( zip_tseitin_0 @ X52 @ X53 )
      | ( zip_tseitin_1 @ X54 @ X52 @ X53 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X52 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('37',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('42',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X32 @ X33 @ X31 )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('43',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['33','40','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('46',plain,(
    ! [X64: $i,X65: $i,X66: $i] :
      ( ~ ( v2_funct_1 @ X64 )
      | ( ( k2_relset_1 @ X66 @ X65 @ X64 )
       != X65 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X64 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X65 @ X66 ) ) )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X66 @ X65 ) ) )
      | ~ ( v1_funct_2 @ X64 @ X66 @ X65 )
      | ~ ( v1_funct_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('47',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['47','48','49','50','51'])).

thf('53',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

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

thf('54',plain,(
    ! [X67: $i,X68: $i,X69: $i] :
      ( ( X67 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X68 )
      | ~ ( v1_funct_2 @ X68 @ X69 @ X67 )
      | ~ ( m1_subset_1 @ X68 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X69 @ X67 ) ) )
      | ( ( k5_relat_1 @ X68 @ ( k2_funct_1 @ X68 ) )
        = ( k6_partfun1 @ X69 ) )
      | ~ ( v2_funct_1 @ X68 )
      | ( ( k2_relset_1 @ X69 @ X67 @ X68 )
       != X67 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('55',plain,(
    ! [X63: $i] :
      ( ( k6_partfun1 @ X63 )
      = ( k6_relat_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('56',plain,(
    ! [X67: $i,X68: $i,X69: $i] :
      ( ( X67 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X68 )
      | ~ ( v1_funct_2 @ X68 @ X69 @ X67 )
      | ~ ( m1_subset_1 @ X68 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X69 @ X67 ) ) )
      | ( ( k5_relat_1 @ X68 @ ( k2_funct_1 @ X68 ) )
        = ( k6_relat_1 @ X69 ) )
      | ~ ( v2_funct_1 @ X68 )
      | ( ( k2_relset_1 @ X69 @ X67 @ X68 )
       != X67 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C ) )
     != sk_A )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('59',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k2_relset_1 @ X35 @ X36 @ X34 )
        = ( k2_relat_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('60',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('61',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k1_relat_1 @ X20 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('62',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( v1_funct_2 @ X51 @ X49 @ X50 )
      | ( X49
        = ( k1_relset_1 @ X49 @ X50 @ X51 ) )
      | ~ ( zip_tseitin_1 @ X51 @ X50 @ X49 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('64',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X47: $i,X48: $i] :
      ( ( zip_tseitin_0 @ X47 @ X48 )
      | ( X47 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( zip_tseitin_0 @ X52 @ X53 )
      | ( zip_tseitin_1 @ X54 @ X52 @ X53 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X52 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('68',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X32 @ X33 @ X31 )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('74',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['64','71','74'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('76',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t58_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('77',plain,(
    ! [X21: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X21 @ ( k2_funct_1 @ X21 ) ) )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('78',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) ) @ ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ( r1_tarski @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['75','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('85',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('86',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('87',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('88',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['83','88','89','90'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('92',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('93',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['61','93'])).

thf('95',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['64','71','74'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('97',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['86','87'])).

thf('99',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['94','95','97','98','99','100'])).

thf('102',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['60','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X64: $i,X65: $i,X66: $i] :
      ( ~ ( v2_funct_1 @ X64 )
      | ( ( k2_relset_1 @ X66 @ X65 @ X64 )
       != X65 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X64 ) @ X65 @ X66 )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X66 @ X65 ) ) )
      | ~ ( v1_funct_2 @ X64 @ X66 @ X65 )
      | ~ ( v1_funct_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('105',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['105','106','107','108','109'])).

thf('111',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X64: $i,X65: $i,X66: $i] :
      ( ~ ( v2_funct_1 @ X64 )
      | ( ( k2_relset_1 @ X66 @ X65 @ X64 )
       != X65 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X64 ) )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X66 @ X65 ) ) )
      | ~ ( v1_funct_2 @ X64 @ X66 @ X65 )
      | ~ ( v1_funct_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('114',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['114','115','116','117','118'])).

thf('120',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','102','111','120'])).

thf('122',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['122','123'])).

thf('125',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X67: $i,X68: $i,X69: $i] :
      ( ( X67 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X68 )
      | ~ ( v1_funct_2 @ X68 @ X69 @ X67 )
      | ~ ( m1_subset_1 @ X68 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X69 @ X67 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X68 ) @ X68 )
        = ( k6_partfun1 @ X67 ) )
      | ~ ( v2_funct_1 @ X68 )
      | ( ( k2_relset_1 @ X69 @ X67 @ X68 )
       != X67 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('127',plain,(
    ! [X63: $i] :
      ( ( k6_partfun1 @ X63 )
      = ( k6_relat_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('128',plain,(
    ! [X67: $i,X68: $i,X69: $i] :
      ( ( X67 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X68 )
      | ~ ( v1_funct_2 @ X68 @ X69 @ X67 )
      | ~ ( m1_subset_1 @ X68 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X69 @ X67 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X68 ) @ X68 )
        = ( k6_relat_1 @ X67 ) )
      | ~ ( v2_funct_1 @ X68 )
      | ( ( k2_relset_1 @ X69 @ X67 @ X68 )
       != X67 ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['125','128'])).

thf('130',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['129','130','131','132','133'])).

thf('135',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['135','136'])).

thf(t53_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ? [B: $i] :
            ( ( ( k5_relat_1 @ A @ B )
              = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
            & ( v1_funct_1 @ B )
            & ( v1_relat_1 @ B ) )
       => ( v2_funct_1 @ A ) ) ) )).

thf('138',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( ( k5_relat_1 @ X19 @ X18 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X19 ) ) )
      | ( v2_funct_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t53_funct_1])).

thf('139',plain,
    ( ( ( k6_relat_1 @ sk_B )
     != ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relat_1 @ X20 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('141',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('142',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k2_relset_1 @ X35 @ X36 @ X34 )
        = ( k2_relat_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('144',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('148',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relat_1 @ X20 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('149',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['96'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('150',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ( v4_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['148','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['147','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['146','154'])).

thf('156',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['86','87'])).

thf('157',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['155','156','157','158'])).

thf('160',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('161',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['141','161'])).

thf('163',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['86','87'])).

thf('164',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['162','163','164'])).

thf('166',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('167',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['140','167'])).

thf('169',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['144','145'])).

thf('170',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['96'])).

thf('171',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['86','87'])).

thf('172',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['168','169','170','171','172','173'])).

thf('175',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('176',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('177',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('179',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('180',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['119'])).

thf('181',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['86','87'])).

thf('183',plain,
    ( ( ( k6_relat_1 @ sk_B )
     != ( k6_relat_1 @ sk_B ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['139','174','179','180','181','182'])).

thf('184',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['124','184'])).

thf('186',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k1_relat_1 @ X20 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(l72_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ! [D: $i] :
              ( ( ( v1_relat_1 @ D )
                & ( v1_funct_1 @ D ) )
             => ( ( ( ( k2_relat_1 @ B )
                    = A )
                  & ( ( k5_relat_1 @ B @ C )
                    = ( k6_relat_1 @ ( k1_relat_1 @ D ) ) )
                  & ( ( k5_relat_1 @ C @ D )
                    = ( k6_relat_1 @ A ) ) )
               => ( D = B ) ) ) ) ) )).

thf('187',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( ( k2_relat_1 @ X16 )
       != X15 )
      | ( ( k5_relat_1 @ X16 @ X14 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X17 ) ) )
      | ( ( k5_relat_1 @ X14 @ X17 )
       != ( k6_relat_1 @ X15 ) )
      | ( X17 = X16 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l72_funct_1])).

thf('188',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ( X17 = X16 )
      | ( ( k5_relat_1 @ X14 @ X17 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X16 ) ) )
      | ( ( k5_relat_1 @ X16 @ X14 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(simplify,[status(thm)],['187'])).

thf('189',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ X2 @ X1 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X2 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) )
      | ( X1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['186','188'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ sk_B )
       != ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
       != ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['185','189'])).

thf('191',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('192',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['119'])).

thf('193',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('194',plain,(
    ! [X64: $i,X65: $i,X66: $i] :
      ( ~ ( v2_funct_1 @ X64 )
      | ( ( k2_relset_1 @ X66 @ X65 @ X64 )
       != X65 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X64 ) )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X66 @ X65 ) ) )
      | ~ ( v1_funct_2 @ X64 @ X66 @ X65 )
      | ~ ( v1_funct_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('195',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C ) )
     != sk_A )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['119'])).

thf('197',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['110'])).

thf('198',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C ) )
     != sk_A )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['195','196','197'])).

thf('199',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['60','101'])).

thf('200',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['198','199'])).

thf('201',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['200'])).

thf('202',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['183'])).

thf('203',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('204',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('205',plain,(
    ! [X64: $i,X65: $i,X66: $i] :
      ( ~ ( v2_funct_1 @ X64 )
      | ( ( k2_relset_1 @ X66 @ X65 @ X64 )
       != X65 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X64 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X65 @ X66 ) ) )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X66 @ X65 ) ) )
      | ~ ( v1_funct_2 @ X64 @ X66 @ X65 )
      | ~ ( v1_funct_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('206',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C ) )
     != sk_A )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['119'])).

thf('208',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['110'])).

thf('209',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C ) )
     != sk_A )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['206','207','208'])).

thf('210',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['60','101'])).

thf('211',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['183'])).

thf('212',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ( sk_A != sk_A ) ),
    inference(demod,[status(thm)],['209','210','211'])).

thf('213',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['212'])).

thf('214',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('215',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('217',plain,(
    v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['215','216'])).

thf('218',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['86','87'])).

thf('221',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['64','71','74'])).

thf('222',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ sk_B )
       != ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k2_funct_1 @ sk_C ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
       != ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['190','191','192','203','217','218','219','220','221'])).

thf('223',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['124','184'])).

thf('224',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('225',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k1_relat_1 @ X20 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('226',plain,(
    ! [X21: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X21 @ ( k2_funct_1 @ X21 ) ) )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('227',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) ) @ ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('228',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('229',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['227','228'])).

thf('230',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['226','229'])).

thf('231',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['230'])).

thf('232',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['225','231'])).

thf('233',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['96'])).

thf('234',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['232','233'])).

thf('235',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['234'])).

thf('236',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['224','235'])).

thf('237',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['236'])).

thf('238',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_relat_1 @ ( k6_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['223','237'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('239',plain,(
    ! [X12: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('240',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('241',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['119'])).

thf('242',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['183'])).

thf('243',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    = sk_B ),
    inference(demod,[status(thm)],['238','239','240','241','242'])).

thf('244',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['135','136'])).

thf('245',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ( X17 = X16 )
      | ( ( k5_relat_1 @ X14 @ X17 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X16 ) ) )
      | ( ( k5_relat_1 @ X16 @ X14 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(simplify,[status(thm)],['187'])).

thf('246',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ sk_B )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ sk_C ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
      | ( sk_C = X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['244','245'])).

thf('247',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('248',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['119'])).

thf('249',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['64','71','74'])).

thf('250',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['86','87'])).

thf('252',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ sk_B )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ sk_C ) )
       != ( k6_relat_1 @ sk_A ) )
      | ( sk_C = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['246','247','248','249','250','251'])).

thf('253',plain,
    ( ( ( k6_relat_1 @ sk_B )
     != ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) )
     != ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['243','252'])).

thf('254',plain,(
    v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['215','216'])).

thf('255',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('256',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('257',plain,(
    ! [X67: $i,X68: $i,X69: $i] :
      ( ( X67 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X68 )
      | ~ ( v1_funct_2 @ X68 @ X69 @ X67 )
      | ~ ( m1_subset_1 @ X68 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X69 @ X67 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X68 ) @ X68 )
        = ( k6_relat_1 @ X67 ) )
      | ~ ( v2_funct_1 @ X68 )
      | ( ( k2_relset_1 @ X69 @ X67 @ X68 )
       != X67 ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('258',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C ) )
     != sk_A )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['256','257'])).

thf('259',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['60','101'])).

thf('260',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['110'])).

thf('261',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['119'])).

thf('262',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['258','259','260','261'])).

thf('263',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['262'])).

thf('264',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['263','264'])).

thf('266',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['183'])).

thf('267',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['265','266'])).

thf('268',plain,
    ( ( ( k6_relat_1 @ sk_B )
     != ( k6_relat_1 @ sk_B ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['253','254','255','267'])).

thf('269',plain,
    ( sk_C
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['268'])).

thf('270',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ sk_B )
       != ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k2_funct_1 @ sk_C ) )
      | ( ( k5_relat_1 @ sk_C @ X0 )
       != ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['222','269'])).

thf('271',plain,
    ( ( ( k6_relat_1 @ sk_B )
     != ( k6_relat_1 @ sk_B ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
     != ( k6_relat_1 @ sk_A ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['44','270'])).

thf('272',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('273',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('274',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('275',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['273','274'])).

thf('276',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('277',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['275','276'])).

thf('278',plain,
    ( ( ( k6_relat_1 @ sk_B )
     != ( k6_relat_1 @ sk_B ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
     != ( k6_relat_1 @ sk_A ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['271','272','277'])).

thf('279',plain,
    ( ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
     != ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['278'])).

thf('280',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,(
    ( k5_relat_1 @ sk_C @ sk_D )
 != ( k6_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['279','280'])).

thf('282',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['30','281'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LoywVgfVqG
% 0.16/0.38  % Computer   : n005.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 12:03:18 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 2.17/2.37  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.17/2.37  % Solved by: fo/fo7.sh
% 2.17/2.37  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.17/2.37  % done 1106 iterations in 1.886s
% 2.17/2.37  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.17/2.37  % SZS output start Refutation
% 2.17/2.37  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.17/2.37  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.17/2.37  thf(sk_A_type, type, sk_A: $i).
% 2.17/2.37  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.17/2.37  thf(sk_D_type, type, sk_D: $i).
% 2.17/2.37  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.17/2.37  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.17/2.37  thf(sk_B_type, type, sk_B: $i).
% 2.17/2.37  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.17/2.37  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.17/2.37  thf(sk_C_type, type, sk_C: $i).
% 2.17/2.37  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.17/2.37  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.17/2.37  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 2.17/2.37  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.17/2.37  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.17/2.37  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.17/2.37  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 2.17/2.37  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.17/2.37  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.17/2.37  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.17/2.37  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.17/2.37  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.17/2.37  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.17/2.37  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.17/2.37  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.17/2.37  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.17/2.37  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.17/2.37  thf(t36_funct_2, conjecture,
% 2.17/2.37    (![A:$i,B:$i,C:$i]:
% 2.17/2.37     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.17/2.37         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.17/2.37       ( ![D:$i]:
% 2.17/2.37         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.17/2.37             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.17/2.37           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.17/2.37               ( r2_relset_1 @
% 2.17/2.37                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.17/2.37                 ( k6_partfun1 @ A ) ) & 
% 2.17/2.37               ( v2_funct_1 @ C ) ) =>
% 2.17/2.37             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.17/2.37               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 2.17/2.37  thf(zf_stmt_0, negated_conjecture,
% 2.17/2.37    (~( ![A:$i,B:$i,C:$i]:
% 2.17/2.37        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.17/2.37            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.17/2.37          ( ![D:$i]:
% 2.17/2.37            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.17/2.37                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.17/2.37              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.17/2.37                  ( r2_relset_1 @
% 2.17/2.37                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.17/2.37                    ( k6_partfun1 @ A ) ) & 
% 2.17/2.37                  ( v2_funct_1 @ C ) ) =>
% 2.17/2.37                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.17/2.37                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 2.17/2.37    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 2.17/2.37  thf('0', plain,
% 2.17/2.37      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.17/2.37        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.17/2.37        (k6_partfun1 @ sk_A))),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf(redefinition_k6_partfun1, axiom,
% 2.17/2.37    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.17/2.37  thf('1', plain, (![X63 : $i]: ((k6_partfun1 @ X63) = (k6_relat_1 @ X63))),
% 2.17/2.37      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.17/2.37  thf('2', plain,
% 2.17/2.37      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.17/2.37        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.17/2.37        (k6_relat_1 @ sk_A))),
% 2.17/2.37      inference('demod', [status(thm)], ['0', '1'])).
% 2.17/2.37  thf('3', plain,
% 2.17/2.37      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf('4', plain,
% 2.17/2.37      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf(redefinition_k1_partfun1, axiom,
% 2.17/2.37    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.17/2.37     ( ( ( v1_funct_1 @ E ) & 
% 2.17/2.37         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.17/2.37         ( v1_funct_1 @ F ) & 
% 2.17/2.37         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.17/2.37       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.17/2.37  thf('5', plain,
% 2.17/2.37      (![X57 : $i, X58 : $i, X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 2.17/2.37         (~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X59)))
% 2.17/2.37          | ~ (v1_funct_1 @ X57)
% 2.17/2.37          | ~ (v1_funct_1 @ X60)
% 2.17/2.37          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X61 @ X62)))
% 2.17/2.37          | ((k1_partfun1 @ X58 @ X59 @ X61 @ X62 @ X57 @ X60)
% 2.17/2.37              = (k5_relat_1 @ X57 @ X60)))),
% 2.17/2.37      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 2.17/2.37  thf('6', plain,
% 2.17/2.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.17/2.37         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.17/2.37            = (k5_relat_1 @ sk_C @ X0))
% 2.17/2.37          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.17/2.37          | ~ (v1_funct_1 @ X0)
% 2.17/2.37          | ~ (v1_funct_1 @ sk_C))),
% 2.17/2.37      inference('sup-', [status(thm)], ['4', '5'])).
% 2.17/2.37  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf('8', plain,
% 2.17/2.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.17/2.37         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.17/2.37            = (k5_relat_1 @ sk_C @ X0))
% 2.17/2.37          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.17/2.37          | ~ (v1_funct_1 @ X0))),
% 2.17/2.37      inference('demod', [status(thm)], ['6', '7'])).
% 2.17/2.37  thf('9', plain,
% 2.17/2.37      ((~ (v1_funct_1 @ sk_D)
% 2.17/2.37        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.17/2.37            = (k5_relat_1 @ sk_C @ sk_D)))),
% 2.17/2.37      inference('sup-', [status(thm)], ['3', '8'])).
% 2.17/2.37  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf('11', plain,
% 2.17/2.37      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.17/2.37         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.17/2.37      inference('demod', [status(thm)], ['9', '10'])).
% 2.17/2.37  thf('12', plain,
% 2.17/2.37      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 2.17/2.37        (k6_relat_1 @ sk_A))),
% 2.17/2.37      inference('demod', [status(thm)], ['2', '11'])).
% 2.17/2.37  thf('13', plain,
% 2.17/2.37      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf('14', plain,
% 2.17/2.37      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf(dt_k4_relset_1, axiom,
% 2.17/2.37    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.17/2.37     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.17/2.37         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.17/2.37       ( m1_subset_1 @
% 2.17/2.37         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.17/2.37         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 2.17/2.37  thf('15', plain,
% 2.17/2.37      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 2.17/2.37         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 2.17/2.37          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 2.17/2.37          | (m1_subset_1 @ (k4_relset_1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28) @ 
% 2.17/2.37             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X30))))),
% 2.17/2.37      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 2.17/2.37  thf('16', plain,
% 2.17/2.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.17/2.37         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.17/2.37           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.17/2.37          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 2.17/2.37      inference('sup-', [status(thm)], ['14', '15'])).
% 2.17/2.37  thf('17', plain,
% 2.17/2.37      ((m1_subset_1 @ 
% 2.17/2.37        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.17/2.37        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.17/2.37      inference('sup-', [status(thm)], ['13', '16'])).
% 2.17/2.37  thf('18', plain,
% 2.17/2.37      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf('19', plain,
% 2.17/2.37      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf(redefinition_k4_relset_1, axiom,
% 2.17/2.37    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.17/2.37     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.17/2.37         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.17/2.37       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.17/2.37  thf('20', plain,
% 2.17/2.37      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 2.17/2.37         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 2.17/2.37          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 2.17/2.37          | ((k4_relset_1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40)
% 2.17/2.37              = (k5_relat_1 @ X37 @ X40)))),
% 2.17/2.37      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 2.17/2.37  thf('21', plain,
% 2.17/2.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.17/2.37         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.17/2.37            = (k5_relat_1 @ sk_C @ X0))
% 2.17/2.37          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 2.17/2.37      inference('sup-', [status(thm)], ['19', '20'])).
% 2.17/2.37  thf('22', plain,
% 2.17/2.37      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.17/2.37         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.17/2.37      inference('sup-', [status(thm)], ['18', '21'])).
% 2.17/2.37  thf('23', plain,
% 2.17/2.37      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 2.17/2.37        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.17/2.37      inference('demod', [status(thm)], ['17', '22'])).
% 2.17/2.37  thf(redefinition_r2_relset_1, axiom,
% 2.17/2.37    (![A:$i,B:$i,C:$i,D:$i]:
% 2.17/2.37     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.17/2.37         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.17/2.37       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.17/2.37  thf('24', plain,
% 2.17/2.37      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 2.17/2.37         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 2.17/2.37          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 2.17/2.37          | ((X43) = (X46))
% 2.17/2.37          | ~ (r2_relset_1 @ X44 @ X45 @ X43 @ X46))),
% 2.17/2.37      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.17/2.37  thf('25', plain,
% 2.17/2.37      (![X0 : $i]:
% 2.17/2.37         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 2.17/2.37          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 2.17/2.37          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.17/2.37      inference('sup-', [status(thm)], ['23', '24'])).
% 2.17/2.37  thf('26', plain,
% 2.17/2.37      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 2.17/2.37           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.17/2.37        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A)))),
% 2.17/2.37      inference('sup-', [status(thm)], ['12', '25'])).
% 2.17/2.37  thf(dt_k6_partfun1, axiom,
% 2.17/2.37    (![A:$i]:
% 2.17/2.37     ( ( m1_subset_1 @
% 2.17/2.37         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 2.17/2.37       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 2.17/2.37  thf('27', plain,
% 2.17/2.37      (![X56 : $i]:
% 2.17/2.37         (m1_subset_1 @ (k6_partfun1 @ X56) @ 
% 2.17/2.37          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X56)))),
% 2.17/2.37      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 2.17/2.37  thf('28', plain, (![X63 : $i]: ((k6_partfun1 @ X63) = (k6_relat_1 @ X63))),
% 2.17/2.37      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.17/2.37  thf('29', plain,
% 2.17/2.37      (![X56 : $i]:
% 2.17/2.37         (m1_subset_1 @ (k6_relat_1 @ X56) @ 
% 2.17/2.37          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X56)))),
% 2.17/2.37      inference('demod', [status(thm)], ['27', '28'])).
% 2.17/2.37  thf('30', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 2.17/2.37      inference('demod', [status(thm)], ['26', '29'])).
% 2.17/2.37  thf('31', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf(d1_funct_2, axiom,
% 2.17/2.37    (![A:$i,B:$i,C:$i]:
% 2.17/2.37     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.17/2.37       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.17/2.37           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.17/2.37             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.17/2.37         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.17/2.37           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.17/2.37             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.17/2.37  thf(zf_stmt_1, axiom,
% 2.17/2.37    (![C:$i,B:$i,A:$i]:
% 2.17/2.37     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.17/2.37       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.17/2.37  thf('32', plain,
% 2.17/2.37      (![X49 : $i, X50 : $i, X51 : $i]:
% 2.17/2.37         (~ (v1_funct_2 @ X51 @ X49 @ X50)
% 2.17/2.37          | ((X49) = (k1_relset_1 @ X49 @ X50 @ X51))
% 2.17/2.37          | ~ (zip_tseitin_1 @ X51 @ X50 @ X49))),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.17/2.37  thf('33', plain,
% 2.17/2.37      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 2.17/2.37        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 2.17/2.37      inference('sup-', [status(thm)], ['31', '32'])).
% 2.17/2.37  thf(zf_stmt_2, axiom,
% 2.17/2.37    (![B:$i,A:$i]:
% 2.17/2.37     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.17/2.37       ( zip_tseitin_0 @ B @ A ) ))).
% 2.17/2.37  thf('34', plain,
% 2.17/2.37      (![X47 : $i, X48 : $i]:
% 2.17/2.37         ((zip_tseitin_0 @ X47 @ X48) | ((X47) = (k1_xboole_0)))),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.17/2.37  thf('35', plain,
% 2.17/2.37      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.17/2.37  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.17/2.37  thf(zf_stmt_5, axiom,
% 2.17/2.37    (![A:$i,B:$i,C:$i]:
% 2.17/2.37     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.17/2.37       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.17/2.37         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.17/2.37           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.17/2.37             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.17/2.37  thf('36', plain,
% 2.17/2.37      (![X52 : $i, X53 : $i, X54 : $i]:
% 2.17/2.37         (~ (zip_tseitin_0 @ X52 @ X53)
% 2.17/2.37          | (zip_tseitin_1 @ X54 @ X52 @ X53)
% 2.17/2.37          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X52))))),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.17/2.37  thf('37', plain,
% 2.17/2.37      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 2.17/2.37      inference('sup-', [status(thm)], ['35', '36'])).
% 2.17/2.37  thf('38', plain,
% 2.17/2.37      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 2.17/2.37      inference('sup-', [status(thm)], ['34', '37'])).
% 2.17/2.37  thf('39', plain, (((sk_A) != (k1_xboole_0))),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf('40', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 2.17/2.37      inference('simplify_reflect-', [status(thm)], ['38', '39'])).
% 2.17/2.37  thf('41', plain,
% 2.17/2.37      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf(redefinition_k1_relset_1, axiom,
% 2.17/2.37    (![A:$i,B:$i,C:$i]:
% 2.17/2.37     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.17/2.37       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.17/2.37  thf('42', plain,
% 2.17/2.37      (![X31 : $i, X32 : $i, X33 : $i]:
% 2.17/2.37         (((k1_relset_1 @ X32 @ X33 @ X31) = (k1_relat_1 @ X31))
% 2.17/2.37          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 2.17/2.37      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.17/2.37  thf('43', plain,
% 2.17/2.37      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 2.17/2.37      inference('sup-', [status(thm)], ['41', '42'])).
% 2.17/2.37  thf('44', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 2.17/2.37      inference('demod', [status(thm)], ['33', '40', '43'])).
% 2.17/2.37  thf('45', plain,
% 2.17/2.37      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf(t31_funct_2, axiom,
% 2.17/2.37    (![A:$i,B:$i,C:$i]:
% 2.17/2.37     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.17/2.37         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.17/2.37       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 2.17/2.37         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 2.17/2.37           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 2.17/2.37           ( m1_subset_1 @
% 2.17/2.37             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 2.17/2.37  thf('46', plain,
% 2.17/2.37      (![X64 : $i, X65 : $i, X66 : $i]:
% 2.17/2.37         (~ (v2_funct_1 @ X64)
% 2.17/2.37          | ((k2_relset_1 @ X66 @ X65 @ X64) != (X65))
% 2.17/2.37          | (m1_subset_1 @ (k2_funct_1 @ X64) @ 
% 2.17/2.37             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X65 @ X66)))
% 2.17/2.37          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X66 @ X65)))
% 2.17/2.37          | ~ (v1_funct_2 @ X64 @ X66 @ X65)
% 2.17/2.37          | ~ (v1_funct_1 @ X64))),
% 2.17/2.37      inference('cnf', [status(esa)], [t31_funct_2])).
% 2.17/2.37  thf('47', plain,
% 2.17/2.37      ((~ (v1_funct_1 @ sk_C)
% 2.17/2.37        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.17/2.37        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.17/2.37           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.17/2.37        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 2.17/2.37        | ~ (v2_funct_1 @ sk_C))),
% 2.17/2.37      inference('sup-', [status(thm)], ['45', '46'])).
% 2.17/2.37  thf('48', plain, ((v1_funct_1 @ sk_C)),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf('49', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf('50', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf('51', plain, ((v2_funct_1 @ sk_C)),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf('52', plain,
% 2.17/2.37      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.17/2.37         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.17/2.37        | ((sk_B) != (sk_B)))),
% 2.17/2.37      inference('demod', [status(thm)], ['47', '48', '49', '50', '51'])).
% 2.17/2.37  thf('53', plain,
% 2.17/2.37      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.17/2.37        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.17/2.37      inference('simplify', [status(thm)], ['52'])).
% 2.17/2.37  thf(t35_funct_2, axiom,
% 2.17/2.37    (![A:$i,B:$i,C:$i]:
% 2.17/2.37     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.17/2.37         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.17/2.37       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 2.17/2.37         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.17/2.37           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 2.17/2.37             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 2.17/2.37  thf('54', plain,
% 2.17/2.37      (![X67 : $i, X68 : $i, X69 : $i]:
% 2.17/2.37         (((X67) = (k1_xboole_0))
% 2.17/2.37          | ~ (v1_funct_1 @ X68)
% 2.17/2.37          | ~ (v1_funct_2 @ X68 @ X69 @ X67)
% 2.17/2.37          | ~ (m1_subset_1 @ X68 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X69 @ X67)))
% 2.17/2.37          | ((k5_relat_1 @ X68 @ (k2_funct_1 @ X68)) = (k6_partfun1 @ X69))
% 2.17/2.37          | ~ (v2_funct_1 @ X68)
% 2.17/2.37          | ((k2_relset_1 @ X69 @ X67 @ X68) != (X67)))),
% 2.17/2.37      inference('cnf', [status(esa)], [t35_funct_2])).
% 2.17/2.37  thf('55', plain, (![X63 : $i]: ((k6_partfun1 @ X63) = (k6_relat_1 @ X63))),
% 2.17/2.37      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.17/2.37  thf('56', plain,
% 2.17/2.37      (![X67 : $i, X68 : $i, X69 : $i]:
% 2.17/2.37         (((X67) = (k1_xboole_0))
% 2.17/2.37          | ~ (v1_funct_1 @ X68)
% 2.17/2.37          | ~ (v1_funct_2 @ X68 @ X69 @ X67)
% 2.17/2.37          | ~ (m1_subset_1 @ X68 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X69 @ X67)))
% 2.17/2.37          | ((k5_relat_1 @ X68 @ (k2_funct_1 @ X68)) = (k6_relat_1 @ X69))
% 2.17/2.37          | ~ (v2_funct_1 @ X68)
% 2.17/2.37          | ((k2_relset_1 @ X69 @ X67 @ X68) != (X67)))),
% 2.17/2.37      inference('demod', [status(thm)], ['54', '55'])).
% 2.17/2.37  thf('57', plain,
% 2.17/2.37      ((((k2_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C)) != (sk_A))
% 2.17/2.37        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 2.17/2.37        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 2.17/2.37            (k2_funct_1 @ (k2_funct_1 @ sk_C))) = (k6_relat_1 @ sk_B))
% 2.17/2.37        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 2.17/2.37        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 2.17/2.37        | ((sk_A) = (k1_xboole_0)))),
% 2.17/2.37      inference('sup-', [status(thm)], ['53', '56'])).
% 2.17/2.37  thf('58', plain,
% 2.17/2.37      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.17/2.37        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.17/2.37      inference('simplify', [status(thm)], ['52'])).
% 2.17/2.37  thf(redefinition_k2_relset_1, axiom,
% 2.17/2.37    (![A:$i,B:$i,C:$i]:
% 2.17/2.37     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.17/2.37       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.17/2.37  thf('59', plain,
% 2.17/2.37      (![X34 : $i, X35 : $i, X36 : $i]:
% 2.17/2.37         (((k2_relset_1 @ X35 @ X36 @ X34) = (k2_relat_1 @ X34))
% 2.17/2.37          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 2.17/2.37      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.17/2.37  thf('60', plain,
% 2.17/2.37      (((k2_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C))
% 2.17/2.37         = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 2.17/2.37      inference('sup-', [status(thm)], ['58', '59'])).
% 2.17/2.37  thf(t55_funct_1, axiom,
% 2.17/2.37    (![A:$i]:
% 2.17/2.37     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.17/2.37       ( ( v2_funct_1 @ A ) =>
% 2.17/2.37         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 2.17/2.37           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.17/2.37  thf('61', plain,
% 2.17/2.37      (![X20 : $i]:
% 2.17/2.37         (~ (v2_funct_1 @ X20)
% 2.17/2.37          | ((k1_relat_1 @ X20) = (k2_relat_1 @ (k2_funct_1 @ X20)))
% 2.17/2.37          | ~ (v1_funct_1 @ X20)
% 2.17/2.37          | ~ (v1_relat_1 @ X20))),
% 2.17/2.37      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.17/2.37  thf('62', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf('63', plain,
% 2.17/2.37      (![X49 : $i, X50 : $i, X51 : $i]:
% 2.17/2.37         (~ (v1_funct_2 @ X51 @ X49 @ X50)
% 2.17/2.37          | ((X49) = (k1_relset_1 @ X49 @ X50 @ X51))
% 2.17/2.37          | ~ (zip_tseitin_1 @ X51 @ X50 @ X49))),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.17/2.37  thf('64', plain,
% 2.17/2.37      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 2.17/2.37        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 2.17/2.37      inference('sup-', [status(thm)], ['62', '63'])).
% 2.17/2.37  thf('65', plain,
% 2.17/2.37      (![X47 : $i, X48 : $i]:
% 2.17/2.37         ((zip_tseitin_0 @ X47 @ X48) | ((X47) = (k1_xboole_0)))),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.17/2.37  thf('66', plain,
% 2.17/2.37      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf('67', plain,
% 2.17/2.37      (![X52 : $i, X53 : $i, X54 : $i]:
% 2.17/2.37         (~ (zip_tseitin_0 @ X52 @ X53)
% 2.17/2.37          | (zip_tseitin_1 @ X54 @ X52 @ X53)
% 2.17/2.37          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X52))))),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.17/2.37  thf('68', plain,
% 2.17/2.37      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 2.17/2.37      inference('sup-', [status(thm)], ['66', '67'])).
% 2.17/2.37  thf('69', plain,
% 2.17/2.37      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 2.17/2.37      inference('sup-', [status(thm)], ['65', '68'])).
% 2.17/2.37  thf('70', plain, (((sk_B) != (k1_xboole_0))),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf('71', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 2.17/2.37      inference('simplify_reflect-', [status(thm)], ['69', '70'])).
% 2.17/2.37  thf('72', plain,
% 2.17/2.37      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf('73', plain,
% 2.17/2.37      (![X31 : $i, X32 : $i, X33 : $i]:
% 2.17/2.37         (((k1_relset_1 @ X32 @ X33 @ X31) = (k1_relat_1 @ X31))
% 2.17/2.37          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 2.17/2.37      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.17/2.37  thf('74', plain,
% 2.17/2.37      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 2.17/2.37      inference('sup-', [status(thm)], ['72', '73'])).
% 2.17/2.37  thf('75', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 2.17/2.37      inference('demod', [status(thm)], ['64', '71', '74'])).
% 2.17/2.37  thf(dt_k2_funct_1, axiom,
% 2.17/2.37    (![A:$i]:
% 2.17/2.37     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.17/2.37       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 2.17/2.37         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 2.17/2.37  thf('76', plain,
% 2.17/2.37      (![X13 : $i]:
% 2.17/2.37         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 2.17/2.37          | ~ (v1_funct_1 @ X13)
% 2.17/2.37          | ~ (v1_relat_1 @ X13))),
% 2.17/2.37      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.17/2.37  thf(t58_funct_1, axiom,
% 2.17/2.37    (![A:$i]:
% 2.17/2.37     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.17/2.37       ( ( v2_funct_1 @ A ) =>
% 2.17/2.37         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 2.17/2.37             ( k1_relat_1 @ A ) ) & 
% 2.17/2.37           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 2.17/2.37             ( k1_relat_1 @ A ) ) ) ) ))).
% 2.17/2.37  thf('77', plain,
% 2.17/2.37      (![X21 : $i]:
% 2.17/2.37         (~ (v2_funct_1 @ X21)
% 2.17/2.37          | ((k2_relat_1 @ (k5_relat_1 @ X21 @ (k2_funct_1 @ X21)))
% 2.17/2.37              = (k1_relat_1 @ X21))
% 2.17/2.37          | ~ (v1_funct_1 @ X21)
% 2.17/2.37          | ~ (v1_relat_1 @ X21))),
% 2.17/2.37      inference('cnf', [status(esa)], [t58_funct_1])).
% 2.17/2.37  thf(t45_relat_1, axiom,
% 2.17/2.37    (![A:$i]:
% 2.17/2.37     ( ( v1_relat_1 @ A ) =>
% 2.17/2.37       ( ![B:$i]:
% 2.17/2.37         ( ( v1_relat_1 @ B ) =>
% 2.17/2.37           ( r1_tarski @
% 2.17/2.37             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 2.17/2.37  thf('78', plain,
% 2.17/2.37      (![X9 : $i, X10 : $i]:
% 2.17/2.37         (~ (v1_relat_1 @ X9)
% 2.17/2.37          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X10 @ X9)) @ 
% 2.17/2.37             (k2_relat_1 @ X9))
% 2.17/2.37          | ~ (v1_relat_1 @ X10))),
% 2.17/2.37      inference('cnf', [status(esa)], [t45_relat_1])).
% 2.17/2.37  thf('79', plain,
% 2.17/2.37      (![X0 : $i]:
% 2.17/2.37         ((r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.17/2.37          | ~ (v1_relat_1 @ X0)
% 2.17/2.37          | ~ (v1_funct_1 @ X0)
% 2.17/2.37          | ~ (v2_funct_1 @ X0)
% 2.17/2.37          | ~ (v1_relat_1 @ X0)
% 2.17/2.37          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 2.17/2.37      inference('sup+', [status(thm)], ['77', '78'])).
% 2.17/2.37  thf('80', plain,
% 2.17/2.37      (![X0 : $i]:
% 2.17/2.37         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.17/2.37          | ~ (v2_funct_1 @ X0)
% 2.17/2.37          | ~ (v1_funct_1 @ X0)
% 2.17/2.37          | ~ (v1_relat_1 @ X0)
% 2.17/2.37          | (r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 2.17/2.37      inference('simplify', [status(thm)], ['79'])).
% 2.17/2.37  thf('81', plain,
% 2.17/2.37      (![X0 : $i]:
% 2.17/2.37         (~ (v1_relat_1 @ X0)
% 2.17/2.37          | ~ (v1_funct_1 @ X0)
% 2.17/2.37          | (r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.17/2.37          | ~ (v1_relat_1 @ X0)
% 2.17/2.37          | ~ (v1_funct_1 @ X0)
% 2.17/2.37          | ~ (v2_funct_1 @ X0))),
% 2.17/2.37      inference('sup-', [status(thm)], ['76', '80'])).
% 2.17/2.37  thf('82', plain,
% 2.17/2.37      (![X0 : $i]:
% 2.17/2.37         (~ (v2_funct_1 @ X0)
% 2.17/2.37          | (r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.17/2.37          | ~ (v1_funct_1 @ X0)
% 2.17/2.37          | ~ (v1_relat_1 @ X0))),
% 2.17/2.37      inference('simplify', [status(thm)], ['81'])).
% 2.17/2.37  thf('83', plain,
% 2.17/2.37      (((r1_tarski @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 2.17/2.37        | ~ (v1_relat_1 @ sk_C)
% 2.17/2.37        | ~ (v1_funct_1 @ sk_C)
% 2.17/2.37        | ~ (v2_funct_1 @ sk_C))),
% 2.17/2.37      inference('sup+', [status(thm)], ['75', '82'])).
% 2.17/2.37  thf('84', plain,
% 2.17/2.37      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf(cc2_relat_1, axiom,
% 2.17/2.37    (![A:$i]:
% 2.17/2.37     ( ( v1_relat_1 @ A ) =>
% 2.17/2.37       ( ![B:$i]:
% 2.17/2.37         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.17/2.37  thf('85', plain,
% 2.17/2.37      (![X3 : $i, X4 : $i]:
% 2.17/2.37         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 2.17/2.37          | (v1_relat_1 @ X3)
% 2.17/2.37          | ~ (v1_relat_1 @ X4))),
% 2.17/2.37      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.17/2.37  thf('86', plain,
% 2.17/2.37      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 2.17/2.37      inference('sup-', [status(thm)], ['84', '85'])).
% 2.17/2.37  thf(fc6_relat_1, axiom,
% 2.17/2.37    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.17/2.37  thf('87', plain,
% 2.17/2.37      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 2.17/2.37      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.17/2.37  thf('88', plain, ((v1_relat_1 @ sk_C)),
% 2.17/2.37      inference('demod', [status(thm)], ['86', '87'])).
% 2.17/2.37  thf('89', plain, ((v1_funct_1 @ sk_C)),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf('90', plain, ((v2_funct_1 @ sk_C)),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf('91', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 2.17/2.37      inference('demod', [status(thm)], ['83', '88', '89', '90'])).
% 2.17/2.37  thf(d10_xboole_0, axiom,
% 2.17/2.37    (![A:$i,B:$i]:
% 2.17/2.37     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.17/2.37  thf('92', plain,
% 2.17/2.37      (![X0 : $i, X2 : $i]:
% 2.17/2.37         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.17/2.37      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.17/2.37  thf('93', plain,
% 2.17/2.37      ((~ (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)
% 2.17/2.37        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_A)))),
% 2.17/2.37      inference('sup-', [status(thm)], ['91', '92'])).
% 2.17/2.37  thf('94', plain,
% 2.17/2.37      ((~ (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)
% 2.17/2.37        | ~ (v1_relat_1 @ sk_C)
% 2.17/2.37        | ~ (v1_funct_1 @ sk_C)
% 2.17/2.37        | ~ (v2_funct_1 @ sk_C)
% 2.17/2.37        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_A)))),
% 2.17/2.37      inference('sup-', [status(thm)], ['61', '93'])).
% 2.17/2.37  thf('95', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 2.17/2.37      inference('demod', [status(thm)], ['64', '71', '74'])).
% 2.17/2.37  thf('96', plain,
% 2.17/2.37      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 2.17/2.37      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.17/2.37  thf('97', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.17/2.37      inference('simplify', [status(thm)], ['96'])).
% 2.17/2.37  thf('98', plain, ((v1_relat_1 @ sk_C)),
% 2.17/2.37      inference('demod', [status(thm)], ['86', '87'])).
% 2.17/2.37  thf('99', plain, ((v1_funct_1 @ sk_C)),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf('100', plain, ((v2_funct_1 @ sk_C)),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf('101', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_A))),
% 2.17/2.37      inference('demod', [status(thm)], ['94', '95', '97', '98', '99', '100'])).
% 2.17/2.37  thf('102', plain,
% 2.17/2.37      (((k2_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C)) = (sk_A))),
% 2.17/2.37      inference('demod', [status(thm)], ['60', '101'])).
% 2.17/2.37  thf('103', plain,
% 2.17/2.37      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf('104', plain,
% 2.17/2.37      (![X64 : $i, X65 : $i, X66 : $i]:
% 2.17/2.37         (~ (v2_funct_1 @ X64)
% 2.17/2.37          | ((k2_relset_1 @ X66 @ X65 @ X64) != (X65))
% 2.17/2.37          | (v1_funct_2 @ (k2_funct_1 @ X64) @ X65 @ X66)
% 2.17/2.37          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X66 @ X65)))
% 2.17/2.37          | ~ (v1_funct_2 @ X64 @ X66 @ X65)
% 2.17/2.37          | ~ (v1_funct_1 @ X64))),
% 2.17/2.37      inference('cnf', [status(esa)], [t31_funct_2])).
% 2.17/2.37  thf('105', plain,
% 2.17/2.37      ((~ (v1_funct_1 @ sk_C)
% 2.17/2.37        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.17/2.37        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 2.17/2.37        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 2.17/2.37        | ~ (v2_funct_1 @ sk_C))),
% 2.17/2.37      inference('sup-', [status(thm)], ['103', '104'])).
% 2.17/2.37  thf('106', plain, ((v1_funct_1 @ sk_C)),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf('107', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf('108', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf('109', plain, ((v2_funct_1 @ sk_C)),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf('110', plain,
% 2.17/2.37      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A) | ((sk_B) != (sk_B)))),
% 2.17/2.37      inference('demod', [status(thm)], ['105', '106', '107', '108', '109'])).
% 2.17/2.37  thf('111', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 2.17/2.37      inference('simplify', [status(thm)], ['110'])).
% 2.17/2.37  thf('112', plain,
% 2.17/2.37      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf('113', plain,
% 2.17/2.37      (![X64 : $i, X65 : $i, X66 : $i]:
% 2.17/2.37         (~ (v2_funct_1 @ X64)
% 2.17/2.37          | ((k2_relset_1 @ X66 @ X65 @ X64) != (X65))
% 2.17/2.37          | (v1_funct_1 @ (k2_funct_1 @ X64))
% 2.17/2.37          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X66 @ X65)))
% 2.17/2.37          | ~ (v1_funct_2 @ X64 @ X66 @ X65)
% 2.17/2.37          | ~ (v1_funct_1 @ X64))),
% 2.17/2.37      inference('cnf', [status(esa)], [t31_funct_2])).
% 2.17/2.37  thf('114', plain,
% 2.17/2.37      ((~ (v1_funct_1 @ sk_C)
% 2.17/2.37        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.17/2.37        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 2.17/2.37        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 2.17/2.37        | ~ (v2_funct_1 @ sk_C))),
% 2.17/2.37      inference('sup-', [status(thm)], ['112', '113'])).
% 2.17/2.37  thf('115', plain, ((v1_funct_1 @ sk_C)),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf('116', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf('117', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf('118', plain, ((v2_funct_1 @ sk_C)),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf('119', plain,
% 2.17/2.37      (((v1_funct_1 @ (k2_funct_1 @ sk_C)) | ((sk_B) != (sk_B)))),
% 2.17/2.37      inference('demod', [status(thm)], ['114', '115', '116', '117', '118'])).
% 2.17/2.37  thf('120', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 2.17/2.37      inference('simplify', [status(thm)], ['119'])).
% 2.17/2.37  thf('121', plain,
% 2.17/2.37      ((((sk_A) != (sk_A))
% 2.17/2.37        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 2.17/2.37        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 2.17/2.37            (k2_funct_1 @ (k2_funct_1 @ sk_C))) = (k6_relat_1 @ sk_B))
% 2.17/2.37        | ((sk_A) = (k1_xboole_0)))),
% 2.17/2.37      inference('demod', [status(thm)], ['57', '102', '111', '120'])).
% 2.17/2.37  thf('122', plain,
% 2.17/2.37      ((((sk_A) = (k1_xboole_0))
% 2.17/2.37        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 2.17/2.37            (k2_funct_1 @ (k2_funct_1 @ sk_C))) = (k6_relat_1 @ sk_B))
% 2.17/2.37        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.17/2.37      inference('simplify', [status(thm)], ['121'])).
% 2.17/2.37  thf('123', plain, (((sk_A) != (k1_xboole_0))),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf('124', plain,
% 2.17/2.37      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 2.17/2.37          = (k6_relat_1 @ sk_B))
% 2.17/2.37        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.17/2.37      inference('simplify_reflect-', [status(thm)], ['122', '123'])).
% 2.17/2.37  thf('125', plain,
% 2.17/2.37      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf('126', plain,
% 2.17/2.37      (![X67 : $i, X68 : $i, X69 : $i]:
% 2.17/2.37         (((X67) = (k1_xboole_0))
% 2.17/2.37          | ~ (v1_funct_1 @ X68)
% 2.17/2.37          | ~ (v1_funct_2 @ X68 @ X69 @ X67)
% 2.17/2.37          | ~ (m1_subset_1 @ X68 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X69 @ X67)))
% 2.17/2.37          | ((k5_relat_1 @ (k2_funct_1 @ X68) @ X68) = (k6_partfun1 @ X67))
% 2.17/2.37          | ~ (v2_funct_1 @ X68)
% 2.17/2.37          | ((k2_relset_1 @ X69 @ X67 @ X68) != (X67)))),
% 2.17/2.37      inference('cnf', [status(esa)], [t35_funct_2])).
% 2.17/2.37  thf('127', plain, (![X63 : $i]: ((k6_partfun1 @ X63) = (k6_relat_1 @ X63))),
% 2.17/2.37      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.17/2.37  thf('128', plain,
% 2.17/2.37      (![X67 : $i, X68 : $i, X69 : $i]:
% 2.17/2.37         (((X67) = (k1_xboole_0))
% 2.17/2.37          | ~ (v1_funct_1 @ X68)
% 2.17/2.37          | ~ (v1_funct_2 @ X68 @ X69 @ X67)
% 2.17/2.37          | ~ (m1_subset_1 @ X68 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X69 @ X67)))
% 2.17/2.37          | ((k5_relat_1 @ (k2_funct_1 @ X68) @ X68) = (k6_relat_1 @ X67))
% 2.17/2.37          | ~ (v2_funct_1 @ X68)
% 2.17/2.37          | ((k2_relset_1 @ X69 @ X67 @ X68) != (X67)))),
% 2.17/2.37      inference('demod', [status(thm)], ['126', '127'])).
% 2.17/2.37  thf('129', plain,
% 2.17/2.37      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 2.17/2.37        | ~ (v2_funct_1 @ sk_C)
% 2.17/2.37        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 2.17/2.37        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.17/2.37        | ~ (v1_funct_1 @ sk_C)
% 2.17/2.37        | ((sk_B) = (k1_xboole_0)))),
% 2.17/2.37      inference('sup-', [status(thm)], ['125', '128'])).
% 2.17/2.37  thf('130', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf('131', plain, ((v2_funct_1 @ sk_C)),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf('132', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf('133', plain, ((v1_funct_1 @ sk_C)),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf('134', plain,
% 2.17/2.37      ((((sk_B) != (sk_B))
% 2.17/2.37        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 2.17/2.37        | ((sk_B) = (k1_xboole_0)))),
% 2.17/2.37      inference('demod', [status(thm)], ['129', '130', '131', '132', '133'])).
% 2.17/2.37  thf('135', plain,
% 2.17/2.37      ((((sk_B) = (k1_xboole_0))
% 2.17/2.37        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B)))),
% 2.17/2.37      inference('simplify', [status(thm)], ['134'])).
% 2.17/2.37  thf('136', plain, (((sk_B) != (k1_xboole_0))),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.37  thf('137', plain,
% 2.17/2.37      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))),
% 2.17/2.37      inference('simplify_reflect-', [status(thm)], ['135', '136'])).
% 2.17/2.37  thf(t53_funct_1, axiom,
% 2.17/2.37    (![A:$i]:
% 2.17/2.37     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.17/2.37       ( ( ?[B:$i]:
% 2.17/2.37           ( ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 2.17/2.37             ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) ) =>
% 2.17/2.37         ( v2_funct_1 @ A ) ) ))).
% 2.17/2.37  thf('138', plain,
% 2.17/2.37      (![X18 : $i, X19 : $i]:
% 2.17/2.37         (~ (v1_relat_1 @ X18)
% 2.17/2.37          | ~ (v1_funct_1 @ X18)
% 2.17/2.37          | ((k5_relat_1 @ X19 @ X18) != (k6_relat_1 @ (k1_relat_1 @ X19)))
% 2.17/2.37          | (v2_funct_1 @ X19)
% 2.17/2.37          | ~ (v1_funct_1 @ X19)
% 2.17/2.37          | ~ (v1_relat_1 @ X19))),
% 2.17/2.37      inference('cnf', [status(esa)], [t53_funct_1])).
% 2.17/2.37  thf('139', plain,
% 2.17/2.37      ((((k6_relat_1 @ sk_B)
% 2.17/2.37          != (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 2.17/2.37        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.17/2.37        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 2.17/2.37        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 2.17/2.37        | ~ (v1_funct_1 @ sk_C)
% 2.17/2.37        | ~ (v1_relat_1 @ sk_C))),
% 2.17/2.37      inference('sup-', [status(thm)], ['137', '138'])).
% 2.17/2.37  thf('140', plain,
% 2.17/2.37      (![X20 : $i]:
% 2.17/2.37         (~ (v2_funct_1 @ X20)
% 2.17/2.37          | ((k2_relat_1 @ X20) = (k1_relat_1 @ (k2_funct_1 @ X20)))
% 2.17/2.37          | ~ (v1_funct_1 @ X20)
% 2.17/2.37          | ~ (v1_relat_1 @ X20))),
% 2.17/2.37      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.17/2.37  thf('141', plain,
% 2.17/2.37      (![X13 : $i]:
% 2.17/2.37         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 2.17/2.37          | ~ (v1_funct_1 @ X13)
% 2.17/2.37          | ~ (v1_relat_1 @ X13))),
% 2.17/2.37      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.17/2.37  thf('142', plain,
% 2.17/2.37      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.17/2.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.38  thf('143', plain,
% 2.17/2.38      (![X34 : $i, X35 : $i, X36 : $i]:
% 2.17/2.38         (((k2_relset_1 @ X35 @ X36 @ X34) = (k2_relat_1 @ X34))
% 2.17/2.38          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 2.17/2.38      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.17/2.38  thf('144', plain,
% 2.17/2.38      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 2.17/2.38      inference('sup-', [status(thm)], ['142', '143'])).
% 2.17/2.38  thf('145', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.17/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.38  thf('146', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.17/2.38      inference('sup+', [status(thm)], ['144', '145'])).
% 2.17/2.38  thf('147', plain,
% 2.17/2.38      (![X13 : $i]:
% 2.17/2.38         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 2.17/2.38          | ~ (v1_funct_1 @ X13)
% 2.17/2.38          | ~ (v1_relat_1 @ X13))),
% 2.17/2.38      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.17/2.38  thf('148', plain,
% 2.17/2.38      (![X20 : $i]:
% 2.17/2.38         (~ (v2_funct_1 @ X20)
% 2.17/2.38          | ((k2_relat_1 @ X20) = (k1_relat_1 @ (k2_funct_1 @ X20)))
% 2.17/2.38          | ~ (v1_funct_1 @ X20)
% 2.17/2.38          | ~ (v1_relat_1 @ X20))),
% 2.17/2.38      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.17/2.38  thf('149', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.17/2.38      inference('simplify', [status(thm)], ['96'])).
% 2.17/2.38  thf(d18_relat_1, axiom,
% 2.17/2.38    (![A:$i,B:$i]:
% 2.17/2.38     ( ( v1_relat_1 @ B ) =>
% 2.17/2.38       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 2.17/2.38  thf('150', plain,
% 2.17/2.38      (![X5 : $i, X6 : $i]:
% 2.17/2.38         (~ (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 2.17/2.38          | (v4_relat_1 @ X5 @ X6)
% 2.17/2.38          | ~ (v1_relat_1 @ X5))),
% 2.17/2.38      inference('cnf', [status(esa)], [d18_relat_1])).
% 2.17/2.38  thf('151', plain,
% 2.17/2.38      (![X0 : $i]:
% 2.17/2.38         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 2.17/2.38      inference('sup-', [status(thm)], ['149', '150'])).
% 2.17/2.38  thf('152', plain,
% 2.17/2.38      (![X0 : $i]:
% 2.17/2.38         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 2.17/2.38          | ~ (v1_relat_1 @ X0)
% 2.17/2.38          | ~ (v1_funct_1 @ X0)
% 2.17/2.38          | ~ (v2_funct_1 @ X0)
% 2.17/2.38          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 2.17/2.38      inference('sup+', [status(thm)], ['148', '151'])).
% 2.17/2.38  thf('153', plain,
% 2.17/2.38      (![X0 : $i]:
% 2.17/2.38         (~ (v1_relat_1 @ X0)
% 2.17/2.38          | ~ (v1_funct_1 @ X0)
% 2.17/2.38          | ~ (v2_funct_1 @ X0)
% 2.17/2.38          | ~ (v1_funct_1 @ X0)
% 2.17/2.38          | ~ (v1_relat_1 @ X0)
% 2.17/2.38          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 2.17/2.38      inference('sup-', [status(thm)], ['147', '152'])).
% 2.17/2.38  thf('154', plain,
% 2.17/2.38      (![X0 : $i]:
% 2.17/2.38         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 2.17/2.38          | ~ (v2_funct_1 @ X0)
% 2.17/2.38          | ~ (v1_funct_1 @ X0)
% 2.17/2.38          | ~ (v1_relat_1 @ X0))),
% 2.17/2.38      inference('simplify', [status(thm)], ['153'])).
% 2.17/2.38  thf('155', plain,
% 2.17/2.38      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)
% 2.17/2.38        | ~ (v1_relat_1 @ sk_C)
% 2.17/2.38        | ~ (v1_funct_1 @ sk_C)
% 2.17/2.38        | ~ (v2_funct_1 @ sk_C))),
% 2.17/2.38      inference('sup+', [status(thm)], ['146', '154'])).
% 2.17/2.38  thf('156', plain, ((v1_relat_1 @ sk_C)),
% 2.17/2.38      inference('demod', [status(thm)], ['86', '87'])).
% 2.17/2.38  thf('157', plain, ((v1_funct_1 @ sk_C)),
% 2.17/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.38  thf('158', plain, ((v2_funct_1 @ sk_C)),
% 2.17/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.38  thf('159', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)),
% 2.17/2.38      inference('demod', [status(thm)], ['155', '156', '157', '158'])).
% 2.17/2.38  thf('160', plain,
% 2.17/2.38      (![X5 : $i, X6 : $i]:
% 2.17/2.38         (~ (v4_relat_1 @ X5 @ X6)
% 2.17/2.38          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 2.17/2.38          | ~ (v1_relat_1 @ X5))),
% 2.17/2.38      inference('cnf', [status(esa)], [d18_relat_1])).
% 2.17/2.38  thf('161', plain,
% 2.17/2.38      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.17/2.38        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 2.17/2.38      inference('sup-', [status(thm)], ['159', '160'])).
% 2.17/2.38  thf('162', plain,
% 2.17/2.38      ((~ (v1_relat_1 @ sk_C)
% 2.17/2.38        | ~ (v1_funct_1 @ sk_C)
% 2.17/2.38        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 2.17/2.38      inference('sup-', [status(thm)], ['141', '161'])).
% 2.17/2.38  thf('163', plain, ((v1_relat_1 @ sk_C)),
% 2.17/2.38      inference('demod', [status(thm)], ['86', '87'])).
% 2.17/2.38  thf('164', plain, ((v1_funct_1 @ sk_C)),
% 2.17/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.38  thf('165', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B)),
% 2.17/2.38      inference('demod', [status(thm)], ['162', '163', '164'])).
% 2.17/2.38  thf('166', plain,
% 2.17/2.38      (![X0 : $i, X2 : $i]:
% 2.17/2.38         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.17/2.38      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.17/2.38  thf('167', plain,
% 2.17/2.38      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 2.17/2.38        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 2.17/2.38      inference('sup-', [status(thm)], ['165', '166'])).
% 2.17/2.38  thf('168', plain,
% 2.17/2.38      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C))
% 2.17/2.38        | ~ (v1_relat_1 @ sk_C)
% 2.17/2.38        | ~ (v1_funct_1 @ sk_C)
% 2.17/2.38        | ~ (v2_funct_1 @ sk_C)
% 2.17/2.38        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 2.17/2.38      inference('sup-', [status(thm)], ['140', '167'])).
% 2.17/2.38  thf('169', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.17/2.38      inference('sup+', [status(thm)], ['144', '145'])).
% 2.17/2.38  thf('170', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.17/2.38      inference('simplify', [status(thm)], ['96'])).
% 2.17/2.38  thf('171', plain, ((v1_relat_1 @ sk_C)),
% 2.17/2.38      inference('demod', [status(thm)], ['86', '87'])).
% 2.17/2.38  thf('172', plain, ((v1_funct_1 @ sk_C)),
% 2.17/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.38  thf('173', plain, ((v2_funct_1 @ sk_C)),
% 2.17/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.38  thf('174', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 2.17/2.38      inference('demod', [status(thm)],
% 2.17/2.38                ['168', '169', '170', '171', '172', '173'])).
% 2.17/2.38  thf('175', plain,
% 2.17/2.38      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.17/2.38        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.17/2.38      inference('simplify', [status(thm)], ['52'])).
% 2.17/2.38  thf('176', plain,
% 2.17/2.38      (![X3 : $i, X4 : $i]:
% 2.17/2.38         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 2.17/2.38          | (v1_relat_1 @ X3)
% 2.17/2.38          | ~ (v1_relat_1 @ X4))),
% 2.17/2.38      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.17/2.38  thf('177', plain,
% 2.17/2.38      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))
% 2.17/2.38        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 2.17/2.38      inference('sup-', [status(thm)], ['175', '176'])).
% 2.17/2.38  thf('178', plain,
% 2.17/2.38      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 2.17/2.38      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.17/2.38  thf('179', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 2.17/2.38      inference('demod', [status(thm)], ['177', '178'])).
% 2.17/2.38  thf('180', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 2.17/2.38      inference('simplify', [status(thm)], ['119'])).
% 2.17/2.38  thf('181', plain, ((v1_funct_1 @ sk_C)),
% 2.17/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.38  thf('182', plain, ((v1_relat_1 @ sk_C)),
% 2.17/2.38      inference('demod', [status(thm)], ['86', '87'])).
% 2.17/2.38  thf('183', plain,
% 2.17/2.38      ((((k6_relat_1 @ sk_B) != (k6_relat_1 @ sk_B))
% 2.17/2.38        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.17/2.38      inference('demod', [status(thm)],
% 2.17/2.38                ['139', '174', '179', '180', '181', '182'])).
% 2.17/2.38  thf('184', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 2.17/2.38      inference('simplify', [status(thm)], ['183'])).
% 2.17/2.38  thf('185', plain,
% 2.17/2.38      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 2.17/2.38         = (k6_relat_1 @ sk_B))),
% 2.17/2.38      inference('demod', [status(thm)], ['124', '184'])).
% 2.17/2.38  thf('186', plain,
% 2.17/2.38      (![X20 : $i]:
% 2.17/2.38         (~ (v2_funct_1 @ X20)
% 2.17/2.38          | ((k1_relat_1 @ X20) = (k2_relat_1 @ (k2_funct_1 @ X20)))
% 2.17/2.38          | ~ (v1_funct_1 @ X20)
% 2.17/2.38          | ~ (v1_relat_1 @ X20))),
% 2.17/2.38      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.17/2.38  thf(l72_funct_1, axiom,
% 2.17/2.38    (![A:$i,B:$i]:
% 2.17/2.38     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.17/2.38       ( ![C:$i]:
% 2.17/2.38         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 2.17/2.38           ( ![D:$i]:
% 2.17/2.38             ( ( ( v1_relat_1 @ D ) & ( v1_funct_1 @ D ) ) =>
% 2.17/2.38               ( ( ( ( k2_relat_1 @ B ) = ( A ) ) & 
% 2.17/2.38                   ( ( k5_relat_1 @ B @ C ) =
% 2.17/2.38                     ( k6_relat_1 @ ( k1_relat_1 @ D ) ) ) & 
% 2.17/2.38                   ( ( k5_relat_1 @ C @ D ) = ( k6_relat_1 @ A ) ) ) =>
% 2.17/2.38                 ( ( D ) = ( B ) ) ) ) ) ) ) ))).
% 2.17/2.38  thf('187', plain,
% 2.17/2.38      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 2.17/2.38         (~ (v1_relat_1 @ X14)
% 2.17/2.38          | ~ (v1_funct_1 @ X14)
% 2.17/2.38          | ((k2_relat_1 @ X16) != (X15))
% 2.17/2.38          | ((k5_relat_1 @ X16 @ X14) != (k6_relat_1 @ (k1_relat_1 @ X17)))
% 2.17/2.38          | ((k5_relat_1 @ X14 @ X17) != (k6_relat_1 @ X15))
% 2.17/2.38          | ((X17) = (X16))
% 2.17/2.38          | ~ (v1_funct_1 @ X17)
% 2.17/2.38          | ~ (v1_relat_1 @ X17)
% 2.17/2.38          | ~ (v1_funct_1 @ X16)
% 2.17/2.38          | ~ (v1_relat_1 @ X16))),
% 2.17/2.38      inference('cnf', [status(esa)], [l72_funct_1])).
% 2.17/2.38  thf('188', plain,
% 2.17/2.38      (![X14 : $i, X16 : $i, X17 : $i]:
% 2.17/2.38         (~ (v1_relat_1 @ X16)
% 2.17/2.38          | ~ (v1_funct_1 @ X16)
% 2.17/2.38          | ~ (v1_relat_1 @ X17)
% 2.17/2.38          | ~ (v1_funct_1 @ X17)
% 2.17/2.38          | ((X17) = (X16))
% 2.17/2.38          | ((k5_relat_1 @ X14 @ X17) != (k6_relat_1 @ (k2_relat_1 @ X16)))
% 2.17/2.38          | ((k5_relat_1 @ X16 @ X14) != (k6_relat_1 @ (k1_relat_1 @ X17)))
% 2.17/2.38          | ~ (v1_funct_1 @ X14)
% 2.17/2.38          | ~ (v1_relat_1 @ X14))),
% 2.17/2.38      inference('simplify', [status(thm)], ['187'])).
% 2.17/2.38  thf('189', plain,
% 2.17/2.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.17/2.38         (((k5_relat_1 @ X2 @ X1) != (k6_relat_1 @ (k1_relat_1 @ X0)))
% 2.17/2.38          | ~ (v1_relat_1 @ X0)
% 2.17/2.38          | ~ (v1_funct_1 @ X0)
% 2.17/2.38          | ~ (v2_funct_1 @ X0)
% 2.17/2.38          | ~ (v1_relat_1 @ X2)
% 2.17/2.38          | ~ (v1_funct_1 @ X2)
% 2.17/2.38          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X2)
% 2.17/2.38              != (k6_relat_1 @ (k1_relat_1 @ X1)))
% 2.17/2.38          | ((X1) = (k2_funct_1 @ X0))
% 2.17/2.38          | ~ (v1_funct_1 @ X1)
% 2.17/2.38          | ~ (v1_relat_1 @ X1)
% 2.17/2.38          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.17/2.38          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 2.17/2.38      inference('sup-', [status(thm)], ['186', '188'])).
% 2.17/2.38  thf('190', plain,
% 2.17/2.38      (![X0 : $i]:
% 2.17/2.38         (((k6_relat_1 @ sk_B) != (k6_relat_1 @ (k1_relat_1 @ X0)))
% 2.17/2.38          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.17/2.38          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 2.17/2.38          | ~ (v1_relat_1 @ X0)
% 2.17/2.38          | ~ (v1_funct_1 @ X0)
% 2.17/2.38          | ((X0) = (k2_funct_1 @ sk_C))
% 2.17/2.38          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 2.17/2.38          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 2.17/2.38          | ~ (v2_funct_1 @ sk_C)
% 2.17/2.38          | ~ (v1_funct_1 @ sk_C)
% 2.17/2.38          | ~ (v1_relat_1 @ sk_C)
% 2.17/2.38          | ((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 2.17/2.38              != (k6_relat_1 @ (k1_relat_1 @ sk_C))))),
% 2.17/2.38      inference('sup-', [status(thm)], ['185', '189'])).
% 2.17/2.38  thf('191', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 2.17/2.38      inference('demod', [status(thm)], ['177', '178'])).
% 2.17/2.38  thf('192', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 2.17/2.38      inference('simplify', [status(thm)], ['119'])).
% 2.17/2.38  thf('193', plain,
% 2.17/2.38      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.17/2.38        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.17/2.38      inference('simplify', [status(thm)], ['52'])).
% 2.17/2.38  thf('194', plain,
% 2.17/2.38      (![X64 : $i, X65 : $i, X66 : $i]:
% 2.17/2.38         (~ (v2_funct_1 @ X64)
% 2.17/2.38          | ((k2_relset_1 @ X66 @ X65 @ X64) != (X65))
% 2.17/2.38          | (v1_funct_1 @ (k2_funct_1 @ X64))
% 2.17/2.38          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X66 @ X65)))
% 2.17/2.38          | ~ (v1_funct_2 @ X64 @ X66 @ X65)
% 2.17/2.38          | ~ (v1_funct_1 @ X64))),
% 2.17/2.38      inference('cnf', [status(esa)], [t31_funct_2])).
% 2.17/2.38  thf('195', plain,
% 2.17/2.38      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 2.17/2.38        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 2.17/2.38        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 2.17/2.38        | ((k2_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C)) != (sk_A))
% 2.17/2.38        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.17/2.38      inference('sup-', [status(thm)], ['193', '194'])).
% 2.17/2.38  thf('196', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 2.17/2.38      inference('simplify', [status(thm)], ['119'])).
% 2.17/2.38  thf('197', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 2.17/2.38      inference('simplify', [status(thm)], ['110'])).
% 2.17/2.38  thf('198', plain,
% 2.17/2.38      (((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 2.17/2.38        | ((k2_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C)) != (sk_A))
% 2.17/2.38        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.17/2.38      inference('demod', [status(thm)], ['195', '196', '197'])).
% 2.17/2.38  thf('199', plain,
% 2.17/2.38      (((k2_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C)) = (sk_A))),
% 2.17/2.38      inference('demod', [status(thm)], ['60', '101'])).
% 2.17/2.38  thf('200', plain,
% 2.17/2.38      (((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 2.17/2.38        | ((sk_A) != (sk_A))
% 2.17/2.38        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.17/2.38      inference('demod', [status(thm)], ['198', '199'])).
% 2.17/2.38  thf('201', plain,
% 2.17/2.38      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 2.17/2.38        | (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 2.17/2.38      inference('simplify', [status(thm)], ['200'])).
% 2.17/2.38  thf('202', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 2.17/2.38      inference('simplify', [status(thm)], ['183'])).
% 2.17/2.38  thf('203', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.17/2.38      inference('demod', [status(thm)], ['201', '202'])).
% 2.17/2.38  thf('204', plain,
% 2.17/2.38      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.17/2.38        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.17/2.38      inference('simplify', [status(thm)], ['52'])).
% 2.17/2.38  thf('205', plain,
% 2.17/2.38      (![X64 : $i, X65 : $i, X66 : $i]:
% 2.17/2.38         (~ (v2_funct_1 @ X64)
% 2.17/2.38          | ((k2_relset_1 @ X66 @ X65 @ X64) != (X65))
% 2.17/2.38          | (m1_subset_1 @ (k2_funct_1 @ X64) @ 
% 2.17/2.38             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X65 @ X66)))
% 2.17/2.38          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X66 @ X65)))
% 2.17/2.38          | ~ (v1_funct_2 @ X64 @ X66 @ X65)
% 2.17/2.38          | ~ (v1_funct_1 @ X64))),
% 2.17/2.38      inference('cnf', [status(esa)], [t31_funct_2])).
% 2.17/2.38  thf('206', plain,
% 2.17/2.38      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 2.17/2.38        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 2.17/2.38        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 2.17/2.38           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 2.17/2.38        | ((k2_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C)) != (sk_A))
% 2.17/2.38        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.17/2.38      inference('sup-', [status(thm)], ['204', '205'])).
% 2.17/2.38  thf('207', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 2.17/2.38      inference('simplify', [status(thm)], ['119'])).
% 2.17/2.38  thf('208', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 2.17/2.38      inference('simplify', [status(thm)], ['110'])).
% 2.17/2.38  thf('209', plain,
% 2.17/2.38      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 2.17/2.38         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 2.17/2.38        | ((k2_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C)) != (sk_A))
% 2.17/2.38        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.17/2.38      inference('demod', [status(thm)], ['206', '207', '208'])).
% 2.17/2.38  thf('210', plain,
% 2.17/2.38      (((k2_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C)) = (sk_A))),
% 2.17/2.38      inference('demod', [status(thm)], ['60', '101'])).
% 2.17/2.38  thf('211', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 2.17/2.38      inference('simplify', [status(thm)], ['183'])).
% 2.17/2.38  thf('212', plain,
% 2.17/2.38      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 2.17/2.38         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 2.17/2.38        | ((sk_A) != (sk_A)))),
% 2.17/2.38      inference('demod', [status(thm)], ['209', '210', '211'])).
% 2.17/2.38  thf('213', plain,
% 2.17/2.38      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 2.17/2.38        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.17/2.38      inference('simplify', [status(thm)], ['212'])).
% 2.17/2.38  thf('214', plain,
% 2.17/2.38      (![X3 : $i, X4 : $i]:
% 2.17/2.38         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 2.17/2.38          | (v1_relat_1 @ X3)
% 2.17/2.38          | ~ (v1_relat_1 @ X4))),
% 2.17/2.38      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.17/2.38  thf('215', plain,
% 2.17/2.38      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 2.17/2.38        | (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 2.17/2.38      inference('sup-', [status(thm)], ['213', '214'])).
% 2.17/2.38  thf('216', plain,
% 2.17/2.38      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 2.17/2.38      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.17/2.38  thf('217', plain, ((v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.17/2.38      inference('demod', [status(thm)], ['215', '216'])).
% 2.17/2.38  thf('218', plain, ((v2_funct_1 @ sk_C)),
% 2.17/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.38  thf('219', plain, ((v1_funct_1 @ sk_C)),
% 2.17/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.38  thf('220', plain, ((v1_relat_1 @ sk_C)),
% 2.17/2.38      inference('demod', [status(thm)], ['86', '87'])).
% 2.17/2.38  thf('221', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 2.17/2.38      inference('demod', [status(thm)], ['64', '71', '74'])).
% 2.17/2.38  thf('222', plain,
% 2.17/2.38      (![X0 : $i]:
% 2.17/2.38         (((k6_relat_1 @ sk_B) != (k6_relat_1 @ (k1_relat_1 @ X0)))
% 2.17/2.38          | ~ (v1_relat_1 @ X0)
% 2.17/2.38          | ~ (v1_funct_1 @ X0)
% 2.17/2.38          | ((X0) = (k2_funct_1 @ sk_C))
% 2.17/2.38          | ((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 2.17/2.38              != (k6_relat_1 @ sk_A)))),
% 2.17/2.38      inference('demod', [status(thm)],
% 2.17/2.38                ['190', '191', '192', '203', '217', '218', '219', '220', '221'])).
% 2.17/2.38  thf('223', plain,
% 2.17/2.38      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 2.17/2.38         = (k6_relat_1 @ sk_B))),
% 2.17/2.38      inference('demod', [status(thm)], ['124', '184'])).
% 2.17/2.38  thf('224', plain,
% 2.17/2.38      (![X13 : $i]:
% 2.17/2.38         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 2.17/2.38          | ~ (v1_funct_1 @ X13)
% 2.17/2.38          | ~ (v1_relat_1 @ X13))),
% 2.17/2.38      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.17/2.38  thf('225', plain,
% 2.17/2.38      (![X20 : $i]:
% 2.17/2.38         (~ (v2_funct_1 @ X20)
% 2.17/2.38          | ((k1_relat_1 @ X20) = (k2_relat_1 @ (k2_funct_1 @ X20)))
% 2.17/2.38          | ~ (v1_funct_1 @ X20)
% 2.17/2.38          | ~ (v1_relat_1 @ X20))),
% 2.17/2.38      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.17/2.38  thf('226', plain,
% 2.17/2.38      (![X21 : $i]:
% 2.17/2.38         (~ (v2_funct_1 @ X21)
% 2.17/2.38          | ((k2_relat_1 @ (k5_relat_1 @ X21 @ (k2_funct_1 @ X21)))
% 2.17/2.38              = (k1_relat_1 @ X21))
% 2.17/2.38          | ~ (v1_funct_1 @ X21)
% 2.17/2.38          | ~ (v1_relat_1 @ X21))),
% 2.17/2.38      inference('cnf', [status(esa)], [t58_funct_1])).
% 2.17/2.38  thf('227', plain,
% 2.17/2.38      (![X9 : $i, X10 : $i]:
% 2.17/2.38         (~ (v1_relat_1 @ X9)
% 2.17/2.38          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X10 @ X9)) @ 
% 2.17/2.38             (k2_relat_1 @ X9))
% 2.17/2.38          | ~ (v1_relat_1 @ X10))),
% 2.17/2.38      inference('cnf', [status(esa)], [t45_relat_1])).
% 2.17/2.38  thf('228', plain,
% 2.17/2.38      (![X0 : $i, X2 : $i]:
% 2.17/2.38         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.17/2.38      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.17/2.38  thf('229', plain,
% 2.17/2.38      (![X0 : $i, X1 : $i]:
% 2.17/2.38         (~ (v1_relat_1 @ X1)
% 2.17/2.38          | ~ (v1_relat_1 @ X0)
% 2.17/2.38          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 2.17/2.38               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 2.17/2.38          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 2.17/2.38      inference('sup-', [status(thm)], ['227', '228'])).
% 2.17/2.38  thf('230', plain,
% 2.17/2.38      (![X0 : $i]:
% 2.17/2.38         (~ (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 2.17/2.38          | ~ (v1_relat_1 @ X0)
% 2.17/2.38          | ~ (v1_funct_1 @ X0)
% 2.17/2.38          | ~ (v2_funct_1 @ X0)
% 2.17/2.38          | ((k2_relat_1 @ (k2_funct_1 @ X0))
% 2.17/2.38              = (k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0))))
% 2.17/2.38          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.17/2.38          | ~ (v1_relat_1 @ X0))),
% 2.17/2.38      inference('sup-', [status(thm)], ['226', '229'])).
% 2.17/2.38  thf('231', plain,
% 2.17/2.38      (![X0 : $i]:
% 2.17/2.38         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.17/2.38          | ((k2_relat_1 @ (k2_funct_1 @ X0))
% 2.17/2.38              = (k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0))))
% 2.17/2.38          | ~ (v2_funct_1 @ X0)
% 2.17/2.38          | ~ (v1_funct_1 @ X0)
% 2.17/2.38          | ~ (v1_relat_1 @ X0)
% 2.17/2.38          | ~ (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 2.17/2.38      inference('simplify', [status(thm)], ['230'])).
% 2.17/2.38  thf('232', plain,
% 2.17/2.38      (![X0 : $i]:
% 2.17/2.38         (~ (r1_tarski @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 2.17/2.38          | ~ (v1_relat_1 @ X0)
% 2.17/2.38          | ~ (v1_funct_1 @ X0)
% 2.17/2.38          | ~ (v2_funct_1 @ X0)
% 2.17/2.38          | ~ (v1_relat_1 @ X0)
% 2.17/2.38          | ~ (v1_funct_1 @ X0)
% 2.17/2.38          | ~ (v2_funct_1 @ X0)
% 2.17/2.38          | ((k2_relat_1 @ (k2_funct_1 @ X0))
% 2.17/2.38              = (k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0))))
% 2.17/2.38          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 2.17/2.38      inference('sup-', [status(thm)], ['225', '231'])).
% 2.17/2.38  thf('233', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.17/2.38      inference('simplify', [status(thm)], ['96'])).
% 2.17/2.38  thf('234', plain,
% 2.17/2.38      (![X0 : $i]:
% 2.17/2.38         (~ (v1_relat_1 @ X0)
% 2.17/2.38          | ~ (v1_funct_1 @ X0)
% 2.17/2.38          | ~ (v2_funct_1 @ X0)
% 2.17/2.38          | ~ (v1_relat_1 @ X0)
% 2.17/2.38          | ~ (v1_funct_1 @ X0)
% 2.17/2.38          | ~ (v2_funct_1 @ X0)
% 2.17/2.38          | ((k2_relat_1 @ (k2_funct_1 @ X0))
% 2.17/2.38              = (k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0))))
% 2.17/2.38          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 2.17/2.38      inference('demod', [status(thm)], ['232', '233'])).
% 2.17/2.38  thf('235', plain,
% 2.17/2.38      (![X0 : $i]:
% 2.17/2.38         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.17/2.38          | ((k2_relat_1 @ (k2_funct_1 @ X0))
% 2.17/2.38              = (k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0))))
% 2.17/2.38          | ~ (v2_funct_1 @ X0)
% 2.17/2.38          | ~ (v1_funct_1 @ X0)
% 2.17/2.38          | ~ (v1_relat_1 @ X0))),
% 2.17/2.38      inference('simplify', [status(thm)], ['234'])).
% 2.17/2.38  thf('236', plain,
% 2.17/2.38      (![X0 : $i]:
% 2.17/2.38         (~ (v1_relat_1 @ X0)
% 2.17/2.38          | ~ (v1_funct_1 @ X0)
% 2.17/2.38          | ~ (v1_relat_1 @ X0)
% 2.17/2.38          | ~ (v1_funct_1 @ X0)
% 2.17/2.38          | ~ (v2_funct_1 @ X0)
% 2.17/2.38          | ((k2_relat_1 @ (k2_funct_1 @ X0))
% 2.17/2.38              = (k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))))),
% 2.17/2.38      inference('sup-', [status(thm)], ['224', '235'])).
% 2.17/2.38  thf('237', plain,
% 2.17/2.38      (![X0 : $i]:
% 2.17/2.38         (((k2_relat_1 @ (k2_funct_1 @ X0))
% 2.17/2.38            = (k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0))))
% 2.17/2.38          | ~ (v2_funct_1 @ X0)
% 2.17/2.38          | ~ (v1_funct_1 @ X0)
% 2.17/2.38          | ~ (v1_relat_1 @ X0))),
% 2.17/2.38      inference('simplify', [status(thm)], ['236'])).
% 2.17/2.38  thf('238', plain,
% 2.17/2.38      ((((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 2.17/2.38          = (k2_relat_1 @ (k6_relat_1 @ sk_B)))
% 2.17/2.38        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.17/2.38        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 2.17/2.38        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.17/2.38      inference('sup+', [status(thm)], ['223', '237'])).
% 2.17/2.38  thf(t71_relat_1, axiom,
% 2.17/2.38    (![A:$i]:
% 2.17/2.38     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 2.17/2.38       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 2.17/2.38  thf('239', plain, (![X12 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 2.17/2.38      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.17/2.38  thf('240', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 2.17/2.38      inference('demod', [status(thm)], ['177', '178'])).
% 2.17/2.38  thf('241', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 2.17/2.38      inference('simplify', [status(thm)], ['119'])).
% 2.17/2.38  thf('242', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 2.17/2.38      inference('simplify', [status(thm)], ['183'])).
% 2.17/2.38  thf('243', plain,
% 2.17/2.38      (((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) = (sk_B))),
% 2.17/2.38      inference('demod', [status(thm)], ['238', '239', '240', '241', '242'])).
% 2.17/2.38  thf('244', plain,
% 2.17/2.38      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))),
% 2.17/2.38      inference('simplify_reflect-', [status(thm)], ['135', '136'])).
% 2.17/2.38  thf('245', plain,
% 2.17/2.38      (![X14 : $i, X16 : $i, X17 : $i]:
% 2.17/2.38         (~ (v1_relat_1 @ X16)
% 2.17/2.38          | ~ (v1_funct_1 @ X16)
% 2.17/2.38          | ~ (v1_relat_1 @ X17)
% 2.17/2.38          | ~ (v1_funct_1 @ X17)
% 2.17/2.38          | ((X17) = (X16))
% 2.17/2.38          | ((k5_relat_1 @ X14 @ X17) != (k6_relat_1 @ (k2_relat_1 @ X16)))
% 2.17/2.38          | ((k5_relat_1 @ X16 @ X14) != (k6_relat_1 @ (k1_relat_1 @ X17)))
% 2.17/2.38          | ~ (v1_funct_1 @ X14)
% 2.17/2.38          | ~ (v1_relat_1 @ X14))),
% 2.17/2.38      inference('simplify', [status(thm)], ['187'])).
% 2.17/2.38  thf('246', plain,
% 2.17/2.38      (![X0 : $i]:
% 2.17/2.38         (((k6_relat_1 @ sk_B) != (k6_relat_1 @ (k2_relat_1 @ X0)))
% 2.17/2.38          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.17/2.38          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 2.17/2.38          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ sk_C))
% 2.17/2.38              != (k6_relat_1 @ (k1_relat_1 @ sk_C)))
% 2.17/2.38          | ((sk_C) = (X0))
% 2.17/2.38          | ~ (v1_funct_1 @ sk_C)
% 2.17/2.38          | ~ (v1_relat_1 @ sk_C)
% 2.17/2.38          | ~ (v1_funct_1 @ X0)
% 2.17/2.38          | ~ (v1_relat_1 @ X0))),
% 2.17/2.38      inference('sup-', [status(thm)], ['244', '245'])).
% 2.17/2.38  thf('247', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 2.17/2.38      inference('demod', [status(thm)], ['177', '178'])).
% 2.17/2.38  thf('248', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 2.17/2.38      inference('simplify', [status(thm)], ['119'])).
% 2.17/2.38  thf('249', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 2.17/2.38      inference('demod', [status(thm)], ['64', '71', '74'])).
% 2.17/2.38  thf('250', plain, ((v1_funct_1 @ sk_C)),
% 2.17/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.38  thf('251', plain, ((v1_relat_1 @ sk_C)),
% 2.17/2.38      inference('demod', [status(thm)], ['86', '87'])).
% 2.17/2.38  thf('252', plain,
% 2.17/2.38      (![X0 : $i]:
% 2.17/2.38         (((k6_relat_1 @ sk_B) != (k6_relat_1 @ (k2_relat_1 @ X0)))
% 2.17/2.38          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ sk_C)) != (k6_relat_1 @ sk_A))
% 2.17/2.38          | ((sk_C) = (X0))
% 2.17/2.38          | ~ (v1_funct_1 @ X0)
% 2.17/2.38          | ~ (v1_relat_1 @ X0))),
% 2.17/2.38      inference('demod', [status(thm)],
% 2.17/2.38                ['246', '247', '248', '249', '250', '251'])).
% 2.17/2.38  thf('253', plain,
% 2.17/2.38      ((((k6_relat_1 @ sk_B) != (k6_relat_1 @ sk_B))
% 2.17/2.38        | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 2.17/2.38        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 2.17/2.38        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 2.17/2.38        | ((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 2.17/2.38            (k2_funct_1 @ sk_C)) != (k6_relat_1 @ sk_A)))),
% 2.17/2.38      inference('sup-', [status(thm)], ['243', '252'])).
% 2.17/2.38  thf('254', plain, ((v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.17/2.38      inference('demod', [status(thm)], ['215', '216'])).
% 2.17/2.38  thf('255', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.17/2.38      inference('demod', [status(thm)], ['201', '202'])).
% 2.17/2.38  thf('256', plain,
% 2.17/2.38      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.17/2.38        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.17/2.38      inference('simplify', [status(thm)], ['52'])).
% 2.17/2.38  thf('257', plain,
% 2.17/2.38      (![X67 : $i, X68 : $i, X69 : $i]:
% 2.17/2.38         (((X67) = (k1_xboole_0))
% 2.17/2.38          | ~ (v1_funct_1 @ X68)
% 2.17/2.38          | ~ (v1_funct_2 @ X68 @ X69 @ X67)
% 2.17/2.38          | ~ (m1_subset_1 @ X68 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X69 @ X67)))
% 2.17/2.38          | ((k5_relat_1 @ (k2_funct_1 @ X68) @ X68) = (k6_relat_1 @ X67))
% 2.17/2.38          | ~ (v2_funct_1 @ X68)
% 2.17/2.38          | ((k2_relset_1 @ X69 @ X67 @ X68) != (X67)))),
% 2.17/2.38      inference('demod', [status(thm)], ['126', '127'])).
% 2.17/2.38  thf('258', plain,
% 2.17/2.38      ((((k2_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C)) != (sk_A))
% 2.17/2.38        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 2.17/2.38        | ((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 2.17/2.38            (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 2.17/2.38        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 2.17/2.38        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 2.17/2.38        | ((sk_A) = (k1_xboole_0)))),
% 2.17/2.38      inference('sup-', [status(thm)], ['256', '257'])).
% 2.17/2.38  thf('259', plain,
% 2.17/2.38      (((k2_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C)) = (sk_A))),
% 2.17/2.38      inference('demod', [status(thm)], ['60', '101'])).
% 2.17/2.38  thf('260', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 2.17/2.38      inference('simplify', [status(thm)], ['110'])).
% 2.17/2.38  thf('261', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 2.17/2.38      inference('simplify', [status(thm)], ['119'])).
% 2.17/2.38  thf('262', plain,
% 2.17/2.38      ((((sk_A) != (sk_A))
% 2.17/2.38        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 2.17/2.38        | ((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 2.17/2.38            (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 2.17/2.38        | ((sk_A) = (k1_xboole_0)))),
% 2.17/2.38      inference('demod', [status(thm)], ['258', '259', '260', '261'])).
% 2.17/2.38  thf('263', plain,
% 2.17/2.38      ((((sk_A) = (k1_xboole_0))
% 2.17/2.38        | ((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 2.17/2.38            (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 2.17/2.38        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.17/2.38      inference('simplify', [status(thm)], ['262'])).
% 2.17/2.38  thf('264', plain, (((sk_A) != (k1_xboole_0))),
% 2.17/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.38  thf('265', plain,
% 2.17/2.38      ((((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ (k2_funct_1 @ sk_C))
% 2.17/2.38          = (k6_relat_1 @ sk_A))
% 2.17/2.38        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.17/2.38      inference('simplify_reflect-', [status(thm)], ['263', '264'])).
% 2.17/2.38  thf('266', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 2.17/2.38      inference('simplify', [status(thm)], ['183'])).
% 2.17/2.38  thf('267', plain,
% 2.17/2.38      (((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ (k2_funct_1 @ sk_C))
% 2.17/2.38         = (k6_relat_1 @ sk_A))),
% 2.17/2.38      inference('demod', [status(thm)], ['265', '266'])).
% 2.17/2.38  thf('268', plain,
% 2.17/2.38      ((((k6_relat_1 @ sk_B) != (k6_relat_1 @ sk_B))
% 2.17/2.38        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 2.17/2.38        | ((k6_relat_1 @ sk_A) != (k6_relat_1 @ sk_A)))),
% 2.17/2.38      inference('demod', [status(thm)], ['253', '254', '255', '267'])).
% 2.17/2.38  thf('269', plain, (((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.17/2.38      inference('simplify', [status(thm)], ['268'])).
% 2.17/2.38  thf('270', plain,
% 2.17/2.38      (![X0 : $i]:
% 2.17/2.38         (((k6_relat_1 @ sk_B) != (k6_relat_1 @ (k1_relat_1 @ X0)))
% 2.17/2.38          | ~ (v1_relat_1 @ X0)
% 2.17/2.38          | ~ (v1_funct_1 @ X0)
% 2.17/2.38          | ((X0) = (k2_funct_1 @ sk_C))
% 2.17/2.38          | ((k5_relat_1 @ sk_C @ X0) != (k6_relat_1 @ sk_A)))),
% 2.17/2.38      inference('demod', [status(thm)], ['222', '269'])).
% 2.17/2.38  thf('271', plain,
% 2.17/2.38      ((((k6_relat_1 @ sk_B) != (k6_relat_1 @ sk_B))
% 2.17/2.38        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_relat_1 @ sk_A))
% 2.17/2.38        | ((sk_D) = (k2_funct_1 @ sk_C))
% 2.17/2.38        | ~ (v1_funct_1 @ sk_D)
% 2.17/2.38        | ~ (v1_relat_1 @ sk_D))),
% 2.17/2.38      inference('sup-', [status(thm)], ['44', '270'])).
% 2.17/2.38  thf('272', plain, ((v1_funct_1 @ sk_D)),
% 2.17/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.38  thf('273', plain,
% 2.17/2.38      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.17/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.38  thf('274', plain,
% 2.17/2.38      (![X3 : $i, X4 : $i]:
% 2.17/2.38         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 2.17/2.38          | (v1_relat_1 @ X3)
% 2.17/2.38          | ~ (v1_relat_1 @ X4))),
% 2.17/2.38      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.17/2.38  thf('275', plain,
% 2.17/2.38      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 2.17/2.38      inference('sup-', [status(thm)], ['273', '274'])).
% 2.17/2.38  thf('276', plain,
% 2.17/2.38      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 2.17/2.38      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.17/2.38  thf('277', plain, ((v1_relat_1 @ sk_D)),
% 2.17/2.38      inference('demod', [status(thm)], ['275', '276'])).
% 2.17/2.38  thf('278', plain,
% 2.17/2.38      ((((k6_relat_1 @ sk_B) != (k6_relat_1 @ sk_B))
% 2.17/2.38        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_relat_1 @ sk_A))
% 2.17/2.38        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 2.17/2.38      inference('demod', [status(thm)], ['271', '272', '277'])).
% 2.17/2.38  thf('279', plain,
% 2.17/2.38      ((((sk_D) = (k2_funct_1 @ sk_C))
% 2.17/2.38        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_relat_1 @ sk_A)))),
% 2.17/2.38      inference('simplify', [status(thm)], ['278'])).
% 2.17/2.38  thf('280', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 2.17/2.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.17/2.38  thf('281', plain, (((k5_relat_1 @ sk_C @ sk_D) != (k6_relat_1 @ sk_A))),
% 2.17/2.38      inference('simplify_reflect-', [status(thm)], ['279', '280'])).
% 2.17/2.38  thf('282', plain, ($false),
% 2.17/2.38      inference('simplify_reflect-', [status(thm)], ['30', '281'])).
% 2.17/2.38  
% 2.17/2.38  % SZS output end Refutation
% 2.17/2.38  
% 2.17/2.38  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

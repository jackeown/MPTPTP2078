%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8Bh6qDDlVs

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:24 EST 2020

% Result     : Theorem 0.99s
% Output     : Refutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 229 expanded)
%              Number of leaves         :   46 (  88 expanded)
%              Depth                    :   14
%              Number of atoms          : 1377 (4855 expanded)
%              Number of equality atoms :  112 ( 371 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
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
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( ( k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41 )
        = ( k5_relat_1 @ X38 @ X41 ) ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X10 @ X11 @ X13 @ X14 @ X9 @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X14 ) ) ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( ( k4_relset_1 @ X19 @ X20 @ X22 @ X23 @ X18 @ X21 )
        = ( k5_relat_1 @ X18 @ X21 ) ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( X24 = X27 )
      | ~ ( r2_relset_1 @ X25 @ X26 @ X24 @ X27 ) ) ),
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
    ! [X37: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('28',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('29',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ( X30
        = ( k1_relset_1 @ X30 @ X31 @ X32 ) )
      | ~ ( zip_tseitin_1 @ X32 @ X31 @ X30 ) ) ),
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
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
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
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ( X30
        = ( k1_relset_1 @ X30 @ X31 @ X32 ) )
      | ~ ( zip_tseitin_1 @ X32 @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('47',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('51',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('57',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['47','54','57'])).

thf(t63_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ( ( k5_relat_1 @ A @ B )
                = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('59',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( X7
        = ( k2_funct_1 @ X8 ) )
      | ( ( k5_relat_1 @ X8 @ X7 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X8 ) ) )
      | ( ( k2_relat_1 @ X8 )
       != ( k1_relat_1 @ X7 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t63_funct_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
       != ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C )
      | ( ( k2_relat_1 @ sk_C )
       != ( k1_relat_1 @ X0 ) )
      | ( X0
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('63',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('64',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('65',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
       != ( k6_relat_1 @ sk_A ) )
      | ( ( k2_relat_1 @ sk_C )
       != ( k1_relat_1 @ X0 ) )
      | ( X0
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['60','65','66','67'])).

thf('69',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != sk_B )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
     != ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('72',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('74',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != sk_B )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
     != ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','74','75'])).

thf('77',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != sk_B )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
     != ( k6_relat_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['76','77'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('79',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X6 ) @ X6 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('80',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('81',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( X45 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X45 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X46 ) @ X46 )
        = ( k6_partfun1 @ X45 ) )
      | ~ ( v2_funct_1 @ X46 )
      | ( ( k2_relset_1 @ X47 @ X45 @ X46 )
       != X45 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('82',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('83',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( X45 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X45 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X46 ) @ X46 )
        = ( k6_relat_1 @ X45 ) )
      | ~ ( v2_funct_1 @ X46 )
      | ( ( k2_relset_1 @ X47 @ X45 @ X46 )
       != X45 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['84','85','86','87','88'])).

thf('90',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['79','92'])).

thf('94',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['63','64'])).

thf('95',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['93','94','95','96'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('98',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('99',plain,
    ( ( k1_relat_1 @ ( k6_relat_1 @ sk_B ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('101',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
     != ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','101'])).

thf('103',plain,(
    ( k5_relat_1 @ sk_C @ sk_D )
 != ( k6_relat_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['30','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8Bh6qDDlVs
% 0.15/0.38  % Computer   : n007.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 20:01:51 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.39  % Number of cores: 8
% 0.15/0.39  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.99/1.17  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.99/1.17  % Solved by: fo/fo7.sh
% 0.99/1.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.99/1.17  % done 364 iterations in 0.676s
% 0.99/1.17  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.99/1.17  % SZS output start Refutation
% 0.99/1.17  thf(sk_C_type, type, sk_C: $i).
% 0.99/1.17  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.99/1.17  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.99/1.17  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.99/1.17  thf(sk_A_type, type, sk_A: $i).
% 0.99/1.17  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.99/1.17  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.99/1.17  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.99/1.17  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.99/1.17  thf(sk_B_type, type, sk_B: $i).
% 0.99/1.17  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.99/1.17  thf(sk_D_type, type, sk_D: $i).
% 0.99/1.17  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.99/1.17  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.99/1.17  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.99/1.17  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 0.99/1.17  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.99/1.17  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.99/1.17  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.99/1.17  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.99/1.17  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.99/1.17  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.99/1.17  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.99/1.17  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.99/1.17  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.99/1.17  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.99/1.17  thf(t36_funct_2, conjecture,
% 0.99/1.17    (![A:$i,B:$i,C:$i]:
% 0.99/1.17     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.99/1.17         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.99/1.17       ( ![D:$i]:
% 0.99/1.17         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.99/1.17             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.99/1.17           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.99/1.17               ( r2_relset_1 @
% 0.99/1.17                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.99/1.17                 ( k6_partfun1 @ A ) ) & 
% 0.99/1.17               ( v2_funct_1 @ C ) ) =>
% 0.99/1.17             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.99/1.17               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.99/1.17  thf(zf_stmt_0, negated_conjecture,
% 0.99/1.17    (~( ![A:$i,B:$i,C:$i]:
% 0.99/1.17        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.99/1.17            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.99/1.17          ( ![D:$i]:
% 0.99/1.17            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.99/1.17                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.99/1.17              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.99/1.17                  ( r2_relset_1 @
% 0.99/1.17                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.99/1.17                    ( k6_partfun1 @ A ) ) & 
% 0.99/1.17                  ( v2_funct_1 @ C ) ) =>
% 0.99/1.17                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.99/1.17                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.99/1.17    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.99/1.17  thf('0', plain,
% 0.99/1.17      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.99/1.17        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.99/1.17        (k6_partfun1 @ sk_A))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf(redefinition_k6_partfun1, axiom,
% 0.99/1.17    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.99/1.17  thf('1', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 0.99/1.17      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.99/1.17  thf('2', plain,
% 0.99/1.17      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.99/1.17        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.99/1.17        (k6_relat_1 @ sk_A))),
% 0.99/1.17      inference('demod', [status(thm)], ['0', '1'])).
% 0.99/1.17  thf('3', plain,
% 0.99/1.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('4', plain,
% 0.99/1.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf(redefinition_k1_partfun1, axiom,
% 0.99/1.17    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.99/1.17     ( ( ( v1_funct_1 @ E ) & 
% 0.99/1.17         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.99/1.17         ( v1_funct_1 @ F ) & 
% 0.99/1.17         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.99/1.17       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.99/1.17  thf('5', plain,
% 0.99/1.17      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.99/1.17          | ~ (v1_funct_1 @ X38)
% 0.99/1.17          | ~ (v1_funct_1 @ X41)
% 0.99/1.17          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 0.99/1.17          | ((k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41)
% 0.99/1.17              = (k5_relat_1 @ X38 @ X41)))),
% 0.99/1.17      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.99/1.17  thf('6', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.17         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.99/1.17            = (k5_relat_1 @ sk_C @ X0))
% 0.99/1.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.99/1.17          | ~ (v1_funct_1 @ X0)
% 0.99/1.17          | ~ (v1_funct_1 @ sk_C))),
% 0.99/1.17      inference('sup-', [status(thm)], ['4', '5'])).
% 0.99/1.17  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('8', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.17         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.99/1.17            = (k5_relat_1 @ sk_C @ X0))
% 0.99/1.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.99/1.17          | ~ (v1_funct_1 @ X0))),
% 0.99/1.17      inference('demod', [status(thm)], ['6', '7'])).
% 0.99/1.17  thf('9', plain,
% 0.99/1.17      ((~ (v1_funct_1 @ sk_D)
% 0.99/1.17        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.99/1.17            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['3', '8'])).
% 0.99/1.17  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('11', plain,
% 0.99/1.17      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.99/1.17         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.99/1.17      inference('demod', [status(thm)], ['9', '10'])).
% 0.99/1.17  thf('12', plain,
% 0.99/1.17      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.99/1.17        (k6_relat_1 @ sk_A))),
% 0.99/1.17      inference('demod', [status(thm)], ['2', '11'])).
% 0.99/1.17  thf('13', plain,
% 0.99/1.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('14', plain,
% 0.99/1.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf(dt_k4_relset_1, axiom,
% 0.99/1.17    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.99/1.17     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.99/1.17         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.99/1.17       ( m1_subset_1 @
% 0.99/1.17         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.99/1.17         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 0.99/1.17  thf('15', plain,
% 0.99/1.17      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.99/1.17          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.99/1.17          | (m1_subset_1 @ (k4_relset_1 @ X10 @ X11 @ X13 @ X14 @ X9 @ X12) @ 
% 0.99/1.17             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X14))))),
% 0.99/1.17      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 0.99/1.17  thf('16', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.17         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.99/1.17           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.99/1.17          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 0.99/1.17      inference('sup-', [status(thm)], ['14', '15'])).
% 0.99/1.17  thf('17', plain,
% 0.99/1.17      ((m1_subset_1 @ 
% 0.99/1.17        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.99/1.17        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['13', '16'])).
% 0.99/1.17  thf('18', plain,
% 0.99/1.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('19', plain,
% 0.99/1.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf(redefinition_k4_relset_1, axiom,
% 0.99/1.17    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.99/1.17     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.99/1.17         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.99/1.17       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.99/1.17  thf('20', plain,
% 0.99/1.17      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.99/1.17          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.99/1.17          | ((k4_relset_1 @ X19 @ X20 @ X22 @ X23 @ X18 @ X21)
% 0.99/1.17              = (k5_relat_1 @ X18 @ X21)))),
% 0.99/1.17      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 0.99/1.17  thf('21', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.17         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.99/1.17            = (k5_relat_1 @ sk_C @ X0))
% 0.99/1.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.99/1.17      inference('sup-', [status(thm)], ['19', '20'])).
% 0.99/1.17  thf('22', plain,
% 0.99/1.17      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.99/1.17         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.99/1.17      inference('sup-', [status(thm)], ['18', '21'])).
% 0.99/1.17  thf('23', plain,
% 0.99/1.17      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.99/1.17        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.99/1.17      inference('demod', [status(thm)], ['17', '22'])).
% 0.99/1.17  thf(redefinition_r2_relset_1, axiom,
% 0.99/1.17    (![A:$i,B:$i,C:$i,D:$i]:
% 0.99/1.17     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.99/1.17         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.99/1.17       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.99/1.17  thf('24', plain,
% 0.99/1.17      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.99/1.17          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.99/1.17          | ((X24) = (X27))
% 0.99/1.17          | ~ (r2_relset_1 @ X25 @ X26 @ X24 @ X27))),
% 0.99/1.17      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.99/1.17  thf('25', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 0.99/1.17          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 0.99/1.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.99/1.17      inference('sup-', [status(thm)], ['23', '24'])).
% 0.99/1.17  thf('26', plain,
% 0.99/1.17      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 0.99/1.17           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.99/1.17        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['12', '25'])).
% 0.99/1.17  thf(dt_k6_partfun1, axiom,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ( m1_subset_1 @
% 0.99/1.17         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.99/1.17       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.99/1.17  thf('27', plain,
% 0.99/1.17      (![X37 : $i]:
% 0.99/1.17         (m1_subset_1 @ (k6_partfun1 @ X37) @ 
% 0.99/1.17          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))),
% 0.99/1.17      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.99/1.17  thf('28', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 0.99/1.17      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.99/1.17  thf('29', plain,
% 0.99/1.17      (![X37 : $i]:
% 0.99/1.17         (m1_subset_1 @ (k6_relat_1 @ X37) @ 
% 0.99/1.17          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))),
% 0.99/1.17      inference('demod', [status(thm)], ['27', '28'])).
% 0.99/1.17  thf('30', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 0.99/1.17      inference('demod', [status(thm)], ['26', '29'])).
% 0.99/1.17  thf('31', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf(d1_funct_2, axiom,
% 0.99/1.17    (![A:$i,B:$i,C:$i]:
% 0.99/1.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.99/1.17       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.99/1.17           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.99/1.17             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.99/1.17         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.99/1.17           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.99/1.17             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.99/1.17  thf(zf_stmt_1, axiom,
% 0.99/1.17    (![C:$i,B:$i,A:$i]:
% 0.99/1.17     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.99/1.17       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.99/1.17  thf('32', plain,
% 0.99/1.17      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.99/1.17         (~ (v1_funct_2 @ X32 @ X30 @ X31)
% 0.99/1.17          | ((X30) = (k1_relset_1 @ X30 @ X31 @ X32))
% 0.99/1.17          | ~ (zip_tseitin_1 @ X32 @ X31 @ X30))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.99/1.17  thf('33', plain,
% 0.99/1.17      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 0.99/1.17        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['31', '32'])).
% 0.99/1.17  thf(zf_stmt_2, axiom,
% 0.99/1.17    (![B:$i,A:$i]:
% 0.99/1.17     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.99/1.17       ( zip_tseitin_0 @ B @ A ) ))).
% 0.99/1.17  thf('34', plain,
% 0.99/1.17      (![X28 : $i, X29 : $i]:
% 0.99/1.17         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.99/1.17  thf('35', plain,
% 0.99/1.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.99/1.17  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.99/1.17  thf(zf_stmt_5, axiom,
% 0.99/1.17    (![A:$i,B:$i,C:$i]:
% 0.99/1.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.99/1.17       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.99/1.17         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.99/1.17           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.99/1.17             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.99/1.17  thf('36', plain,
% 0.99/1.17      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.99/1.17         (~ (zip_tseitin_0 @ X33 @ X34)
% 0.99/1.17          | (zip_tseitin_1 @ X35 @ X33 @ X34)
% 0.99/1.17          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.99/1.17  thf('37', plain,
% 0.99/1.17      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 0.99/1.17      inference('sup-', [status(thm)], ['35', '36'])).
% 0.99/1.17  thf('38', plain,
% 0.99/1.17      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 0.99/1.17      inference('sup-', [status(thm)], ['34', '37'])).
% 0.99/1.17  thf('39', plain, (((sk_A) != (k1_xboole_0))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('40', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 0.99/1.17      inference('simplify_reflect-', [status(thm)], ['38', '39'])).
% 0.99/1.17  thf('41', plain,
% 0.99/1.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf(redefinition_k1_relset_1, axiom,
% 0.99/1.17    (![A:$i,B:$i,C:$i]:
% 0.99/1.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.99/1.17       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.99/1.17  thf('42', plain,
% 0.99/1.17      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.99/1.17         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 0.99/1.17          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.99/1.17      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.99/1.17  thf('43', plain,
% 0.99/1.17      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.99/1.17      inference('sup-', [status(thm)], ['41', '42'])).
% 0.99/1.17  thf('44', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.99/1.17      inference('demod', [status(thm)], ['33', '40', '43'])).
% 0.99/1.17  thf('45', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('46', plain,
% 0.99/1.17      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.99/1.17         (~ (v1_funct_2 @ X32 @ X30 @ X31)
% 0.99/1.17          | ((X30) = (k1_relset_1 @ X30 @ X31 @ X32))
% 0.99/1.17          | ~ (zip_tseitin_1 @ X32 @ X31 @ X30))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.99/1.17  thf('47', plain,
% 0.99/1.17      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.99/1.17        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['45', '46'])).
% 0.99/1.17  thf('48', plain,
% 0.99/1.17      (![X28 : $i, X29 : $i]:
% 0.99/1.17         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.99/1.17  thf('49', plain,
% 0.99/1.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('50', plain,
% 0.99/1.17      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.99/1.17         (~ (zip_tseitin_0 @ X33 @ X34)
% 0.99/1.17          | (zip_tseitin_1 @ X35 @ X33 @ X34)
% 0.99/1.17          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.99/1.17  thf('51', plain,
% 0.99/1.17      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.99/1.17      inference('sup-', [status(thm)], ['49', '50'])).
% 0.99/1.17  thf('52', plain,
% 0.99/1.17      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.99/1.17      inference('sup-', [status(thm)], ['48', '51'])).
% 0.99/1.17  thf('53', plain, (((sk_B) != (k1_xboole_0))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('54', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.99/1.17      inference('simplify_reflect-', [status(thm)], ['52', '53'])).
% 0.99/1.17  thf('55', plain,
% 0.99/1.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('56', plain,
% 0.99/1.17      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.99/1.17         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 0.99/1.17          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.99/1.17      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.99/1.17  thf('57', plain,
% 0.99/1.17      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.99/1.17      inference('sup-', [status(thm)], ['55', '56'])).
% 0.99/1.17  thf('58', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.99/1.17      inference('demod', [status(thm)], ['47', '54', '57'])).
% 0.99/1.17  thf(t63_funct_1, axiom,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.99/1.17       ( ![B:$i]:
% 0.99/1.17         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.99/1.17           ( ( ( v2_funct_1 @ A ) & 
% 0.99/1.17               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.99/1.17               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.99/1.17             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.99/1.17  thf('59', plain,
% 0.99/1.17      (![X7 : $i, X8 : $i]:
% 0.99/1.17         (~ (v1_relat_1 @ X7)
% 0.99/1.17          | ~ (v1_funct_1 @ X7)
% 0.99/1.17          | ((X7) = (k2_funct_1 @ X8))
% 0.99/1.17          | ((k5_relat_1 @ X8 @ X7) != (k6_relat_1 @ (k1_relat_1 @ X8)))
% 0.99/1.17          | ((k2_relat_1 @ X8) != (k1_relat_1 @ X7))
% 0.99/1.17          | ~ (v2_funct_1 @ X8)
% 0.99/1.17          | ~ (v1_funct_1 @ X8)
% 0.99/1.17          | ~ (v1_relat_1 @ X8))),
% 0.99/1.17      inference('cnf', [status(esa)], [t63_funct_1])).
% 0.99/1.17  thf('60', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         (((k5_relat_1 @ sk_C @ X0) != (k6_relat_1 @ sk_A))
% 0.99/1.17          | ~ (v1_relat_1 @ sk_C)
% 0.99/1.17          | ~ (v1_funct_1 @ sk_C)
% 0.99/1.17          | ~ (v2_funct_1 @ sk_C)
% 0.99/1.17          | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ X0))
% 0.99/1.17          | ((X0) = (k2_funct_1 @ sk_C))
% 0.99/1.17          | ~ (v1_funct_1 @ X0)
% 0.99/1.17          | ~ (v1_relat_1 @ X0))),
% 0.99/1.17      inference('sup-', [status(thm)], ['58', '59'])).
% 0.99/1.17  thf('61', plain,
% 0.99/1.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf(cc2_relat_1, axiom,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ( v1_relat_1 @ A ) =>
% 0.99/1.17       ( ![B:$i]:
% 0.99/1.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.99/1.17  thf('62', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.99/1.17          | (v1_relat_1 @ X0)
% 0.99/1.17          | ~ (v1_relat_1 @ X1))),
% 0.99/1.17      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.99/1.17  thf('63', plain,
% 0.99/1.17      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.99/1.17      inference('sup-', [status(thm)], ['61', '62'])).
% 0.99/1.17  thf(fc6_relat_1, axiom,
% 0.99/1.17    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.99/1.17  thf('64', plain,
% 0.99/1.17      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.99/1.17      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.99/1.17  thf('65', plain, ((v1_relat_1 @ sk_C)),
% 0.99/1.17      inference('demod', [status(thm)], ['63', '64'])).
% 0.99/1.17  thf('66', plain, ((v1_funct_1 @ sk_C)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('67', plain, ((v2_funct_1 @ sk_C)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('68', plain,
% 0.99/1.17      (![X0 : $i]:
% 0.99/1.17         (((k5_relat_1 @ sk_C @ X0) != (k6_relat_1 @ sk_A))
% 0.99/1.17          | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ X0))
% 0.99/1.17          | ((X0) = (k2_funct_1 @ sk_C))
% 0.99/1.17          | ~ (v1_funct_1 @ X0)
% 0.99/1.17          | ~ (v1_relat_1 @ X0))),
% 0.99/1.17      inference('demod', [status(thm)], ['60', '65', '66', '67'])).
% 0.99/1.17  thf('69', plain,
% 0.99/1.17      ((((k2_relat_1 @ sk_C) != (sk_B))
% 0.99/1.17        | ~ (v1_relat_1 @ sk_D)
% 0.99/1.17        | ~ (v1_funct_1 @ sk_D)
% 0.99/1.17        | ((sk_D) = (k2_funct_1 @ sk_C))
% 0.99/1.17        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_relat_1 @ sk_A)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['44', '68'])).
% 0.99/1.17  thf('70', plain,
% 0.99/1.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('71', plain,
% 0.99/1.17      (![X0 : $i, X1 : $i]:
% 0.99/1.17         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.99/1.17          | (v1_relat_1 @ X0)
% 0.99/1.17          | ~ (v1_relat_1 @ X1))),
% 0.99/1.17      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.99/1.17  thf('72', plain,
% 0.99/1.17      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.99/1.17      inference('sup-', [status(thm)], ['70', '71'])).
% 0.99/1.17  thf('73', plain,
% 0.99/1.17      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.99/1.17      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.99/1.17  thf('74', plain, ((v1_relat_1 @ sk_D)),
% 0.99/1.17      inference('demod', [status(thm)], ['72', '73'])).
% 0.99/1.17  thf('75', plain, ((v1_funct_1 @ sk_D)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('76', plain,
% 0.99/1.17      ((((k2_relat_1 @ sk_C) != (sk_B))
% 0.99/1.17        | ((sk_D) = (k2_funct_1 @ sk_C))
% 0.99/1.17        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_relat_1 @ sk_A)))),
% 0.99/1.17      inference('demod', [status(thm)], ['69', '74', '75'])).
% 0.99/1.17  thf('77', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('78', plain,
% 0.99/1.17      ((((k2_relat_1 @ sk_C) != (sk_B))
% 0.99/1.17        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_relat_1 @ sk_A)))),
% 0.99/1.17      inference('simplify_reflect-', [status(thm)], ['76', '77'])).
% 0.99/1.17  thf(t61_funct_1, axiom,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.99/1.17       ( ( v2_funct_1 @ A ) =>
% 0.99/1.17         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.99/1.17             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.99/1.17           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.99/1.17             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.99/1.17  thf('79', plain,
% 0.99/1.17      (![X6 : $i]:
% 0.99/1.17         (~ (v2_funct_1 @ X6)
% 0.99/1.17          | ((k5_relat_1 @ (k2_funct_1 @ X6) @ X6)
% 0.99/1.17              = (k6_relat_1 @ (k2_relat_1 @ X6)))
% 0.99/1.17          | ~ (v1_funct_1 @ X6)
% 0.99/1.17          | ~ (v1_relat_1 @ X6))),
% 0.99/1.17      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.99/1.17  thf('80', plain,
% 0.99/1.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf(t35_funct_2, axiom,
% 0.99/1.17    (![A:$i,B:$i,C:$i]:
% 0.99/1.17     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.99/1.17         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.99/1.17       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.99/1.17         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.99/1.17           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.99/1.17             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.99/1.17  thf('81', plain,
% 0.99/1.17      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.99/1.17         (((X45) = (k1_xboole_0))
% 0.99/1.17          | ~ (v1_funct_1 @ X46)
% 0.99/1.17          | ~ (v1_funct_2 @ X46 @ X47 @ X45)
% 0.99/1.17          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X45)))
% 0.99/1.17          | ((k5_relat_1 @ (k2_funct_1 @ X46) @ X46) = (k6_partfun1 @ X45))
% 0.99/1.17          | ~ (v2_funct_1 @ X46)
% 0.99/1.17          | ((k2_relset_1 @ X47 @ X45 @ X46) != (X45)))),
% 0.99/1.17      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.99/1.17  thf('82', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 0.99/1.17      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.99/1.17  thf('83', plain,
% 0.99/1.17      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.99/1.17         (((X45) = (k1_xboole_0))
% 0.99/1.17          | ~ (v1_funct_1 @ X46)
% 0.99/1.17          | ~ (v1_funct_2 @ X46 @ X47 @ X45)
% 0.99/1.17          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X45)))
% 0.99/1.17          | ((k5_relat_1 @ (k2_funct_1 @ X46) @ X46) = (k6_relat_1 @ X45))
% 0.99/1.17          | ~ (v2_funct_1 @ X46)
% 0.99/1.17          | ((k2_relset_1 @ X47 @ X45 @ X46) != (X45)))),
% 0.99/1.17      inference('demod', [status(thm)], ['81', '82'])).
% 0.99/1.17  thf('84', plain,
% 0.99/1.17      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.99/1.17        | ~ (v2_funct_1 @ sk_C)
% 0.99/1.17        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 0.99/1.17        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.99/1.17        | ~ (v1_funct_1 @ sk_C)
% 0.99/1.17        | ((sk_B) = (k1_xboole_0)))),
% 0.99/1.17      inference('sup-', [status(thm)], ['80', '83'])).
% 0.99/1.17  thf('85', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('86', plain, ((v2_funct_1 @ sk_C)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('87', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('88', plain, ((v1_funct_1 @ sk_C)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('89', plain,
% 0.99/1.17      ((((sk_B) != (sk_B))
% 0.99/1.17        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 0.99/1.17        | ((sk_B) = (k1_xboole_0)))),
% 0.99/1.17      inference('demod', [status(thm)], ['84', '85', '86', '87', '88'])).
% 0.99/1.17  thf('90', plain,
% 0.99/1.17      ((((sk_B) = (k1_xboole_0))
% 0.99/1.17        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B)))),
% 0.99/1.17      inference('simplify', [status(thm)], ['89'])).
% 0.99/1.17  thf('91', plain, (((sk_B) != (k1_xboole_0))),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('92', plain,
% 0.99/1.17      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))),
% 0.99/1.17      inference('simplify_reflect-', [status(thm)], ['90', '91'])).
% 0.99/1.17  thf('93', plain,
% 0.99/1.17      ((((k6_relat_1 @ (k2_relat_1 @ sk_C)) = (k6_relat_1 @ sk_B))
% 0.99/1.17        | ~ (v1_relat_1 @ sk_C)
% 0.99/1.17        | ~ (v1_funct_1 @ sk_C)
% 0.99/1.17        | ~ (v2_funct_1 @ sk_C))),
% 0.99/1.17      inference('sup+', [status(thm)], ['79', '92'])).
% 0.99/1.17  thf('94', plain, ((v1_relat_1 @ sk_C)),
% 0.99/1.17      inference('demod', [status(thm)], ['63', '64'])).
% 0.99/1.17  thf('95', plain, ((v1_funct_1 @ sk_C)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('96', plain, ((v2_funct_1 @ sk_C)),
% 0.99/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.17  thf('97', plain,
% 0.99/1.17      (((k6_relat_1 @ (k2_relat_1 @ sk_C)) = (k6_relat_1 @ sk_B))),
% 0.99/1.17      inference('demod', [status(thm)], ['93', '94', '95', '96'])).
% 0.99/1.17  thf(t71_relat_1, axiom,
% 0.99/1.17    (![A:$i]:
% 0.99/1.17     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.99/1.17       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.99/1.17  thf('98', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 0.99/1.17      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.99/1.17  thf('99', plain,
% 0.99/1.17      (((k1_relat_1 @ (k6_relat_1 @ sk_B)) = (k2_relat_1 @ sk_C))),
% 0.99/1.17      inference('sup+', [status(thm)], ['97', '98'])).
% 0.99/1.17  thf('100', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 0.99/1.17      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.99/1.17  thf('101', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 0.99/1.17      inference('demod', [status(thm)], ['99', '100'])).
% 0.99/1.17  thf('102', plain,
% 0.99/1.17      ((((sk_B) != (sk_B))
% 0.99/1.17        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_relat_1 @ sk_A)))),
% 0.99/1.17      inference('demod', [status(thm)], ['78', '101'])).
% 0.99/1.17  thf('103', plain, (((k5_relat_1 @ sk_C @ sk_D) != (k6_relat_1 @ sk_A))),
% 0.99/1.17      inference('simplify', [status(thm)], ['102'])).
% 0.99/1.17  thf('104', plain, ($false),
% 0.99/1.17      inference('simplify_reflect-', [status(thm)], ['30', '103'])).
% 0.99/1.17  
% 0.99/1.17  % SZS output end Refutation
% 0.99/1.17  
% 0.99/1.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

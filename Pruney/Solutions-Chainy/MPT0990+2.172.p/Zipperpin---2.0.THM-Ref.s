%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7mVPXgV2to

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:24 EST 2020

% Result     : Theorem 0.99s
% Output     : Refutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 274 expanded)
%              Number of leaves         :   45 ( 101 expanded)
%              Depth                    :   15
%              Number of atoms          : 1465 (6218 expanded)
%              Number of equality atoms :  102 ( 451 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

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
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
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
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( ( k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39 )
        = ( k5_relat_1 @ X36 @ X39 ) ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X8 @ X9 @ X11 @ X12 @ X7 @ X10 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X12 ) ) ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( ( k4_relset_1 @ X17 @ X18 @ X20 @ X21 @ X16 @ X19 )
        = ( k5_relat_1 @ X16 @ X19 ) ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( X22 = X25 )
      | ~ ( r2_relset_1 @ X23 @ X24 @ X22 @ X25 ) ) ),
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
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('28',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('29',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
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
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('47',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ( X5
        = ( k2_funct_1 @ X6 ) )
      | ( ( k5_relat_1 @ X6 @ X5 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X6 ) ) )
      | ( ( k2_relat_1 @ X6 )
       != ( k1_relat_1 @ X5 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
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

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('79',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('80',plain,(
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

thf('81',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v2_funct_1 @ X43 )
      | ( ( k2_relset_1 @ X45 @ X44 @ X43 )
       != X44 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X45 @ X44 )
      | ~ ( v1_funct_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('82',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['82','83','84','85','86'])).

thf('88',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('90',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v2_funct_1 @ X43 )
      | ( ( k2_relset_1 @ X45 @ X44 @ X43 )
       != X44 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X43 ) @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X45 @ X44 )
      | ~ ( v1_funct_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('93',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['93','94','95','96','97'])).

thf('99',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('101',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('103',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('104',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('105',plain,
    ( ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('107',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['106','107'])).

thf('109',plain,
    ( sk_B
    = ( k1_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['101','108'])).

thf('110',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['90','109'])).

thf('111',plain,
    ( ( sk_B
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['79','110'])).

thf('112',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['63','64'])).

thf('113',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['111','112','113','114'])).

thf('116',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
     != ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','115'])).

thf('117',plain,(
    ( k5_relat_1 @ sk_C @ sk_D )
 != ( k6_relat_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['30','117'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7mVPXgV2to
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:48:11 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  % Running portfolio for 600 s
% 0.20/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.36  % Python version: Python 3.6.8
% 0.20/0.36  % Running in FO mode
% 0.99/1.19  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.99/1.19  % Solved by: fo/fo7.sh
% 0.99/1.19  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.99/1.19  % done 363 iterations in 0.723s
% 0.99/1.19  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.99/1.19  % SZS output start Refutation
% 0.99/1.19  thf(sk_C_type, type, sk_C: $i).
% 0.99/1.19  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.99/1.19  thf(sk_A_type, type, sk_A: $i).
% 0.99/1.19  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.99/1.19  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.99/1.19  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.99/1.19  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.99/1.19  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.99/1.19  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.99/1.19  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.99/1.19  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.99/1.19  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.99/1.19  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.99/1.19  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.99/1.19  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.99/1.19  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.99/1.19  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 0.99/1.19  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.99/1.19  thf(sk_B_type, type, sk_B: $i).
% 0.99/1.19  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.99/1.19  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.99/1.19  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.99/1.19  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.99/1.19  thf(sk_D_type, type, sk_D: $i).
% 0.99/1.19  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.99/1.19  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.99/1.19  thf(t36_funct_2, conjecture,
% 0.99/1.19    (![A:$i,B:$i,C:$i]:
% 0.99/1.19     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.99/1.19         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.99/1.19       ( ![D:$i]:
% 0.99/1.19         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.99/1.19             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.99/1.19           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.99/1.19               ( r2_relset_1 @
% 0.99/1.19                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.99/1.19                 ( k6_partfun1 @ A ) ) & 
% 0.99/1.19               ( v2_funct_1 @ C ) ) =>
% 0.99/1.19             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.99/1.19               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.99/1.19  thf(zf_stmt_0, negated_conjecture,
% 0.99/1.19    (~( ![A:$i,B:$i,C:$i]:
% 0.99/1.19        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.99/1.19            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.99/1.19          ( ![D:$i]:
% 0.99/1.19            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.99/1.19                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.99/1.19              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.99/1.19                  ( r2_relset_1 @
% 0.99/1.19                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.99/1.19                    ( k6_partfun1 @ A ) ) & 
% 0.99/1.19                  ( v2_funct_1 @ C ) ) =>
% 0.99/1.19                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.99/1.19                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.99/1.19    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.99/1.19  thf('0', plain,
% 0.99/1.19      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.99/1.19        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.99/1.19        (k6_partfun1 @ sk_A))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf(redefinition_k6_partfun1, axiom,
% 0.99/1.19    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.99/1.19  thf('1', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 0.99/1.19      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.99/1.19  thf('2', plain,
% 0.99/1.19      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.99/1.19        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.99/1.19        (k6_relat_1 @ sk_A))),
% 0.99/1.19      inference('demod', [status(thm)], ['0', '1'])).
% 0.99/1.19  thf('3', plain,
% 0.99/1.19      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('4', plain,
% 0.99/1.19      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf(redefinition_k1_partfun1, axiom,
% 0.99/1.19    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.99/1.19     ( ( ( v1_funct_1 @ E ) & 
% 0.99/1.19         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.99/1.19         ( v1_funct_1 @ F ) & 
% 0.99/1.19         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.99/1.19       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.99/1.19  thf('5', plain,
% 0.99/1.19      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.99/1.19         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.99/1.19          | ~ (v1_funct_1 @ X36)
% 0.99/1.19          | ~ (v1_funct_1 @ X39)
% 0.99/1.19          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.99/1.19          | ((k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39)
% 0.99/1.19              = (k5_relat_1 @ X36 @ X39)))),
% 0.99/1.19      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.99/1.19  thf('6', plain,
% 0.99/1.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.19         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.99/1.19            = (k5_relat_1 @ sk_C @ X0))
% 0.99/1.19          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.99/1.19          | ~ (v1_funct_1 @ X0)
% 0.99/1.19          | ~ (v1_funct_1 @ sk_C))),
% 0.99/1.19      inference('sup-', [status(thm)], ['4', '5'])).
% 0.99/1.19  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('8', plain,
% 0.99/1.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.19         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.99/1.19            = (k5_relat_1 @ sk_C @ X0))
% 0.99/1.19          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.99/1.19          | ~ (v1_funct_1 @ X0))),
% 0.99/1.19      inference('demod', [status(thm)], ['6', '7'])).
% 0.99/1.19  thf('9', plain,
% 0.99/1.19      ((~ (v1_funct_1 @ sk_D)
% 0.99/1.19        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.99/1.19            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.99/1.19      inference('sup-', [status(thm)], ['3', '8'])).
% 0.99/1.19  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('11', plain,
% 0.99/1.19      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.99/1.19         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.99/1.19      inference('demod', [status(thm)], ['9', '10'])).
% 0.99/1.19  thf('12', plain,
% 0.99/1.19      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.99/1.19        (k6_relat_1 @ sk_A))),
% 0.99/1.19      inference('demod', [status(thm)], ['2', '11'])).
% 0.99/1.19  thf('13', plain,
% 0.99/1.19      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('14', plain,
% 0.99/1.19      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf(dt_k4_relset_1, axiom,
% 0.99/1.19    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.99/1.19     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.99/1.19         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.99/1.19       ( m1_subset_1 @
% 0.99/1.19         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.99/1.19         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 0.99/1.19  thf('15', plain,
% 0.99/1.19      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.99/1.19         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.99/1.19          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.99/1.19          | (m1_subset_1 @ (k4_relset_1 @ X8 @ X9 @ X11 @ X12 @ X7 @ X10) @ 
% 0.99/1.19             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X12))))),
% 0.99/1.19      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 0.99/1.19  thf('16', plain,
% 0.99/1.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.19         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.99/1.19           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.99/1.19          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 0.99/1.19      inference('sup-', [status(thm)], ['14', '15'])).
% 0.99/1.19  thf('17', plain,
% 0.99/1.19      ((m1_subset_1 @ 
% 0.99/1.19        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.99/1.19        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.99/1.19      inference('sup-', [status(thm)], ['13', '16'])).
% 0.99/1.19  thf('18', plain,
% 0.99/1.19      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('19', plain,
% 0.99/1.19      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf(redefinition_k4_relset_1, axiom,
% 0.99/1.19    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.99/1.19     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.99/1.19         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.99/1.19       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.99/1.19  thf('20', plain,
% 0.99/1.19      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.99/1.19         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.99/1.19          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.99/1.19          | ((k4_relset_1 @ X17 @ X18 @ X20 @ X21 @ X16 @ X19)
% 0.99/1.19              = (k5_relat_1 @ X16 @ X19)))),
% 0.99/1.19      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 0.99/1.19  thf('21', plain,
% 0.99/1.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.19         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.99/1.19            = (k5_relat_1 @ sk_C @ X0))
% 0.99/1.19          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.99/1.19      inference('sup-', [status(thm)], ['19', '20'])).
% 0.99/1.19  thf('22', plain,
% 0.99/1.19      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.99/1.19         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.99/1.19      inference('sup-', [status(thm)], ['18', '21'])).
% 0.99/1.19  thf('23', plain,
% 0.99/1.19      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.99/1.19        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.99/1.19      inference('demod', [status(thm)], ['17', '22'])).
% 0.99/1.19  thf(redefinition_r2_relset_1, axiom,
% 0.99/1.19    (![A:$i,B:$i,C:$i,D:$i]:
% 0.99/1.19     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.99/1.19         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.99/1.19       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.99/1.19  thf('24', plain,
% 0.99/1.19      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.99/1.19         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.99/1.19          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.99/1.19          | ((X22) = (X25))
% 0.99/1.19          | ~ (r2_relset_1 @ X23 @ X24 @ X22 @ X25))),
% 0.99/1.19      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.99/1.19  thf('25', plain,
% 0.99/1.19      (![X0 : $i]:
% 0.99/1.19         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 0.99/1.19          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 0.99/1.19          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.99/1.19      inference('sup-', [status(thm)], ['23', '24'])).
% 0.99/1.19  thf('26', plain,
% 0.99/1.19      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 0.99/1.19           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.99/1.19        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A)))),
% 0.99/1.19      inference('sup-', [status(thm)], ['12', '25'])).
% 0.99/1.19  thf(dt_k6_partfun1, axiom,
% 0.99/1.19    (![A:$i]:
% 0.99/1.19     ( ( m1_subset_1 @
% 0.99/1.19         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.99/1.19       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.99/1.19  thf('27', plain,
% 0.99/1.19      (![X35 : $i]:
% 0.99/1.19         (m1_subset_1 @ (k6_partfun1 @ X35) @ 
% 0.99/1.19          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 0.99/1.19      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.99/1.19  thf('28', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 0.99/1.19      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.99/1.19  thf('29', plain,
% 0.99/1.19      (![X35 : $i]:
% 0.99/1.19         (m1_subset_1 @ (k6_relat_1 @ X35) @ 
% 0.99/1.19          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 0.99/1.19      inference('demod', [status(thm)], ['27', '28'])).
% 0.99/1.19  thf('30', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 0.99/1.19      inference('demod', [status(thm)], ['26', '29'])).
% 0.99/1.19  thf('31', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf(d1_funct_2, axiom,
% 0.99/1.19    (![A:$i,B:$i,C:$i]:
% 0.99/1.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.99/1.19       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.99/1.19           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.99/1.19             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.99/1.19         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.99/1.19           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.99/1.19             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.99/1.19  thf(zf_stmt_1, axiom,
% 0.99/1.19    (![C:$i,B:$i,A:$i]:
% 0.99/1.19     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.99/1.19       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.99/1.19  thf('32', plain,
% 0.99/1.19      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.99/1.19         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 0.99/1.19          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 0.99/1.19          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.99/1.19  thf('33', plain,
% 0.99/1.19      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 0.99/1.19        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 0.99/1.19      inference('sup-', [status(thm)], ['31', '32'])).
% 0.99/1.19  thf(zf_stmt_2, axiom,
% 0.99/1.19    (![B:$i,A:$i]:
% 0.99/1.19     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.99/1.19       ( zip_tseitin_0 @ B @ A ) ))).
% 0.99/1.19  thf('34', plain,
% 0.99/1.19      (![X26 : $i, X27 : $i]:
% 0.99/1.19         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.99/1.19  thf('35', plain,
% 0.99/1.19      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.99/1.19  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.99/1.19  thf(zf_stmt_5, axiom,
% 0.99/1.19    (![A:$i,B:$i,C:$i]:
% 0.99/1.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.99/1.19       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.99/1.19         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.99/1.19           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.99/1.19             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.99/1.19  thf('36', plain,
% 0.99/1.19      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.99/1.19         (~ (zip_tseitin_0 @ X31 @ X32)
% 0.99/1.19          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 0.99/1.19          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.99/1.19  thf('37', plain,
% 0.99/1.19      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 0.99/1.19      inference('sup-', [status(thm)], ['35', '36'])).
% 0.99/1.19  thf('38', plain,
% 0.99/1.19      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 0.99/1.19      inference('sup-', [status(thm)], ['34', '37'])).
% 0.99/1.19  thf('39', plain, (((sk_A) != (k1_xboole_0))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('40', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 0.99/1.19      inference('simplify_reflect-', [status(thm)], ['38', '39'])).
% 0.99/1.19  thf('41', plain,
% 0.99/1.19      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf(redefinition_k1_relset_1, axiom,
% 0.99/1.19    (![A:$i,B:$i,C:$i]:
% 0.99/1.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.99/1.19       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.99/1.19  thf('42', plain,
% 0.99/1.19      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.99/1.19         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 0.99/1.19          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.99/1.19      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.99/1.19  thf('43', plain,
% 0.99/1.19      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.99/1.19      inference('sup-', [status(thm)], ['41', '42'])).
% 0.99/1.19  thf('44', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.99/1.19      inference('demod', [status(thm)], ['33', '40', '43'])).
% 0.99/1.19  thf('45', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('46', plain,
% 0.99/1.19      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.99/1.19         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 0.99/1.19          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 0.99/1.19          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.99/1.19  thf('47', plain,
% 0.99/1.19      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.99/1.19        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.99/1.19      inference('sup-', [status(thm)], ['45', '46'])).
% 0.99/1.19  thf('48', plain,
% 0.99/1.19      (![X26 : $i, X27 : $i]:
% 0.99/1.19         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.99/1.19  thf('49', plain,
% 0.99/1.19      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('50', plain,
% 0.99/1.19      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.99/1.19         (~ (zip_tseitin_0 @ X31 @ X32)
% 0.99/1.19          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 0.99/1.19          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.99/1.19  thf('51', plain,
% 0.99/1.19      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.99/1.19      inference('sup-', [status(thm)], ['49', '50'])).
% 0.99/1.19  thf('52', plain,
% 0.99/1.19      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.99/1.19      inference('sup-', [status(thm)], ['48', '51'])).
% 0.99/1.19  thf('53', plain, (((sk_B) != (k1_xboole_0))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('54', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.99/1.19      inference('simplify_reflect-', [status(thm)], ['52', '53'])).
% 0.99/1.19  thf('55', plain,
% 0.99/1.19      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('56', plain,
% 0.99/1.19      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.99/1.19         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 0.99/1.19          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.99/1.19      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.99/1.19  thf('57', plain,
% 0.99/1.19      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.99/1.19      inference('sup-', [status(thm)], ['55', '56'])).
% 0.99/1.19  thf('58', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.99/1.19      inference('demod', [status(thm)], ['47', '54', '57'])).
% 0.99/1.19  thf(t63_funct_1, axiom,
% 0.99/1.19    (![A:$i]:
% 0.99/1.19     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.99/1.19       ( ![B:$i]:
% 0.99/1.19         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.99/1.19           ( ( ( v2_funct_1 @ A ) & 
% 0.99/1.19               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.99/1.19               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.99/1.19             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.99/1.19  thf('59', plain,
% 0.99/1.19      (![X5 : $i, X6 : $i]:
% 0.99/1.19         (~ (v1_relat_1 @ X5)
% 0.99/1.19          | ~ (v1_funct_1 @ X5)
% 0.99/1.19          | ((X5) = (k2_funct_1 @ X6))
% 0.99/1.19          | ((k5_relat_1 @ X6 @ X5) != (k6_relat_1 @ (k1_relat_1 @ X6)))
% 0.99/1.19          | ((k2_relat_1 @ X6) != (k1_relat_1 @ X5))
% 0.99/1.19          | ~ (v2_funct_1 @ X6)
% 0.99/1.19          | ~ (v1_funct_1 @ X6)
% 0.99/1.19          | ~ (v1_relat_1 @ X6))),
% 0.99/1.19      inference('cnf', [status(esa)], [t63_funct_1])).
% 0.99/1.19  thf('60', plain,
% 0.99/1.19      (![X0 : $i]:
% 0.99/1.19         (((k5_relat_1 @ sk_C @ X0) != (k6_relat_1 @ sk_A))
% 0.99/1.19          | ~ (v1_relat_1 @ sk_C)
% 0.99/1.19          | ~ (v1_funct_1 @ sk_C)
% 0.99/1.19          | ~ (v2_funct_1 @ sk_C)
% 0.99/1.19          | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ X0))
% 0.99/1.19          | ((X0) = (k2_funct_1 @ sk_C))
% 0.99/1.19          | ~ (v1_funct_1 @ X0)
% 0.99/1.19          | ~ (v1_relat_1 @ X0))),
% 0.99/1.19      inference('sup-', [status(thm)], ['58', '59'])).
% 0.99/1.19  thf('61', plain,
% 0.99/1.19      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf(cc2_relat_1, axiom,
% 0.99/1.19    (![A:$i]:
% 0.99/1.19     ( ( v1_relat_1 @ A ) =>
% 0.99/1.19       ( ![B:$i]:
% 0.99/1.19         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.99/1.19  thf('62', plain,
% 0.99/1.19      (![X0 : $i, X1 : $i]:
% 0.99/1.19         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.99/1.19          | (v1_relat_1 @ X0)
% 0.99/1.19          | ~ (v1_relat_1 @ X1))),
% 0.99/1.19      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.99/1.19  thf('63', plain,
% 0.99/1.19      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.99/1.19      inference('sup-', [status(thm)], ['61', '62'])).
% 0.99/1.19  thf(fc6_relat_1, axiom,
% 0.99/1.19    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.99/1.19  thf('64', plain,
% 0.99/1.19      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.99/1.19      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.99/1.19  thf('65', plain, ((v1_relat_1 @ sk_C)),
% 0.99/1.19      inference('demod', [status(thm)], ['63', '64'])).
% 0.99/1.19  thf('66', plain, ((v1_funct_1 @ sk_C)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('67', plain, ((v2_funct_1 @ sk_C)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('68', plain,
% 0.99/1.19      (![X0 : $i]:
% 0.99/1.19         (((k5_relat_1 @ sk_C @ X0) != (k6_relat_1 @ sk_A))
% 0.99/1.19          | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ X0))
% 0.99/1.19          | ((X0) = (k2_funct_1 @ sk_C))
% 0.99/1.19          | ~ (v1_funct_1 @ X0)
% 0.99/1.19          | ~ (v1_relat_1 @ X0))),
% 0.99/1.19      inference('demod', [status(thm)], ['60', '65', '66', '67'])).
% 0.99/1.19  thf('69', plain,
% 0.99/1.19      ((((k2_relat_1 @ sk_C) != (sk_B))
% 0.99/1.19        | ~ (v1_relat_1 @ sk_D)
% 0.99/1.19        | ~ (v1_funct_1 @ sk_D)
% 0.99/1.19        | ((sk_D) = (k2_funct_1 @ sk_C))
% 0.99/1.19        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_relat_1 @ sk_A)))),
% 0.99/1.19      inference('sup-', [status(thm)], ['44', '68'])).
% 0.99/1.19  thf('70', plain,
% 0.99/1.19      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('71', plain,
% 0.99/1.19      (![X0 : $i, X1 : $i]:
% 0.99/1.19         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.99/1.19          | (v1_relat_1 @ X0)
% 0.99/1.19          | ~ (v1_relat_1 @ X1))),
% 0.99/1.19      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.99/1.19  thf('72', plain,
% 0.99/1.19      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.99/1.19      inference('sup-', [status(thm)], ['70', '71'])).
% 0.99/1.19  thf('73', plain,
% 0.99/1.19      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.99/1.19      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.99/1.19  thf('74', plain, ((v1_relat_1 @ sk_D)),
% 0.99/1.19      inference('demod', [status(thm)], ['72', '73'])).
% 0.99/1.19  thf('75', plain, ((v1_funct_1 @ sk_D)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('76', plain,
% 0.99/1.19      ((((k2_relat_1 @ sk_C) != (sk_B))
% 0.99/1.19        | ((sk_D) = (k2_funct_1 @ sk_C))
% 0.99/1.19        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_relat_1 @ sk_A)))),
% 0.99/1.19      inference('demod', [status(thm)], ['69', '74', '75'])).
% 0.99/1.19  thf('77', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('78', plain,
% 0.99/1.19      ((((k2_relat_1 @ sk_C) != (sk_B))
% 0.99/1.19        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_relat_1 @ sk_A)))),
% 0.99/1.19      inference('simplify_reflect-', [status(thm)], ['76', '77'])).
% 0.99/1.19  thf(t55_funct_1, axiom,
% 0.99/1.19    (![A:$i]:
% 0.99/1.19     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.99/1.19       ( ( v2_funct_1 @ A ) =>
% 0.99/1.19         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.99/1.19           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.99/1.19  thf('79', plain,
% 0.99/1.19      (![X4 : $i]:
% 0.99/1.19         (~ (v2_funct_1 @ X4)
% 0.99/1.19          | ((k2_relat_1 @ X4) = (k1_relat_1 @ (k2_funct_1 @ X4)))
% 0.99/1.19          | ~ (v1_funct_1 @ X4)
% 0.99/1.19          | ~ (v1_relat_1 @ X4))),
% 0.99/1.19      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.99/1.19  thf('80', plain,
% 0.99/1.19      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf(t31_funct_2, axiom,
% 0.99/1.19    (![A:$i,B:$i,C:$i]:
% 0.99/1.19     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.99/1.19         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.99/1.19       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.99/1.19         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.99/1.19           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.99/1.19           ( m1_subset_1 @
% 0.99/1.19             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.99/1.19  thf('81', plain,
% 0.99/1.19      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.99/1.19         (~ (v2_funct_1 @ X43)
% 0.99/1.19          | ((k2_relset_1 @ X45 @ X44 @ X43) != (X44))
% 0.99/1.19          | (m1_subset_1 @ (k2_funct_1 @ X43) @ 
% 0.99/1.19             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 0.99/1.19          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 0.99/1.19          | ~ (v1_funct_2 @ X43 @ X45 @ X44)
% 0.99/1.19          | ~ (v1_funct_1 @ X43))),
% 0.99/1.19      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.99/1.19  thf('82', plain,
% 0.99/1.19      ((~ (v1_funct_1 @ sk_C)
% 0.99/1.19        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.99/1.19        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.99/1.19           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.99/1.19        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.99/1.19        | ~ (v2_funct_1 @ sk_C))),
% 0.99/1.19      inference('sup-', [status(thm)], ['80', '81'])).
% 0.99/1.19  thf('83', plain, ((v1_funct_1 @ sk_C)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('84', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('85', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('86', plain, ((v2_funct_1 @ sk_C)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('87', plain,
% 0.99/1.19      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.99/1.19         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.99/1.19        | ((sk_B) != (sk_B)))),
% 0.99/1.19      inference('demod', [status(thm)], ['82', '83', '84', '85', '86'])).
% 0.99/1.19  thf('88', plain,
% 0.99/1.19      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.99/1.19        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.99/1.19      inference('simplify', [status(thm)], ['87'])).
% 0.99/1.19  thf('89', plain,
% 0.99/1.19      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.99/1.19         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 0.99/1.19          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.99/1.19      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.99/1.19  thf('90', plain,
% 0.99/1.19      (((k1_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C))
% 0.99/1.19         = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.99/1.19      inference('sup-', [status(thm)], ['88', '89'])).
% 0.99/1.19  thf('91', plain,
% 0.99/1.19      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('92', plain,
% 0.99/1.19      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.99/1.19         (~ (v2_funct_1 @ X43)
% 0.99/1.19          | ((k2_relset_1 @ X45 @ X44 @ X43) != (X44))
% 0.99/1.19          | (v1_funct_2 @ (k2_funct_1 @ X43) @ X44 @ X45)
% 0.99/1.19          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 0.99/1.19          | ~ (v1_funct_2 @ X43 @ X45 @ X44)
% 0.99/1.19          | ~ (v1_funct_1 @ X43))),
% 0.99/1.19      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.99/1.19  thf('93', plain,
% 0.99/1.19      ((~ (v1_funct_1 @ sk_C)
% 0.99/1.19        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.99/1.19        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.99/1.19        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.99/1.19        | ~ (v2_funct_1 @ sk_C))),
% 0.99/1.19      inference('sup-', [status(thm)], ['91', '92'])).
% 0.99/1.19  thf('94', plain, ((v1_funct_1 @ sk_C)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('95', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('96', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('97', plain, ((v2_funct_1 @ sk_C)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('98', plain,
% 0.99/1.19      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A) | ((sk_B) != (sk_B)))),
% 0.99/1.19      inference('demod', [status(thm)], ['93', '94', '95', '96', '97'])).
% 0.99/1.19  thf('99', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 0.99/1.19      inference('simplify', [status(thm)], ['98'])).
% 0.99/1.19  thf('100', plain,
% 0.99/1.19      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.99/1.19         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 0.99/1.19          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 0.99/1.19          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.99/1.19  thf('101', plain,
% 0.99/1.19      ((~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_B)
% 0.99/1.19        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C))))),
% 0.99/1.19      inference('sup-', [status(thm)], ['99', '100'])).
% 0.99/1.19  thf('102', plain,
% 0.99/1.19      (![X26 : $i, X27 : $i]:
% 0.99/1.19         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.99/1.19  thf('103', plain,
% 0.99/1.19      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.99/1.19        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.99/1.19      inference('simplify', [status(thm)], ['87'])).
% 0.99/1.19  thf('104', plain,
% 0.99/1.19      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.99/1.19         (~ (zip_tseitin_0 @ X31 @ X32)
% 0.99/1.19          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 0.99/1.19          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.99/1.19  thf('105', plain,
% 0.99/1.19      (((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_B)
% 0.99/1.19        | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 0.99/1.19      inference('sup-', [status(thm)], ['103', '104'])).
% 0.99/1.19  thf('106', plain,
% 0.99/1.19      ((((sk_A) = (k1_xboole_0))
% 0.99/1.19        | (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_B))),
% 0.99/1.19      inference('sup-', [status(thm)], ['102', '105'])).
% 0.99/1.19  thf('107', plain, (((sk_A) != (k1_xboole_0))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('108', plain, ((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_B)),
% 0.99/1.19      inference('simplify_reflect-', [status(thm)], ['106', '107'])).
% 0.99/1.19  thf('109', plain,
% 0.99/1.19      (((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C)))),
% 0.99/1.19      inference('demod', [status(thm)], ['101', '108'])).
% 0.99/1.19  thf('110', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.99/1.19      inference('sup+', [status(thm)], ['90', '109'])).
% 0.99/1.19  thf('111', plain,
% 0.99/1.19      ((((sk_B) = (k2_relat_1 @ sk_C))
% 0.99/1.19        | ~ (v1_relat_1 @ sk_C)
% 0.99/1.19        | ~ (v1_funct_1 @ sk_C)
% 0.99/1.19        | ~ (v2_funct_1 @ sk_C))),
% 0.99/1.19      inference('sup+', [status(thm)], ['79', '110'])).
% 0.99/1.19  thf('112', plain, ((v1_relat_1 @ sk_C)),
% 0.99/1.19      inference('demod', [status(thm)], ['63', '64'])).
% 0.99/1.19  thf('113', plain, ((v1_funct_1 @ sk_C)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('114', plain, ((v2_funct_1 @ sk_C)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('115', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 0.99/1.19      inference('demod', [status(thm)], ['111', '112', '113', '114'])).
% 0.99/1.19  thf('116', plain,
% 0.99/1.19      ((((sk_B) != (sk_B))
% 0.99/1.19        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_relat_1 @ sk_A)))),
% 0.99/1.19      inference('demod', [status(thm)], ['78', '115'])).
% 0.99/1.19  thf('117', plain, (((k5_relat_1 @ sk_C @ sk_D) != (k6_relat_1 @ sk_A))),
% 0.99/1.19      inference('simplify', [status(thm)], ['116'])).
% 0.99/1.19  thf('118', plain, ($false),
% 0.99/1.19      inference('simplify_reflect-', [status(thm)], ['30', '117'])).
% 0.99/1.19  
% 0.99/1.19  % SZS output end Refutation
% 0.99/1.19  
% 1.03/1.20  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

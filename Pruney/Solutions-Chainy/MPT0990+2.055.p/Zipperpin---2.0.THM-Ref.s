%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tj8SwHYeI5

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:03 EST 2020

% Result     : Theorem 0.92s
% Output     : Refutation 0.92s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 239 expanded)
%              Number of leaves         :   42 (  89 expanded)
%              Depth                    :   14
%              Number of atoms          : 1328 (5363 expanded)
%              Number of equality atoms :  112 ( 412 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

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

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( ( k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33 )
        = ( k5_relat_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('20',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('21',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( X11 = X14 )
      | ~ ( r2_relset_1 @ X12 @ X13 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','22'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('24',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('25',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('26',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
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

thf('29',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ( X18
        = ( k1_relset_1 @ X18 @ X19 @ X20 ) )
      | ~ ( zip_tseitin_1 @ X20 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('30',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('31',plain,(
    ! [X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('32',plain,(
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

thf('33',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( zip_tseitin_0 @ X21 @ X22 )
      | ( zip_tseitin_1 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('34',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('39',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('40',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['30','37','40'])).

thf('42',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ( X18
        = ( k1_relset_1 @ X18 @ X19 @ X20 ) )
      | ~ ( zip_tseitin_1 @ X20 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('44',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( zip_tseitin_0 @ X21 @ X22 )
      | ( zip_tseitin_1 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('48',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('54',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['44','51','54'])).

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

thf('56',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ( X3
        = ( k2_funct_1 @ X4 ) )
      | ( ( k5_relat_1 @ X4 @ X3 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X4 ) ) )
      | ( ( k2_relat_1 @ X4 )
       != ( k1_relat_1 @ X3 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t63_funct_1])).

thf('57',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('58',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ( X3
        = ( k2_funct_1 @ X4 ) )
      | ( ( k5_relat_1 @ X4 @ X3 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X4 ) ) )
      | ( ( k2_relat_1 @ X4 )
       != ( k1_relat_1 @ X3 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
       != ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C )
      | ( ( k2_relat_1 @ sk_C )
       != ( k1_relat_1 @ X0 ) )
      | ( X0
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('61',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('62',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
       != ( k6_partfun1 @ sk_A ) )
      | ( ( k2_relat_1 @ sk_C )
       != ( k1_relat_1 @ X0 ) )
      | ( X0
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','62','63','64'])).

thf('66',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != sk_B )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
     != ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('69',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != sk_B )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
     != ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','69','70'])).

thf('72',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != sk_B )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
     != ( k6_partfun1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['71','72'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('74',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X2 ) @ X2 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('75',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('76',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X2 ) @ X2 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
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

thf('78',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( X37 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X37 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X38 ) @ X38 )
        = ( k6_partfun1 @ X37 ) )
      | ~ ( v2_funct_1 @ X38 )
      | ( ( k2_relset_1 @ X39 @ X37 @ X38 )
       != X37 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('79',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','80','81','82','83'])).

thf('85',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['76','87'])).

thf('89',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['60','61'])).

thf('90',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['88','89','90','91'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('94',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['92','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('98',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
     != ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','98'])).

thf('100',plain,(
    ( k5_relat_1 @ sk_C @ sk_D )
 != ( k6_partfun1 @ sk_A ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['27','100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tj8SwHYeI5
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:52:03 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.92/1.10  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.92/1.10  % Solved by: fo/fo7.sh
% 0.92/1.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.92/1.10  % done 324 iterations in 0.640s
% 0.92/1.10  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.92/1.10  % SZS output start Refutation
% 0.92/1.10  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.92/1.10  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.92/1.10  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.92/1.10  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.92/1.10  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.92/1.10  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.92/1.10  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.92/1.10  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.92/1.10  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.92/1.10  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.92/1.10  thf(sk_B_type, type, sk_B: $i).
% 0.92/1.10  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.92/1.10  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.92/1.10  thf(sk_C_type, type, sk_C: $i).
% 0.92/1.10  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.92/1.10  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.92/1.10  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.92/1.10  thf(sk_A_type, type, sk_A: $i).
% 0.92/1.10  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.92/1.10  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.92/1.10  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.92/1.10  thf(sk_D_type, type, sk_D: $i).
% 0.92/1.10  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.92/1.10  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.92/1.10  thf(t36_funct_2, conjecture,
% 0.92/1.10    (![A:$i,B:$i,C:$i]:
% 0.92/1.10     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.92/1.10         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.92/1.10       ( ![D:$i]:
% 0.92/1.10         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.92/1.10             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.92/1.10           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.92/1.10               ( r2_relset_1 @
% 0.92/1.10                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.92/1.10                 ( k6_partfun1 @ A ) ) & 
% 0.92/1.10               ( v2_funct_1 @ C ) ) =>
% 0.92/1.10             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.92/1.10               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.92/1.10  thf(zf_stmt_0, negated_conjecture,
% 0.92/1.10    (~( ![A:$i,B:$i,C:$i]:
% 0.92/1.10        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.92/1.10            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.92/1.10          ( ![D:$i]:
% 0.92/1.10            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.92/1.10                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.92/1.10              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.92/1.10                  ( r2_relset_1 @
% 0.92/1.10                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.92/1.10                    ( k6_partfun1 @ A ) ) & 
% 0.92/1.10                  ( v2_funct_1 @ C ) ) =>
% 0.92/1.10                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.92/1.10                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.92/1.10    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.92/1.10  thf('0', plain,
% 0.92/1.10      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.92/1.10        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.92/1.10        (k6_partfun1 @ sk_A))),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf('1', plain,
% 0.92/1.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf('2', plain,
% 0.92/1.10      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf(redefinition_k1_partfun1, axiom,
% 0.92/1.10    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.92/1.10     ( ( ( v1_funct_1 @ E ) & 
% 0.92/1.10         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.92/1.10         ( v1_funct_1 @ F ) & 
% 0.92/1.10         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.92/1.10       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.92/1.10  thf('3', plain,
% 0.92/1.10      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.92/1.10         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.92/1.10          | ~ (v1_funct_1 @ X30)
% 0.92/1.10          | ~ (v1_funct_1 @ X33)
% 0.92/1.10          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.92/1.10          | ((k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33)
% 0.92/1.10              = (k5_relat_1 @ X30 @ X33)))),
% 0.92/1.10      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.92/1.10  thf('4', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.10         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.92/1.10            = (k5_relat_1 @ sk_C @ X0))
% 0.92/1.10          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.92/1.10          | ~ (v1_funct_1 @ X0)
% 0.92/1.10          | ~ (v1_funct_1 @ sk_C))),
% 0.92/1.10      inference('sup-', [status(thm)], ['2', '3'])).
% 0.92/1.10  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf('6', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.10         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.92/1.10            = (k5_relat_1 @ sk_C @ X0))
% 0.92/1.10          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.92/1.10          | ~ (v1_funct_1 @ X0))),
% 0.92/1.10      inference('demod', [status(thm)], ['4', '5'])).
% 0.92/1.10  thf('7', plain,
% 0.92/1.10      ((~ (v1_funct_1 @ sk_D)
% 0.92/1.10        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.92/1.10            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.92/1.10      inference('sup-', [status(thm)], ['1', '6'])).
% 0.92/1.10  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf('9', plain,
% 0.92/1.10      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.92/1.10         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.92/1.10      inference('demod', [status(thm)], ['7', '8'])).
% 0.92/1.10  thf('10', plain,
% 0.92/1.10      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.92/1.10        (k6_partfun1 @ sk_A))),
% 0.92/1.10      inference('demod', [status(thm)], ['0', '9'])).
% 0.92/1.10  thf('11', plain,
% 0.92/1.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf('12', plain,
% 0.92/1.10      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf(dt_k1_partfun1, axiom,
% 0.92/1.10    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.92/1.10     ( ( ( v1_funct_1 @ E ) & 
% 0.92/1.10         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.92/1.10         ( v1_funct_1 @ F ) & 
% 0.92/1.10         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.92/1.10       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.92/1.10         ( m1_subset_1 @
% 0.92/1.10           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.92/1.10           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.92/1.10  thf('13', plain,
% 0.92/1.10      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.92/1.10         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.92/1.10          | ~ (v1_funct_1 @ X24)
% 0.92/1.10          | ~ (v1_funct_1 @ X27)
% 0.92/1.10          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.92/1.10          | (m1_subset_1 @ (k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27) @ 
% 0.92/1.10             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X29))))),
% 0.92/1.10      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.92/1.10  thf('14', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.10         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.92/1.10           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.92/1.10          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.92/1.10          | ~ (v1_funct_1 @ X1)
% 0.92/1.10          | ~ (v1_funct_1 @ sk_C))),
% 0.92/1.10      inference('sup-', [status(thm)], ['12', '13'])).
% 0.92/1.10  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf('16', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.10         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.92/1.10           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.92/1.10          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.92/1.10          | ~ (v1_funct_1 @ X1))),
% 0.92/1.10      inference('demod', [status(thm)], ['14', '15'])).
% 0.92/1.10  thf('17', plain,
% 0.92/1.10      ((~ (v1_funct_1 @ sk_D)
% 0.92/1.10        | (m1_subset_1 @ 
% 0.92/1.10           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.92/1.10           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.92/1.10      inference('sup-', [status(thm)], ['11', '16'])).
% 0.92/1.10  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf('19', plain,
% 0.92/1.10      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.92/1.10         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.92/1.10      inference('demod', [status(thm)], ['7', '8'])).
% 0.92/1.10  thf('20', plain,
% 0.92/1.10      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.92/1.10        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.92/1.10      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.92/1.10  thf(redefinition_r2_relset_1, axiom,
% 0.92/1.10    (![A:$i,B:$i,C:$i,D:$i]:
% 0.92/1.10     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.92/1.10         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.92/1.10       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.92/1.10  thf('21', plain,
% 0.92/1.10      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.92/1.10         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.92/1.10          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.92/1.10          | ((X11) = (X14))
% 0.92/1.10          | ~ (r2_relset_1 @ X12 @ X13 @ X11 @ X14))),
% 0.92/1.10      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.92/1.10  thf('22', plain,
% 0.92/1.10      (![X0 : $i]:
% 0.92/1.10         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 0.92/1.10          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 0.92/1.10          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.92/1.10      inference('sup-', [status(thm)], ['20', '21'])).
% 0.92/1.10  thf('23', plain,
% 0.92/1.10      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.92/1.10           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.92/1.10        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 0.92/1.10      inference('sup-', [status(thm)], ['10', '22'])).
% 0.92/1.10  thf(t29_relset_1, axiom,
% 0.92/1.10    (![A:$i]:
% 0.92/1.10     ( m1_subset_1 @
% 0.92/1.10       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.92/1.10  thf('24', plain,
% 0.92/1.10      (![X15 : $i]:
% 0.92/1.10         (m1_subset_1 @ (k6_relat_1 @ X15) @ 
% 0.92/1.10          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X15)))),
% 0.92/1.10      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.92/1.10  thf(redefinition_k6_partfun1, axiom,
% 0.92/1.10    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.92/1.10  thf('25', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.92/1.10      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.92/1.10  thf('26', plain,
% 0.92/1.10      (![X15 : $i]:
% 0.92/1.10         (m1_subset_1 @ (k6_partfun1 @ X15) @ 
% 0.92/1.10          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X15)))),
% 0.92/1.10      inference('demod', [status(thm)], ['24', '25'])).
% 0.92/1.10  thf('27', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.92/1.10      inference('demod', [status(thm)], ['23', '26'])).
% 0.92/1.10  thf('28', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf(d1_funct_2, axiom,
% 0.92/1.10    (![A:$i,B:$i,C:$i]:
% 0.92/1.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.92/1.10       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.92/1.10           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.92/1.10             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.92/1.10         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.92/1.10           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.92/1.10             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.92/1.10  thf(zf_stmt_1, axiom,
% 0.92/1.10    (![C:$i,B:$i,A:$i]:
% 0.92/1.10     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.92/1.10       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.92/1.10  thf('29', plain,
% 0.92/1.10      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.92/1.10         (~ (v1_funct_2 @ X20 @ X18 @ X19)
% 0.92/1.10          | ((X18) = (k1_relset_1 @ X18 @ X19 @ X20))
% 0.92/1.10          | ~ (zip_tseitin_1 @ X20 @ X19 @ X18))),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.92/1.10  thf('30', plain,
% 0.92/1.10      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 0.92/1.10        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 0.92/1.10      inference('sup-', [status(thm)], ['28', '29'])).
% 0.92/1.10  thf(zf_stmt_2, axiom,
% 0.92/1.10    (![B:$i,A:$i]:
% 0.92/1.10     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.92/1.10       ( zip_tseitin_0 @ B @ A ) ))).
% 0.92/1.10  thf('31', plain,
% 0.92/1.10      (![X16 : $i, X17 : $i]:
% 0.92/1.10         ((zip_tseitin_0 @ X16 @ X17) | ((X16) = (k1_xboole_0)))),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.92/1.10  thf('32', plain,
% 0.92/1.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.92/1.10  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.92/1.10  thf(zf_stmt_5, axiom,
% 0.92/1.10    (![A:$i,B:$i,C:$i]:
% 0.92/1.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.92/1.10       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.92/1.10         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.92/1.10           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.92/1.10             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.92/1.10  thf('33', plain,
% 0.92/1.10      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.92/1.10         (~ (zip_tseitin_0 @ X21 @ X22)
% 0.92/1.10          | (zip_tseitin_1 @ X23 @ X21 @ X22)
% 0.92/1.10          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21))))),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.92/1.10  thf('34', plain,
% 0.92/1.10      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 0.92/1.10      inference('sup-', [status(thm)], ['32', '33'])).
% 0.92/1.10  thf('35', plain,
% 0.92/1.10      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 0.92/1.10      inference('sup-', [status(thm)], ['31', '34'])).
% 0.92/1.10  thf('36', plain, (((sk_A) != (k1_xboole_0))),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf('37', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 0.92/1.10      inference('simplify_reflect-', [status(thm)], ['35', '36'])).
% 0.92/1.10  thf('38', plain,
% 0.92/1.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf(redefinition_k1_relset_1, axiom,
% 0.92/1.10    (![A:$i,B:$i,C:$i]:
% 0.92/1.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.92/1.10       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.92/1.10  thf('39', plain,
% 0.92/1.10      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.92/1.10         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 0.92/1.10          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.92/1.10      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.92/1.10  thf('40', plain,
% 0.92/1.10      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.92/1.10      inference('sup-', [status(thm)], ['38', '39'])).
% 0.92/1.10  thf('41', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.92/1.10      inference('demod', [status(thm)], ['30', '37', '40'])).
% 0.92/1.10  thf('42', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf('43', plain,
% 0.92/1.10      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.92/1.10         (~ (v1_funct_2 @ X20 @ X18 @ X19)
% 0.92/1.10          | ((X18) = (k1_relset_1 @ X18 @ X19 @ X20))
% 0.92/1.10          | ~ (zip_tseitin_1 @ X20 @ X19 @ X18))),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.92/1.10  thf('44', plain,
% 0.92/1.10      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.92/1.10        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.92/1.10      inference('sup-', [status(thm)], ['42', '43'])).
% 0.92/1.10  thf('45', plain,
% 0.92/1.10      (![X16 : $i, X17 : $i]:
% 0.92/1.10         ((zip_tseitin_0 @ X16 @ X17) | ((X16) = (k1_xboole_0)))),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.92/1.10  thf('46', plain,
% 0.92/1.10      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf('47', plain,
% 0.92/1.10      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.92/1.10         (~ (zip_tseitin_0 @ X21 @ X22)
% 0.92/1.10          | (zip_tseitin_1 @ X23 @ X21 @ X22)
% 0.92/1.10          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21))))),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.92/1.10  thf('48', plain,
% 0.92/1.10      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.92/1.10      inference('sup-', [status(thm)], ['46', '47'])).
% 0.92/1.10  thf('49', plain,
% 0.92/1.10      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.92/1.10      inference('sup-', [status(thm)], ['45', '48'])).
% 0.92/1.10  thf('50', plain, (((sk_B) != (k1_xboole_0))),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf('51', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.92/1.10      inference('simplify_reflect-', [status(thm)], ['49', '50'])).
% 0.92/1.10  thf('52', plain,
% 0.92/1.10      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf('53', plain,
% 0.92/1.10      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.92/1.10         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 0.92/1.10          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.92/1.10      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.92/1.10  thf('54', plain,
% 0.92/1.10      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.92/1.10      inference('sup-', [status(thm)], ['52', '53'])).
% 0.92/1.10  thf('55', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.92/1.10      inference('demod', [status(thm)], ['44', '51', '54'])).
% 0.92/1.10  thf(t63_funct_1, axiom,
% 0.92/1.10    (![A:$i]:
% 0.92/1.10     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.92/1.10       ( ![B:$i]:
% 0.92/1.10         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.92/1.10           ( ( ( v2_funct_1 @ A ) & 
% 0.92/1.10               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.92/1.10               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.92/1.10             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.92/1.10  thf('56', plain,
% 0.92/1.10      (![X3 : $i, X4 : $i]:
% 0.92/1.10         (~ (v1_relat_1 @ X3)
% 0.92/1.10          | ~ (v1_funct_1 @ X3)
% 0.92/1.10          | ((X3) = (k2_funct_1 @ X4))
% 0.92/1.10          | ((k5_relat_1 @ X4 @ X3) != (k6_relat_1 @ (k1_relat_1 @ X4)))
% 0.92/1.10          | ((k2_relat_1 @ X4) != (k1_relat_1 @ X3))
% 0.92/1.10          | ~ (v2_funct_1 @ X4)
% 0.92/1.10          | ~ (v1_funct_1 @ X4)
% 0.92/1.10          | ~ (v1_relat_1 @ X4))),
% 0.92/1.10      inference('cnf', [status(esa)], [t63_funct_1])).
% 0.92/1.10  thf('57', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.92/1.10      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.92/1.10  thf('58', plain,
% 0.92/1.10      (![X3 : $i, X4 : $i]:
% 0.92/1.10         (~ (v1_relat_1 @ X3)
% 0.92/1.10          | ~ (v1_funct_1 @ X3)
% 0.92/1.10          | ((X3) = (k2_funct_1 @ X4))
% 0.92/1.10          | ((k5_relat_1 @ X4 @ X3) != (k6_partfun1 @ (k1_relat_1 @ X4)))
% 0.92/1.10          | ((k2_relat_1 @ X4) != (k1_relat_1 @ X3))
% 0.92/1.10          | ~ (v2_funct_1 @ X4)
% 0.92/1.10          | ~ (v1_funct_1 @ X4)
% 0.92/1.10          | ~ (v1_relat_1 @ X4))),
% 0.92/1.10      inference('demod', [status(thm)], ['56', '57'])).
% 0.92/1.10  thf('59', plain,
% 0.92/1.10      (![X0 : $i]:
% 0.92/1.10         (((k5_relat_1 @ sk_C @ X0) != (k6_partfun1 @ sk_A))
% 0.92/1.10          | ~ (v1_relat_1 @ sk_C)
% 0.92/1.10          | ~ (v1_funct_1 @ sk_C)
% 0.92/1.10          | ~ (v2_funct_1 @ sk_C)
% 0.92/1.10          | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ X0))
% 0.92/1.10          | ((X0) = (k2_funct_1 @ sk_C))
% 0.92/1.10          | ~ (v1_funct_1 @ X0)
% 0.92/1.10          | ~ (v1_relat_1 @ X0))),
% 0.92/1.10      inference('sup-', [status(thm)], ['55', '58'])).
% 0.92/1.10  thf('60', plain,
% 0.92/1.10      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf(cc1_relset_1, axiom,
% 0.92/1.10    (![A:$i,B:$i,C:$i]:
% 0.92/1.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.92/1.10       ( v1_relat_1 @ C ) ))).
% 0.92/1.10  thf('61', plain,
% 0.92/1.10      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.92/1.10         ((v1_relat_1 @ X5)
% 0.92/1.10          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.92/1.10      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.92/1.10  thf('62', plain, ((v1_relat_1 @ sk_C)),
% 0.92/1.10      inference('sup-', [status(thm)], ['60', '61'])).
% 0.92/1.10  thf('63', plain, ((v1_funct_1 @ sk_C)),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf('64', plain, ((v2_funct_1 @ sk_C)),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf('65', plain,
% 0.92/1.10      (![X0 : $i]:
% 0.92/1.10         (((k5_relat_1 @ sk_C @ X0) != (k6_partfun1 @ sk_A))
% 0.92/1.10          | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ X0))
% 0.92/1.10          | ((X0) = (k2_funct_1 @ sk_C))
% 0.92/1.10          | ~ (v1_funct_1 @ X0)
% 0.92/1.10          | ~ (v1_relat_1 @ X0))),
% 0.92/1.10      inference('demod', [status(thm)], ['59', '62', '63', '64'])).
% 0.92/1.10  thf('66', plain,
% 0.92/1.10      ((((k2_relat_1 @ sk_C) != (sk_B))
% 0.92/1.10        | ~ (v1_relat_1 @ sk_D)
% 0.92/1.10        | ~ (v1_funct_1 @ sk_D)
% 0.92/1.10        | ((sk_D) = (k2_funct_1 @ sk_C))
% 0.92/1.10        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_partfun1 @ sk_A)))),
% 0.92/1.10      inference('sup-', [status(thm)], ['41', '65'])).
% 0.92/1.10  thf('67', plain,
% 0.92/1.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf('68', plain,
% 0.92/1.10      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.92/1.10         ((v1_relat_1 @ X5)
% 0.92/1.10          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.92/1.10      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.92/1.10  thf('69', plain, ((v1_relat_1 @ sk_D)),
% 0.92/1.10      inference('sup-', [status(thm)], ['67', '68'])).
% 0.92/1.10  thf('70', plain, ((v1_funct_1 @ sk_D)),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf('71', plain,
% 0.92/1.10      ((((k2_relat_1 @ sk_C) != (sk_B))
% 0.92/1.10        | ((sk_D) = (k2_funct_1 @ sk_C))
% 0.92/1.10        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_partfun1 @ sk_A)))),
% 0.92/1.10      inference('demod', [status(thm)], ['66', '69', '70'])).
% 0.92/1.10  thf('72', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf('73', plain,
% 0.92/1.10      ((((k2_relat_1 @ sk_C) != (sk_B))
% 0.92/1.10        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_partfun1 @ sk_A)))),
% 0.92/1.10      inference('simplify_reflect-', [status(thm)], ['71', '72'])).
% 0.92/1.10  thf(t61_funct_1, axiom,
% 0.92/1.10    (![A:$i]:
% 0.92/1.10     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.92/1.10       ( ( v2_funct_1 @ A ) =>
% 0.92/1.10         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.92/1.10             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.92/1.10           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.92/1.10             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.92/1.10  thf('74', plain,
% 0.92/1.10      (![X2 : $i]:
% 0.92/1.10         (~ (v2_funct_1 @ X2)
% 0.92/1.10          | ((k5_relat_1 @ (k2_funct_1 @ X2) @ X2)
% 0.92/1.10              = (k6_relat_1 @ (k2_relat_1 @ X2)))
% 0.92/1.10          | ~ (v1_funct_1 @ X2)
% 0.92/1.10          | ~ (v1_relat_1 @ X2))),
% 0.92/1.10      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.92/1.10  thf('75', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.92/1.10      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.92/1.10  thf('76', plain,
% 0.92/1.10      (![X2 : $i]:
% 0.92/1.10         (~ (v2_funct_1 @ X2)
% 0.92/1.10          | ((k5_relat_1 @ (k2_funct_1 @ X2) @ X2)
% 0.92/1.10              = (k6_partfun1 @ (k2_relat_1 @ X2)))
% 0.92/1.10          | ~ (v1_funct_1 @ X2)
% 0.92/1.10          | ~ (v1_relat_1 @ X2))),
% 0.92/1.10      inference('demod', [status(thm)], ['74', '75'])).
% 0.92/1.10  thf('77', plain,
% 0.92/1.10      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf(t35_funct_2, axiom,
% 0.92/1.10    (![A:$i,B:$i,C:$i]:
% 0.92/1.10     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.92/1.10         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.92/1.10       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.92/1.10         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.92/1.10           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.92/1.10             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.92/1.10  thf('78', plain,
% 0.92/1.10      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.92/1.10         (((X37) = (k1_xboole_0))
% 0.92/1.10          | ~ (v1_funct_1 @ X38)
% 0.92/1.10          | ~ (v1_funct_2 @ X38 @ X39 @ X37)
% 0.92/1.10          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X37)))
% 0.92/1.10          | ((k5_relat_1 @ (k2_funct_1 @ X38) @ X38) = (k6_partfun1 @ X37))
% 0.92/1.10          | ~ (v2_funct_1 @ X38)
% 0.92/1.10          | ((k2_relset_1 @ X39 @ X37 @ X38) != (X37)))),
% 0.92/1.10      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.92/1.10  thf('79', plain,
% 0.92/1.10      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.92/1.10        | ~ (v2_funct_1 @ sk_C)
% 0.92/1.10        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 0.92/1.10        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.92/1.10        | ~ (v1_funct_1 @ sk_C)
% 0.92/1.10        | ((sk_B) = (k1_xboole_0)))),
% 0.92/1.10      inference('sup-', [status(thm)], ['77', '78'])).
% 0.92/1.10  thf('80', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf('81', plain, ((v2_funct_1 @ sk_C)),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf('82', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf('83', plain, ((v1_funct_1 @ sk_C)),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf('84', plain,
% 0.92/1.10      ((((sk_B) != (sk_B))
% 0.92/1.10        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 0.92/1.10        | ((sk_B) = (k1_xboole_0)))),
% 0.92/1.10      inference('demod', [status(thm)], ['79', '80', '81', '82', '83'])).
% 0.92/1.10  thf('85', plain,
% 0.92/1.10      ((((sk_B) = (k1_xboole_0))
% 0.92/1.10        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 0.92/1.10      inference('simplify', [status(thm)], ['84'])).
% 0.92/1.10  thf('86', plain, (((sk_B) != (k1_xboole_0))),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf('87', plain,
% 0.92/1.10      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 0.92/1.10      inference('simplify_reflect-', [status(thm)], ['85', '86'])).
% 0.92/1.10  thf('88', plain,
% 0.92/1.10      ((((k6_partfun1 @ (k2_relat_1 @ sk_C)) = (k6_partfun1 @ sk_B))
% 0.92/1.10        | ~ (v1_relat_1 @ sk_C)
% 0.92/1.10        | ~ (v1_funct_1 @ sk_C)
% 0.92/1.10        | ~ (v2_funct_1 @ sk_C))),
% 0.92/1.10      inference('sup+', [status(thm)], ['76', '87'])).
% 0.92/1.10  thf('89', plain, ((v1_relat_1 @ sk_C)),
% 0.92/1.10      inference('sup-', [status(thm)], ['60', '61'])).
% 0.92/1.10  thf('90', plain, ((v1_funct_1 @ sk_C)),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf('91', plain, ((v2_funct_1 @ sk_C)),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf('92', plain,
% 0.92/1.10      (((k6_partfun1 @ (k2_relat_1 @ sk_C)) = (k6_partfun1 @ sk_B))),
% 0.92/1.10      inference('demod', [status(thm)], ['88', '89', '90', '91'])).
% 0.92/1.10  thf(t71_relat_1, axiom,
% 0.92/1.10    (![A:$i]:
% 0.92/1.10     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.92/1.10       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.92/1.10  thf('93', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 0.92/1.10      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.92/1.10  thf('94', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.92/1.10      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.92/1.10  thf('95', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 0.92/1.10      inference('demod', [status(thm)], ['93', '94'])).
% 0.92/1.10  thf('96', plain,
% 0.92/1.10      (((k1_relat_1 @ (k6_partfun1 @ sk_B)) = (k2_relat_1 @ sk_C))),
% 0.92/1.10      inference('sup+', [status(thm)], ['92', '95'])).
% 0.92/1.10  thf('97', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 0.92/1.10      inference('demod', [status(thm)], ['93', '94'])).
% 0.92/1.10  thf('98', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 0.92/1.10      inference('demod', [status(thm)], ['96', '97'])).
% 0.92/1.10  thf('99', plain,
% 0.92/1.10      ((((sk_B) != (sk_B))
% 0.92/1.10        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_partfun1 @ sk_A)))),
% 0.92/1.10      inference('demod', [status(thm)], ['73', '98'])).
% 0.92/1.10  thf('100', plain, (((k5_relat_1 @ sk_C @ sk_D) != (k6_partfun1 @ sk_A))),
% 0.92/1.10      inference('simplify', [status(thm)], ['99'])).
% 0.92/1.10  thf('101', plain, ($false),
% 0.92/1.10      inference('simplify_reflect-', [status(thm)], ['27', '100'])).
% 0.92/1.10  
% 0.92/1.10  % SZS output end Refutation
% 0.92/1.10  
% 0.92/1.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

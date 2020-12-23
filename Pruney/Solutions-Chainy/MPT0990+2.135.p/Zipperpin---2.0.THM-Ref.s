%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8OTtr8tZe7

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:18 EST 2020

% Result     : Theorem 5.64s
% Output     : Refutation 5.64s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 296 expanded)
%              Number of leaves         :   46 ( 107 expanded)
%              Depth                    :   21
%              Number of atoms          : 1618 (6329 expanded)
%              Number of equality atoms :  113 ( 457 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

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
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( ( k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41 )
        = ( k5_relat_1 @ X38 @ X41 ) ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X37 ) ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( X19 = X22 )
      | ~ ( r2_relset_1 @ X20 @ X21 @ X19 @ X22 ) ) ),
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
    ! [X23: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('25',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('26',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ( X26
        = ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('40',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['30','37','40'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('42',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k1_relat_1 @ X14 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('44',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
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

thf('46',plain,(
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

thf('47',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','48','49','50','51'])).

thf('53',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['53','54'])).

thf(t82_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ! [D: $i] :
              ( ( v1_relat_1 @ D )
             => ( ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
                  & ( ( k5_relat_1 @ B @ C )
                    = ( k6_relat_1 @ ( k1_relat_1 @ D ) ) )
                  & ( ( k5_relat_1 @ C @ D )
                    = ( k6_relat_1 @ A ) ) )
               => ( D = B ) ) ) ) ) )).

thf('56',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X10 ) @ X11 )
      | ( ( k5_relat_1 @ X10 @ X9 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X12 ) ) )
      | ( ( k5_relat_1 @ X9 @ X12 )
       != ( k6_relat_1 @ X11 ) )
      | ( X12 = X10 )
      | ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t82_relat_1])).

thf('57',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('58',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('59',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X10 ) @ X11 )
      | ( ( k5_relat_1 @ X10 @ X9 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X12 ) ) )
      | ( ( k5_relat_1 @ X9 @ X12 )
       != ( k6_partfun1 @ X11 ) )
      | ( X12 = X10 )
      | ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_partfun1 @ sk_B )
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k2_funct_1 @ sk_C ) )
      | ( ( k5_relat_1 @ sk_C @ X0 )
       != ( k6_partfun1 @ X1 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X1 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['55','59'])).

thf('61',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ( X26
        = ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('63',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('67',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('73',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['63','70','73'])).

thf('75',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k1_relat_1 @ X14 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('76',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('77',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('78',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k2_relat_1 @ X14 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('79',plain,(
    ! [X48: $i] :
      ( ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X48 ) @ ( k2_relat_1 @ X48 ) ) ) )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['76','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['75','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['74','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('89',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('90',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('91',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('92',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','92','93','94'])).

thf('96',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('97',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ sk_A ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('99',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['90','91'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_partfun1 @ sk_B )
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k2_funct_1 @ sk_C ) )
      | ( ( k5_relat_1 @ sk_C @ X0 )
       != ( k6_partfun1 @ X1 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['60','99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
       != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
      | ( X0
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_partfun1 @ sk_B )
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['44','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
       != ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C )
      | ( ( k6_partfun1 @ sk_B )
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['42','102'])).

thf('104',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['63','70','73'])).

thf('105',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['90','91'])).

thf('106',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
       != ( k6_partfun1 @ sk_A ) )
      | ( ( k6_partfun1 @ sk_B )
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['103','104','105','106','107'])).

thf('109',plain,
    ( ( ( k6_partfun1 @ sk_B )
     != ( k6_partfun1 @ sk_B ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
     != ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','108'])).

thf('110',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('112',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('114',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( ( k6_partfun1 @ sk_B )
     != ( k6_partfun1 @ sk_B ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
     != ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['109','114'])).

thf('116',plain,
    ( ( ( k5_relat_1 @ sk_C @ sk_D )
     != ( k6_partfun1 @ sk_A ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ( k5_relat_1 @ sk_C @ sk_D )
 != ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['116','117'])).

thf('119',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['27','118'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8OTtr8tZe7
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:45:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 5.64/5.87  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.64/5.87  % Solved by: fo/fo7.sh
% 5.64/5.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.64/5.87  % done 2167 iterations in 5.409s
% 5.64/5.87  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.64/5.87  % SZS output start Refutation
% 5.64/5.87  thf(sk_D_type, type, sk_D: $i).
% 5.64/5.87  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 5.64/5.87  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 5.64/5.87  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 5.64/5.87  thf(sk_B_type, type, sk_B: $i).
% 5.64/5.87  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.64/5.87  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 5.64/5.87  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 5.64/5.87  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.64/5.87  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 5.64/5.87  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 5.64/5.87  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.64/5.87  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 5.64/5.87  thf(sk_A_type, type, sk_A: $i).
% 5.64/5.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.64/5.87  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.64/5.87  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 5.64/5.87  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 5.64/5.87  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 5.64/5.87  thf(sk_C_type, type, sk_C: $i).
% 5.64/5.87  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 5.64/5.87  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 5.64/5.87  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.64/5.87  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 5.64/5.87  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 5.64/5.87  thf(t36_funct_2, conjecture,
% 5.64/5.87    (![A:$i,B:$i,C:$i]:
% 5.64/5.87     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.64/5.87         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.64/5.87       ( ![D:$i]:
% 5.64/5.87         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 5.64/5.87             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 5.64/5.87           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 5.64/5.87               ( r2_relset_1 @
% 5.64/5.87                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 5.64/5.87                 ( k6_partfun1 @ A ) ) & 
% 5.64/5.87               ( v2_funct_1 @ C ) ) =>
% 5.64/5.87             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 5.64/5.87               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 5.64/5.87  thf(zf_stmt_0, negated_conjecture,
% 5.64/5.87    (~( ![A:$i,B:$i,C:$i]:
% 5.64/5.87        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.64/5.87            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.64/5.87          ( ![D:$i]:
% 5.64/5.87            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 5.64/5.87                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 5.64/5.87              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 5.64/5.87                  ( r2_relset_1 @
% 5.64/5.87                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 5.64/5.87                    ( k6_partfun1 @ A ) ) & 
% 5.64/5.87                  ( v2_funct_1 @ C ) ) =>
% 5.64/5.87                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 5.64/5.87                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 5.64/5.87    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 5.64/5.87  thf('0', plain,
% 5.64/5.87      ((r2_relset_1 @ sk_A @ sk_A @ 
% 5.64/5.87        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 5.64/5.87        (k6_partfun1 @ sk_A))),
% 5.64/5.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.64/5.87  thf('1', plain,
% 5.64/5.87      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 5.64/5.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.64/5.87  thf('2', plain,
% 5.64/5.87      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.64/5.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.64/5.87  thf(redefinition_k1_partfun1, axiom,
% 5.64/5.87    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 5.64/5.87     ( ( ( v1_funct_1 @ E ) & 
% 5.64/5.87         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.64/5.87         ( v1_funct_1 @ F ) & 
% 5.64/5.87         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 5.64/5.87       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 5.64/5.87  thf('3', plain,
% 5.64/5.87      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 5.64/5.87         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 5.64/5.87          | ~ (v1_funct_1 @ X38)
% 5.64/5.87          | ~ (v1_funct_1 @ X41)
% 5.64/5.87          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 5.64/5.87          | ((k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41)
% 5.64/5.87              = (k5_relat_1 @ X38 @ X41)))),
% 5.64/5.87      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 5.64/5.87  thf('4', plain,
% 5.64/5.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.64/5.87         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 5.64/5.87            = (k5_relat_1 @ sk_C @ X0))
% 5.64/5.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 5.64/5.87          | ~ (v1_funct_1 @ X0)
% 5.64/5.87          | ~ (v1_funct_1 @ sk_C))),
% 5.64/5.87      inference('sup-', [status(thm)], ['2', '3'])).
% 5.64/5.87  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 5.64/5.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.64/5.87  thf('6', plain,
% 5.64/5.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.64/5.87         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 5.64/5.87            = (k5_relat_1 @ sk_C @ X0))
% 5.64/5.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 5.64/5.87          | ~ (v1_funct_1 @ X0))),
% 5.64/5.87      inference('demod', [status(thm)], ['4', '5'])).
% 5.64/5.87  thf('7', plain,
% 5.64/5.87      ((~ (v1_funct_1 @ sk_D)
% 5.64/5.87        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 5.64/5.87            = (k5_relat_1 @ sk_C @ sk_D)))),
% 5.64/5.87      inference('sup-', [status(thm)], ['1', '6'])).
% 5.64/5.87  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 5.64/5.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.64/5.87  thf('9', plain,
% 5.64/5.87      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 5.64/5.87         = (k5_relat_1 @ sk_C @ sk_D))),
% 5.64/5.87      inference('demod', [status(thm)], ['7', '8'])).
% 5.64/5.87  thf('10', plain,
% 5.64/5.87      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 5.64/5.87        (k6_partfun1 @ sk_A))),
% 5.64/5.87      inference('demod', [status(thm)], ['0', '9'])).
% 5.64/5.87  thf('11', plain,
% 5.64/5.87      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 5.64/5.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.64/5.87  thf('12', plain,
% 5.64/5.87      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.64/5.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.64/5.87  thf(dt_k1_partfun1, axiom,
% 5.64/5.87    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 5.64/5.87     ( ( ( v1_funct_1 @ E ) & 
% 5.64/5.87         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.64/5.87         ( v1_funct_1 @ F ) & 
% 5.64/5.87         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 5.64/5.87       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 5.64/5.87         ( m1_subset_1 @
% 5.64/5.87           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 5.64/5.87           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 5.64/5.87  thf('13', plain,
% 5.64/5.87      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 5.64/5.87         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 5.64/5.87          | ~ (v1_funct_1 @ X32)
% 5.64/5.87          | ~ (v1_funct_1 @ X35)
% 5.64/5.87          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 5.64/5.87          | (m1_subset_1 @ (k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35) @ 
% 5.64/5.87             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X37))))),
% 5.64/5.87      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 5.64/5.87  thf('14', plain,
% 5.64/5.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.64/5.87         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 5.64/5.87           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 5.64/5.87          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 5.64/5.87          | ~ (v1_funct_1 @ X1)
% 5.64/5.87          | ~ (v1_funct_1 @ sk_C))),
% 5.64/5.87      inference('sup-', [status(thm)], ['12', '13'])).
% 5.64/5.87  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 5.64/5.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.64/5.87  thf('16', plain,
% 5.64/5.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.64/5.87         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 5.64/5.87           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 5.64/5.87          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 5.64/5.87          | ~ (v1_funct_1 @ X1))),
% 5.64/5.87      inference('demod', [status(thm)], ['14', '15'])).
% 5.64/5.87  thf('17', plain,
% 5.64/5.87      ((~ (v1_funct_1 @ sk_D)
% 5.64/5.87        | (m1_subset_1 @ 
% 5.64/5.87           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 5.64/5.87           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 5.64/5.87      inference('sup-', [status(thm)], ['11', '16'])).
% 5.64/5.87  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 5.64/5.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.64/5.87  thf('19', plain,
% 5.64/5.87      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 5.64/5.87         = (k5_relat_1 @ sk_C @ sk_D))),
% 5.64/5.87      inference('demod', [status(thm)], ['7', '8'])).
% 5.64/5.87  thf('20', plain,
% 5.64/5.87      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 5.64/5.87        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.64/5.87      inference('demod', [status(thm)], ['17', '18', '19'])).
% 5.64/5.87  thf(redefinition_r2_relset_1, axiom,
% 5.64/5.87    (![A:$i,B:$i,C:$i,D:$i]:
% 5.64/5.87     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.64/5.87         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.64/5.87       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 5.64/5.87  thf('21', plain,
% 5.64/5.87      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 5.64/5.87         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 5.64/5.87          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 5.64/5.87          | ((X19) = (X22))
% 5.64/5.87          | ~ (r2_relset_1 @ X20 @ X21 @ X19 @ X22))),
% 5.64/5.87      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 5.64/5.87  thf('22', plain,
% 5.64/5.87      (![X0 : $i]:
% 5.64/5.87         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 5.64/5.87          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 5.64/5.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 5.64/5.87      inference('sup-', [status(thm)], ['20', '21'])).
% 5.64/5.87  thf('23', plain,
% 5.64/5.87      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 5.64/5.87           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 5.64/5.87        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 5.64/5.87      inference('sup-', [status(thm)], ['10', '22'])).
% 5.64/5.87  thf(t29_relset_1, axiom,
% 5.64/5.87    (![A:$i]:
% 5.64/5.87     ( m1_subset_1 @
% 5.64/5.87       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 5.64/5.87  thf('24', plain,
% 5.64/5.87      (![X23 : $i]:
% 5.64/5.87         (m1_subset_1 @ (k6_relat_1 @ X23) @ 
% 5.64/5.87          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 5.64/5.87      inference('cnf', [status(esa)], [t29_relset_1])).
% 5.64/5.87  thf(redefinition_k6_partfun1, axiom,
% 5.64/5.87    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 5.64/5.87  thf('25', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 5.64/5.87      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.64/5.87  thf('26', plain,
% 5.64/5.87      (![X23 : $i]:
% 5.64/5.87         (m1_subset_1 @ (k6_partfun1 @ X23) @ 
% 5.64/5.87          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 5.64/5.87      inference('demod', [status(thm)], ['24', '25'])).
% 5.64/5.87  thf('27', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 5.64/5.87      inference('demod', [status(thm)], ['23', '26'])).
% 5.64/5.87  thf('28', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 5.64/5.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.64/5.87  thf(d1_funct_2, axiom,
% 5.64/5.87    (![A:$i,B:$i,C:$i]:
% 5.64/5.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.64/5.87       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 5.64/5.87           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 5.64/5.87             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 5.64/5.87         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 5.64/5.87           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 5.64/5.87             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 5.64/5.87  thf(zf_stmt_1, axiom,
% 5.64/5.87    (![C:$i,B:$i,A:$i]:
% 5.64/5.87     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 5.64/5.87       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 5.64/5.87  thf('29', plain,
% 5.64/5.87      (![X26 : $i, X27 : $i, X28 : $i]:
% 5.64/5.87         (~ (v1_funct_2 @ X28 @ X26 @ X27)
% 5.64/5.87          | ((X26) = (k1_relset_1 @ X26 @ X27 @ X28))
% 5.64/5.87          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 5.64/5.87      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.64/5.87  thf('30', plain,
% 5.64/5.87      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 5.64/5.87        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 5.64/5.87      inference('sup-', [status(thm)], ['28', '29'])).
% 5.64/5.87  thf(zf_stmt_2, axiom,
% 5.64/5.87    (![B:$i,A:$i]:
% 5.64/5.87     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 5.64/5.87       ( zip_tseitin_0 @ B @ A ) ))).
% 5.64/5.87  thf('31', plain,
% 5.64/5.87      (![X24 : $i, X25 : $i]:
% 5.64/5.87         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 5.64/5.87      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.64/5.87  thf('32', plain,
% 5.64/5.87      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 5.64/5.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.64/5.87  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 5.64/5.87  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 5.64/5.87  thf(zf_stmt_5, axiom,
% 5.64/5.87    (![A:$i,B:$i,C:$i]:
% 5.64/5.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.64/5.87       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 5.64/5.87         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 5.64/5.87           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 5.64/5.87             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 5.64/5.87  thf('33', plain,
% 5.64/5.87      (![X29 : $i, X30 : $i, X31 : $i]:
% 5.64/5.87         (~ (zip_tseitin_0 @ X29 @ X30)
% 5.64/5.87          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 5.64/5.87          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 5.64/5.87      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.64/5.87  thf('34', plain,
% 5.64/5.87      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 5.64/5.87      inference('sup-', [status(thm)], ['32', '33'])).
% 5.64/5.87  thf('35', plain,
% 5.64/5.87      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 5.64/5.87      inference('sup-', [status(thm)], ['31', '34'])).
% 5.64/5.87  thf('36', plain, (((sk_A) != (k1_xboole_0))),
% 5.64/5.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.64/5.87  thf('37', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 5.64/5.87      inference('simplify_reflect-', [status(thm)], ['35', '36'])).
% 5.64/5.87  thf('38', plain,
% 5.64/5.87      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 5.64/5.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.64/5.87  thf(redefinition_k1_relset_1, axiom,
% 5.64/5.87    (![A:$i,B:$i,C:$i]:
% 5.64/5.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.64/5.87       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 5.64/5.87  thf('39', plain,
% 5.64/5.87      (![X16 : $i, X17 : $i, X18 : $i]:
% 5.64/5.87         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 5.64/5.87          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 5.64/5.87      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 5.64/5.87  thf('40', plain,
% 5.64/5.87      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 5.64/5.87      inference('sup-', [status(thm)], ['38', '39'])).
% 5.64/5.87  thf('41', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 5.64/5.87      inference('demod', [status(thm)], ['30', '37', '40'])).
% 5.64/5.87  thf(t55_funct_1, axiom,
% 5.64/5.87    (![A:$i]:
% 5.64/5.87     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.64/5.87       ( ( v2_funct_1 @ A ) =>
% 5.64/5.87         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 5.64/5.87           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 5.64/5.87  thf('42', plain,
% 5.64/5.87      (![X14 : $i]:
% 5.64/5.87         (~ (v2_funct_1 @ X14)
% 5.64/5.87          | ((k1_relat_1 @ X14) = (k2_relat_1 @ (k2_funct_1 @ X14)))
% 5.64/5.87          | ~ (v1_funct_1 @ X14)
% 5.64/5.87          | ~ (v1_relat_1 @ X14))),
% 5.64/5.87      inference('cnf', [status(esa)], [t55_funct_1])).
% 5.64/5.87  thf(d10_xboole_0, axiom,
% 5.64/5.87    (![A:$i,B:$i]:
% 5.64/5.87     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.64/5.87  thf('43', plain,
% 5.64/5.87      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 5.64/5.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.64/5.87  thf('44', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 5.64/5.87      inference('simplify', [status(thm)], ['43'])).
% 5.64/5.87  thf('45', plain,
% 5.64/5.87      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.64/5.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.64/5.87  thf(t35_funct_2, axiom,
% 5.64/5.87    (![A:$i,B:$i,C:$i]:
% 5.64/5.87     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.64/5.87         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.64/5.87       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 5.64/5.87         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 5.64/5.87           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 5.64/5.87             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 5.64/5.87  thf('46', plain,
% 5.64/5.87      (![X45 : $i, X46 : $i, X47 : $i]:
% 5.64/5.87         (((X45) = (k1_xboole_0))
% 5.64/5.87          | ~ (v1_funct_1 @ X46)
% 5.64/5.87          | ~ (v1_funct_2 @ X46 @ X47 @ X45)
% 5.64/5.87          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X45)))
% 5.64/5.87          | ((k5_relat_1 @ (k2_funct_1 @ X46) @ X46) = (k6_partfun1 @ X45))
% 5.64/5.87          | ~ (v2_funct_1 @ X46)
% 5.64/5.87          | ((k2_relset_1 @ X47 @ X45 @ X46) != (X45)))),
% 5.64/5.87      inference('cnf', [status(esa)], [t35_funct_2])).
% 5.64/5.87  thf('47', plain,
% 5.64/5.87      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 5.64/5.87        | ~ (v2_funct_1 @ sk_C)
% 5.64/5.87        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 5.64/5.87        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 5.64/5.87        | ~ (v1_funct_1 @ sk_C)
% 5.64/5.87        | ((sk_B) = (k1_xboole_0)))),
% 5.64/5.87      inference('sup-', [status(thm)], ['45', '46'])).
% 5.64/5.87  thf('48', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 5.64/5.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.64/5.87  thf('49', plain, ((v2_funct_1 @ sk_C)),
% 5.64/5.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.64/5.87  thf('50', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 5.64/5.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.64/5.87  thf('51', plain, ((v1_funct_1 @ sk_C)),
% 5.64/5.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.64/5.87  thf('52', plain,
% 5.64/5.87      ((((sk_B) != (sk_B))
% 5.64/5.87        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 5.64/5.87        | ((sk_B) = (k1_xboole_0)))),
% 5.64/5.87      inference('demod', [status(thm)], ['47', '48', '49', '50', '51'])).
% 5.64/5.87  thf('53', plain,
% 5.64/5.87      ((((sk_B) = (k1_xboole_0))
% 5.64/5.87        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 5.64/5.87      inference('simplify', [status(thm)], ['52'])).
% 5.64/5.87  thf('54', plain, (((sk_B) != (k1_xboole_0))),
% 5.64/5.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.64/5.87  thf('55', plain,
% 5.64/5.87      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 5.64/5.87      inference('simplify_reflect-', [status(thm)], ['53', '54'])).
% 5.64/5.87  thf(t82_relat_1, axiom,
% 5.64/5.87    (![A:$i,B:$i]:
% 5.64/5.87     ( ( v1_relat_1 @ B ) =>
% 5.64/5.87       ( ![C:$i]:
% 5.64/5.87         ( ( v1_relat_1 @ C ) =>
% 5.64/5.87           ( ![D:$i]:
% 5.64/5.87             ( ( v1_relat_1 @ D ) =>
% 5.64/5.87               ( ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) & 
% 5.64/5.87                   ( ( k5_relat_1 @ B @ C ) =
% 5.64/5.87                     ( k6_relat_1 @ ( k1_relat_1 @ D ) ) ) & 
% 5.64/5.87                   ( ( k5_relat_1 @ C @ D ) = ( k6_relat_1 @ A ) ) ) =>
% 5.64/5.87                 ( ( D ) = ( B ) ) ) ) ) ) ) ))).
% 5.64/5.87  thf('56', plain,
% 5.64/5.87      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 5.64/5.87         (~ (v1_relat_1 @ X9)
% 5.64/5.87          | ~ (r1_tarski @ (k2_relat_1 @ X10) @ X11)
% 5.64/5.87          | ((k5_relat_1 @ X10 @ X9) != (k6_relat_1 @ (k1_relat_1 @ X12)))
% 5.64/5.87          | ((k5_relat_1 @ X9 @ X12) != (k6_relat_1 @ X11))
% 5.64/5.87          | ((X12) = (X10))
% 5.64/5.87          | ~ (v1_relat_1 @ X12)
% 5.64/5.87          | ~ (v1_relat_1 @ X10))),
% 5.64/5.87      inference('cnf', [status(esa)], [t82_relat_1])).
% 5.64/5.87  thf('57', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 5.64/5.87      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.64/5.87  thf('58', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 5.64/5.87      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.64/5.87  thf('59', plain,
% 5.64/5.87      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 5.64/5.87         (~ (v1_relat_1 @ X9)
% 5.64/5.87          | ~ (r1_tarski @ (k2_relat_1 @ X10) @ X11)
% 5.64/5.87          | ((k5_relat_1 @ X10 @ X9) != (k6_partfun1 @ (k1_relat_1 @ X12)))
% 5.64/5.87          | ((k5_relat_1 @ X9 @ X12) != (k6_partfun1 @ X11))
% 5.64/5.87          | ((X12) = (X10))
% 5.64/5.87          | ~ (v1_relat_1 @ X12)
% 5.64/5.87          | ~ (v1_relat_1 @ X10))),
% 5.64/5.87      inference('demod', [status(thm)], ['56', '57', '58'])).
% 5.64/5.87  thf('60', plain,
% 5.64/5.87      (![X0 : $i, X1 : $i]:
% 5.64/5.87         (((k6_partfun1 @ sk_B) != (k6_partfun1 @ (k1_relat_1 @ X0)))
% 5.64/5.87          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 5.64/5.87          | ~ (v1_relat_1 @ X0)
% 5.64/5.87          | ((X0) = (k2_funct_1 @ sk_C))
% 5.64/5.87          | ((k5_relat_1 @ sk_C @ X0) != (k6_partfun1 @ X1))
% 5.64/5.87          | ~ (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ X1)
% 5.64/5.87          | ~ (v1_relat_1 @ sk_C))),
% 5.64/5.87      inference('sup-', [status(thm)], ['55', '59'])).
% 5.64/5.87  thf('61', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 5.64/5.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.64/5.87  thf('62', plain,
% 5.64/5.87      (![X26 : $i, X27 : $i, X28 : $i]:
% 5.64/5.87         (~ (v1_funct_2 @ X28 @ X26 @ X27)
% 5.64/5.87          | ((X26) = (k1_relset_1 @ X26 @ X27 @ X28))
% 5.64/5.87          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 5.64/5.87      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.64/5.87  thf('63', plain,
% 5.64/5.87      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 5.64/5.87        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 5.64/5.87      inference('sup-', [status(thm)], ['61', '62'])).
% 5.64/5.87  thf('64', plain,
% 5.64/5.87      (![X24 : $i, X25 : $i]:
% 5.64/5.87         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 5.64/5.87      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.64/5.87  thf('65', plain,
% 5.64/5.87      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.64/5.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.64/5.87  thf('66', plain,
% 5.64/5.87      (![X29 : $i, X30 : $i, X31 : $i]:
% 5.64/5.87         (~ (zip_tseitin_0 @ X29 @ X30)
% 5.64/5.87          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 5.64/5.87          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 5.64/5.87      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.64/5.87  thf('67', plain,
% 5.64/5.87      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 5.64/5.87      inference('sup-', [status(thm)], ['65', '66'])).
% 5.64/5.87  thf('68', plain,
% 5.64/5.87      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 5.64/5.87      inference('sup-', [status(thm)], ['64', '67'])).
% 5.64/5.87  thf('69', plain, (((sk_B) != (k1_xboole_0))),
% 5.64/5.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.64/5.87  thf('70', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 5.64/5.87      inference('simplify_reflect-', [status(thm)], ['68', '69'])).
% 5.64/5.87  thf('71', plain,
% 5.64/5.87      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.64/5.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.64/5.87  thf('72', plain,
% 5.64/5.87      (![X16 : $i, X17 : $i, X18 : $i]:
% 5.64/5.87         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 5.64/5.87          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 5.64/5.87      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 5.64/5.87  thf('73', plain,
% 5.64/5.87      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 5.64/5.87      inference('sup-', [status(thm)], ['71', '72'])).
% 5.64/5.87  thf('74', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 5.64/5.87      inference('demod', [status(thm)], ['63', '70', '73'])).
% 5.64/5.87  thf('75', plain,
% 5.64/5.87      (![X14 : $i]:
% 5.64/5.87         (~ (v2_funct_1 @ X14)
% 5.64/5.87          | ((k1_relat_1 @ X14) = (k2_relat_1 @ (k2_funct_1 @ X14)))
% 5.64/5.87          | ~ (v1_funct_1 @ X14)
% 5.64/5.87          | ~ (v1_relat_1 @ X14))),
% 5.64/5.87      inference('cnf', [status(esa)], [t55_funct_1])).
% 5.64/5.87  thf(dt_k2_funct_1, axiom,
% 5.64/5.87    (![A:$i]:
% 5.64/5.87     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.64/5.87       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 5.64/5.87         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 5.64/5.87  thf('76', plain,
% 5.64/5.87      (![X13 : $i]:
% 5.64/5.87         ((v1_funct_1 @ (k2_funct_1 @ X13))
% 5.64/5.87          | ~ (v1_funct_1 @ X13)
% 5.64/5.87          | ~ (v1_relat_1 @ X13))),
% 5.64/5.87      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 5.64/5.87  thf('77', plain,
% 5.64/5.87      (![X13 : $i]:
% 5.64/5.87         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 5.64/5.87          | ~ (v1_funct_1 @ X13)
% 5.64/5.87          | ~ (v1_relat_1 @ X13))),
% 5.64/5.87      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 5.64/5.87  thf('78', plain,
% 5.64/5.87      (![X14 : $i]:
% 5.64/5.87         (~ (v2_funct_1 @ X14)
% 5.64/5.87          | ((k2_relat_1 @ X14) = (k1_relat_1 @ (k2_funct_1 @ X14)))
% 5.64/5.87          | ~ (v1_funct_1 @ X14)
% 5.64/5.87          | ~ (v1_relat_1 @ X14))),
% 5.64/5.87      inference('cnf', [status(esa)], [t55_funct_1])).
% 5.64/5.87  thf(t3_funct_2, axiom,
% 5.64/5.87    (![A:$i]:
% 5.64/5.87     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.64/5.87       ( ( v1_funct_1 @ A ) & 
% 5.64/5.87         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 5.64/5.87         ( m1_subset_1 @
% 5.64/5.87           A @ 
% 5.64/5.87           ( k1_zfmisc_1 @
% 5.64/5.87             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 5.64/5.87  thf('79', plain,
% 5.64/5.87      (![X48 : $i]:
% 5.64/5.87         ((m1_subset_1 @ X48 @ 
% 5.64/5.87           (k1_zfmisc_1 @ 
% 5.64/5.87            (k2_zfmisc_1 @ (k1_relat_1 @ X48) @ (k2_relat_1 @ X48))))
% 5.64/5.87          | ~ (v1_funct_1 @ X48)
% 5.64/5.87          | ~ (v1_relat_1 @ X48))),
% 5.64/5.87      inference('cnf', [status(esa)], [t3_funct_2])).
% 5.64/5.87  thf('80', plain,
% 5.64/5.87      (![X0 : $i]:
% 5.64/5.87         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 5.64/5.87           (k1_zfmisc_1 @ 
% 5.64/5.87            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 5.64/5.87          | ~ (v1_relat_1 @ X0)
% 5.64/5.87          | ~ (v1_funct_1 @ X0)
% 5.64/5.87          | ~ (v2_funct_1 @ X0)
% 5.64/5.87          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 5.64/5.87          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 5.64/5.87      inference('sup+', [status(thm)], ['78', '79'])).
% 5.64/5.87  thf('81', plain,
% 5.64/5.87      (![X0 : $i]:
% 5.64/5.87         (~ (v1_relat_1 @ X0)
% 5.64/5.87          | ~ (v1_funct_1 @ X0)
% 5.64/5.87          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 5.64/5.87          | ~ (v2_funct_1 @ X0)
% 5.64/5.87          | ~ (v1_funct_1 @ X0)
% 5.64/5.87          | ~ (v1_relat_1 @ X0)
% 5.64/5.87          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 5.64/5.87             (k1_zfmisc_1 @ 
% 5.64/5.87              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 5.64/5.87               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 5.64/5.87      inference('sup-', [status(thm)], ['77', '80'])).
% 5.64/5.87  thf('82', plain,
% 5.64/5.87      (![X0 : $i]:
% 5.64/5.87         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 5.64/5.87           (k1_zfmisc_1 @ 
% 5.64/5.87            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 5.64/5.87          | ~ (v2_funct_1 @ X0)
% 5.64/5.87          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 5.64/5.87          | ~ (v1_funct_1 @ X0)
% 5.64/5.87          | ~ (v1_relat_1 @ X0))),
% 5.64/5.87      inference('simplify', [status(thm)], ['81'])).
% 5.64/5.87  thf('83', plain,
% 5.64/5.87      (![X0 : $i]:
% 5.64/5.87         (~ (v1_relat_1 @ X0)
% 5.64/5.87          | ~ (v1_funct_1 @ X0)
% 5.64/5.87          | ~ (v1_relat_1 @ X0)
% 5.64/5.87          | ~ (v1_funct_1 @ X0)
% 5.64/5.87          | ~ (v2_funct_1 @ X0)
% 5.64/5.87          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 5.64/5.87             (k1_zfmisc_1 @ 
% 5.64/5.87              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 5.64/5.87               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 5.64/5.87      inference('sup-', [status(thm)], ['76', '82'])).
% 5.64/5.87  thf('84', plain,
% 5.64/5.87      (![X0 : $i]:
% 5.64/5.87         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 5.64/5.87           (k1_zfmisc_1 @ 
% 5.64/5.87            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 5.64/5.87          | ~ (v2_funct_1 @ X0)
% 5.64/5.87          | ~ (v1_funct_1 @ X0)
% 5.64/5.87          | ~ (v1_relat_1 @ X0))),
% 5.64/5.87      inference('simplify', [status(thm)], ['83'])).
% 5.64/5.87  thf('85', plain,
% 5.64/5.87      (![X0 : $i]:
% 5.64/5.87         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 5.64/5.87           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 5.64/5.87          | ~ (v1_relat_1 @ X0)
% 5.64/5.87          | ~ (v1_funct_1 @ X0)
% 5.64/5.87          | ~ (v2_funct_1 @ X0)
% 5.64/5.87          | ~ (v1_relat_1 @ X0)
% 5.64/5.87          | ~ (v1_funct_1 @ X0)
% 5.64/5.87          | ~ (v2_funct_1 @ X0))),
% 5.64/5.87      inference('sup+', [status(thm)], ['75', '84'])).
% 5.64/5.87  thf('86', plain,
% 5.64/5.87      (![X0 : $i]:
% 5.64/5.87         (~ (v2_funct_1 @ X0)
% 5.64/5.87          | ~ (v1_funct_1 @ X0)
% 5.64/5.87          | ~ (v1_relat_1 @ X0)
% 5.64/5.87          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 5.64/5.87             (k1_zfmisc_1 @ 
% 5.64/5.87              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 5.64/5.87      inference('simplify', [status(thm)], ['85'])).
% 5.64/5.87  thf('87', plain,
% 5.64/5.87      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.64/5.87         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ sk_A)))
% 5.64/5.87        | ~ (v1_relat_1 @ sk_C)
% 5.64/5.87        | ~ (v1_funct_1 @ sk_C)
% 5.64/5.87        | ~ (v2_funct_1 @ sk_C))),
% 5.64/5.87      inference('sup+', [status(thm)], ['74', '86'])).
% 5.64/5.87  thf('88', plain,
% 5.64/5.87      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.64/5.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.64/5.87  thf(cc2_relat_1, axiom,
% 5.64/5.87    (![A:$i]:
% 5.64/5.87     ( ( v1_relat_1 @ A ) =>
% 5.64/5.87       ( ![B:$i]:
% 5.64/5.87         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 5.64/5.87  thf('89', plain,
% 5.64/5.87      (![X3 : $i, X4 : $i]:
% 5.64/5.87         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 5.64/5.87          | (v1_relat_1 @ X3)
% 5.64/5.87          | ~ (v1_relat_1 @ X4))),
% 5.64/5.87      inference('cnf', [status(esa)], [cc2_relat_1])).
% 5.64/5.87  thf('90', plain,
% 5.64/5.87      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 5.64/5.87      inference('sup-', [status(thm)], ['88', '89'])).
% 5.64/5.87  thf(fc6_relat_1, axiom,
% 5.64/5.87    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 5.64/5.87  thf('91', plain,
% 5.64/5.87      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 5.64/5.87      inference('cnf', [status(esa)], [fc6_relat_1])).
% 5.64/5.87  thf('92', plain, ((v1_relat_1 @ sk_C)),
% 5.64/5.87      inference('demod', [status(thm)], ['90', '91'])).
% 5.64/5.87  thf('93', plain, ((v1_funct_1 @ sk_C)),
% 5.64/5.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.64/5.87  thf('94', plain, ((v2_funct_1 @ sk_C)),
% 5.64/5.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.64/5.87  thf('95', plain,
% 5.64/5.87      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.64/5.87        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ sk_A)))),
% 5.64/5.87      inference('demod', [status(thm)], ['87', '92', '93', '94'])).
% 5.64/5.87  thf('96', plain,
% 5.64/5.87      (![X3 : $i, X4 : $i]:
% 5.64/5.87         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 5.64/5.87          | (v1_relat_1 @ X3)
% 5.64/5.87          | ~ (v1_relat_1 @ X4))),
% 5.64/5.87      inference('cnf', [status(esa)], [cc2_relat_1])).
% 5.64/5.87  thf('97', plain,
% 5.64/5.87      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ sk_A))
% 5.64/5.87        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 5.64/5.87      inference('sup-', [status(thm)], ['95', '96'])).
% 5.64/5.87  thf('98', plain,
% 5.64/5.87      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 5.64/5.87      inference('cnf', [status(esa)], [fc6_relat_1])).
% 5.64/5.87  thf('99', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 5.64/5.87      inference('demod', [status(thm)], ['97', '98'])).
% 5.64/5.87  thf('100', plain, ((v1_relat_1 @ sk_C)),
% 5.64/5.87      inference('demod', [status(thm)], ['90', '91'])).
% 5.64/5.87  thf('101', plain,
% 5.64/5.87      (![X0 : $i, X1 : $i]:
% 5.64/5.87         (((k6_partfun1 @ sk_B) != (k6_partfun1 @ (k1_relat_1 @ X0)))
% 5.64/5.87          | ~ (v1_relat_1 @ X0)
% 5.64/5.87          | ((X0) = (k2_funct_1 @ sk_C))
% 5.64/5.87          | ((k5_relat_1 @ sk_C @ X0) != (k6_partfun1 @ X1))
% 5.64/5.87          | ~ (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ X1))),
% 5.64/5.87      inference('demod', [status(thm)], ['60', '99', '100'])).
% 5.64/5.87  thf('102', plain,
% 5.64/5.87      (![X0 : $i]:
% 5.64/5.87         (((k5_relat_1 @ sk_C @ X0)
% 5.64/5.87            != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 5.64/5.87          | ((X0) = (k2_funct_1 @ sk_C))
% 5.64/5.87          | ~ (v1_relat_1 @ X0)
% 5.64/5.87          | ((k6_partfun1 @ sk_B) != (k6_partfun1 @ (k1_relat_1 @ X0))))),
% 5.64/5.87      inference('sup-', [status(thm)], ['44', '101'])).
% 5.64/5.87  thf('103', plain,
% 5.64/5.87      (![X0 : $i]:
% 5.64/5.87         (((k5_relat_1 @ sk_C @ X0) != (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 5.64/5.87          | ~ (v1_relat_1 @ sk_C)
% 5.64/5.87          | ~ (v1_funct_1 @ sk_C)
% 5.64/5.87          | ~ (v2_funct_1 @ sk_C)
% 5.64/5.87          | ((k6_partfun1 @ sk_B) != (k6_partfun1 @ (k1_relat_1 @ X0)))
% 5.64/5.87          | ~ (v1_relat_1 @ X0)
% 5.64/5.87          | ((X0) = (k2_funct_1 @ sk_C)))),
% 5.64/5.87      inference('sup-', [status(thm)], ['42', '102'])).
% 5.64/5.87  thf('104', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 5.64/5.87      inference('demod', [status(thm)], ['63', '70', '73'])).
% 5.64/5.87  thf('105', plain, ((v1_relat_1 @ sk_C)),
% 5.64/5.87      inference('demod', [status(thm)], ['90', '91'])).
% 5.64/5.87  thf('106', plain, ((v1_funct_1 @ sk_C)),
% 5.64/5.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.64/5.87  thf('107', plain, ((v2_funct_1 @ sk_C)),
% 5.64/5.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.64/5.87  thf('108', plain,
% 5.64/5.87      (![X0 : $i]:
% 5.64/5.87         (((k5_relat_1 @ sk_C @ X0) != (k6_partfun1 @ sk_A))
% 5.64/5.87          | ((k6_partfun1 @ sk_B) != (k6_partfun1 @ (k1_relat_1 @ X0)))
% 5.64/5.87          | ~ (v1_relat_1 @ X0)
% 5.64/5.87          | ((X0) = (k2_funct_1 @ sk_C)))),
% 5.64/5.87      inference('demod', [status(thm)], ['103', '104', '105', '106', '107'])).
% 5.64/5.87  thf('109', plain,
% 5.64/5.87      ((((k6_partfun1 @ sk_B) != (k6_partfun1 @ sk_B))
% 5.64/5.87        | ((sk_D) = (k2_funct_1 @ sk_C))
% 5.64/5.87        | ~ (v1_relat_1 @ sk_D)
% 5.64/5.87        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_partfun1 @ sk_A)))),
% 5.64/5.87      inference('sup-', [status(thm)], ['41', '108'])).
% 5.64/5.87  thf('110', plain,
% 5.64/5.87      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 5.64/5.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.64/5.87  thf('111', plain,
% 5.64/5.87      (![X3 : $i, X4 : $i]:
% 5.64/5.87         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 5.64/5.87          | (v1_relat_1 @ X3)
% 5.64/5.87          | ~ (v1_relat_1 @ X4))),
% 5.64/5.87      inference('cnf', [status(esa)], [cc2_relat_1])).
% 5.64/5.87  thf('112', plain,
% 5.64/5.87      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 5.64/5.87      inference('sup-', [status(thm)], ['110', '111'])).
% 5.64/5.87  thf('113', plain,
% 5.64/5.87      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 5.64/5.87      inference('cnf', [status(esa)], [fc6_relat_1])).
% 5.64/5.87  thf('114', plain, ((v1_relat_1 @ sk_D)),
% 5.64/5.87      inference('demod', [status(thm)], ['112', '113'])).
% 5.64/5.87  thf('115', plain,
% 5.64/5.87      ((((k6_partfun1 @ sk_B) != (k6_partfun1 @ sk_B))
% 5.64/5.87        | ((sk_D) = (k2_funct_1 @ sk_C))
% 5.64/5.87        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_partfun1 @ sk_A)))),
% 5.64/5.87      inference('demod', [status(thm)], ['109', '114'])).
% 5.64/5.87  thf('116', plain,
% 5.64/5.87      ((((k5_relat_1 @ sk_C @ sk_D) != (k6_partfun1 @ sk_A))
% 5.64/5.87        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 5.64/5.87      inference('simplify', [status(thm)], ['115'])).
% 5.64/5.87  thf('117', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 5.64/5.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.64/5.87  thf('118', plain, (((k5_relat_1 @ sk_C @ sk_D) != (k6_partfun1 @ sk_A))),
% 5.64/5.87      inference('simplify_reflect-', [status(thm)], ['116', '117'])).
% 5.64/5.87  thf('119', plain, ($false),
% 5.64/5.87      inference('simplify_reflect-', [status(thm)], ['27', '118'])).
% 5.64/5.87  
% 5.64/5.87  % SZS output end Refutation
% 5.64/5.87  
% 5.64/5.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

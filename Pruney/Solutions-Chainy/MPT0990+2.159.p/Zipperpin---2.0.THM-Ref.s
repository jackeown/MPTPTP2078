%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PIQ25suzt8

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:22 EST 2020

% Result     : Theorem 0.80s
% Output     : Refutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 239 expanded)
%              Number of leaves         :   44 (  90 expanded)
%              Depth                    :   14
%              Number of atoms          : 1331 (5354 expanded)
%              Number of equality atoms :  106 ( 400 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

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
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( ( k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38 )
        = ( k5_relat_1 @ X35 @ X38 ) ) ) ),
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

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('15',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('22',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('23',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( X15 = X18 )
      | ~ ( r2_relset_1 @ X16 @ X17 @ X15 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','24'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('26',plain,(
    ! [X34: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('27',plain,(
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
    ! [X34: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,(
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

thf('31',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ( X21
        = ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('32',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('33',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('34',plain,(
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

thf('35',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('36',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('41',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('42',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['32','39','42'])).

thf('44',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ( X21
        = ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('46',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('50',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('56',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['46','53','56'])).

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

thf('58',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( X10
        = ( k2_funct_1 @ X11 ) )
      | ( ( k5_relat_1 @ X11 @ X10 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X11 ) ) )
      | ( ( k2_relat_1 @ X11 )
       != ( k1_relat_1 @ X10 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t63_funct_1])).

thf('59',plain,(
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
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('63',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('64',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
       != ( k6_relat_1 @ sk_A ) )
      | ( ( k2_relat_1 @ sk_C )
       != ( k1_relat_1 @ X0 ) )
      | ( X0
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','64','65','66'])).

thf('68',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != sk_B )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
     != ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('71',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('73',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != sk_B )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
     != ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','73','74'])).

thf('76',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != sk_B )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
     != ( k6_relat_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['75','76'])).

thf('78',plain,(
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

thf('79',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( X42 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X42 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X43 ) @ X43 )
        = ( k6_partfun1 @ X42 ) )
      | ~ ( v2_funct_1 @ X43 )
      | ( ( k2_relset_1 @ X44 @ X42 @ X43 )
       != X42 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('80',plain,(
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('81',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( X42 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X42 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X43 ) @ X43 )
        = ( k6_relat_1 @ X42 ) )
      | ~ ( v2_funct_1 @ X43 )
      | ( ( k2_relset_1 @ X44 @ X42 @ X43 )
       != X42 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['82','83','84','85','86'])).

thf('88',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['88','89'])).

thf(t59_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
            = ( k2_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
            = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('91',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X9 ) @ X9 ) )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t59_funct_1])).

thf('92',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ sk_B ) )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('93',plain,(
    ! [X5: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('94',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['62','63'])).

thf('95',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['92','93','94','95','96'])).

thf('98',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
     != ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','97'])).

thf('99',plain,(
    ( k5_relat_1 @ sk_C @ sk_D )
 != ( k6_relat_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['29','99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PIQ25suzt8
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:52:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.80/1.01  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.80/1.01  % Solved by: fo/fo7.sh
% 0.80/1.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.80/1.01  % done 306 iterations in 0.576s
% 0.80/1.01  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.80/1.01  % SZS output start Refutation
% 0.80/1.01  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.80/1.01  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.80/1.01  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.80/1.01  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.80/1.01  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.80/1.01  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.80/1.01  thf(sk_B_type, type, sk_B: $i).
% 0.80/1.01  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.80/1.01  thf(sk_D_type, type, sk_D: $i).
% 0.80/1.01  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.80/1.01  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.80/1.01  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.80/1.01  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.80/1.01  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.80/1.01  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.80/1.01  thf(sk_A_type, type, sk_A: $i).
% 0.80/1.01  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.80/1.01  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.80/1.01  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.80/1.01  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.80/1.01  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.80/1.01  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.80/1.01  thf(sk_C_type, type, sk_C: $i).
% 0.80/1.01  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.80/1.01  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.80/1.01  thf(t36_funct_2, conjecture,
% 0.80/1.01    (![A:$i,B:$i,C:$i]:
% 0.80/1.01     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.80/1.01         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.80/1.01       ( ![D:$i]:
% 0.80/1.01         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.80/1.01             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.80/1.01           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.80/1.01               ( r2_relset_1 @
% 0.80/1.01                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.80/1.01                 ( k6_partfun1 @ A ) ) & 
% 0.80/1.01               ( v2_funct_1 @ C ) ) =>
% 0.80/1.01             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.80/1.01               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.80/1.01  thf(zf_stmt_0, negated_conjecture,
% 0.80/1.01    (~( ![A:$i,B:$i,C:$i]:
% 0.80/1.01        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.80/1.01            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.80/1.01          ( ![D:$i]:
% 0.80/1.01            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.80/1.01                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.80/1.01              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.80/1.01                  ( r2_relset_1 @
% 0.80/1.01                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.80/1.01                    ( k6_partfun1 @ A ) ) & 
% 0.80/1.01                  ( v2_funct_1 @ C ) ) =>
% 0.80/1.01                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.80/1.01                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.80/1.01    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.80/1.01  thf('0', plain,
% 0.80/1.01      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.80/1.01        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.80/1.01        (k6_partfun1 @ sk_A))),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf(redefinition_k6_partfun1, axiom,
% 0.80/1.01    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.80/1.01  thf('1', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 0.80/1.01      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.80/1.01  thf('2', plain,
% 0.80/1.01      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.80/1.01        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.80/1.01        (k6_relat_1 @ sk_A))),
% 0.80/1.01      inference('demod', [status(thm)], ['0', '1'])).
% 0.80/1.01  thf('3', plain,
% 0.80/1.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('4', plain,
% 0.80/1.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf(redefinition_k1_partfun1, axiom,
% 0.80/1.01    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.80/1.01     ( ( ( v1_funct_1 @ E ) & 
% 0.80/1.01         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.80/1.01         ( v1_funct_1 @ F ) & 
% 0.80/1.01         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.80/1.01       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.80/1.01  thf('5', plain,
% 0.80/1.01      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.80/1.01         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.80/1.01          | ~ (v1_funct_1 @ X35)
% 0.80/1.01          | ~ (v1_funct_1 @ X38)
% 0.80/1.01          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.80/1.01          | ((k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38)
% 0.80/1.01              = (k5_relat_1 @ X35 @ X38)))),
% 0.80/1.01      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.80/1.01  thf('6', plain,
% 0.80/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.80/1.01         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.80/1.01            = (k5_relat_1 @ sk_C @ X0))
% 0.80/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.80/1.01          | ~ (v1_funct_1 @ X0)
% 0.80/1.01          | ~ (v1_funct_1 @ sk_C))),
% 0.80/1.01      inference('sup-', [status(thm)], ['4', '5'])).
% 0.80/1.01  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('8', plain,
% 0.80/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.80/1.01         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.80/1.01            = (k5_relat_1 @ sk_C @ X0))
% 0.80/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.80/1.01          | ~ (v1_funct_1 @ X0))),
% 0.80/1.01      inference('demod', [status(thm)], ['6', '7'])).
% 0.80/1.01  thf('9', plain,
% 0.80/1.01      ((~ (v1_funct_1 @ sk_D)
% 0.80/1.01        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.80/1.01            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.80/1.01      inference('sup-', [status(thm)], ['3', '8'])).
% 0.80/1.01  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('11', plain,
% 0.80/1.01      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.80/1.01         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.80/1.01      inference('demod', [status(thm)], ['9', '10'])).
% 0.80/1.01  thf('12', plain,
% 0.80/1.01      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.80/1.01        (k6_relat_1 @ sk_A))),
% 0.80/1.01      inference('demod', [status(thm)], ['2', '11'])).
% 0.80/1.01  thf('13', plain,
% 0.80/1.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('14', plain,
% 0.80/1.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf(dt_k1_partfun1, axiom,
% 0.80/1.01    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.80/1.01     ( ( ( v1_funct_1 @ E ) & 
% 0.80/1.01         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.80/1.01         ( v1_funct_1 @ F ) & 
% 0.80/1.01         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.80/1.01       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.80/1.01         ( m1_subset_1 @
% 0.80/1.01           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.80/1.01           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.80/1.01  thf('15', plain,
% 0.80/1.01      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.80/1.01         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.80/1.01          | ~ (v1_funct_1 @ X27)
% 0.80/1.01          | ~ (v1_funct_1 @ X30)
% 0.80/1.01          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.80/1.01          | (m1_subset_1 @ (k1_partfun1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30) @ 
% 0.80/1.01             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X32))))),
% 0.80/1.01      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.80/1.01  thf('16', plain,
% 0.80/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.80/1.01         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.80/1.01           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.80/1.01          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.80/1.01          | ~ (v1_funct_1 @ X1)
% 0.80/1.01          | ~ (v1_funct_1 @ sk_C))),
% 0.80/1.01      inference('sup-', [status(thm)], ['14', '15'])).
% 0.80/1.01  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('18', plain,
% 0.80/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.80/1.01         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.80/1.01           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.80/1.01          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.80/1.01          | ~ (v1_funct_1 @ X1))),
% 0.80/1.01      inference('demod', [status(thm)], ['16', '17'])).
% 0.80/1.01  thf('19', plain,
% 0.80/1.01      ((~ (v1_funct_1 @ sk_D)
% 0.80/1.01        | (m1_subset_1 @ 
% 0.80/1.01           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.80/1.01           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.80/1.01      inference('sup-', [status(thm)], ['13', '18'])).
% 0.80/1.01  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('21', plain,
% 0.80/1.01      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.80/1.01         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.80/1.01      inference('demod', [status(thm)], ['9', '10'])).
% 0.80/1.01  thf('22', plain,
% 0.80/1.01      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.80/1.01        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.80/1.01      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.80/1.01  thf(redefinition_r2_relset_1, axiom,
% 0.80/1.01    (![A:$i,B:$i,C:$i,D:$i]:
% 0.80/1.01     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.80/1.01         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.80/1.01       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.80/1.01  thf('23', plain,
% 0.80/1.01      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.80/1.01         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.80/1.01          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.80/1.01          | ((X15) = (X18))
% 0.80/1.01          | ~ (r2_relset_1 @ X16 @ X17 @ X15 @ X18))),
% 0.80/1.01      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.80/1.01  thf('24', plain,
% 0.80/1.01      (![X0 : $i]:
% 0.80/1.01         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 0.80/1.01          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 0.80/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.80/1.01      inference('sup-', [status(thm)], ['22', '23'])).
% 0.80/1.01  thf('25', plain,
% 0.80/1.01      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 0.80/1.01           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.80/1.01        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A)))),
% 0.80/1.01      inference('sup-', [status(thm)], ['12', '24'])).
% 0.80/1.01  thf(dt_k6_partfun1, axiom,
% 0.80/1.01    (![A:$i]:
% 0.80/1.01     ( ( m1_subset_1 @
% 0.80/1.01         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.80/1.01       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.80/1.01  thf('26', plain,
% 0.80/1.01      (![X34 : $i]:
% 0.80/1.01         (m1_subset_1 @ (k6_partfun1 @ X34) @ 
% 0.80/1.01          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))),
% 0.80/1.01      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.80/1.01  thf('27', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 0.80/1.01      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.80/1.01  thf('28', plain,
% 0.80/1.01      (![X34 : $i]:
% 0.80/1.01         (m1_subset_1 @ (k6_relat_1 @ X34) @ 
% 0.80/1.01          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))),
% 0.80/1.01      inference('demod', [status(thm)], ['26', '27'])).
% 0.80/1.01  thf('29', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 0.80/1.01      inference('demod', [status(thm)], ['25', '28'])).
% 0.80/1.01  thf('30', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf(d1_funct_2, axiom,
% 0.80/1.01    (![A:$i,B:$i,C:$i]:
% 0.80/1.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.80/1.01       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.80/1.01           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.80/1.01             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.80/1.01         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.80/1.01           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.80/1.01             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.80/1.01  thf(zf_stmt_1, axiom,
% 0.80/1.01    (![C:$i,B:$i,A:$i]:
% 0.80/1.01     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.80/1.01       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.80/1.01  thf('31', plain,
% 0.80/1.01      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.80/1.01         (~ (v1_funct_2 @ X23 @ X21 @ X22)
% 0.80/1.01          | ((X21) = (k1_relset_1 @ X21 @ X22 @ X23))
% 0.80/1.01          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.80/1.01  thf('32', plain,
% 0.80/1.01      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 0.80/1.01        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 0.80/1.01      inference('sup-', [status(thm)], ['30', '31'])).
% 0.80/1.01  thf(zf_stmt_2, axiom,
% 0.80/1.01    (![B:$i,A:$i]:
% 0.80/1.01     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.80/1.01       ( zip_tseitin_0 @ B @ A ) ))).
% 0.80/1.01  thf('33', plain,
% 0.80/1.01      (![X19 : $i, X20 : $i]:
% 0.80/1.01         ((zip_tseitin_0 @ X19 @ X20) | ((X19) = (k1_xboole_0)))),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.80/1.01  thf('34', plain,
% 0.80/1.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.80/1.01  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.80/1.01  thf(zf_stmt_5, axiom,
% 0.80/1.01    (![A:$i,B:$i,C:$i]:
% 0.80/1.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.80/1.01       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.80/1.01         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.80/1.01           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.80/1.01             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.80/1.01  thf('35', plain,
% 0.80/1.01      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.80/1.01         (~ (zip_tseitin_0 @ X24 @ X25)
% 0.80/1.01          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 0.80/1.01          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.80/1.01  thf('36', plain,
% 0.80/1.01      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 0.80/1.01      inference('sup-', [status(thm)], ['34', '35'])).
% 0.80/1.01  thf('37', plain,
% 0.80/1.01      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 0.80/1.01      inference('sup-', [status(thm)], ['33', '36'])).
% 0.80/1.01  thf('38', plain, (((sk_A) != (k1_xboole_0))),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('39', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 0.80/1.01      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.80/1.01  thf('40', plain,
% 0.80/1.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf(redefinition_k1_relset_1, axiom,
% 0.80/1.01    (![A:$i,B:$i,C:$i]:
% 0.80/1.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.80/1.01       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.80/1.01  thf('41', plain,
% 0.80/1.01      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.80/1.01         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 0.80/1.01          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.80/1.01      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.80/1.01  thf('42', plain,
% 0.80/1.01      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.80/1.01      inference('sup-', [status(thm)], ['40', '41'])).
% 0.80/1.01  thf('43', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.80/1.01      inference('demod', [status(thm)], ['32', '39', '42'])).
% 0.80/1.01  thf('44', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('45', plain,
% 0.80/1.01      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.80/1.01         (~ (v1_funct_2 @ X23 @ X21 @ X22)
% 0.80/1.01          | ((X21) = (k1_relset_1 @ X21 @ X22 @ X23))
% 0.80/1.01          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.80/1.01  thf('46', plain,
% 0.80/1.01      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.80/1.01        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.80/1.01      inference('sup-', [status(thm)], ['44', '45'])).
% 0.80/1.01  thf('47', plain,
% 0.80/1.01      (![X19 : $i, X20 : $i]:
% 0.80/1.01         ((zip_tseitin_0 @ X19 @ X20) | ((X19) = (k1_xboole_0)))),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.80/1.01  thf('48', plain,
% 0.80/1.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('49', plain,
% 0.80/1.01      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.80/1.01         (~ (zip_tseitin_0 @ X24 @ X25)
% 0.80/1.01          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 0.80/1.01          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.80/1.01  thf('50', plain,
% 0.80/1.01      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.80/1.01      inference('sup-', [status(thm)], ['48', '49'])).
% 0.80/1.01  thf('51', plain,
% 0.80/1.01      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.80/1.01      inference('sup-', [status(thm)], ['47', '50'])).
% 0.80/1.01  thf('52', plain, (((sk_B) != (k1_xboole_0))),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('53', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.80/1.01      inference('simplify_reflect-', [status(thm)], ['51', '52'])).
% 0.80/1.01  thf('54', plain,
% 0.80/1.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('55', plain,
% 0.80/1.01      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.80/1.01         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 0.80/1.01          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.80/1.01      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.80/1.01  thf('56', plain,
% 0.80/1.01      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.80/1.01      inference('sup-', [status(thm)], ['54', '55'])).
% 0.80/1.01  thf('57', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.80/1.01      inference('demod', [status(thm)], ['46', '53', '56'])).
% 0.80/1.01  thf(t63_funct_1, axiom,
% 0.80/1.01    (![A:$i]:
% 0.80/1.01     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.80/1.01       ( ![B:$i]:
% 0.80/1.01         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.80/1.01           ( ( ( v2_funct_1 @ A ) & 
% 0.80/1.01               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.80/1.01               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.80/1.01             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.80/1.01  thf('58', plain,
% 0.80/1.01      (![X10 : $i, X11 : $i]:
% 0.80/1.01         (~ (v1_relat_1 @ X10)
% 0.80/1.01          | ~ (v1_funct_1 @ X10)
% 0.80/1.01          | ((X10) = (k2_funct_1 @ X11))
% 0.80/1.01          | ((k5_relat_1 @ X11 @ X10) != (k6_relat_1 @ (k1_relat_1 @ X11)))
% 0.80/1.01          | ((k2_relat_1 @ X11) != (k1_relat_1 @ X10))
% 0.80/1.01          | ~ (v2_funct_1 @ X11)
% 0.80/1.01          | ~ (v1_funct_1 @ X11)
% 0.80/1.01          | ~ (v1_relat_1 @ X11))),
% 0.80/1.01      inference('cnf', [status(esa)], [t63_funct_1])).
% 0.80/1.01  thf('59', plain,
% 0.80/1.01      (![X0 : $i]:
% 0.80/1.01         (((k5_relat_1 @ sk_C @ X0) != (k6_relat_1 @ sk_A))
% 0.80/1.01          | ~ (v1_relat_1 @ sk_C)
% 0.80/1.01          | ~ (v1_funct_1 @ sk_C)
% 0.80/1.01          | ~ (v2_funct_1 @ sk_C)
% 0.80/1.01          | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ X0))
% 0.80/1.01          | ((X0) = (k2_funct_1 @ sk_C))
% 0.80/1.01          | ~ (v1_funct_1 @ X0)
% 0.80/1.01          | ~ (v1_relat_1 @ X0))),
% 0.80/1.01      inference('sup-', [status(thm)], ['57', '58'])).
% 0.80/1.01  thf('60', plain,
% 0.80/1.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf(cc2_relat_1, axiom,
% 0.80/1.01    (![A:$i]:
% 0.80/1.01     ( ( v1_relat_1 @ A ) =>
% 0.80/1.01       ( ![B:$i]:
% 0.80/1.01         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.80/1.01  thf('61', plain,
% 0.80/1.01      (![X0 : $i, X1 : $i]:
% 0.80/1.01         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.80/1.01          | (v1_relat_1 @ X0)
% 0.80/1.01          | ~ (v1_relat_1 @ X1))),
% 0.80/1.01      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.80/1.01  thf('62', plain,
% 0.80/1.01      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.80/1.01      inference('sup-', [status(thm)], ['60', '61'])).
% 0.80/1.01  thf(fc6_relat_1, axiom,
% 0.80/1.01    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.80/1.01  thf('63', plain,
% 0.80/1.01      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.80/1.01      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.80/1.01  thf('64', plain, ((v1_relat_1 @ sk_C)),
% 0.80/1.01      inference('demod', [status(thm)], ['62', '63'])).
% 0.80/1.01  thf('65', plain, ((v1_funct_1 @ sk_C)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('66', plain, ((v2_funct_1 @ sk_C)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('67', plain,
% 0.80/1.01      (![X0 : $i]:
% 0.80/1.01         (((k5_relat_1 @ sk_C @ X0) != (k6_relat_1 @ sk_A))
% 0.80/1.01          | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ X0))
% 0.80/1.01          | ((X0) = (k2_funct_1 @ sk_C))
% 0.80/1.01          | ~ (v1_funct_1 @ X0)
% 0.80/1.01          | ~ (v1_relat_1 @ X0))),
% 0.80/1.01      inference('demod', [status(thm)], ['59', '64', '65', '66'])).
% 0.80/1.01  thf('68', plain,
% 0.80/1.01      ((((k2_relat_1 @ sk_C) != (sk_B))
% 0.80/1.01        | ~ (v1_relat_1 @ sk_D)
% 0.80/1.01        | ~ (v1_funct_1 @ sk_D)
% 0.80/1.01        | ((sk_D) = (k2_funct_1 @ sk_C))
% 0.80/1.01        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_relat_1 @ sk_A)))),
% 0.80/1.01      inference('sup-', [status(thm)], ['43', '67'])).
% 0.80/1.01  thf('69', plain,
% 0.80/1.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('70', plain,
% 0.80/1.01      (![X0 : $i, X1 : $i]:
% 0.80/1.01         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.80/1.01          | (v1_relat_1 @ X0)
% 0.80/1.01          | ~ (v1_relat_1 @ X1))),
% 0.80/1.01      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.80/1.01  thf('71', plain,
% 0.80/1.01      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.80/1.01      inference('sup-', [status(thm)], ['69', '70'])).
% 0.80/1.01  thf('72', plain,
% 0.80/1.01      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.80/1.01      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.80/1.01  thf('73', plain, ((v1_relat_1 @ sk_D)),
% 0.80/1.01      inference('demod', [status(thm)], ['71', '72'])).
% 0.80/1.01  thf('74', plain, ((v1_funct_1 @ sk_D)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('75', plain,
% 0.80/1.01      ((((k2_relat_1 @ sk_C) != (sk_B))
% 0.80/1.01        | ((sk_D) = (k2_funct_1 @ sk_C))
% 0.80/1.01        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_relat_1 @ sk_A)))),
% 0.80/1.01      inference('demod', [status(thm)], ['68', '73', '74'])).
% 0.80/1.01  thf('76', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('77', plain,
% 0.80/1.01      ((((k2_relat_1 @ sk_C) != (sk_B))
% 0.80/1.01        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_relat_1 @ sk_A)))),
% 0.80/1.01      inference('simplify_reflect-', [status(thm)], ['75', '76'])).
% 0.80/1.01  thf('78', plain,
% 0.80/1.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf(t35_funct_2, axiom,
% 0.80/1.01    (![A:$i,B:$i,C:$i]:
% 0.80/1.01     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.80/1.01         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.80/1.01       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.80/1.01         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.80/1.01           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.80/1.01             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.80/1.01  thf('79', plain,
% 0.80/1.01      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.80/1.01         (((X42) = (k1_xboole_0))
% 0.80/1.01          | ~ (v1_funct_1 @ X43)
% 0.80/1.01          | ~ (v1_funct_2 @ X43 @ X44 @ X42)
% 0.80/1.01          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X42)))
% 0.80/1.01          | ((k5_relat_1 @ (k2_funct_1 @ X43) @ X43) = (k6_partfun1 @ X42))
% 0.80/1.01          | ~ (v2_funct_1 @ X43)
% 0.80/1.01          | ((k2_relset_1 @ X44 @ X42 @ X43) != (X42)))),
% 0.80/1.01      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.80/1.01  thf('80', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 0.80/1.01      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.80/1.01  thf('81', plain,
% 0.80/1.01      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.80/1.01         (((X42) = (k1_xboole_0))
% 0.80/1.01          | ~ (v1_funct_1 @ X43)
% 0.80/1.01          | ~ (v1_funct_2 @ X43 @ X44 @ X42)
% 0.80/1.01          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X42)))
% 0.80/1.01          | ((k5_relat_1 @ (k2_funct_1 @ X43) @ X43) = (k6_relat_1 @ X42))
% 0.80/1.01          | ~ (v2_funct_1 @ X43)
% 0.80/1.01          | ((k2_relset_1 @ X44 @ X42 @ X43) != (X42)))),
% 0.80/1.01      inference('demod', [status(thm)], ['79', '80'])).
% 0.80/1.01  thf('82', plain,
% 0.80/1.01      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.80/1.01        | ~ (v2_funct_1 @ sk_C)
% 0.80/1.01        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 0.80/1.01        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.80/1.01        | ~ (v1_funct_1 @ sk_C)
% 0.80/1.01        | ((sk_B) = (k1_xboole_0)))),
% 0.80/1.01      inference('sup-', [status(thm)], ['78', '81'])).
% 0.80/1.01  thf('83', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('84', plain, ((v2_funct_1 @ sk_C)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('85', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('86', plain, ((v1_funct_1 @ sk_C)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('87', plain,
% 0.80/1.01      ((((sk_B) != (sk_B))
% 0.80/1.01        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 0.80/1.01        | ((sk_B) = (k1_xboole_0)))),
% 0.80/1.01      inference('demod', [status(thm)], ['82', '83', '84', '85', '86'])).
% 0.80/1.01  thf('88', plain,
% 0.80/1.01      ((((sk_B) = (k1_xboole_0))
% 0.80/1.01        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B)))),
% 0.80/1.01      inference('simplify', [status(thm)], ['87'])).
% 0.80/1.01  thf('89', plain, (((sk_B) != (k1_xboole_0))),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('90', plain,
% 0.80/1.01      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))),
% 0.80/1.01      inference('simplify_reflect-', [status(thm)], ['88', '89'])).
% 0.80/1.01  thf(t59_funct_1, axiom,
% 0.80/1.01    (![A:$i]:
% 0.80/1.01     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.80/1.01       ( ( v2_funct_1 @ A ) =>
% 0.80/1.01         ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.80/1.01             ( k2_relat_1 @ A ) ) & 
% 0.80/1.01           ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.80/1.01             ( k2_relat_1 @ A ) ) ) ) ))).
% 0.80/1.01  thf('91', plain,
% 0.80/1.01      (![X9 : $i]:
% 0.80/1.01         (~ (v2_funct_1 @ X9)
% 0.80/1.01          | ((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X9) @ X9))
% 0.80/1.01              = (k2_relat_1 @ X9))
% 0.80/1.01          | ~ (v1_funct_1 @ X9)
% 0.80/1.01          | ~ (v1_relat_1 @ X9))),
% 0.80/1.01      inference('cnf', [status(esa)], [t59_funct_1])).
% 0.80/1.01  thf('92', plain,
% 0.80/1.01      ((((k2_relat_1 @ (k6_relat_1 @ sk_B)) = (k2_relat_1 @ sk_C))
% 0.80/1.01        | ~ (v1_relat_1 @ sk_C)
% 0.80/1.01        | ~ (v1_funct_1 @ sk_C)
% 0.80/1.01        | ~ (v2_funct_1 @ sk_C))),
% 0.80/1.01      inference('sup+', [status(thm)], ['90', '91'])).
% 0.80/1.01  thf(t71_relat_1, axiom,
% 0.80/1.01    (![A:$i]:
% 0.80/1.01     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.80/1.01       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.80/1.01  thf('93', plain, (![X5 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 0.80/1.01      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.80/1.01  thf('94', plain, ((v1_relat_1 @ sk_C)),
% 0.80/1.01      inference('demod', [status(thm)], ['62', '63'])).
% 0.80/1.01  thf('95', plain, ((v1_funct_1 @ sk_C)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('96', plain, ((v2_funct_1 @ sk_C)),
% 0.80/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.01  thf('97', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 0.80/1.01      inference('demod', [status(thm)], ['92', '93', '94', '95', '96'])).
% 0.80/1.01  thf('98', plain,
% 0.80/1.01      ((((sk_B) != (sk_B))
% 0.80/1.01        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_relat_1 @ sk_A)))),
% 0.80/1.01      inference('demod', [status(thm)], ['77', '97'])).
% 0.80/1.01  thf('99', plain, (((k5_relat_1 @ sk_C @ sk_D) != (k6_relat_1 @ sk_A))),
% 0.80/1.01      inference('simplify', [status(thm)], ['98'])).
% 0.80/1.01  thf('100', plain, ($false),
% 0.80/1.01      inference('simplify_reflect-', [status(thm)], ['29', '99'])).
% 0.80/1.01  
% 0.80/1.01  % SZS output end Refutation
% 0.80/1.01  
% 0.80/1.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

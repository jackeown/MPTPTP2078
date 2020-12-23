%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Thk0RpEQR6

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:22 EST 2020

% Result     : Theorem 2.44s
% Output     : Refutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 227 expanded)
%              Number of leaves         :   44 (  87 expanded)
%              Depth                    :   14
%              Number of atoms          : 1340 (4833 expanded)
%              Number of equality atoms :  110 ( 372 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
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

thf('2',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( ( k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37 )
        = ( k5_relat_1 @ X34 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('18',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( X14 = X17 )
      | ~ ( r2_relset_1 @ X15 @ X16 @ X14 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','19'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('21',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('22',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['6','7','22'])).

thf('24',plain,(
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

thf('25',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ( X20
        = ( k1_relset_1 @ X20 @ X21 @ X22 ) )
      | ~ ( zip_tseitin_1 @ X22 @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('26',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('28',plain,(
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

thf('29',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X24 )
      | ( zip_tseitin_1 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('30',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('35',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('36',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['26','33','36'])).

thf('38',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ( X20
        = ( k1_relset_1 @ X20 @ X21 @ X22 ) )
      | ~ ( zip_tseitin_1 @ X22 @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('40',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X24 )
      | ( zip_tseitin_1 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('44',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('50',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['40','47','50'])).

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

thf('52',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( X9
        = ( k2_funct_1 @ X10 ) )
      | ( ( k5_relat_1 @ X10 @ X9 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X10 ) ) )
      | ( ( k2_relat_1 @ X10 )
       != ( k1_relat_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t63_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('53',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('54',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( X9
        = ( k2_funct_1 @ X10 ) )
      | ( ( k5_relat_1 @ X10 @ X9 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X10 ) ) )
      | ( ( k2_relat_1 @ X10 )
       != ( k1_relat_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
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
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('58',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('59',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('60',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
       != ( k6_partfun1 @ sk_A ) )
      | ( ( k2_relat_1 @ sk_C )
       != ( k1_relat_1 @ X0 ) )
      | ( X0
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['55','60','61','62'])).

thf('64',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != sk_B )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
     != ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('67',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('69',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['67','68'])).

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
    inference(demod,[status(thm)],['64','69','70'])).

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
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X8 ) @ X8 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('75',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('76',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X8 ) @ X8 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
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
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( X41 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ X43 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X41 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X42 ) @ X42 )
        = ( k6_partfun1 @ X41 ) )
      | ~ ( v2_funct_1 @ X42 )
      | ( ( k2_relset_1 @ X43 @ X41 @ X42 )
       != X41 ) ) ),
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
    inference(demod,[status(thm)],['58','59'])).

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
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('94',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('95',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['92','95'])).

thf('97',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
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
    inference('simplify_reflect-',[status(thm)],['23','100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Thk0RpEQR6
% 0.16/0.38  % Computer   : n024.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 16:01:06 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 2.44/2.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.44/2.66  % Solved by: fo/fo7.sh
% 2.44/2.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.44/2.66  % done 810 iterations in 2.174s
% 2.44/2.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.44/2.66  % SZS output start Refutation
% 2.44/2.66  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.44/2.66  thf(sk_B_type, type, sk_B: $i).
% 2.44/2.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.44/2.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.44/2.66  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.44/2.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.44/2.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.44/2.66  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.44/2.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.44/2.66  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.44/2.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.44/2.66  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.44/2.66  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.44/2.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.44/2.66  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.44/2.66  thf(sk_C_type, type, sk_C: $i).
% 2.44/2.66  thf(sk_D_type, type, sk_D: $i).
% 2.44/2.66  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.44/2.66  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 2.44/2.66  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.44/2.66  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.44/2.66  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.44/2.66  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.44/2.66  thf(sk_A_type, type, sk_A: $i).
% 2.44/2.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.44/2.66  thf(t36_funct_2, conjecture,
% 2.44/2.66    (![A:$i,B:$i,C:$i]:
% 2.44/2.66     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.44/2.66         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.44/2.66       ( ![D:$i]:
% 2.44/2.66         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.44/2.66             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.44/2.66           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.44/2.66               ( r2_relset_1 @
% 2.44/2.66                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.44/2.66                 ( k6_partfun1 @ A ) ) & 
% 2.44/2.66               ( v2_funct_1 @ C ) ) =>
% 2.44/2.66             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.44/2.66               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 2.44/2.66  thf(zf_stmt_0, negated_conjecture,
% 2.44/2.66    (~( ![A:$i,B:$i,C:$i]:
% 2.44/2.66        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.44/2.66            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.44/2.66          ( ![D:$i]:
% 2.44/2.66            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.44/2.66                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.44/2.66              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.44/2.66                  ( r2_relset_1 @
% 2.44/2.66                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.44/2.66                    ( k6_partfun1 @ A ) ) & 
% 2.44/2.66                  ( v2_funct_1 @ C ) ) =>
% 2.44/2.66                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.44/2.66                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 2.44/2.66    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 2.44/2.66  thf('0', plain,
% 2.44/2.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('1', plain,
% 2.44/2.66      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf(redefinition_k1_partfun1, axiom,
% 2.44/2.66    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.44/2.66     ( ( ( v1_funct_1 @ E ) & 
% 2.44/2.66         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.44/2.66         ( v1_funct_1 @ F ) & 
% 2.44/2.66         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.44/2.66       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.44/2.66  thf('2', plain,
% 2.44/2.66      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 2.44/2.66         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 2.44/2.66          | ~ (v1_funct_1 @ X34)
% 2.44/2.66          | ~ (v1_funct_1 @ X37)
% 2.44/2.66          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 2.44/2.66          | ((k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37)
% 2.44/2.66              = (k5_relat_1 @ X34 @ X37)))),
% 2.44/2.66      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 2.44/2.66  thf('3', plain,
% 2.44/2.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.44/2.66         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.44/2.66            = (k5_relat_1 @ sk_C @ X0))
% 2.44/2.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.44/2.66          | ~ (v1_funct_1 @ X0)
% 2.44/2.66          | ~ (v1_funct_1 @ sk_C))),
% 2.44/2.66      inference('sup-', [status(thm)], ['1', '2'])).
% 2.44/2.66  thf('4', plain, ((v1_funct_1 @ sk_C)),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('5', plain,
% 2.44/2.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.44/2.66         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.44/2.66            = (k5_relat_1 @ sk_C @ X0))
% 2.44/2.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.44/2.66          | ~ (v1_funct_1 @ X0))),
% 2.44/2.66      inference('demod', [status(thm)], ['3', '4'])).
% 2.44/2.66  thf('6', plain,
% 2.44/2.66      ((~ (v1_funct_1 @ sk_D)
% 2.44/2.66        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.44/2.66            = (k5_relat_1 @ sk_C @ sk_D)))),
% 2.44/2.66      inference('sup-', [status(thm)], ['0', '5'])).
% 2.44/2.66  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('8', plain,
% 2.44/2.66      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.44/2.66        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.44/2.66        (k6_partfun1 @ sk_A))),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('9', plain,
% 2.44/2.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('10', plain,
% 2.44/2.66      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf(dt_k1_partfun1, axiom,
% 2.44/2.66    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.44/2.66     ( ( ( v1_funct_1 @ E ) & 
% 2.44/2.66         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.44/2.66         ( v1_funct_1 @ F ) & 
% 2.44/2.66         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.44/2.66       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.44/2.66         ( m1_subset_1 @
% 2.44/2.66           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.44/2.66           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.44/2.66  thf('11', plain,
% 2.44/2.66      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 2.44/2.66         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 2.44/2.66          | ~ (v1_funct_1 @ X26)
% 2.44/2.66          | ~ (v1_funct_1 @ X29)
% 2.44/2.66          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 2.44/2.66          | (m1_subset_1 @ (k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29) @ 
% 2.44/2.66             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X31))))),
% 2.44/2.66      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.44/2.66  thf('12', plain,
% 2.44/2.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.44/2.66         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.44/2.66           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.44/2.66          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.44/2.66          | ~ (v1_funct_1 @ X1)
% 2.44/2.66          | ~ (v1_funct_1 @ sk_C))),
% 2.44/2.66      inference('sup-', [status(thm)], ['10', '11'])).
% 2.44/2.66  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('14', plain,
% 2.44/2.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.44/2.66         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.44/2.66           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.44/2.66          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.44/2.66          | ~ (v1_funct_1 @ X1))),
% 2.44/2.66      inference('demod', [status(thm)], ['12', '13'])).
% 2.44/2.66  thf('15', plain,
% 2.44/2.66      ((~ (v1_funct_1 @ sk_D)
% 2.44/2.66        | (m1_subset_1 @ 
% 2.44/2.66           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.44/2.66           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.44/2.66      inference('sup-', [status(thm)], ['9', '14'])).
% 2.44/2.66  thf('16', plain, ((v1_funct_1 @ sk_D)),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('17', plain,
% 2.44/2.66      ((m1_subset_1 @ 
% 2.44/2.66        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.44/2.66        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.44/2.66      inference('demod', [status(thm)], ['15', '16'])).
% 2.44/2.66  thf(redefinition_r2_relset_1, axiom,
% 2.44/2.66    (![A:$i,B:$i,C:$i,D:$i]:
% 2.44/2.66     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.44/2.66         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.44/2.66       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.44/2.66  thf('18', plain,
% 2.44/2.66      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 2.44/2.66         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 2.44/2.66          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 2.44/2.66          | ((X14) = (X17))
% 2.44/2.66          | ~ (r2_relset_1 @ X15 @ X16 @ X14 @ X17))),
% 2.44/2.66      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.44/2.66  thf('19', plain,
% 2.44/2.66      (![X0 : $i]:
% 2.44/2.66         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.44/2.66             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 2.44/2.66          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 2.44/2.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.44/2.66      inference('sup-', [status(thm)], ['17', '18'])).
% 2.44/2.66  thf('20', plain,
% 2.44/2.66      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 2.44/2.66           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.44/2.66        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.44/2.66            = (k6_partfun1 @ sk_A)))),
% 2.44/2.66      inference('sup-', [status(thm)], ['8', '19'])).
% 2.44/2.66  thf(dt_k6_partfun1, axiom,
% 2.44/2.66    (![A:$i]:
% 2.44/2.66     ( ( m1_subset_1 @
% 2.44/2.66         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 2.44/2.66       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 2.44/2.66  thf('21', plain,
% 2.44/2.66      (![X33 : $i]:
% 2.44/2.66         (m1_subset_1 @ (k6_partfun1 @ X33) @ 
% 2.44/2.66          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 2.44/2.66      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 2.44/2.66  thf('22', plain,
% 2.44/2.66      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.44/2.66         = (k6_partfun1 @ sk_A))),
% 2.44/2.66      inference('demod', [status(thm)], ['20', '21'])).
% 2.44/2.66  thf('23', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 2.44/2.66      inference('demod', [status(thm)], ['6', '7', '22'])).
% 2.44/2.66  thf('24', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf(d1_funct_2, axiom,
% 2.44/2.66    (![A:$i,B:$i,C:$i]:
% 2.44/2.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.44/2.66       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.44/2.66           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.44/2.66             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.44/2.66         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.44/2.66           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.44/2.66             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.44/2.66  thf(zf_stmt_1, axiom,
% 2.44/2.66    (![C:$i,B:$i,A:$i]:
% 2.44/2.66     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.44/2.66       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.44/2.66  thf('25', plain,
% 2.44/2.66      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.44/2.66         (~ (v1_funct_2 @ X22 @ X20 @ X21)
% 2.44/2.66          | ((X20) = (k1_relset_1 @ X20 @ X21 @ X22))
% 2.44/2.66          | ~ (zip_tseitin_1 @ X22 @ X21 @ X20))),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.44/2.66  thf('26', plain,
% 2.44/2.66      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 2.44/2.66        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 2.44/2.66      inference('sup-', [status(thm)], ['24', '25'])).
% 2.44/2.66  thf(zf_stmt_2, axiom,
% 2.44/2.66    (![B:$i,A:$i]:
% 2.44/2.66     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.44/2.66       ( zip_tseitin_0 @ B @ A ) ))).
% 2.44/2.66  thf('27', plain,
% 2.44/2.66      (![X18 : $i, X19 : $i]:
% 2.44/2.66         ((zip_tseitin_0 @ X18 @ X19) | ((X18) = (k1_xboole_0)))),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.44/2.66  thf('28', plain,
% 2.44/2.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.44/2.66  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.44/2.66  thf(zf_stmt_5, axiom,
% 2.44/2.66    (![A:$i,B:$i,C:$i]:
% 2.44/2.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.44/2.66       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.44/2.66         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.44/2.66           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.44/2.66             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.44/2.66  thf('29', plain,
% 2.44/2.66      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.44/2.66         (~ (zip_tseitin_0 @ X23 @ X24)
% 2.44/2.66          | (zip_tseitin_1 @ X25 @ X23 @ X24)
% 2.44/2.66          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23))))),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.44/2.66  thf('30', plain,
% 2.44/2.66      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 2.44/2.66      inference('sup-', [status(thm)], ['28', '29'])).
% 2.44/2.66  thf('31', plain,
% 2.44/2.66      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 2.44/2.66      inference('sup-', [status(thm)], ['27', '30'])).
% 2.44/2.66  thf('32', plain, (((sk_A) != (k1_xboole_0))),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('33', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 2.44/2.66      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 2.44/2.66  thf('34', plain,
% 2.44/2.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf(redefinition_k1_relset_1, axiom,
% 2.44/2.66    (![A:$i,B:$i,C:$i]:
% 2.44/2.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.44/2.66       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.44/2.66  thf('35', plain,
% 2.44/2.66      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.44/2.66         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 2.44/2.66          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 2.44/2.66      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.44/2.66  thf('36', plain,
% 2.44/2.66      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 2.44/2.66      inference('sup-', [status(thm)], ['34', '35'])).
% 2.44/2.66  thf('37', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 2.44/2.66      inference('demod', [status(thm)], ['26', '33', '36'])).
% 2.44/2.66  thf('38', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('39', plain,
% 2.44/2.66      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.44/2.66         (~ (v1_funct_2 @ X22 @ X20 @ X21)
% 2.44/2.66          | ((X20) = (k1_relset_1 @ X20 @ X21 @ X22))
% 2.44/2.66          | ~ (zip_tseitin_1 @ X22 @ X21 @ X20))),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.44/2.66  thf('40', plain,
% 2.44/2.66      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 2.44/2.66        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 2.44/2.66      inference('sup-', [status(thm)], ['38', '39'])).
% 2.44/2.66  thf('41', plain,
% 2.44/2.66      (![X18 : $i, X19 : $i]:
% 2.44/2.66         ((zip_tseitin_0 @ X18 @ X19) | ((X18) = (k1_xboole_0)))),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.44/2.66  thf('42', plain,
% 2.44/2.66      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('43', plain,
% 2.44/2.66      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.44/2.66         (~ (zip_tseitin_0 @ X23 @ X24)
% 2.44/2.66          | (zip_tseitin_1 @ X25 @ X23 @ X24)
% 2.44/2.66          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23))))),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.44/2.66  thf('44', plain,
% 2.44/2.66      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 2.44/2.66      inference('sup-', [status(thm)], ['42', '43'])).
% 2.44/2.66  thf('45', plain,
% 2.44/2.66      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 2.44/2.66      inference('sup-', [status(thm)], ['41', '44'])).
% 2.44/2.66  thf('46', plain, (((sk_B) != (k1_xboole_0))),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('47', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 2.44/2.66      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 2.44/2.66  thf('48', plain,
% 2.44/2.66      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('49', plain,
% 2.44/2.66      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.44/2.66         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 2.44/2.66          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 2.44/2.66      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.44/2.66  thf('50', plain,
% 2.44/2.66      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 2.44/2.66      inference('sup-', [status(thm)], ['48', '49'])).
% 2.44/2.66  thf('51', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 2.44/2.66      inference('demod', [status(thm)], ['40', '47', '50'])).
% 2.44/2.66  thf(t63_funct_1, axiom,
% 2.44/2.66    (![A:$i]:
% 2.44/2.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.44/2.66       ( ![B:$i]:
% 2.44/2.66         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.44/2.66           ( ( ( v2_funct_1 @ A ) & 
% 2.44/2.66               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 2.44/2.66               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 2.44/2.66             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.44/2.66  thf('52', plain,
% 2.44/2.66      (![X9 : $i, X10 : $i]:
% 2.44/2.66         (~ (v1_relat_1 @ X9)
% 2.44/2.66          | ~ (v1_funct_1 @ X9)
% 2.44/2.66          | ((X9) = (k2_funct_1 @ X10))
% 2.44/2.66          | ((k5_relat_1 @ X10 @ X9) != (k6_relat_1 @ (k1_relat_1 @ X10)))
% 2.44/2.66          | ((k2_relat_1 @ X10) != (k1_relat_1 @ X9))
% 2.44/2.66          | ~ (v2_funct_1 @ X10)
% 2.44/2.66          | ~ (v1_funct_1 @ X10)
% 2.44/2.66          | ~ (v1_relat_1 @ X10))),
% 2.44/2.66      inference('cnf', [status(esa)], [t63_funct_1])).
% 2.44/2.66  thf(redefinition_k6_partfun1, axiom,
% 2.44/2.66    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.44/2.66  thf('53', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 2.44/2.66      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.44/2.66  thf('54', plain,
% 2.44/2.66      (![X9 : $i, X10 : $i]:
% 2.44/2.66         (~ (v1_relat_1 @ X9)
% 2.44/2.66          | ~ (v1_funct_1 @ X9)
% 2.44/2.66          | ((X9) = (k2_funct_1 @ X10))
% 2.44/2.66          | ((k5_relat_1 @ X10 @ X9) != (k6_partfun1 @ (k1_relat_1 @ X10)))
% 2.44/2.66          | ((k2_relat_1 @ X10) != (k1_relat_1 @ X9))
% 2.44/2.66          | ~ (v2_funct_1 @ X10)
% 2.44/2.66          | ~ (v1_funct_1 @ X10)
% 2.44/2.66          | ~ (v1_relat_1 @ X10))),
% 2.44/2.66      inference('demod', [status(thm)], ['52', '53'])).
% 2.44/2.66  thf('55', plain,
% 2.44/2.66      (![X0 : $i]:
% 2.44/2.66         (((k5_relat_1 @ sk_C @ X0) != (k6_partfun1 @ sk_A))
% 2.44/2.66          | ~ (v1_relat_1 @ sk_C)
% 2.44/2.66          | ~ (v1_funct_1 @ sk_C)
% 2.44/2.66          | ~ (v2_funct_1 @ sk_C)
% 2.44/2.66          | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ X0))
% 2.44/2.66          | ((X0) = (k2_funct_1 @ sk_C))
% 2.44/2.66          | ~ (v1_funct_1 @ X0)
% 2.44/2.66          | ~ (v1_relat_1 @ X0))),
% 2.44/2.66      inference('sup-', [status(thm)], ['51', '54'])).
% 2.44/2.66  thf('56', plain,
% 2.44/2.66      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf(cc2_relat_1, axiom,
% 2.44/2.66    (![A:$i]:
% 2.44/2.66     ( ( v1_relat_1 @ A ) =>
% 2.44/2.66       ( ![B:$i]:
% 2.44/2.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.44/2.66  thf('57', plain,
% 2.44/2.66      (![X0 : $i, X1 : $i]:
% 2.44/2.66         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 2.44/2.66          | (v1_relat_1 @ X0)
% 2.44/2.66          | ~ (v1_relat_1 @ X1))),
% 2.44/2.66      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.44/2.66  thf('58', plain,
% 2.44/2.66      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 2.44/2.66      inference('sup-', [status(thm)], ['56', '57'])).
% 2.44/2.66  thf(fc6_relat_1, axiom,
% 2.44/2.66    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.44/2.66  thf('59', plain,
% 2.44/2.66      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 2.44/2.66      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.44/2.66  thf('60', plain, ((v1_relat_1 @ sk_C)),
% 2.44/2.66      inference('demod', [status(thm)], ['58', '59'])).
% 2.44/2.66  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('62', plain, ((v2_funct_1 @ sk_C)),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('63', plain,
% 2.44/2.66      (![X0 : $i]:
% 2.44/2.66         (((k5_relat_1 @ sk_C @ X0) != (k6_partfun1 @ sk_A))
% 2.44/2.66          | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ X0))
% 2.44/2.66          | ((X0) = (k2_funct_1 @ sk_C))
% 2.44/2.66          | ~ (v1_funct_1 @ X0)
% 2.44/2.66          | ~ (v1_relat_1 @ X0))),
% 2.44/2.66      inference('demod', [status(thm)], ['55', '60', '61', '62'])).
% 2.44/2.66  thf('64', plain,
% 2.44/2.66      ((((k2_relat_1 @ sk_C) != (sk_B))
% 2.44/2.66        | ~ (v1_relat_1 @ sk_D)
% 2.44/2.66        | ~ (v1_funct_1 @ sk_D)
% 2.44/2.66        | ((sk_D) = (k2_funct_1 @ sk_C))
% 2.44/2.66        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_partfun1 @ sk_A)))),
% 2.44/2.66      inference('sup-', [status(thm)], ['37', '63'])).
% 2.44/2.66  thf('65', plain,
% 2.44/2.66      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('66', plain,
% 2.44/2.66      (![X0 : $i, X1 : $i]:
% 2.44/2.66         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 2.44/2.66          | (v1_relat_1 @ X0)
% 2.44/2.66          | ~ (v1_relat_1 @ X1))),
% 2.44/2.66      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.44/2.66  thf('67', plain,
% 2.44/2.66      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 2.44/2.66      inference('sup-', [status(thm)], ['65', '66'])).
% 2.44/2.66  thf('68', plain,
% 2.44/2.66      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 2.44/2.66      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.44/2.66  thf('69', plain, ((v1_relat_1 @ sk_D)),
% 2.44/2.66      inference('demod', [status(thm)], ['67', '68'])).
% 2.44/2.66  thf('70', plain, ((v1_funct_1 @ sk_D)),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('71', plain,
% 2.44/2.66      ((((k2_relat_1 @ sk_C) != (sk_B))
% 2.44/2.66        | ((sk_D) = (k2_funct_1 @ sk_C))
% 2.44/2.66        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_partfun1 @ sk_A)))),
% 2.44/2.66      inference('demod', [status(thm)], ['64', '69', '70'])).
% 2.44/2.66  thf('72', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('73', plain,
% 2.44/2.66      ((((k2_relat_1 @ sk_C) != (sk_B))
% 2.44/2.66        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_partfun1 @ sk_A)))),
% 2.44/2.66      inference('simplify_reflect-', [status(thm)], ['71', '72'])).
% 2.44/2.66  thf(t61_funct_1, axiom,
% 2.44/2.66    (![A:$i]:
% 2.44/2.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.44/2.66       ( ( v2_funct_1 @ A ) =>
% 2.44/2.66         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 2.44/2.66             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 2.44/2.66           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 2.44/2.66             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 2.44/2.66  thf('74', plain,
% 2.44/2.66      (![X8 : $i]:
% 2.44/2.66         (~ (v2_funct_1 @ X8)
% 2.44/2.66          | ((k5_relat_1 @ (k2_funct_1 @ X8) @ X8)
% 2.44/2.66              = (k6_relat_1 @ (k2_relat_1 @ X8)))
% 2.44/2.66          | ~ (v1_funct_1 @ X8)
% 2.44/2.66          | ~ (v1_relat_1 @ X8))),
% 2.44/2.66      inference('cnf', [status(esa)], [t61_funct_1])).
% 2.44/2.66  thf('75', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 2.44/2.66      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.44/2.66  thf('76', plain,
% 2.44/2.66      (![X8 : $i]:
% 2.44/2.66         (~ (v2_funct_1 @ X8)
% 2.44/2.66          | ((k5_relat_1 @ (k2_funct_1 @ X8) @ X8)
% 2.44/2.66              = (k6_partfun1 @ (k2_relat_1 @ X8)))
% 2.44/2.66          | ~ (v1_funct_1 @ X8)
% 2.44/2.66          | ~ (v1_relat_1 @ X8))),
% 2.44/2.66      inference('demod', [status(thm)], ['74', '75'])).
% 2.44/2.66  thf('77', plain,
% 2.44/2.66      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf(t35_funct_2, axiom,
% 2.44/2.66    (![A:$i,B:$i,C:$i]:
% 2.44/2.66     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.44/2.66         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.44/2.66       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 2.44/2.66         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.44/2.66           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 2.44/2.66             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 2.44/2.66  thf('78', plain,
% 2.44/2.66      (![X41 : $i, X42 : $i, X43 : $i]:
% 2.44/2.66         (((X41) = (k1_xboole_0))
% 2.44/2.66          | ~ (v1_funct_1 @ X42)
% 2.44/2.66          | ~ (v1_funct_2 @ X42 @ X43 @ X41)
% 2.44/2.66          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X41)))
% 2.44/2.66          | ((k5_relat_1 @ (k2_funct_1 @ X42) @ X42) = (k6_partfun1 @ X41))
% 2.44/2.66          | ~ (v2_funct_1 @ X42)
% 2.44/2.66          | ((k2_relset_1 @ X43 @ X41 @ X42) != (X41)))),
% 2.44/2.66      inference('cnf', [status(esa)], [t35_funct_2])).
% 2.44/2.66  thf('79', plain,
% 2.44/2.66      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 2.44/2.66        | ~ (v2_funct_1 @ sk_C)
% 2.44/2.66        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 2.44/2.66        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.44/2.66        | ~ (v1_funct_1 @ sk_C)
% 2.44/2.66        | ((sk_B) = (k1_xboole_0)))),
% 2.44/2.66      inference('sup-', [status(thm)], ['77', '78'])).
% 2.44/2.66  thf('80', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('81', plain, ((v2_funct_1 @ sk_C)),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('82', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('83', plain, ((v1_funct_1 @ sk_C)),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('84', plain,
% 2.44/2.66      ((((sk_B) != (sk_B))
% 2.44/2.66        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 2.44/2.66        | ((sk_B) = (k1_xboole_0)))),
% 2.44/2.66      inference('demod', [status(thm)], ['79', '80', '81', '82', '83'])).
% 2.44/2.66  thf('85', plain,
% 2.44/2.66      ((((sk_B) = (k1_xboole_0))
% 2.44/2.66        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 2.44/2.66      inference('simplify', [status(thm)], ['84'])).
% 2.44/2.66  thf('86', plain, (((sk_B) != (k1_xboole_0))),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('87', plain,
% 2.44/2.66      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 2.44/2.66      inference('simplify_reflect-', [status(thm)], ['85', '86'])).
% 2.44/2.66  thf('88', plain,
% 2.44/2.66      ((((k6_partfun1 @ (k2_relat_1 @ sk_C)) = (k6_partfun1 @ sk_B))
% 2.44/2.66        | ~ (v1_relat_1 @ sk_C)
% 2.44/2.66        | ~ (v1_funct_1 @ sk_C)
% 2.44/2.66        | ~ (v2_funct_1 @ sk_C))),
% 2.44/2.66      inference('sup+', [status(thm)], ['76', '87'])).
% 2.44/2.66  thf('89', plain, ((v1_relat_1 @ sk_C)),
% 2.44/2.66      inference('demod', [status(thm)], ['58', '59'])).
% 2.44/2.66  thf('90', plain, ((v1_funct_1 @ sk_C)),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('91', plain, ((v2_funct_1 @ sk_C)),
% 2.44/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.44/2.66  thf('92', plain,
% 2.44/2.66      (((k6_partfun1 @ (k2_relat_1 @ sk_C)) = (k6_partfun1 @ sk_B))),
% 2.44/2.66      inference('demod', [status(thm)], ['88', '89', '90', '91'])).
% 2.44/2.66  thf(t71_relat_1, axiom,
% 2.44/2.66    (![A:$i]:
% 2.44/2.66     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 2.44/2.66       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 2.44/2.66  thf('93', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 2.44/2.66      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.44/2.66  thf('94', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 2.44/2.66      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.44/2.66  thf('95', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 2.44/2.66      inference('demod', [status(thm)], ['93', '94'])).
% 2.44/2.66  thf('96', plain,
% 2.44/2.66      (((k1_relat_1 @ (k6_partfun1 @ sk_B)) = (k2_relat_1 @ sk_C))),
% 2.44/2.66      inference('sup+', [status(thm)], ['92', '95'])).
% 2.44/2.66  thf('97', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 2.44/2.66      inference('demod', [status(thm)], ['93', '94'])).
% 2.44/2.66  thf('98', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 2.44/2.66      inference('demod', [status(thm)], ['96', '97'])).
% 2.44/2.66  thf('99', plain,
% 2.44/2.66      ((((sk_B) != (sk_B))
% 2.44/2.66        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_partfun1 @ sk_A)))),
% 2.44/2.66      inference('demod', [status(thm)], ['73', '98'])).
% 2.44/2.66  thf('100', plain, (((k5_relat_1 @ sk_C @ sk_D) != (k6_partfun1 @ sk_A))),
% 2.44/2.66      inference('simplify', [status(thm)], ['99'])).
% 2.44/2.66  thf('101', plain, ($false),
% 2.44/2.66      inference('simplify_reflect-', [status(thm)], ['23', '100'])).
% 2.44/2.66  
% 2.44/2.66  % SZS output end Refutation
% 2.44/2.66  
% 2.44/2.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

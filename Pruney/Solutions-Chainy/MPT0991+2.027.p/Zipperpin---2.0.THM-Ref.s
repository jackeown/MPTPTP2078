%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.phdPLtZuYq

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:33 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 329 expanded)
%              Number of leaves         :   50 ( 117 expanded)
%              Depth                    :   14
%              Number of atoms          : 1079 (6573 expanded)
%              Number of equality atoms :   44 ( 196 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t25_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_2 @ C @ A @ B )
        & ( v1_funct_1 @ C ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( v2_funct_1 @ C )
        <=> ! [D: $i,E: $i] :
              ( ( ( ( k1_funct_1 @ C @ D )
                  = ( k1_funct_1 @ C @ E ) )
                & ( r2_hidden @ E @ A )
                & ( r2_hidden @ D @ A ) )
             => ( D = E ) ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t37_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ~ ( ( B != k1_xboole_0 )
          & ? [D: $i] :
              ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
              & ( v1_funct_2 @ D @ B @ A )
              & ( v1_funct_1 @ D ) )
          & ~ ( v2_funct_1 @ C ) ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ~ ( ( B != k1_xboole_0 )
            & ? [D: $i] :
                ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
                & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
                & ( v1_funct_2 @ D @ B @ A )
                & ( v1_funct_1 @ D ) )
            & ~ ( v2_funct_1 @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t37_funct_2])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(zf_stmt_2,type,(
    zip_tseitin_2: $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ A )
     => ( ( v2_funct_1 @ C )
      <=> ! [D: $i,E: $i] :
            ( ( zip_tseitin_1 @ E @ D @ C @ A )
           => ( D = E ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [E: $i,D: $i,C: $i,A: $i] :
      ( ( zip_tseitin_1 @ E @ D @ C @ A )
    <=> ( ( r2_hidden @ D @ A )
        & ( r2_hidden @ E @ A )
        & ( ( k1_funct_1 @ C @ D )
          = ( k1_funct_1 @ C @ E ) ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( zip_tseitin_0 @ B @ A )
       => ( zip_tseitin_2 @ C @ A ) ) ) )).

thf('2',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( zip_tseitin_0 @ X44 @ X45 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X45 @ X44 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) )
      | ( zip_tseitin_2 @ X46 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('3',plain,
    ( ( zip_tseitin_2 @ sk_C @ sk_A )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('5',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,
    ( ( zip_tseitin_2 @ sk_C @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('9',plain,(
    zip_tseitin_2 @ sk_C @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X40: $i,X41: $i] :
      ( ( zip_tseitin_1 @ ( sk_E @ X40 @ X41 ) @ ( sk_D @ X40 @ X41 ) @ X41 @ X40 )
      | ( v2_funct_1 @ X41 )
      | ~ ( zip_tseitin_2 @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('11',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( zip_tseitin_1 @ ( sk_E @ sk_A @ sk_C ) @ ( sk_D @ sk_A @ sk_C ) @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('13',plain,(
    zip_tseitin_1 @ ( sk_E @ sk_A @ sk_C ) @ ( sk_D @ sk_A @ sk_C ) @ sk_C @ sk_A ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( r2_hidden @ X35 @ X36 )
      | ~ ( zip_tseitin_1 @ X37 @ X35 @ X38 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('15',plain,(
    r2_hidden @ ( sk_D @ sk_A @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('18',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( ( k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29 )
        = ( k5_relat_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( v1_funct_1 @ sk_D_1 )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D_1 )
      = ( k5_relat_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('24',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D_1 )
    = ( k5_relat_1 @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t26_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
           => ( ( ( C = k1_xboole_0 )
                & ( B != k1_xboole_0 ) )
              | ( v2_funct_1 @ D ) ) ) ) ) )).

thf('26',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X50 @ X48 @ X48 @ X49 @ X51 @ X47 ) )
      | ( v2_funct_1 @ X51 )
      | ( X49 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X48 ) ) )
      | ~ ( v1_funct_2 @ X51 @ X50 @ X48 )
      | ~ ( v1_funct_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D_1 ) )
      | ~ ( v1_funct_2 @ sk_D_1 @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('29',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D_1 ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('33',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('34',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('35',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D_1 ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('36',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('37',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('39',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D_1 )
    = ( k5_relat_1 @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('40',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D_1 ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('43',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X21 @ X22 @ X24 @ X25 @ X20 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ( v1_funct_1 @ sk_D_1 )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('49',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D_1 )
    = ( k5_relat_1 @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('50',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('51',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( X15 = X18 )
      | ~ ( r2_relset_1 @ X16 @ X17 @ X15 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D_1 ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D_1 )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D_1 )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','52'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('54',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('55',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('56',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D_1 )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['53','56'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('58',plain,(
    ! [X14: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('59',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('60',plain,(
    ! [X14: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X14 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['37','57','60'])).

thf('62',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['37','57','60'])).

thf('63',plain,(
    r2_hidden @ ( sk_D @ k1_xboole_0 @ sk_C ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['15','61','62'])).

thf(t111_relat_1,axiom,(
    ! [A: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('64',plain,(
    ! [X10: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t111_relat_1])).

thf(t86_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('65',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X12 ) ) )
      | ( r2_hidden @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('67',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('68',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('69',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('70',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('71',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('72',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['70','71'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('73',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('74',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['66','67','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_D @ k1_xboole_0 @ sk_C ) @ X0 ) ),
    inference('sup-',[status(thm)],['63','77'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('80',plain,(
    $false ),
    inference('sup-',[status(thm)],['78','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.phdPLtZuYq
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:44:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.46/1.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.46/1.64  % Solved by: fo/fo7.sh
% 1.46/1.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.46/1.64  % done 1238 iterations in 1.179s
% 1.46/1.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.46/1.64  % SZS output start Refutation
% 1.46/1.64  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.46/1.64  thf(sk_A_type, type, sk_A: $i).
% 1.46/1.64  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.46/1.64  thf(sk_E_type, type, sk_E: $i > $i > $i).
% 1.46/1.64  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 1.46/1.64  thf(sk_C_type, type, sk_C: $i).
% 1.46/1.64  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.46/1.64  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 1.46/1.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.46/1.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.46/1.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.46/1.64  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.46/1.64  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.46/1.64  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.46/1.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.46/1.64  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.46/1.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.46/1.64  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.46/1.64  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $o).
% 1.46/1.64  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.46/1.64  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.46/1.64  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.46/1.64  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.46/1.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.46/1.64  thf(sk_B_type, type, sk_B: $i).
% 1.46/1.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.46/1.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.46/1.64  thf(t25_funct_2, axiom,
% 1.46/1.64    (![A:$i,B:$i,C:$i]:
% 1.46/1.64     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.46/1.64         ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) =>
% 1.46/1.64       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.46/1.64         ( ( v2_funct_1 @ C ) <=>
% 1.46/1.64           ( ![D:$i,E:$i]:
% 1.46/1.64             ( ( ( ( k1_funct_1 @ C @ D ) = ( k1_funct_1 @ C @ E ) ) & 
% 1.46/1.64                 ( r2_hidden @ E @ A ) & ( r2_hidden @ D @ A ) ) =>
% 1.46/1.64               ( ( D ) = ( E ) ) ) ) ) ) ))).
% 1.46/1.64  thf(zf_stmt_0, axiom,
% 1.46/1.64    (![B:$i,A:$i]:
% 1.46/1.64     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.46/1.64       ( zip_tseitin_0 @ B @ A ) ))).
% 1.46/1.64  thf('0', plain,
% 1.46/1.64      (![X33 : $i, X34 : $i]:
% 1.46/1.64         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 1.46/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.64  thf(t37_funct_2, conjecture,
% 1.46/1.64    (![A:$i,B:$i,C:$i]:
% 1.46/1.64     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.46/1.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.46/1.64       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.46/1.64            ( ?[D:$i]:
% 1.46/1.64              ( ( r2_relset_1 @
% 1.46/1.64                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.46/1.64                  ( k6_partfun1 @ A ) ) & 
% 1.46/1.64                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) & 
% 1.46/1.64                ( v1_funct_2 @ D @ B @ A ) & ( v1_funct_1 @ D ) ) ) & 
% 1.46/1.64            ( ~( v2_funct_1 @ C ) ) ) ) ))).
% 1.46/1.64  thf(zf_stmt_1, negated_conjecture,
% 1.46/1.64    (~( ![A:$i,B:$i,C:$i]:
% 1.46/1.64        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.46/1.64            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.46/1.64          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.46/1.64               ( ?[D:$i]:
% 1.46/1.64                 ( ( r2_relset_1 @
% 1.46/1.64                     A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.46/1.64                     ( k6_partfun1 @ A ) ) & 
% 1.46/1.64                   ( m1_subset_1 @
% 1.46/1.64                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) & 
% 1.46/1.64                   ( v1_funct_2 @ D @ B @ A ) & ( v1_funct_1 @ D ) ) ) & 
% 1.46/1.64               ( ~( v2_funct_1 @ C ) ) ) ) ) )),
% 1.46/1.64    inference('cnf.neg', [status(esa)], [t37_funct_2])).
% 1.46/1.64  thf('1', plain,
% 1.46/1.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.46/1.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.46/1.64  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $o).
% 1.46/1.64  thf(zf_stmt_3, axiom,
% 1.46/1.64    (![C:$i,A:$i]:
% 1.46/1.64     ( ( zip_tseitin_2 @ C @ A ) =>
% 1.46/1.64       ( ( v2_funct_1 @ C ) <=>
% 1.46/1.64         ( ![D:$i,E:$i]:
% 1.46/1.64           ( ( zip_tseitin_1 @ E @ D @ C @ A ) => ( ( D ) = ( E ) ) ) ) ) ))).
% 1.46/1.64  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 1.46/1.64  thf(zf_stmt_5, axiom,
% 1.46/1.64    (![E:$i,D:$i,C:$i,A:$i]:
% 1.46/1.64     ( ( zip_tseitin_1 @ E @ D @ C @ A ) <=>
% 1.46/1.64       ( ( r2_hidden @ D @ A ) & ( r2_hidden @ E @ A ) & 
% 1.46/1.64         ( ( k1_funct_1 @ C @ D ) = ( k1_funct_1 @ C @ E ) ) ) ))).
% 1.46/1.64  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $o).
% 1.46/1.64  thf(zf_stmt_7, axiom,
% 1.46/1.64    (![A:$i,B:$i,C:$i]:
% 1.46/1.64     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.46/1.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.46/1.64       ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_2 @ C @ A ) ) ))).
% 1.46/1.64  thf('2', plain,
% 1.46/1.64      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.46/1.64         (~ (zip_tseitin_0 @ X44 @ X45)
% 1.46/1.64          | ~ (v1_funct_1 @ X46)
% 1.46/1.64          | ~ (v1_funct_2 @ X46 @ X45 @ X44)
% 1.46/1.64          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 1.46/1.64          | (zip_tseitin_2 @ X46 @ X45))),
% 1.46/1.64      inference('cnf', [status(esa)], [zf_stmt_7])).
% 1.46/1.64  thf('3', plain,
% 1.46/1.64      (((zip_tseitin_2 @ sk_C @ sk_A)
% 1.46/1.64        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.46/1.64        | ~ (v1_funct_1 @ sk_C)
% 1.46/1.64        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.46/1.64      inference('sup-', [status(thm)], ['1', '2'])).
% 1.46/1.64  thf('4', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.46/1.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.46/1.64  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 1.46/1.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.46/1.64  thf('6', plain,
% 1.46/1.64      (((zip_tseitin_2 @ sk_C @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.46/1.64      inference('demod', [status(thm)], ['3', '4', '5'])).
% 1.46/1.64  thf('7', plain, ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_2 @ sk_C @ sk_A))),
% 1.46/1.64      inference('sup-', [status(thm)], ['0', '6'])).
% 1.46/1.64  thf('8', plain, (((sk_B) != (k1_xboole_0))),
% 1.46/1.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.46/1.64  thf('9', plain, ((zip_tseitin_2 @ sk_C @ sk_A)),
% 1.46/1.64      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 1.46/1.64  thf('10', plain,
% 1.46/1.64      (![X40 : $i, X41 : $i]:
% 1.46/1.64         ((zip_tseitin_1 @ (sk_E @ X40 @ X41) @ (sk_D @ X40 @ X41) @ X41 @ X40)
% 1.46/1.64          | (v2_funct_1 @ X41)
% 1.46/1.64          | ~ (zip_tseitin_2 @ X41 @ X40))),
% 1.46/1.64      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.46/1.64  thf('11', plain,
% 1.46/1.64      (((v2_funct_1 @ sk_C)
% 1.46/1.64        | (zip_tseitin_1 @ (sk_E @ sk_A @ sk_C) @ (sk_D @ sk_A @ sk_C) @ 
% 1.46/1.64           sk_C @ sk_A))),
% 1.46/1.64      inference('sup-', [status(thm)], ['9', '10'])).
% 1.46/1.64  thf('12', plain, (~ (v2_funct_1 @ sk_C)),
% 1.46/1.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.46/1.64  thf('13', plain,
% 1.46/1.64      ((zip_tseitin_1 @ (sk_E @ sk_A @ sk_C) @ (sk_D @ sk_A @ sk_C) @ sk_C @ 
% 1.46/1.64        sk_A)),
% 1.46/1.64      inference('clc', [status(thm)], ['11', '12'])).
% 1.46/1.64  thf('14', plain,
% 1.46/1.64      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.46/1.64         ((r2_hidden @ X35 @ X36) | ~ (zip_tseitin_1 @ X37 @ X35 @ X38 @ X36))),
% 1.46/1.64      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.46/1.64  thf('15', plain, ((r2_hidden @ (sk_D @ sk_A @ sk_C) @ sk_A)),
% 1.46/1.64      inference('sup-', [status(thm)], ['13', '14'])).
% 1.46/1.64  thf('16', plain,
% 1.46/1.64      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.46/1.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.46/1.64  thf('17', plain,
% 1.46/1.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.46/1.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.46/1.64  thf(redefinition_k1_partfun1, axiom,
% 1.46/1.64    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.46/1.64     ( ( ( v1_funct_1 @ E ) & 
% 1.46/1.64         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.46/1.64         ( v1_funct_1 @ F ) & 
% 1.46/1.64         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.46/1.64       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.46/1.64  thf('18', plain,
% 1.46/1.64      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.46/1.64         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 1.46/1.64          | ~ (v1_funct_1 @ X26)
% 1.46/1.64          | ~ (v1_funct_1 @ X29)
% 1.46/1.64          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.46/1.64          | ((k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29)
% 1.46/1.64              = (k5_relat_1 @ X26 @ X29)))),
% 1.46/1.64      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.46/1.64  thf('19', plain,
% 1.46/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.46/1.64         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.46/1.64            = (k5_relat_1 @ sk_C @ X0))
% 1.46/1.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.46/1.64          | ~ (v1_funct_1 @ X0)
% 1.46/1.64          | ~ (v1_funct_1 @ sk_C))),
% 1.46/1.64      inference('sup-', [status(thm)], ['17', '18'])).
% 1.46/1.64  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 1.46/1.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.46/1.64  thf('21', plain,
% 1.46/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.46/1.64         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.46/1.64            = (k5_relat_1 @ sk_C @ X0))
% 1.46/1.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.46/1.64          | ~ (v1_funct_1 @ X0))),
% 1.46/1.64      inference('demod', [status(thm)], ['19', '20'])).
% 1.46/1.64  thf('22', plain,
% 1.46/1.64      ((~ (v1_funct_1 @ sk_D_1)
% 1.46/1.64        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D_1)
% 1.46/1.64            = (k5_relat_1 @ sk_C @ sk_D_1)))),
% 1.46/1.64      inference('sup-', [status(thm)], ['16', '21'])).
% 1.46/1.64  thf('23', plain, ((v1_funct_1 @ sk_D_1)),
% 1.46/1.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.46/1.64  thf('24', plain,
% 1.46/1.64      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D_1)
% 1.46/1.64         = (k5_relat_1 @ sk_C @ sk_D_1))),
% 1.46/1.64      inference('demod', [status(thm)], ['22', '23'])).
% 1.46/1.64  thf('25', plain,
% 1.46/1.64      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.46/1.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.46/1.64  thf(t26_funct_2, axiom,
% 1.46/1.64    (![A:$i,B:$i,C:$i,D:$i]:
% 1.46/1.64     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.46/1.64         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.46/1.64       ( ![E:$i]:
% 1.46/1.64         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.46/1.64             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.46/1.64           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 1.46/1.64             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 1.46/1.64               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 1.46/1.64  thf('26', plain,
% 1.46/1.64      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 1.46/1.64         (~ (v1_funct_1 @ X47)
% 1.46/1.64          | ~ (v1_funct_2 @ X47 @ X48 @ X49)
% 1.46/1.64          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 1.46/1.64          | ~ (v2_funct_1 @ (k1_partfun1 @ X50 @ X48 @ X48 @ X49 @ X51 @ X47))
% 1.46/1.64          | (v2_funct_1 @ X51)
% 1.46/1.64          | ((X49) = (k1_xboole_0))
% 1.46/1.64          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X48)))
% 1.46/1.64          | ~ (v1_funct_2 @ X51 @ X50 @ X48)
% 1.46/1.64          | ~ (v1_funct_1 @ X51))),
% 1.46/1.64      inference('cnf', [status(esa)], [t26_funct_2])).
% 1.46/1.64  thf('27', plain,
% 1.46/1.64      (![X0 : $i, X1 : $i]:
% 1.46/1.64         (~ (v1_funct_1 @ X0)
% 1.46/1.64          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.46/1.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.46/1.64          | ((sk_A) = (k1_xboole_0))
% 1.46/1.64          | (v2_funct_1 @ X0)
% 1.46/1.64          | ~ (v2_funct_1 @ 
% 1.46/1.64               (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D_1))
% 1.46/1.64          | ~ (v1_funct_2 @ sk_D_1 @ sk_B @ sk_A)
% 1.46/1.64          | ~ (v1_funct_1 @ sk_D_1))),
% 1.46/1.64      inference('sup-', [status(thm)], ['25', '26'])).
% 1.46/1.64  thf('28', plain, ((v1_funct_2 @ sk_D_1 @ sk_B @ sk_A)),
% 1.46/1.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.46/1.64  thf('29', plain, ((v1_funct_1 @ sk_D_1)),
% 1.46/1.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.46/1.64  thf('30', plain,
% 1.46/1.64      (![X0 : $i, X1 : $i]:
% 1.46/1.64         (~ (v1_funct_1 @ X0)
% 1.46/1.64          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.46/1.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.46/1.64          | ((sk_A) = (k1_xboole_0))
% 1.46/1.64          | (v2_funct_1 @ X0)
% 1.46/1.64          | ~ (v2_funct_1 @ 
% 1.46/1.64               (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D_1)))),
% 1.46/1.64      inference('demod', [status(thm)], ['27', '28', '29'])).
% 1.46/1.64  thf('31', plain,
% 1.46/1.64      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D_1))
% 1.46/1.64        | (v2_funct_1 @ sk_C)
% 1.46/1.64        | ((sk_A) = (k1_xboole_0))
% 1.46/1.64        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.46/1.64        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.46/1.64        | ~ (v1_funct_1 @ sk_C))),
% 1.46/1.64      inference('sup-', [status(thm)], ['24', '30'])).
% 1.46/1.64  thf('32', plain,
% 1.46/1.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.46/1.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.46/1.64  thf('33', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.46/1.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.46/1.64  thf('34', plain, ((v1_funct_1 @ sk_C)),
% 1.46/1.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.46/1.64  thf('35', plain,
% 1.46/1.64      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D_1))
% 1.46/1.64        | (v2_funct_1 @ sk_C)
% 1.46/1.64        | ((sk_A) = (k1_xboole_0)))),
% 1.46/1.64      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 1.46/1.64  thf('36', plain, (~ (v2_funct_1 @ sk_C)),
% 1.46/1.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.46/1.64  thf('37', plain,
% 1.46/1.64      ((((sk_A) = (k1_xboole_0))
% 1.46/1.64        | ~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D_1)))),
% 1.46/1.64      inference('clc', [status(thm)], ['35', '36'])).
% 1.46/1.64  thf('38', plain,
% 1.46/1.64      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.46/1.64        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D_1) @ 
% 1.46/1.64        (k6_partfun1 @ sk_A))),
% 1.46/1.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.46/1.64  thf('39', plain,
% 1.46/1.64      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D_1)
% 1.46/1.64         = (k5_relat_1 @ sk_C @ sk_D_1))),
% 1.46/1.64      inference('demod', [status(thm)], ['22', '23'])).
% 1.46/1.64  thf('40', plain,
% 1.46/1.64      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D_1) @ 
% 1.46/1.64        (k6_partfun1 @ sk_A))),
% 1.46/1.64      inference('demod', [status(thm)], ['38', '39'])).
% 1.46/1.64  thf('41', plain,
% 1.46/1.64      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.46/1.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.46/1.64  thf('42', plain,
% 1.46/1.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.46/1.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.46/1.64  thf(dt_k1_partfun1, axiom,
% 1.46/1.64    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.46/1.64     ( ( ( v1_funct_1 @ E ) & 
% 1.46/1.64         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.46/1.64         ( v1_funct_1 @ F ) & 
% 1.46/1.64         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.46/1.64       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.46/1.64         ( m1_subset_1 @
% 1.46/1.64           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.46/1.64           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.46/1.64  thf('43', plain,
% 1.46/1.64      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 1.46/1.64         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 1.46/1.64          | ~ (v1_funct_1 @ X20)
% 1.46/1.64          | ~ (v1_funct_1 @ X23)
% 1.46/1.64          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 1.46/1.64          | (m1_subset_1 @ (k1_partfun1 @ X21 @ X22 @ X24 @ X25 @ X20 @ X23) @ 
% 1.46/1.64             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X25))))),
% 1.46/1.64      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.46/1.64  thf('44', plain,
% 1.46/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.46/1.64         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.46/1.64           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.46/1.64          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.46/1.64          | ~ (v1_funct_1 @ X1)
% 1.46/1.64          | ~ (v1_funct_1 @ sk_C))),
% 1.46/1.64      inference('sup-', [status(thm)], ['42', '43'])).
% 1.46/1.64  thf('45', plain, ((v1_funct_1 @ sk_C)),
% 1.46/1.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.46/1.64  thf('46', plain,
% 1.46/1.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.46/1.64         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.46/1.64           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.46/1.64          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.46/1.64          | ~ (v1_funct_1 @ X1))),
% 1.46/1.64      inference('demod', [status(thm)], ['44', '45'])).
% 1.46/1.64  thf('47', plain,
% 1.46/1.64      ((~ (v1_funct_1 @ sk_D_1)
% 1.46/1.64        | (m1_subset_1 @ 
% 1.46/1.64           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D_1) @ 
% 1.46/1.64           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.46/1.64      inference('sup-', [status(thm)], ['41', '46'])).
% 1.46/1.64  thf('48', plain, ((v1_funct_1 @ sk_D_1)),
% 1.46/1.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.46/1.64  thf('49', plain,
% 1.46/1.64      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D_1)
% 1.46/1.64         = (k5_relat_1 @ sk_C @ sk_D_1))),
% 1.46/1.64      inference('demod', [status(thm)], ['22', '23'])).
% 1.46/1.64  thf('50', plain,
% 1.46/1.64      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D_1) @ 
% 1.46/1.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.46/1.64      inference('demod', [status(thm)], ['47', '48', '49'])).
% 1.46/1.64  thf(redefinition_r2_relset_1, axiom,
% 1.46/1.64    (![A:$i,B:$i,C:$i,D:$i]:
% 1.46/1.64     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.46/1.64         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.46/1.64       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.46/1.64  thf('51', plain,
% 1.46/1.64      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 1.46/1.64         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 1.46/1.64          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 1.46/1.64          | ((X15) = (X18))
% 1.46/1.64          | ~ (r2_relset_1 @ X16 @ X17 @ X15 @ X18))),
% 1.46/1.64      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.46/1.64  thf('52', plain,
% 1.46/1.64      (![X0 : $i]:
% 1.46/1.64         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D_1) @ X0)
% 1.46/1.64          | ((k5_relat_1 @ sk_C @ sk_D_1) = (X0))
% 1.46/1.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.46/1.64      inference('sup-', [status(thm)], ['50', '51'])).
% 1.46/1.64  thf('53', plain,
% 1.46/1.64      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.46/1.64           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.46/1.64        | ((k5_relat_1 @ sk_C @ sk_D_1) = (k6_partfun1 @ sk_A)))),
% 1.46/1.64      inference('sup-', [status(thm)], ['40', '52'])).
% 1.46/1.64  thf(t29_relset_1, axiom,
% 1.46/1.64    (![A:$i]:
% 1.46/1.64     ( m1_subset_1 @
% 1.46/1.64       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.46/1.64  thf('54', plain,
% 1.46/1.64      (![X19 : $i]:
% 1.46/1.64         (m1_subset_1 @ (k6_relat_1 @ X19) @ 
% 1.46/1.64          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))),
% 1.46/1.64      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.46/1.64  thf(redefinition_k6_partfun1, axiom,
% 1.46/1.64    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.46/1.64  thf('55', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 1.46/1.64      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.46/1.64  thf('56', plain,
% 1.46/1.64      (![X19 : $i]:
% 1.46/1.64         (m1_subset_1 @ (k6_partfun1 @ X19) @ 
% 1.46/1.64          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))),
% 1.46/1.64      inference('demod', [status(thm)], ['54', '55'])).
% 1.46/1.64  thf('57', plain, (((k5_relat_1 @ sk_C @ sk_D_1) = (k6_partfun1 @ sk_A))),
% 1.46/1.64      inference('demod', [status(thm)], ['53', '56'])).
% 1.46/1.64  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 1.46/1.64  thf('58', plain, (![X14 : $i]: (v2_funct_1 @ (k6_relat_1 @ X14))),
% 1.46/1.64      inference('cnf', [status(esa)], [t52_funct_1])).
% 1.46/1.64  thf('59', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 1.46/1.64      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.46/1.64  thf('60', plain, (![X14 : $i]: (v2_funct_1 @ (k6_partfun1 @ X14))),
% 1.46/1.64      inference('demod', [status(thm)], ['58', '59'])).
% 1.46/1.64  thf('61', plain, (((sk_A) = (k1_xboole_0))),
% 1.46/1.64      inference('demod', [status(thm)], ['37', '57', '60'])).
% 1.46/1.64  thf('62', plain, (((sk_A) = (k1_xboole_0))),
% 1.46/1.64      inference('demod', [status(thm)], ['37', '57', '60'])).
% 1.46/1.64  thf('63', plain, ((r2_hidden @ (sk_D @ k1_xboole_0 @ sk_C) @ k1_xboole_0)),
% 1.46/1.64      inference('demod', [status(thm)], ['15', '61', '62'])).
% 1.46/1.64  thf(t111_relat_1, axiom,
% 1.46/1.64    (![A:$i]: ( ( k7_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 1.46/1.64  thf('64', plain,
% 1.46/1.64      (![X10 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 1.46/1.64      inference('cnf', [status(esa)], [t111_relat_1])).
% 1.46/1.64  thf(t86_relat_1, axiom,
% 1.46/1.64    (![A:$i,B:$i,C:$i]:
% 1.46/1.64     ( ( v1_relat_1 @ C ) =>
% 1.46/1.64       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 1.46/1.64         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 1.46/1.64  thf('65', plain,
% 1.46/1.64      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.46/1.64         (~ (r2_hidden @ X11 @ (k1_relat_1 @ (k7_relat_1 @ X13 @ X12)))
% 1.46/1.64          | (r2_hidden @ X11 @ X12)
% 1.46/1.64          | ~ (v1_relat_1 @ X13))),
% 1.46/1.64      inference('cnf', [status(esa)], [t86_relat_1])).
% 1.46/1.64  thf('66', plain,
% 1.46/1.64      (![X0 : $i, X1 : $i]:
% 1.46/1.64         (~ (r2_hidden @ X1 @ (k1_relat_1 @ k1_xboole_0))
% 1.46/1.64          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.46/1.64          | (r2_hidden @ X1 @ X0))),
% 1.46/1.64      inference('sup-', [status(thm)], ['64', '65'])).
% 1.46/1.64  thf(t60_relat_1, axiom,
% 1.46/1.64    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 1.46/1.64     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.46/1.64  thf('67', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.46/1.64      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.46/1.64  thf('68', plain,
% 1.46/1.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.46/1.64      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.46/1.64  thf(cc2_relat_1, axiom,
% 1.46/1.64    (![A:$i]:
% 1.46/1.64     ( ( v1_relat_1 @ A ) =>
% 1.46/1.64       ( ![B:$i]:
% 1.46/1.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.46/1.64  thf('69', plain,
% 1.46/1.64      (![X6 : $i, X7 : $i]:
% 1.46/1.64         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 1.46/1.64          | (v1_relat_1 @ X6)
% 1.46/1.64          | ~ (v1_relat_1 @ X7))),
% 1.46/1.64      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.46/1.64  thf('70', plain,
% 1.46/1.64      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 1.46/1.64      inference('sup-', [status(thm)], ['68', '69'])).
% 1.46/1.64  thf(fc6_relat_1, axiom,
% 1.46/1.64    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.46/1.64  thf('71', plain,
% 1.46/1.64      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 1.46/1.64      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.46/1.64  thf('72', plain, ((v1_relat_1 @ sk_C)),
% 1.46/1.64      inference('demod', [status(thm)], ['70', '71'])).
% 1.46/1.64  thf(t4_subset_1, axiom,
% 1.46/1.64    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.46/1.64  thf('73', plain,
% 1.46/1.64      (![X2 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X2))),
% 1.46/1.64      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.46/1.64  thf('74', plain,
% 1.46/1.64      (![X6 : $i, X7 : $i]:
% 1.46/1.64         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 1.46/1.64          | (v1_relat_1 @ X6)
% 1.46/1.64          | ~ (v1_relat_1 @ X7))),
% 1.46/1.64      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.46/1.64  thf('75', plain,
% 1.46/1.64      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 1.46/1.64      inference('sup-', [status(thm)], ['73', '74'])).
% 1.46/1.64  thf('76', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.46/1.64      inference('sup-', [status(thm)], ['72', '75'])).
% 1.46/1.64  thf('77', plain,
% 1.46/1.64      (![X0 : $i, X1 : $i]:
% 1.46/1.64         (~ (r2_hidden @ X1 @ k1_xboole_0) | (r2_hidden @ X1 @ X0))),
% 1.46/1.64      inference('demod', [status(thm)], ['66', '67', '76'])).
% 1.46/1.64  thf('78', plain,
% 1.46/1.64      (![X0 : $i]: (r2_hidden @ (sk_D @ k1_xboole_0 @ sk_C) @ X0)),
% 1.46/1.64      inference('sup-', [status(thm)], ['63', '77'])).
% 1.46/1.64  thf(t152_zfmisc_1, axiom,
% 1.46/1.64    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 1.46/1.64  thf('79', plain,
% 1.46/1.64      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ X0 @ X1))),
% 1.46/1.64      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 1.46/1.64  thf('80', plain, ($false), inference('sup-', [status(thm)], ['78', '79'])).
% 1.46/1.64  
% 1.46/1.64  % SZS output end Refutation
% 1.46/1.64  
% 1.46/1.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5sqzpYtmwV

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:25 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 273 expanded)
%              Number of leaves         :   44 ( 100 expanded)
%              Depth                    :   15
%              Number of atoms          : 1475 (6228 expanded)
%              Number of equality atoms :  105 ( 454 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

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
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( ( k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40 )
        = ( k5_relat_1 @ X37 @ X40 ) ) ) ),
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

thf(dt_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( m1_subset_1 @ ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X10 @ X11 @ X13 @ X14 @ X9 @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relset_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('18',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( ( k4_relset_1 @ X19 @ X20 @ X22 @ X23 @ X18 @ X21 )
        = ( k5_relat_1 @ X18 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','20'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('22',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( X24 = X27 )
      | ~ ( r2_relset_1 @ X25 @ X26 @ X24 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','23'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('25',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('26',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('27',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,(
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

thf('30',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('31',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('32',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('33',plain,(
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

thf('34',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('35',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('40',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('41',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['31','38','41'])).

thf('43',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('45',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('49',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('55',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['45','52','55'])).

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

thf('57',plain,(
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

thf('58',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('59',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( X7
        = ( k2_funct_1 @ X8 ) )
      | ( ( k5_relat_1 @ X8 @ X7 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X8 ) ) )
      | ( ( k2_relat_1 @ X8 )
       != ( k1_relat_1 @ X7 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
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
    inference('sup-',[status(thm)],['56','59'])).

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
       != ( k6_partfun1 @ sk_A ) )
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
     != ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','68'])).

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
     != ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','74','75'])).

thf('77',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != sk_B )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
     != ( k6_partfun1 @ sk_A ) ) ),
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
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_relat_1 @ X6 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
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
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( v2_funct_1 @ X44 )
      | ( ( k2_relset_1 @ X46 @ X45 @ X44 )
       != X45 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X44 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X46 @ X45 )
      | ~ ( v1_funct_1 @ X44 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('90',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( v2_funct_1 @ X44 )
      | ( ( k2_relset_1 @ X46 @ X45 @ X44 )
       != X45 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X44 ) @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X46 @ X45 )
      | ~ ( v1_funct_1 @ X44 ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('101',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('103',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('104',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
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
     != ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','115'])).

thf('117',plain,(
    ( k5_relat_1 @ sk_C @ sk_D )
 != ( k6_partfun1 @ sk_A ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['28','117'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5sqzpYtmwV
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:35:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.20/0.34  % Running in FO mode
% 1.29/1.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.29/1.49  % Solved by: fo/fo7.sh
% 1.29/1.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.29/1.49  % done 460 iterations in 1.040s
% 1.29/1.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.29/1.49  % SZS output start Refutation
% 1.29/1.49  thf(sk_B_type, type, sk_B: $i).
% 1.29/1.49  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.29/1.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.29/1.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.29/1.49  thf(sk_D_type, type, sk_D: $i).
% 1.29/1.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.29/1.49  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.29/1.49  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.29/1.49  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.29/1.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.29/1.49  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.29/1.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.29/1.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.29/1.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.29/1.49  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.29/1.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.29/1.49  thf(sk_A_type, type, sk_A: $i).
% 1.29/1.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.29/1.49  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.29/1.49  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 1.29/1.49  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.29/1.49  thf(sk_C_type, type, sk_C: $i).
% 1.29/1.49  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.29/1.49  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.29/1.49  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.29/1.49  thf(t36_funct_2, conjecture,
% 1.29/1.49    (![A:$i,B:$i,C:$i]:
% 1.29/1.49     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.29/1.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.29/1.49       ( ![D:$i]:
% 1.29/1.49         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.29/1.49             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.29/1.49           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.29/1.49               ( r2_relset_1 @
% 1.29/1.49                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.29/1.49                 ( k6_partfun1 @ A ) ) & 
% 1.29/1.49               ( v2_funct_1 @ C ) ) =>
% 1.29/1.49             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.29/1.49               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.29/1.49  thf(zf_stmt_0, negated_conjecture,
% 1.29/1.49    (~( ![A:$i,B:$i,C:$i]:
% 1.29/1.49        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.29/1.49            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.29/1.49          ( ![D:$i]:
% 1.29/1.49            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.29/1.49                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.29/1.49              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.29/1.49                  ( r2_relset_1 @
% 1.29/1.49                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.29/1.49                    ( k6_partfun1 @ A ) ) & 
% 1.29/1.49                  ( v2_funct_1 @ C ) ) =>
% 1.29/1.49                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.29/1.49                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.29/1.49    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.29/1.49  thf('0', plain,
% 1.29/1.49      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.29/1.49        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.29/1.49        (k6_partfun1 @ sk_A))),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf('1', plain,
% 1.29/1.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf('2', plain,
% 1.29/1.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf(redefinition_k1_partfun1, axiom,
% 1.29/1.49    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.29/1.49     ( ( ( v1_funct_1 @ E ) & 
% 1.29/1.49         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.29/1.49         ( v1_funct_1 @ F ) & 
% 1.29/1.49         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.29/1.49       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.29/1.49  thf('3', plain,
% 1.29/1.49      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 1.29/1.49         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 1.29/1.49          | ~ (v1_funct_1 @ X37)
% 1.29/1.49          | ~ (v1_funct_1 @ X40)
% 1.29/1.49          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 1.29/1.49          | ((k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40)
% 1.29/1.49              = (k5_relat_1 @ X37 @ X40)))),
% 1.29/1.49      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.29/1.49  thf('4', plain,
% 1.29/1.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.49         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.29/1.49            = (k5_relat_1 @ sk_C @ X0))
% 1.29/1.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.29/1.49          | ~ (v1_funct_1 @ X0)
% 1.29/1.49          | ~ (v1_funct_1 @ sk_C))),
% 1.29/1.49      inference('sup-', [status(thm)], ['2', '3'])).
% 1.29/1.49  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf('6', plain,
% 1.29/1.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.49         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.29/1.49            = (k5_relat_1 @ sk_C @ X0))
% 1.29/1.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.29/1.49          | ~ (v1_funct_1 @ X0))),
% 1.29/1.49      inference('demod', [status(thm)], ['4', '5'])).
% 1.29/1.49  thf('7', plain,
% 1.29/1.49      ((~ (v1_funct_1 @ sk_D)
% 1.29/1.49        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.29/1.49            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.29/1.49      inference('sup-', [status(thm)], ['1', '6'])).
% 1.29/1.49  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf('9', plain,
% 1.29/1.49      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.29/1.49         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.29/1.49      inference('demod', [status(thm)], ['7', '8'])).
% 1.29/1.49  thf('10', plain,
% 1.29/1.49      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.29/1.49        (k6_partfun1 @ sk_A))),
% 1.29/1.49      inference('demod', [status(thm)], ['0', '9'])).
% 1.29/1.49  thf('11', plain,
% 1.29/1.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf('12', plain,
% 1.29/1.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf(dt_k4_relset_1, axiom,
% 1.29/1.49    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.29/1.49     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.29/1.49         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.29/1.49       ( m1_subset_1 @
% 1.29/1.49         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.29/1.49         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 1.29/1.49  thf('13', plain,
% 1.29/1.49      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 1.29/1.49         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 1.29/1.49          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 1.29/1.49          | (m1_subset_1 @ (k4_relset_1 @ X10 @ X11 @ X13 @ X14 @ X9 @ X12) @ 
% 1.29/1.49             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X14))))),
% 1.29/1.49      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 1.29/1.49  thf('14', plain,
% 1.29/1.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.49         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.29/1.49           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.29/1.49          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 1.29/1.49      inference('sup-', [status(thm)], ['12', '13'])).
% 1.29/1.49  thf('15', plain,
% 1.29/1.49      ((m1_subset_1 @ 
% 1.29/1.49        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.29/1.49        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.29/1.49      inference('sup-', [status(thm)], ['11', '14'])).
% 1.29/1.49  thf('16', plain,
% 1.29/1.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf('17', plain,
% 1.29/1.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf(redefinition_k4_relset_1, axiom,
% 1.29/1.49    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.29/1.49     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.29/1.49         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.29/1.49       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.29/1.49  thf('18', plain,
% 1.29/1.49      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 1.29/1.49         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 1.29/1.49          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 1.29/1.49          | ((k4_relset_1 @ X19 @ X20 @ X22 @ X23 @ X18 @ X21)
% 1.29/1.49              = (k5_relat_1 @ X18 @ X21)))),
% 1.29/1.49      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 1.29/1.49  thf('19', plain,
% 1.29/1.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.49         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.29/1.49            = (k5_relat_1 @ sk_C @ X0))
% 1.29/1.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 1.29/1.49      inference('sup-', [status(thm)], ['17', '18'])).
% 1.29/1.49  thf('20', plain,
% 1.29/1.49      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.29/1.49         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.29/1.49      inference('sup-', [status(thm)], ['16', '19'])).
% 1.29/1.49  thf('21', plain,
% 1.29/1.49      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.29/1.49        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.29/1.49      inference('demod', [status(thm)], ['15', '20'])).
% 1.29/1.49  thf(redefinition_r2_relset_1, axiom,
% 1.29/1.49    (![A:$i,B:$i,C:$i,D:$i]:
% 1.29/1.49     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.29/1.49         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.29/1.49       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.29/1.49  thf('22', plain,
% 1.29/1.49      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.29/1.49         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 1.29/1.49          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 1.29/1.49          | ((X24) = (X27))
% 1.29/1.49          | ~ (r2_relset_1 @ X25 @ X26 @ X24 @ X27))),
% 1.29/1.49      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.29/1.49  thf('23', plain,
% 1.29/1.49      (![X0 : $i]:
% 1.29/1.49         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 1.29/1.49          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 1.29/1.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.29/1.49      inference('sup-', [status(thm)], ['21', '22'])).
% 1.29/1.49  thf('24', plain,
% 1.29/1.49      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.29/1.49           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.29/1.49        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 1.29/1.49      inference('sup-', [status(thm)], ['10', '23'])).
% 1.29/1.49  thf(t29_relset_1, axiom,
% 1.29/1.49    (![A:$i]:
% 1.29/1.49     ( m1_subset_1 @
% 1.29/1.49       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.29/1.49  thf('25', plain,
% 1.29/1.49      (![X28 : $i]:
% 1.29/1.49         (m1_subset_1 @ (k6_relat_1 @ X28) @ 
% 1.29/1.49          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 1.29/1.49      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.29/1.49  thf(redefinition_k6_partfun1, axiom,
% 1.29/1.49    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.29/1.49  thf('26', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 1.29/1.49      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.29/1.49  thf('27', plain,
% 1.29/1.49      (![X28 : $i]:
% 1.29/1.49         (m1_subset_1 @ (k6_partfun1 @ X28) @ 
% 1.29/1.49          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 1.29/1.49      inference('demod', [status(thm)], ['25', '26'])).
% 1.29/1.49  thf('28', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.29/1.49      inference('demod', [status(thm)], ['24', '27'])).
% 1.29/1.49  thf('29', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf(d1_funct_2, axiom,
% 1.29/1.49    (![A:$i,B:$i,C:$i]:
% 1.29/1.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.29/1.49       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.29/1.49           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.29/1.49             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.29/1.49         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.29/1.49           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.29/1.49             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.29/1.49  thf(zf_stmt_1, axiom,
% 1.29/1.49    (![C:$i,B:$i,A:$i]:
% 1.29/1.49     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.29/1.49       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.29/1.49  thf('30', plain,
% 1.29/1.49      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.29/1.49         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 1.29/1.49          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 1.29/1.49          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.29/1.49  thf('31', plain,
% 1.29/1.49      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 1.29/1.49        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 1.29/1.49      inference('sup-', [status(thm)], ['29', '30'])).
% 1.29/1.49  thf(zf_stmt_2, axiom,
% 1.29/1.49    (![B:$i,A:$i]:
% 1.29/1.49     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.29/1.49       ( zip_tseitin_0 @ B @ A ) ))).
% 1.29/1.49  thf('32', plain,
% 1.29/1.49      (![X29 : $i, X30 : $i]:
% 1.29/1.49         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.29/1.49  thf('33', plain,
% 1.29/1.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.29/1.49  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.29/1.49  thf(zf_stmt_5, axiom,
% 1.29/1.49    (![A:$i,B:$i,C:$i]:
% 1.29/1.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.29/1.49       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.29/1.49         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.29/1.49           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.29/1.49             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.29/1.49  thf('34', plain,
% 1.29/1.49      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.29/1.49         (~ (zip_tseitin_0 @ X34 @ X35)
% 1.29/1.49          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 1.29/1.49          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.29/1.49  thf('35', plain,
% 1.29/1.49      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 1.29/1.49      inference('sup-', [status(thm)], ['33', '34'])).
% 1.29/1.49  thf('36', plain,
% 1.29/1.49      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 1.29/1.49      inference('sup-', [status(thm)], ['32', '35'])).
% 1.29/1.49  thf('37', plain, (((sk_A) != (k1_xboole_0))),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf('38', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 1.29/1.49      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 1.29/1.49  thf('39', plain,
% 1.29/1.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf(redefinition_k1_relset_1, axiom,
% 1.29/1.49    (![A:$i,B:$i,C:$i]:
% 1.29/1.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.29/1.49       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.29/1.49  thf('40', plain,
% 1.29/1.49      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.29/1.49         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 1.29/1.49          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 1.29/1.49      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.29/1.49  thf('41', plain,
% 1.29/1.49      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.29/1.49      inference('sup-', [status(thm)], ['39', '40'])).
% 1.29/1.49  thf('42', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.29/1.49      inference('demod', [status(thm)], ['31', '38', '41'])).
% 1.29/1.49  thf('43', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf('44', plain,
% 1.29/1.49      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.29/1.49         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 1.29/1.49          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 1.29/1.49          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.29/1.49  thf('45', plain,
% 1.29/1.49      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 1.29/1.49        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 1.29/1.49      inference('sup-', [status(thm)], ['43', '44'])).
% 1.29/1.49  thf('46', plain,
% 1.29/1.49      (![X29 : $i, X30 : $i]:
% 1.29/1.49         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.29/1.49  thf('47', plain,
% 1.29/1.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf('48', plain,
% 1.29/1.49      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.29/1.49         (~ (zip_tseitin_0 @ X34 @ X35)
% 1.29/1.49          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 1.29/1.49          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.29/1.49  thf('49', plain,
% 1.29/1.49      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.29/1.49      inference('sup-', [status(thm)], ['47', '48'])).
% 1.29/1.49  thf('50', plain,
% 1.29/1.49      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 1.29/1.49      inference('sup-', [status(thm)], ['46', '49'])).
% 1.29/1.49  thf('51', plain, (((sk_B) != (k1_xboole_0))),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf('52', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 1.29/1.49      inference('simplify_reflect-', [status(thm)], ['50', '51'])).
% 1.29/1.49  thf('53', plain,
% 1.29/1.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf('54', plain,
% 1.29/1.49      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.29/1.49         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 1.29/1.49          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 1.29/1.49      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.29/1.49  thf('55', plain,
% 1.29/1.49      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 1.29/1.49      inference('sup-', [status(thm)], ['53', '54'])).
% 1.29/1.49  thf('56', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 1.29/1.49      inference('demod', [status(thm)], ['45', '52', '55'])).
% 1.29/1.49  thf(t63_funct_1, axiom,
% 1.29/1.49    (![A:$i]:
% 1.29/1.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.29/1.49       ( ![B:$i]:
% 1.29/1.49         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.29/1.49           ( ( ( v2_funct_1 @ A ) & 
% 1.29/1.49               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 1.29/1.49               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 1.29/1.49             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.29/1.49  thf('57', plain,
% 1.29/1.49      (![X7 : $i, X8 : $i]:
% 1.29/1.49         (~ (v1_relat_1 @ X7)
% 1.29/1.49          | ~ (v1_funct_1 @ X7)
% 1.29/1.49          | ((X7) = (k2_funct_1 @ X8))
% 1.29/1.49          | ((k5_relat_1 @ X8 @ X7) != (k6_relat_1 @ (k1_relat_1 @ X8)))
% 1.29/1.49          | ((k2_relat_1 @ X8) != (k1_relat_1 @ X7))
% 1.29/1.49          | ~ (v2_funct_1 @ X8)
% 1.29/1.49          | ~ (v1_funct_1 @ X8)
% 1.29/1.49          | ~ (v1_relat_1 @ X8))),
% 1.29/1.49      inference('cnf', [status(esa)], [t63_funct_1])).
% 1.29/1.49  thf('58', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 1.29/1.49      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.29/1.49  thf('59', plain,
% 1.29/1.49      (![X7 : $i, X8 : $i]:
% 1.29/1.49         (~ (v1_relat_1 @ X7)
% 1.29/1.49          | ~ (v1_funct_1 @ X7)
% 1.29/1.49          | ((X7) = (k2_funct_1 @ X8))
% 1.29/1.49          | ((k5_relat_1 @ X8 @ X7) != (k6_partfun1 @ (k1_relat_1 @ X8)))
% 1.29/1.49          | ((k2_relat_1 @ X8) != (k1_relat_1 @ X7))
% 1.29/1.49          | ~ (v2_funct_1 @ X8)
% 1.29/1.49          | ~ (v1_funct_1 @ X8)
% 1.29/1.49          | ~ (v1_relat_1 @ X8))),
% 1.29/1.49      inference('demod', [status(thm)], ['57', '58'])).
% 1.29/1.49  thf('60', plain,
% 1.29/1.49      (![X0 : $i]:
% 1.29/1.49         (((k5_relat_1 @ sk_C @ X0) != (k6_partfun1 @ sk_A))
% 1.29/1.49          | ~ (v1_relat_1 @ sk_C)
% 1.29/1.49          | ~ (v1_funct_1 @ sk_C)
% 1.29/1.49          | ~ (v2_funct_1 @ sk_C)
% 1.29/1.49          | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ X0))
% 1.29/1.49          | ((X0) = (k2_funct_1 @ sk_C))
% 1.29/1.49          | ~ (v1_funct_1 @ X0)
% 1.29/1.49          | ~ (v1_relat_1 @ X0))),
% 1.29/1.49      inference('sup-', [status(thm)], ['56', '59'])).
% 1.29/1.49  thf('61', plain,
% 1.29/1.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf(cc2_relat_1, axiom,
% 1.29/1.49    (![A:$i]:
% 1.29/1.49     ( ( v1_relat_1 @ A ) =>
% 1.29/1.49       ( ![B:$i]:
% 1.29/1.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.29/1.49  thf('62', plain,
% 1.29/1.49      (![X0 : $i, X1 : $i]:
% 1.29/1.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.29/1.49          | (v1_relat_1 @ X0)
% 1.29/1.49          | ~ (v1_relat_1 @ X1))),
% 1.29/1.49      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.29/1.49  thf('63', plain,
% 1.29/1.49      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 1.29/1.49      inference('sup-', [status(thm)], ['61', '62'])).
% 1.29/1.49  thf(fc6_relat_1, axiom,
% 1.29/1.49    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.29/1.49  thf('64', plain,
% 1.29/1.49      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.29/1.49      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.29/1.49  thf('65', plain, ((v1_relat_1 @ sk_C)),
% 1.29/1.49      inference('demod', [status(thm)], ['63', '64'])).
% 1.29/1.49  thf('66', plain, ((v1_funct_1 @ sk_C)),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf('67', plain, ((v2_funct_1 @ sk_C)),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf('68', plain,
% 1.29/1.49      (![X0 : $i]:
% 1.29/1.49         (((k5_relat_1 @ sk_C @ X0) != (k6_partfun1 @ sk_A))
% 1.29/1.49          | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ X0))
% 1.29/1.49          | ((X0) = (k2_funct_1 @ sk_C))
% 1.29/1.49          | ~ (v1_funct_1 @ X0)
% 1.29/1.49          | ~ (v1_relat_1 @ X0))),
% 1.29/1.49      inference('demod', [status(thm)], ['60', '65', '66', '67'])).
% 1.29/1.49  thf('69', plain,
% 1.29/1.49      ((((k2_relat_1 @ sk_C) != (sk_B))
% 1.29/1.49        | ~ (v1_relat_1 @ sk_D)
% 1.29/1.49        | ~ (v1_funct_1 @ sk_D)
% 1.29/1.49        | ((sk_D) = (k2_funct_1 @ sk_C))
% 1.29/1.49        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_partfun1 @ sk_A)))),
% 1.29/1.49      inference('sup-', [status(thm)], ['42', '68'])).
% 1.29/1.49  thf('70', plain,
% 1.29/1.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf('71', plain,
% 1.29/1.49      (![X0 : $i, X1 : $i]:
% 1.29/1.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.29/1.49          | (v1_relat_1 @ X0)
% 1.29/1.49          | ~ (v1_relat_1 @ X1))),
% 1.29/1.49      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.29/1.49  thf('72', plain,
% 1.29/1.49      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 1.29/1.49      inference('sup-', [status(thm)], ['70', '71'])).
% 1.29/1.49  thf('73', plain,
% 1.29/1.49      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.29/1.49      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.29/1.49  thf('74', plain, ((v1_relat_1 @ sk_D)),
% 1.29/1.49      inference('demod', [status(thm)], ['72', '73'])).
% 1.29/1.49  thf('75', plain, ((v1_funct_1 @ sk_D)),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf('76', plain,
% 1.29/1.49      ((((k2_relat_1 @ sk_C) != (sk_B))
% 1.29/1.49        | ((sk_D) = (k2_funct_1 @ sk_C))
% 1.29/1.49        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_partfun1 @ sk_A)))),
% 1.29/1.49      inference('demod', [status(thm)], ['69', '74', '75'])).
% 1.29/1.49  thf('77', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf('78', plain,
% 1.29/1.49      ((((k2_relat_1 @ sk_C) != (sk_B))
% 1.29/1.49        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_partfun1 @ sk_A)))),
% 1.29/1.49      inference('simplify_reflect-', [status(thm)], ['76', '77'])).
% 1.29/1.49  thf(t55_funct_1, axiom,
% 1.29/1.49    (![A:$i]:
% 1.29/1.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.29/1.49       ( ( v2_funct_1 @ A ) =>
% 1.29/1.49         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.29/1.49           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.29/1.49  thf('79', plain,
% 1.29/1.49      (![X6 : $i]:
% 1.29/1.49         (~ (v2_funct_1 @ X6)
% 1.29/1.49          | ((k2_relat_1 @ X6) = (k1_relat_1 @ (k2_funct_1 @ X6)))
% 1.29/1.49          | ~ (v1_funct_1 @ X6)
% 1.29/1.49          | ~ (v1_relat_1 @ X6))),
% 1.29/1.49      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.29/1.49  thf('80', plain,
% 1.29/1.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf(t31_funct_2, axiom,
% 1.29/1.49    (![A:$i,B:$i,C:$i]:
% 1.29/1.49     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.29/1.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.29/1.49       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.29/1.49         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.29/1.49           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.29/1.49           ( m1_subset_1 @
% 1.29/1.49             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.29/1.49  thf('81', plain,
% 1.29/1.49      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.29/1.49         (~ (v2_funct_1 @ X44)
% 1.29/1.49          | ((k2_relset_1 @ X46 @ X45 @ X44) != (X45))
% 1.29/1.49          | (m1_subset_1 @ (k2_funct_1 @ X44) @ 
% 1.29/1.49             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 1.29/1.49          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45)))
% 1.29/1.49          | ~ (v1_funct_2 @ X44 @ X46 @ X45)
% 1.29/1.49          | ~ (v1_funct_1 @ X44))),
% 1.29/1.49      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.29/1.49  thf('82', plain,
% 1.29/1.49      ((~ (v1_funct_1 @ sk_C)
% 1.29/1.49        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.29/1.49        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.29/1.49           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.29/1.49        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.29/1.49        | ~ (v2_funct_1 @ sk_C))),
% 1.29/1.49      inference('sup-', [status(thm)], ['80', '81'])).
% 1.29/1.49  thf('83', plain, ((v1_funct_1 @ sk_C)),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf('84', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf('85', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf('86', plain, ((v2_funct_1 @ sk_C)),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf('87', plain,
% 1.29/1.49      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.29/1.49         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.29/1.49        | ((sk_B) != (sk_B)))),
% 1.29/1.49      inference('demod', [status(thm)], ['82', '83', '84', '85', '86'])).
% 1.29/1.49  thf('88', plain,
% 1.29/1.49      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.29/1.49        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.29/1.49      inference('simplify', [status(thm)], ['87'])).
% 1.29/1.49  thf('89', plain,
% 1.29/1.49      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.29/1.49         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 1.29/1.49          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 1.29/1.49      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.29/1.49  thf('90', plain,
% 1.29/1.49      (((k1_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C))
% 1.29/1.49         = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.29/1.49      inference('sup-', [status(thm)], ['88', '89'])).
% 1.29/1.49  thf('91', plain,
% 1.29/1.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf('92', plain,
% 1.29/1.49      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.29/1.49         (~ (v2_funct_1 @ X44)
% 1.29/1.49          | ((k2_relset_1 @ X46 @ X45 @ X44) != (X45))
% 1.29/1.49          | (v1_funct_2 @ (k2_funct_1 @ X44) @ X45 @ X46)
% 1.29/1.49          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45)))
% 1.29/1.49          | ~ (v1_funct_2 @ X44 @ X46 @ X45)
% 1.29/1.49          | ~ (v1_funct_1 @ X44))),
% 1.29/1.49      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.29/1.49  thf('93', plain,
% 1.29/1.49      ((~ (v1_funct_1 @ sk_C)
% 1.29/1.49        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.29/1.49        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 1.29/1.49        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.29/1.49        | ~ (v2_funct_1 @ sk_C))),
% 1.29/1.49      inference('sup-', [status(thm)], ['91', '92'])).
% 1.29/1.49  thf('94', plain, ((v1_funct_1 @ sk_C)),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf('95', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf('96', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf('97', plain, ((v2_funct_1 @ sk_C)),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf('98', plain,
% 1.29/1.49      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A) | ((sk_B) != (sk_B)))),
% 1.29/1.49      inference('demod', [status(thm)], ['93', '94', '95', '96', '97'])).
% 1.29/1.49  thf('99', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 1.29/1.49      inference('simplify', [status(thm)], ['98'])).
% 1.29/1.49  thf('100', plain,
% 1.29/1.49      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.29/1.49         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 1.29/1.49          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 1.29/1.49          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.29/1.49  thf('101', plain,
% 1.29/1.49      ((~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_B)
% 1.29/1.49        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C))))),
% 1.29/1.49      inference('sup-', [status(thm)], ['99', '100'])).
% 1.29/1.49  thf('102', plain,
% 1.29/1.49      (![X29 : $i, X30 : $i]:
% 1.29/1.49         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.29/1.49  thf('103', plain,
% 1.29/1.49      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.29/1.49        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.29/1.49      inference('simplify', [status(thm)], ['87'])).
% 1.29/1.49  thf('104', plain,
% 1.29/1.49      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.29/1.49         (~ (zip_tseitin_0 @ X34 @ X35)
% 1.29/1.49          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 1.29/1.49          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.29/1.49  thf('105', plain,
% 1.29/1.49      (((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_B)
% 1.29/1.49        | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 1.29/1.49      inference('sup-', [status(thm)], ['103', '104'])).
% 1.29/1.49  thf('106', plain,
% 1.29/1.49      ((((sk_A) = (k1_xboole_0))
% 1.29/1.49        | (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_B))),
% 1.29/1.49      inference('sup-', [status(thm)], ['102', '105'])).
% 1.29/1.49  thf('107', plain, (((sk_A) != (k1_xboole_0))),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf('108', plain, ((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_B)),
% 1.29/1.49      inference('simplify_reflect-', [status(thm)], ['106', '107'])).
% 1.29/1.49  thf('109', plain,
% 1.29/1.49      (((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C)))),
% 1.29/1.49      inference('demod', [status(thm)], ['101', '108'])).
% 1.29/1.49  thf('110', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.29/1.49      inference('sup+', [status(thm)], ['90', '109'])).
% 1.29/1.49  thf('111', plain,
% 1.29/1.49      ((((sk_B) = (k2_relat_1 @ sk_C))
% 1.29/1.49        | ~ (v1_relat_1 @ sk_C)
% 1.29/1.49        | ~ (v1_funct_1 @ sk_C)
% 1.29/1.49        | ~ (v2_funct_1 @ sk_C))),
% 1.29/1.49      inference('sup+', [status(thm)], ['79', '110'])).
% 1.29/1.49  thf('112', plain, ((v1_relat_1 @ sk_C)),
% 1.29/1.49      inference('demod', [status(thm)], ['63', '64'])).
% 1.29/1.49  thf('113', plain, ((v1_funct_1 @ sk_C)),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf('114', plain, ((v2_funct_1 @ sk_C)),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf('115', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 1.29/1.49      inference('demod', [status(thm)], ['111', '112', '113', '114'])).
% 1.29/1.49  thf('116', plain,
% 1.29/1.49      ((((sk_B) != (sk_B))
% 1.29/1.49        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_partfun1 @ sk_A)))),
% 1.29/1.49      inference('demod', [status(thm)], ['78', '115'])).
% 1.29/1.49  thf('117', plain, (((k5_relat_1 @ sk_C @ sk_D) != (k6_partfun1 @ sk_A))),
% 1.29/1.49      inference('simplify', [status(thm)], ['116'])).
% 1.29/1.49  thf('118', plain, ($false),
% 1.29/1.49      inference('simplify_reflect-', [status(thm)], ['28', '117'])).
% 1.29/1.49  
% 1.29/1.49  % SZS output end Refutation
% 1.29/1.49  
% 1.29/1.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

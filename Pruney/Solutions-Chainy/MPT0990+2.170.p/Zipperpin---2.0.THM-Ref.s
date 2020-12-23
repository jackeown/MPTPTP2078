%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TkvzQePdiU

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:24 EST 2020

% Result     : Theorem 2.03s
% Output     : Refutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 243 expanded)
%              Number of leaves         :   47 (  92 expanded)
%              Depth                    :   14
%              Number of atoms          : 1650 (5453 expanded)
%              Number of equality atoms :  119 ( 401 expanded)
%              Maximal formula depth    :   21 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ( ( k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45 )
        = ( k5_relat_1 @ X42 @ X45 ) ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X11 @ X12 @ X14 @ X15 @ X10 @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X15 ) ) ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k4_relset_1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 )
        = ( k5_relat_1 @ X22 @ X25 ) ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( X28 = X31 )
      | ~ ( r2_relset_1 @ X29 @ X30 @ X28 @ X31 ) ) ),
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

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('25',plain,(
    ! [X41: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('26',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
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

thf('28',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ( X34
        = ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('29',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('30',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('31',plain,(
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

thf('32',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('33',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('38',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('39',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['29','36','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('42',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('43',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['43','44'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('46',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X9 ) @ X9 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('47',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('48',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X9 ) @ X9 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('49',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k1_relat_1 @ X8 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
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

thf('50',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( ( k2_relat_1 @ X6 )
       != X5 )
      | ( ( k5_relat_1 @ X6 @ X4 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X7 ) ) )
      | ( ( k5_relat_1 @ X4 @ X7 )
       != ( k6_relat_1 @ X5 ) )
      | ( X7 = X6 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l72_funct_1])).

thf('51',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( X7 = X6 )
      | ( ( k5_relat_1 @ X4 @ X7 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X6 ) ) )
      | ( ( k5_relat_1 @ X6 @ X4 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('53',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('54',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( X7 = X6 )
      | ( ( k5_relat_1 @ X4 @ X7 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X6 ) ) )
      | ( ( k5_relat_1 @ X6 @ X4 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ X2 @ X1 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X2 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X1 ) ) )
      | ( X1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_partfun1 @ ( k2_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['48','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ( X1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_partfun1 @ ( k2_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k1_relat_1 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ sk_B )
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k2_funct_1 @ sk_C ) )
      | ( ( k5_relat_1 @ sk_C @ X0 )
       != ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['45','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('61',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('62',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('63',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ sk_B )
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k2_funct_1 @ sk_C ) )
      | ( ( k5_relat_1 @ sk_C @ X0 )
       != ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['58','63','64','65'])).

thf('67',plain,(
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

thf('68',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( v2_funct_1 @ X49 )
      | ( ( k2_relset_1 @ X51 @ X50 @ X49 )
       != X50 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X49 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X50 ) ) )
      | ~ ( v1_funct_2 @ X49 @ X51 @ X50 )
      | ~ ( v1_funct_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('69',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['69','70','71','72','73'])).

thf('75',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('77',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('79',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( v2_funct_1 @ X49 )
      | ( ( k2_relset_1 @ X51 @ X50 @ X49 )
       != X50 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X49 ) )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X50 ) ) )
      | ~ ( v1_funct_2 @ X49 @ X51 @ X50 )
      | ~ ( v1_funct_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('82',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
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
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['82','83','84','85','86'])).

thf('88',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ( X34
        = ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('91',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('93',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('95',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['96','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('101',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['91','98','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ sk_B )
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k2_funct_1 @ sk_C ) )
      | ( ( k5_relat_1 @ sk_C @ X0 )
       != ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['66','79','88','102'])).

thf('104',plain,
    ( ( ( k6_partfun1 @ sk_B )
     != ( k6_partfun1 @ sk_B ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
     != ( k6_partfun1 @ sk_A ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['40','103'])).

thf('105',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('108',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('110',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( ( k6_partfun1 @ sk_B )
     != ( k6_partfun1 @ sk_B ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
     != ( k6_partfun1 @ sk_A ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['104','105','110'])).

thf('112',plain,
    ( ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
     != ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ( k5_relat_1 @ sk_C @ sk_D )
 != ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['112','113'])).

thf('115',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['26','114'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TkvzQePdiU
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:53:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.03/2.22  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.03/2.22  % Solved by: fo/fo7.sh
% 2.03/2.22  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.03/2.22  % done 595 iterations in 1.763s
% 2.03/2.22  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.03/2.22  % SZS output start Refutation
% 2.03/2.22  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.03/2.22  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.03/2.22  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.03/2.22  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.03/2.22  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.03/2.22  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.03/2.22  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.03/2.22  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.03/2.22  thf(sk_A_type, type, sk_A: $i).
% 2.03/2.22  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.03/2.22  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.03/2.22  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.03/2.22  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 2.03/2.22  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.03/2.22  thf(sk_B_type, type, sk_B: $i).
% 2.03/2.22  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.03/2.22  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.03/2.22  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.03/2.22  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.03/2.22  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.03/2.22  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 2.03/2.22  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.03/2.22  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.03/2.22  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.03/2.22  thf(sk_D_type, type, sk_D: $i).
% 2.03/2.22  thf(sk_C_type, type, sk_C: $i).
% 2.03/2.22  thf(t36_funct_2, conjecture,
% 2.03/2.22    (![A:$i,B:$i,C:$i]:
% 2.03/2.22     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.03/2.22         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.03/2.22       ( ![D:$i]:
% 2.03/2.22         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.03/2.22             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.03/2.22           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.03/2.22               ( r2_relset_1 @
% 2.03/2.22                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.03/2.22                 ( k6_partfun1 @ A ) ) & 
% 2.03/2.22               ( v2_funct_1 @ C ) ) =>
% 2.03/2.22             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.03/2.22               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 2.03/2.22  thf(zf_stmt_0, negated_conjecture,
% 2.03/2.22    (~( ![A:$i,B:$i,C:$i]:
% 2.03/2.22        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.03/2.22            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.03/2.22          ( ![D:$i]:
% 2.03/2.22            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.03/2.22                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.03/2.22              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.03/2.22                  ( r2_relset_1 @
% 2.03/2.22                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.03/2.22                    ( k6_partfun1 @ A ) ) & 
% 2.03/2.22                  ( v2_funct_1 @ C ) ) =>
% 2.03/2.22                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.03/2.22                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 2.03/2.22    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 2.03/2.22  thf('0', plain,
% 2.03/2.22      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.03/2.22        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.03/2.22        (k6_partfun1 @ sk_A))),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.22  thf('1', plain,
% 2.03/2.22      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.22  thf('2', plain,
% 2.03/2.22      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.22  thf(redefinition_k1_partfun1, axiom,
% 2.03/2.22    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.03/2.22     ( ( ( v1_funct_1 @ E ) & 
% 2.03/2.22         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.03/2.22         ( v1_funct_1 @ F ) & 
% 2.03/2.22         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.03/2.22       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.03/2.22  thf('3', plain,
% 2.03/2.22      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 2.03/2.22         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 2.03/2.22          | ~ (v1_funct_1 @ X42)
% 2.03/2.22          | ~ (v1_funct_1 @ X45)
% 2.03/2.22          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 2.03/2.22          | ((k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45)
% 2.03/2.22              = (k5_relat_1 @ X42 @ X45)))),
% 2.03/2.22      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 2.03/2.22  thf('4', plain,
% 2.03/2.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.03/2.22         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.03/2.22            = (k5_relat_1 @ sk_C @ X0))
% 2.03/2.22          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.03/2.22          | ~ (v1_funct_1 @ X0)
% 2.03/2.22          | ~ (v1_funct_1 @ sk_C))),
% 2.03/2.22      inference('sup-', [status(thm)], ['2', '3'])).
% 2.03/2.22  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.22  thf('6', plain,
% 2.03/2.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.03/2.22         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.03/2.22            = (k5_relat_1 @ sk_C @ X0))
% 2.03/2.22          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.03/2.22          | ~ (v1_funct_1 @ X0))),
% 2.03/2.22      inference('demod', [status(thm)], ['4', '5'])).
% 2.03/2.22  thf('7', plain,
% 2.03/2.22      ((~ (v1_funct_1 @ sk_D)
% 2.03/2.22        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.03/2.22            = (k5_relat_1 @ sk_C @ sk_D)))),
% 2.03/2.22      inference('sup-', [status(thm)], ['1', '6'])).
% 2.03/2.22  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.22  thf('9', plain,
% 2.03/2.22      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.03/2.22         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.03/2.22      inference('demod', [status(thm)], ['7', '8'])).
% 2.03/2.22  thf('10', plain,
% 2.03/2.22      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 2.03/2.22        (k6_partfun1 @ sk_A))),
% 2.03/2.22      inference('demod', [status(thm)], ['0', '9'])).
% 2.03/2.22  thf('11', plain,
% 2.03/2.22      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.22  thf('12', plain,
% 2.03/2.22      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.22  thf(dt_k4_relset_1, axiom,
% 2.03/2.22    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.03/2.22     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.03/2.22         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.03/2.22       ( m1_subset_1 @
% 2.03/2.22         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.03/2.22         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 2.03/2.22  thf('13', plain,
% 2.03/2.22      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 2.03/2.22         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 2.03/2.22          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 2.03/2.22          | (m1_subset_1 @ (k4_relset_1 @ X11 @ X12 @ X14 @ X15 @ X10 @ X13) @ 
% 2.03/2.22             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X15))))),
% 2.03/2.22      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 2.03/2.22  thf('14', plain,
% 2.03/2.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.03/2.22         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.03/2.22           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.03/2.22          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 2.03/2.22      inference('sup-', [status(thm)], ['12', '13'])).
% 2.03/2.22  thf('15', plain,
% 2.03/2.22      ((m1_subset_1 @ 
% 2.03/2.22        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.03/2.22        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.03/2.22      inference('sup-', [status(thm)], ['11', '14'])).
% 2.03/2.22  thf('16', plain,
% 2.03/2.22      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.22  thf('17', plain,
% 2.03/2.22      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.22  thf(redefinition_k4_relset_1, axiom,
% 2.03/2.22    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.03/2.22     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.03/2.22         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.03/2.22       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.03/2.22  thf('18', plain,
% 2.03/2.22      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 2.03/2.22         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 2.03/2.22          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 2.03/2.22          | ((k4_relset_1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25)
% 2.03/2.22              = (k5_relat_1 @ X22 @ X25)))),
% 2.03/2.22      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 2.03/2.22  thf('19', plain,
% 2.03/2.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.03/2.22         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.03/2.22            = (k5_relat_1 @ sk_C @ X0))
% 2.03/2.22          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 2.03/2.22      inference('sup-', [status(thm)], ['17', '18'])).
% 2.03/2.22  thf('20', plain,
% 2.03/2.22      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.03/2.22         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.03/2.22      inference('sup-', [status(thm)], ['16', '19'])).
% 2.03/2.22  thf('21', plain,
% 2.03/2.22      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 2.03/2.22        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.03/2.22      inference('demod', [status(thm)], ['15', '20'])).
% 2.03/2.22  thf(redefinition_r2_relset_1, axiom,
% 2.03/2.22    (![A:$i,B:$i,C:$i,D:$i]:
% 2.03/2.22     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.03/2.22         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.03/2.22       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.03/2.22  thf('22', plain,
% 2.03/2.22      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 2.03/2.22         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 2.03/2.22          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 2.03/2.22          | ((X28) = (X31))
% 2.03/2.22          | ~ (r2_relset_1 @ X29 @ X30 @ X28 @ X31))),
% 2.03/2.22      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.03/2.22  thf('23', plain,
% 2.03/2.22      (![X0 : $i]:
% 2.03/2.22         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 2.03/2.22          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 2.03/2.22          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.03/2.22      inference('sup-', [status(thm)], ['21', '22'])).
% 2.03/2.22  thf('24', plain,
% 2.03/2.22      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 2.03/2.22           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.03/2.22        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 2.03/2.22      inference('sup-', [status(thm)], ['10', '23'])).
% 2.03/2.22  thf(dt_k6_partfun1, axiom,
% 2.03/2.22    (![A:$i]:
% 2.03/2.22     ( ( m1_subset_1 @
% 2.03/2.22         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 2.03/2.22       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 2.03/2.22  thf('25', plain,
% 2.03/2.22      (![X41 : $i]:
% 2.03/2.22         (m1_subset_1 @ (k6_partfun1 @ X41) @ 
% 2.03/2.22          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))),
% 2.03/2.22      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 2.03/2.22  thf('26', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 2.03/2.22      inference('demod', [status(thm)], ['24', '25'])).
% 2.03/2.22  thf('27', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.22  thf(d1_funct_2, axiom,
% 2.03/2.22    (![A:$i,B:$i,C:$i]:
% 2.03/2.22     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.03/2.22       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.03/2.22           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.03/2.22             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.03/2.22         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.03/2.22           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.03/2.22             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.03/2.22  thf(zf_stmt_1, axiom,
% 2.03/2.22    (![C:$i,B:$i,A:$i]:
% 2.03/2.22     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.03/2.22       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.03/2.22  thf('28', plain,
% 2.03/2.22      (![X34 : $i, X35 : $i, X36 : $i]:
% 2.03/2.22         (~ (v1_funct_2 @ X36 @ X34 @ X35)
% 2.03/2.22          | ((X34) = (k1_relset_1 @ X34 @ X35 @ X36))
% 2.03/2.22          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.03/2.22  thf('29', plain,
% 2.03/2.22      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 2.03/2.22        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 2.03/2.22      inference('sup-', [status(thm)], ['27', '28'])).
% 2.03/2.22  thf(zf_stmt_2, axiom,
% 2.03/2.22    (![B:$i,A:$i]:
% 2.03/2.22     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.03/2.22       ( zip_tseitin_0 @ B @ A ) ))).
% 2.03/2.22  thf('30', plain,
% 2.03/2.22      (![X32 : $i, X33 : $i]:
% 2.03/2.22         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.03/2.22  thf('31', plain,
% 2.03/2.22      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.22  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.03/2.22  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.03/2.22  thf(zf_stmt_5, axiom,
% 2.03/2.22    (![A:$i,B:$i,C:$i]:
% 2.03/2.22     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.03/2.22       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.03/2.22         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.03/2.22           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.03/2.22             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.03/2.22  thf('32', plain,
% 2.03/2.22      (![X37 : $i, X38 : $i, X39 : $i]:
% 2.03/2.22         (~ (zip_tseitin_0 @ X37 @ X38)
% 2.03/2.22          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 2.03/2.22          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.03/2.22  thf('33', plain,
% 2.03/2.22      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 2.03/2.22      inference('sup-', [status(thm)], ['31', '32'])).
% 2.03/2.22  thf('34', plain,
% 2.03/2.22      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 2.03/2.22      inference('sup-', [status(thm)], ['30', '33'])).
% 2.03/2.22  thf('35', plain, (((sk_A) != (k1_xboole_0))),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.22  thf('36', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 2.03/2.22      inference('simplify_reflect-', [status(thm)], ['34', '35'])).
% 2.03/2.22  thf('37', plain,
% 2.03/2.22      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.22  thf(redefinition_k1_relset_1, axiom,
% 2.03/2.22    (![A:$i,B:$i,C:$i]:
% 2.03/2.22     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.03/2.22       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.03/2.22  thf('38', plain,
% 2.03/2.22      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.03/2.22         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 2.03/2.22          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 2.03/2.22      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.03/2.22  thf('39', plain,
% 2.03/2.22      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 2.03/2.22      inference('sup-', [status(thm)], ['37', '38'])).
% 2.03/2.22  thf('40', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 2.03/2.22      inference('demod', [status(thm)], ['29', '36', '39'])).
% 2.03/2.22  thf('41', plain,
% 2.03/2.22      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.22  thf(redefinition_k2_relset_1, axiom,
% 2.03/2.22    (![A:$i,B:$i,C:$i]:
% 2.03/2.22     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.03/2.22       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.03/2.22  thf('42', plain,
% 2.03/2.22      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.03/2.22         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 2.03/2.22          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 2.03/2.22      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.03/2.22  thf('43', plain,
% 2.03/2.22      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 2.03/2.22      inference('sup-', [status(thm)], ['41', '42'])).
% 2.03/2.22  thf('44', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.22  thf('45', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.03/2.22      inference('sup+', [status(thm)], ['43', '44'])).
% 2.03/2.22  thf(t61_funct_1, axiom,
% 2.03/2.22    (![A:$i]:
% 2.03/2.22     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.03/2.22       ( ( v2_funct_1 @ A ) =>
% 2.03/2.22         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 2.03/2.22             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 2.03/2.22           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 2.03/2.22             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 2.03/2.22  thf('46', plain,
% 2.03/2.22      (![X9 : $i]:
% 2.03/2.22         (~ (v2_funct_1 @ X9)
% 2.03/2.22          | ((k5_relat_1 @ (k2_funct_1 @ X9) @ X9)
% 2.03/2.22              = (k6_relat_1 @ (k2_relat_1 @ X9)))
% 2.03/2.22          | ~ (v1_funct_1 @ X9)
% 2.03/2.22          | ~ (v1_relat_1 @ X9))),
% 2.03/2.22      inference('cnf', [status(esa)], [t61_funct_1])).
% 2.03/2.22  thf(redefinition_k6_partfun1, axiom,
% 2.03/2.22    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.03/2.22  thf('47', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 2.03/2.22      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.03/2.22  thf('48', plain,
% 2.03/2.22      (![X9 : $i]:
% 2.03/2.22         (~ (v2_funct_1 @ X9)
% 2.03/2.22          | ((k5_relat_1 @ (k2_funct_1 @ X9) @ X9)
% 2.03/2.22              = (k6_partfun1 @ (k2_relat_1 @ X9)))
% 2.03/2.22          | ~ (v1_funct_1 @ X9)
% 2.03/2.22          | ~ (v1_relat_1 @ X9))),
% 2.03/2.22      inference('demod', [status(thm)], ['46', '47'])).
% 2.03/2.22  thf(t55_funct_1, axiom,
% 2.03/2.22    (![A:$i]:
% 2.03/2.22     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.03/2.22       ( ( v2_funct_1 @ A ) =>
% 2.03/2.22         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 2.03/2.22           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.03/2.22  thf('49', plain,
% 2.03/2.22      (![X8 : $i]:
% 2.03/2.22         (~ (v2_funct_1 @ X8)
% 2.03/2.22          | ((k1_relat_1 @ X8) = (k2_relat_1 @ (k2_funct_1 @ X8)))
% 2.03/2.22          | ~ (v1_funct_1 @ X8)
% 2.03/2.22          | ~ (v1_relat_1 @ X8))),
% 2.03/2.22      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.03/2.22  thf(l72_funct_1, axiom,
% 2.03/2.22    (![A:$i,B:$i]:
% 2.03/2.22     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.03/2.22       ( ![C:$i]:
% 2.03/2.22         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 2.03/2.22           ( ![D:$i]:
% 2.03/2.22             ( ( ( v1_relat_1 @ D ) & ( v1_funct_1 @ D ) ) =>
% 2.03/2.22               ( ( ( ( k2_relat_1 @ B ) = ( A ) ) & 
% 2.03/2.22                   ( ( k5_relat_1 @ B @ C ) =
% 2.03/2.22                     ( k6_relat_1 @ ( k1_relat_1 @ D ) ) ) & 
% 2.03/2.22                   ( ( k5_relat_1 @ C @ D ) = ( k6_relat_1 @ A ) ) ) =>
% 2.03/2.22                 ( ( D ) = ( B ) ) ) ) ) ) ) ))).
% 2.03/2.22  thf('50', plain,
% 2.03/2.22      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 2.03/2.22         (~ (v1_relat_1 @ X4)
% 2.03/2.22          | ~ (v1_funct_1 @ X4)
% 2.03/2.22          | ((k2_relat_1 @ X6) != (X5))
% 2.03/2.22          | ((k5_relat_1 @ X6 @ X4) != (k6_relat_1 @ (k1_relat_1 @ X7)))
% 2.03/2.22          | ((k5_relat_1 @ X4 @ X7) != (k6_relat_1 @ X5))
% 2.03/2.22          | ((X7) = (X6))
% 2.03/2.22          | ~ (v1_funct_1 @ X7)
% 2.03/2.22          | ~ (v1_relat_1 @ X7)
% 2.03/2.22          | ~ (v1_funct_1 @ X6)
% 2.03/2.22          | ~ (v1_relat_1 @ X6))),
% 2.03/2.22      inference('cnf', [status(esa)], [l72_funct_1])).
% 2.03/2.22  thf('51', plain,
% 2.03/2.22      (![X4 : $i, X6 : $i, X7 : $i]:
% 2.03/2.22         (~ (v1_relat_1 @ X6)
% 2.03/2.22          | ~ (v1_funct_1 @ X6)
% 2.03/2.22          | ~ (v1_relat_1 @ X7)
% 2.03/2.22          | ~ (v1_funct_1 @ X7)
% 2.03/2.22          | ((X7) = (X6))
% 2.03/2.22          | ((k5_relat_1 @ X4 @ X7) != (k6_relat_1 @ (k2_relat_1 @ X6)))
% 2.03/2.22          | ((k5_relat_1 @ X6 @ X4) != (k6_relat_1 @ (k1_relat_1 @ X7)))
% 2.03/2.22          | ~ (v1_funct_1 @ X4)
% 2.03/2.22          | ~ (v1_relat_1 @ X4))),
% 2.03/2.22      inference('simplify', [status(thm)], ['50'])).
% 2.03/2.22  thf('52', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 2.03/2.22      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.03/2.22  thf('53', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 2.03/2.22      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.03/2.22  thf('54', plain,
% 2.03/2.22      (![X4 : $i, X6 : $i, X7 : $i]:
% 2.03/2.22         (~ (v1_relat_1 @ X6)
% 2.03/2.22          | ~ (v1_funct_1 @ X6)
% 2.03/2.22          | ~ (v1_relat_1 @ X7)
% 2.03/2.22          | ~ (v1_funct_1 @ X7)
% 2.03/2.22          | ((X7) = (X6))
% 2.03/2.22          | ((k5_relat_1 @ X4 @ X7) != (k6_partfun1 @ (k2_relat_1 @ X6)))
% 2.03/2.22          | ((k5_relat_1 @ X6 @ X4) != (k6_partfun1 @ (k1_relat_1 @ X7)))
% 2.03/2.22          | ~ (v1_funct_1 @ X4)
% 2.03/2.22          | ~ (v1_relat_1 @ X4))),
% 2.03/2.22      inference('demod', [status(thm)], ['51', '52', '53'])).
% 2.03/2.22  thf('55', plain,
% 2.03/2.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.03/2.22         (((k5_relat_1 @ X2 @ X1) != (k6_partfun1 @ (k1_relat_1 @ X0)))
% 2.03/2.22          | ~ (v1_relat_1 @ X0)
% 2.03/2.22          | ~ (v1_funct_1 @ X0)
% 2.03/2.22          | ~ (v2_funct_1 @ X0)
% 2.03/2.22          | ~ (v1_relat_1 @ X2)
% 2.03/2.22          | ~ (v1_funct_1 @ X2)
% 2.03/2.22          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X2)
% 2.03/2.22              != (k6_partfun1 @ (k1_relat_1 @ X1)))
% 2.03/2.22          | ((X1) = (k2_funct_1 @ X0))
% 2.03/2.22          | ~ (v1_funct_1 @ X1)
% 2.03/2.22          | ~ (v1_relat_1 @ X1)
% 2.03/2.22          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.03/2.22          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 2.03/2.22      inference('sup-', [status(thm)], ['49', '54'])).
% 2.03/2.22  thf('56', plain,
% 2.03/2.22      (![X0 : $i, X1 : $i]:
% 2.03/2.22         (((k6_partfun1 @ (k2_relat_1 @ X0))
% 2.03/2.22            != (k6_partfun1 @ (k1_relat_1 @ X1)))
% 2.03/2.22          | ~ (v1_relat_1 @ X0)
% 2.03/2.22          | ~ (v1_funct_1 @ X0)
% 2.03/2.22          | ~ (v2_funct_1 @ X0)
% 2.03/2.22          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.03/2.22          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.03/2.22          | ~ (v1_relat_1 @ X1)
% 2.03/2.22          | ~ (v1_funct_1 @ X1)
% 2.03/2.22          | ((X1) = (k2_funct_1 @ X0))
% 2.03/2.22          | ~ (v1_funct_1 @ X0)
% 2.03/2.22          | ~ (v1_relat_1 @ X0)
% 2.03/2.22          | ~ (v2_funct_1 @ X0)
% 2.03/2.22          | ~ (v1_funct_1 @ X0)
% 2.03/2.22          | ~ (v1_relat_1 @ X0)
% 2.03/2.22          | ((k5_relat_1 @ X0 @ X1) != (k6_partfun1 @ (k1_relat_1 @ X0))))),
% 2.03/2.22      inference('sup-', [status(thm)], ['48', '55'])).
% 2.03/2.22  thf('57', plain,
% 2.03/2.22      (![X0 : $i, X1 : $i]:
% 2.03/2.22         (((k5_relat_1 @ X0 @ X1) != (k6_partfun1 @ (k1_relat_1 @ X0)))
% 2.03/2.22          | ((X1) = (k2_funct_1 @ X0))
% 2.03/2.22          | ~ (v1_funct_1 @ X1)
% 2.03/2.22          | ~ (v1_relat_1 @ X1)
% 2.03/2.22          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.03/2.22          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.03/2.22          | ~ (v2_funct_1 @ X0)
% 2.03/2.22          | ~ (v1_funct_1 @ X0)
% 2.03/2.22          | ~ (v1_relat_1 @ X0)
% 2.03/2.22          | ((k6_partfun1 @ (k2_relat_1 @ X0))
% 2.03/2.22              != (k6_partfun1 @ (k1_relat_1 @ X1))))),
% 2.03/2.22      inference('simplify', [status(thm)], ['56'])).
% 2.03/2.22  thf('58', plain,
% 2.03/2.22      (![X0 : $i]:
% 2.03/2.22         (((k6_partfun1 @ sk_B) != (k6_partfun1 @ (k1_relat_1 @ X0)))
% 2.03/2.22          | ~ (v1_relat_1 @ sk_C)
% 2.03/2.22          | ~ (v1_funct_1 @ sk_C)
% 2.03/2.22          | ~ (v2_funct_1 @ sk_C)
% 2.03/2.22          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.03/2.22          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 2.03/2.22          | ~ (v1_relat_1 @ X0)
% 2.03/2.22          | ~ (v1_funct_1 @ X0)
% 2.03/2.22          | ((X0) = (k2_funct_1 @ sk_C))
% 2.03/2.22          | ((k5_relat_1 @ sk_C @ X0) != (k6_partfun1 @ (k1_relat_1 @ sk_C))))),
% 2.03/2.22      inference('sup-', [status(thm)], ['45', '57'])).
% 2.03/2.22  thf('59', plain,
% 2.03/2.22      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.22  thf(cc2_relat_1, axiom,
% 2.03/2.22    (![A:$i]:
% 2.03/2.22     ( ( v1_relat_1 @ A ) =>
% 2.03/2.22       ( ![B:$i]:
% 2.03/2.22         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.03/2.22  thf('60', plain,
% 2.03/2.22      (![X0 : $i, X1 : $i]:
% 2.03/2.22         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 2.03/2.22          | (v1_relat_1 @ X0)
% 2.03/2.22          | ~ (v1_relat_1 @ X1))),
% 2.03/2.22      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.03/2.22  thf('61', plain,
% 2.03/2.22      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 2.03/2.22      inference('sup-', [status(thm)], ['59', '60'])).
% 2.03/2.22  thf(fc6_relat_1, axiom,
% 2.03/2.22    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.03/2.22  thf('62', plain,
% 2.03/2.22      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 2.03/2.22      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.03/2.22  thf('63', plain, ((v1_relat_1 @ sk_C)),
% 2.03/2.22      inference('demod', [status(thm)], ['61', '62'])).
% 2.03/2.22  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.22  thf('65', plain, ((v2_funct_1 @ sk_C)),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.22  thf('66', plain,
% 2.03/2.22      (![X0 : $i]:
% 2.03/2.22         (((k6_partfun1 @ sk_B) != (k6_partfun1 @ (k1_relat_1 @ X0)))
% 2.03/2.22          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.03/2.22          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 2.03/2.22          | ~ (v1_relat_1 @ X0)
% 2.03/2.22          | ~ (v1_funct_1 @ X0)
% 2.03/2.22          | ((X0) = (k2_funct_1 @ sk_C))
% 2.03/2.22          | ((k5_relat_1 @ sk_C @ X0) != (k6_partfun1 @ (k1_relat_1 @ sk_C))))),
% 2.03/2.22      inference('demod', [status(thm)], ['58', '63', '64', '65'])).
% 2.03/2.22  thf('67', plain,
% 2.03/2.22      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.22  thf(t31_funct_2, axiom,
% 2.03/2.22    (![A:$i,B:$i,C:$i]:
% 2.03/2.22     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.03/2.22         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.03/2.22       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 2.03/2.22         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 2.03/2.22           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 2.03/2.22           ( m1_subset_1 @
% 2.03/2.22             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 2.03/2.22  thf('68', plain,
% 2.03/2.22      (![X49 : $i, X50 : $i, X51 : $i]:
% 2.03/2.22         (~ (v2_funct_1 @ X49)
% 2.03/2.22          | ((k2_relset_1 @ X51 @ X50 @ X49) != (X50))
% 2.03/2.22          | (m1_subset_1 @ (k2_funct_1 @ X49) @ 
% 2.03/2.22             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 2.03/2.22          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X50)))
% 2.03/2.22          | ~ (v1_funct_2 @ X49 @ X51 @ X50)
% 2.03/2.22          | ~ (v1_funct_1 @ X49))),
% 2.03/2.22      inference('cnf', [status(esa)], [t31_funct_2])).
% 2.03/2.22  thf('69', plain,
% 2.03/2.22      ((~ (v1_funct_1 @ sk_C)
% 2.03/2.22        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.03/2.22        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.03/2.22           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.03/2.22        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 2.03/2.22        | ~ (v2_funct_1 @ sk_C))),
% 2.03/2.22      inference('sup-', [status(thm)], ['67', '68'])).
% 2.03/2.22  thf('70', plain, ((v1_funct_1 @ sk_C)),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.22  thf('71', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.22  thf('72', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.22  thf('73', plain, ((v2_funct_1 @ sk_C)),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.22  thf('74', plain,
% 2.03/2.22      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.03/2.22         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.03/2.22        | ((sk_B) != (sk_B)))),
% 2.03/2.22      inference('demod', [status(thm)], ['69', '70', '71', '72', '73'])).
% 2.03/2.22  thf('75', plain,
% 2.03/2.22      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.03/2.22        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.03/2.22      inference('simplify', [status(thm)], ['74'])).
% 2.03/2.22  thf('76', plain,
% 2.03/2.22      (![X0 : $i, X1 : $i]:
% 2.03/2.22         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 2.03/2.22          | (v1_relat_1 @ X0)
% 2.03/2.22          | ~ (v1_relat_1 @ X1))),
% 2.03/2.22      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.03/2.22  thf('77', plain,
% 2.03/2.22      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))
% 2.03/2.22        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 2.03/2.22      inference('sup-', [status(thm)], ['75', '76'])).
% 2.03/2.22  thf('78', plain,
% 2.03/2.22      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 2.03/2.22      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.03/2.22  thf('79', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 2.03/2.22      inference('demod', [status(thm)], ['77', '78'])).
% 2.03/2.22  thf('80', plain,
% 2.03/2.22      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.22  thf('81', plain,
% 2.03/2.22      (![X49 : $i, X50 : $i, X51 : $i]:
% 2.03/2.22         (~ (v2_funct_1 @ X49)
% 2.03/2.22          | ((k2_relset_1 @ X51 @ X50 @ X49) != (X50))
% 2.03/2.22          | (v1_funct_1 @ (k2_funct_1 @ X49))
% 2.03/2.22          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X50)))
% 2.03/2.22          | ~ (v1_funct_2 @ X49 @ X51 @ X50)
% 2.03/2.22          | ~ (v1_funct_1 @ X49))),
% 2.03/2.22      inference('cnf', [status(esa)], [t31_funct_2])).
% 2.03/2.22  thf('82', plain,
% 2.03/2.22      ((~ (v1_funct_1 @ sk_C)
% 2.03/2.22        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.03/2.22        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 2.03/2.22        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 2.03/2.22        | ~ (v2_funct_1 @ sk_C))),
% 2.03/2.22      inference('sup-', [status(thm)], ['80', '81'])).
% 2.03/2.22  thf('83', plain, ((v1_funct_1 @ sk_C)),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.22  thf('84', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.22  thf('85', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.22  thf('86', plain, ((v2_funct_1 @ sk_C)),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.22  thf('87', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)) | ((sk_B) != (sk_B)))),
% 2.03/2.22      inference('demod', [status(thm)], ['82', '83', '84', '85', '86'])).
% 2.03/2.22  thf('88', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 2.03/2.22      inference('simplify', [status(thm)], ['87'])).
% 2.03/2.22  thf('89', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.22  thf('90', plain,
% 2.03/2.22      (![X34 : $i, X35 : $i, X36 : $i]:
% 2.03/2.22         (~ (v1_funct_2 @ X36 @ X34 @ X35)
% 2.03/2.22          | ((X34) = (k1_relset_1 @ X34 @ X35 @ X36))
% 2.03/2.22          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.03/2.22  thf('91', plain,
% 2.03/2.22      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 2.03/2.22        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 2.03/2.22      inference('sup-', [status(thm)], ['89', '90'])).
% 2.03/2.22  thf('92', plain,
% 2.03/2.22      (![X32 : $i, X33 : $i]:
% 2.03/2.22         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.03/2.22  thf('93', plain,
% 2.03/2.22      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.22  thf('94', plain,
% 2.03/2.22      (![X37 : $i, X38 : $i, X39 : $i]:
% 2.03/2.22         (~ (zip_tseitin_0 @ X37 @ X38)
% 2.03/2.22          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 2.03/2.22          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.03/2.22  thf('95', plain,
% 2.03/2.22      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 2.03/2.22      inference('sup-', [status(thm)], ['93', '94'])).
% 2.03/2.22  thf('96', plain,
% 2.03/2.22      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 2.03/2.22      inference('sup-', [status(thm)], ['92', '95'])).
% 2.03/2.22  thf('97', plain, (((sk_B) != (k1_xboole_0))),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.22  thf('98', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 2.03/2.22      inference('simplify_reflect-', [status(thm)], ['96', '97'])).
% 2.03/2.22  thf('99', plain,
% 2.03/2.22      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.22  thf('100', plain,
% 2.03/2.22      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.03/2.22         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 2.03/2.22          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 2.03/2.22      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.03/2.22  thf('101', plain,
% 2.03/2.22      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 2.03/2.22      inference('sup-', [status(thm)], ['99', '100'])).
% 2.03/2.22  thf('102', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 2.03/2.22      inference('demod', [status(thm)], ['91', '98', '101'])).
% 2.03/2.22  thf('103', plain,
% 2.03/2.22      (![X0 : $i]:
% 2.03/2.22         (((k6_partfun1 @ sk_B) != (k6_partfun1 @ (k1_relat_1 @ X0)))
% 2.03/2.22          | ~ (v1_relat_1 @ X0)
% 2.03/2.22          | ~ (v1_funct_1 @ X0)
% 2.03/2.22          | ((X0) = (k2_funct_1 @ sk_C))
% 2.03/2.22          | ((k5_relat_1 @ sk_C @ X0) != (k6_partfun1 @ sk_A)))),
% 2.03/2.22      inference('demod', [status(thm)], ['66', '79', '88', '102'])).
% 2.03/2.22  thf('104', plain,
% 2.03/2.22      ((((k6_partfun1 @ sk_B) != (k6_partfun1 @ sk_B))
% 2.03/2.22        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_partfun1 @ sk_A))
% 2.03/2.22        | ((sk_D) = (k2_funct_1 @ sk_C))
% 2.03/2.22        | ~ (v1_funct_1 @ sk_D)
% 2.03/2.22        | ~ (v1_relat_1 @ sk_D))),
% 2.03/2.22      inference('sup-', [status(thm)], ['40', '103'])).
% 2.03/2.22  thf('105', plain, ((v1_funct_1 @ sk_D)),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.22  thf('106', plain,
% 2.03/2.22      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.22  thf('107', plain,
% 2.03/2.22      (![X0 : $i, X1 : $i]:
% 2.03/2.22         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 2.03/2.22          | (v1_relat_1 @ X0)
% 2.03/2.22          | ~ (v1_relat_1 @ X1))),
% 2.03/2.22      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.03/2.22  thf('108', plain,
% 2.03/2.22      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 2.03/2.22      inference('sup-', [status(thm)], ['106', '107'])).
% 2.03/2.22  thf('109', plain,
% 2.03/2.22      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 2.03/2.22      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.03/2.22  thf('110', plain, ((v1_relat_1 @ sk_D)),
% 2.03/2.22      inference('demod', [status(thm)], ['108', '109'])).
% 2.03/2.22  thf('111', plain,
% 2.03/2.22      ((((k6_partfun1 @ sk_B) != (k6_partfun1 @ sk_B))
% 2.03/2.22        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_partfun1 @ sk_A))
% 2.03/2.22        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 2.03/2.22      inference('demod', [status(thm)], ['104', '105', '110'])).
% 2.03/2.22  thf('112', plain,
% 2.03/2.22      ((((sk_D) = (k2_funct_1 @ sk_C))
% 2.03/2.22        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_partfun1 @ sk_A)))),
% 2.03/2.22      inference('simplify', [status(thm)], ['111'])).
% 2.03/2.22  thf('113', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 2.03/2.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.22  thf('114', plain, (((k5_relat_1 @ sk_C @ sk_D) != (k6_partfun1 @ sk_A))),
% 2.03/2.22      inference('simplify_reflect-', [status(thm)], ['112', '113'])).
% 2.03/2.22  thf('115', plain, ($false),
% 2.03/2.22      inference('simplify_reflect-', [status(thm)], ['26', '114'])).
% 2.03/2.22  
% 2.03/2.22  % SZS output end Refutation
% 2.03/2.22  
% 2.03/2.23  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

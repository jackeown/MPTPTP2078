%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.atXBRYSkLy

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:24 EST 2020

% Result     : Theorem 1.97s
% Output     : Refutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :  274 ( 660 expanded)
%              Number of leaves         :   47 ( 214 expanded)
%              Depth                    :   66
%              Number of atoms          : 3490 (14030 expanded)
%              Number of equality atoms :  245 ( 988 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

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
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( ( k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46 )
        = ( k5_relat_1 @ X43 @ X46 ) ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X12 @ X13 @ X15 @ X16 @ X11 @ X14 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X16 ) ) ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k4_relset_1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 )
        = ( k5_relat_1 @ X23 @ X26 ) ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( X29 = X32 )
      | ~ ( r2_relset_1 @ X30 @ X31 @ X29 @ X32 ) ) ),
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
    ! [X42: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X42 ) ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ( X35
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
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
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
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
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('39',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['29','36','39'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('41',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('42',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('43',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('44',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('45',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('46',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_relat_1 @ X9 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('47',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('48',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('49',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k5_relat_1 @ X10 @ ( k2_funct_1 @ X10 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('50',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('51',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k5_relat_1 @ X10 @ ( k2_funct_1 @ X10 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_relat_1 @ X9 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('53',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('54',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('55',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('56',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('57',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('58',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('59',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('60',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('61',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('62',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_relat_1 @ X9 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('63',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('64',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('65',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_relat_1 @ X9 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('66',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k5_relat_1 @ X10 @ ( k2_funct_1 @ X10 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('67',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k5_relat_1 @ X10 @ ( k2_funct_1 @ X10 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

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

thf('68',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X7 )
       != X6 )
      | ( ( k5_relat_1 @ X7 @ X5 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X8 ) ) )
      | ( ( k5_relat_1 @ X5 @ X8 )
       != ( k6_relat_1 @ X6 ) )
      | ( X8 = X7 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l72_funct_1])).

thf('69',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( X8 = X7 )
      | ( ( k5_relat_1 @ X5 @ X8 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X7 ) ) )
      | ( ( k5_relat_1 @ X7 @ X5 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('71',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('72',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( X8 = X7 )
      | ( ( k5_relat_1 @ X5 @ X8 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X7 ) ) )
      | ( ( k5_relat_1 @ X7 @ X5 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X1 @ X0 )
       != ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ( ( k2_funct_1 @ X0 )
        = X1 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['67','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ X0 )
        = X1 )
      | ( ( k5_relat_1 @ X1 @ X0 )
       != ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['65','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 )
      | ( ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['64','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 )
      | ( ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['63','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 )
      | ( ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ ( k2_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['62','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 )
      | ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['61','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['60','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['59','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['58','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X10 ) @ X10 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('94',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('95',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X10 ) @ X10 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['92','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['57','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['56','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['55','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('104',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_relset_1 @ X21 @ X22 @ X20 )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('105',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( X8 = X7 )
      | ( ( k5_relat_1 @ X5 @ X8 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X7 ) ) )
      | ( ( k5_relat_1 @ X7 @ X5 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X1 @ X0 )
       != ( k6_partfun1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k5_relat_1 @ sk_C @ X1 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ( X0 = sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('113',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('114',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('115',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X1 @ X0 )
       != ( k6_partfun1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k5_relat_1 @ sk_C @ X1 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ( X0 = sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['109','110','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0 = sk_C )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
       != ( k6_partfun1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['102','116'])).

thf('118',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['113','114'])).

thf('119',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0 = sk_C )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
       != ( k6_partfun1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['117','118','119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
       != ( k6_partfun1 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ( X0 = sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['54','121'])).

thf('123',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['113','114'])).

thf('124',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
       != ( k6_partfun1 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ( X0 = sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['122','123','124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C )
      | ( ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0 = sk_C )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
       != ( k6_partfun1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['53','126'])).

thf('128',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['113','114'])).

thf('129',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0 = sk_C )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
       != ( k6_partfun1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['127','128','129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_funct_1 @ X0 ) )
       != ( k6_partfun1 @ sk_B ) )
      | ( ( k2_funct_1 @ X0 )
        = sk_C )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','131'])).

thf('133',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
     != ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(eq_res,[status(thm)],['132'])).

thf('134',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
     != ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['51','133'])).

thf('135',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
     != ( k6_partfun1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
     != ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['48','135'])).

thf('137',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ( ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
     != ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
     != ( k6_partfun1 @ sk_B ) )
    | ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['47','137'])).

thf('139',plain,
    ( ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ( ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
     != ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,
    ( ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
     != ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['46','139'])).

thf('141',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['105','106'])).

thf('142',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['113','114'])).

thf('143',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( ( k6_partfun1 @ sk_B )
     != ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference(demod,[status(thm)],['140','141','142','143','144'])).

thf('146',plain,
    ( ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['45','146'])).

thf('148',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['113','114'])).

thf('149',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference(demod,[status(thm)],['147','148','149','150'])).

thf('152',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['44','151'])).

thf('153',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['113','114'])).

thf('154',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['152','153','154','155'])).

thf('157',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['43','156'])).

thf('158',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['113','114'])).

thf('159',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['157','158','159','160'])).

thf('162',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('163',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('164',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['164','167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['163','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['162','171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['161','173'])).

thf('175',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['105','106'])).

thf('176',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['113','114'])).

thf('177',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['174','175','176','177','178'])).

thf('180',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('181',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( X8 = X7 )
      | ( ( k5_relat_1 @ X5 @ X8 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X7 ) ) )
      | ( ( k5_relat_1 @ X7 @ X5 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('182',plain,(
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
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ sk_B )
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C )
      | ( ( k5_relat_1 @ sk_C @ X0 )
       != ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['179','182'])).

thf('184',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['113','114'])).

thf('186',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['113','114'])).

thf('189',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ( X35
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('191',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('193',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('195',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['192','195'])).

thf('197',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['196','197'])).

thf('199',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('201',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['191','198','201'])).

thf('203',plain,(
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
       != ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['183','184','185','186','187','188','202'])).

thf('204',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C )
      | ( ( k5_relat_1 @ sk_C @ X0 )
       != ( k6_partfun1 @ sk_A ) )
      | ( X0
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ( ( k6_partfun1 @ sk_B )
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['42','203'])).

thf('205',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['113','114'])).

thf('206',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
       != ( k6_partfun1 @ sk_A ) )
      | ( X0
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ( ( k6_partfun1 @ sk_B )
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['204','205','206','207'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C )
      | ( ( k6_partfun1 @ sk_B )
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k2_funct_1 @ sk_C ) )
      | ( ( k5_relat_1 @ sk_C @ X0 )
       != ( k6_partfun1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','208'])).

thf('210',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['113','114'])).

thf('211',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ sk_B )
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k2_funct_1 @ sk_C ) )
      | ( ( k5_relat_1 @ sk_C @ X0 )
       != ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['209','210','211','212'])).

thf('214',plain,
    ( ( ( k6_partfun1 @ sk_B )
     != ( k6_partfun1 @ sk_B ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
     != ( k6_partfun1 @ sk_A ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['40','213'])).

thf('215',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('218',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['216','217'])).

thf('219',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('220',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['218','219'])).

thf('221',plain,
    ( ( ( k6_partfun1 @ sk_B )
     != ( k6_partfun1 @ sk_B ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
     != ( k6_partfun1 @ sk_A ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['214','215','220'])).

thf('222',plain,
    ( ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
     != ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['221'])).

thf('223',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,(
    ( k5_relat_1 @ sk_C @ sk_D )
 != ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['222','223'])).

thf('225',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['26','224'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.atXBRYSkLy
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:19:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.97/2.16  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.97/2.16  % Solved by: fo/fo7.sh
% 1.97/2.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.97/2.16  % done 670 iterations in 1.695s
% 1.97/2.16  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.97/2.16  % SZS output start Refutation
% 1.97/2.16  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.97/2.16  thf(sk_D_type, type, sk_D: $i).
% 1.97/2.16  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.97/2.16  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.97/2.16  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.97/2.16  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.97/2.16  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.97/2.16  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.97/2.16  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.97/2.16  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.97/2.16  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.97/2.16  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.97/2.16  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.97/2.16  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.97/2.16  thf(sk_C_type, type, sk_C: $i).
% 1.97/2.16  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.97/2.16  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.97/2.16  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.97/2.16  thf(sk_B_type, type, sk_B: $i).
% 1.97/2.16  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.97/2.16  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.97/2.16  thf(sk_A_type, type, sk_A: $i).
% 1.97/2.16  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.97/2.16  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.97/2.16  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 1.97/2.16  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.97/2.16  thf(t36_funct_2, conjecture,
% 1.97/2.16    (![A:$i,B:$i,C:$i]:
% 1.97/2.16     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.97/2.16         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.97/2.16       ( ![D:$i]:
% 1.97/2.16         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.97/2.16             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.97/2.16           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.97/2.16               ( r2_relset_1 @
% 1.97/2.16                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.97/2.16                 ( k6_partfun1 @ A ) ) & 
% 1.97/2.16               ( v2_funct_1 @ C ) ) =>
% 1.97/2.16             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.97/2.16               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.97/2.16  thf(zf_stmt_0, negated_conjecture,
% 1.97/2.16    (~( ![A:$i,B:$i,C:$i]:
% 1.97/2.16        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.97/2.16            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.97/2.16          ( ![D:$i]:
% 1.97/2.16            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.97/2.16                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.97/2.16              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.97/2.16                  ( r2_relset_1 @
% 1.97/2.16                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.97/2.16                    ( k6_partfun1 @ A ) ) & 
% 1.97/2.16                  ( v2_funct_1 @ C ) ) =>
% 1.97/2.16                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.97/2.16                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.97/2.16    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.97/2.16  thf('0', plain,
% 1.97/2.16      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.97/2.16        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.97/2.16        (k6_partfun1 @ sk_A))),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf('1', plain,
% 1.97/2.16      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf('2', plain,
% 1.97/2.16      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf(redefinition_k1_partfun1, axiom,
% 1.97/2.16    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.97/2.16     ( ( ( v1_funct_1 @ E ) & 
% 1.97/2.16         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.97/2.16         ( v1_funct_1 @ F ) & 
% 1.97/2.16         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.97/2.16       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.97/2.16  thf('3', plain,
% 1.97/2.16      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 1.97/2.16         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 1.97/2.16          | ~ (v1_funct_1 @ X43)
% 1.97/2.16          | ~ (v1_funct_1 @ X46)
% 1.97/2.16          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 1.97/2.16          | ((k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46)
% 1.97/2.16              = (k5_relat_1 @ X43 @ X46)))),
% 1.97/2.16      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.97/2.16  thf('4', plain,
% 1.97/2.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.97/2.16         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.97/2.16            = (k5_relat_1 @ sk_C @ X0))
% 1.97/2.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ sk_C))),
% 1.97/2.16      inference('sup-', [status(thm)], ['2', '3'])).
% 1.97/2.16  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf('6', plain,
% 1.97/2.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.97/2.16         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.97/2.16            = (k5_relat_1 @ sk_C @ X0))
% 1.97/2.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.97/2.16          | ~ (v1_funct_1 @ X0))),
% 1.97/2.16      inference('demod', [status(thm)], ['4', '5'])).
% 1.97/2.16  thf('7', plain,
% 1.97/2.16      ((~ (v1_funct_1 @ sk_D)
% 1.97/2.16        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.97/2.16            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.97/2.16      inference('sup-', [status(thm)], ['1', '6'])).
% 1.97/2.16  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf('9', plain,
% 1.97/2.16      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.97/2.16         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.97/2.16      inference('demod', [status(thm)], ['7', '8'])).
% 1.97/2.16  thf('10', plain,
% 1.97/2.16      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.97/2.16        (k6_partfun1 @ sk_A))),
% 1.97/2.16      inference('demod', [status(thm)], ['0', '9'])).
% 1.97/2.16  thf('11', plain,
% 1.97/2.16      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf('12', plain,
% 1.97/2.16      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf(dt_k4_relset_1, axiom,
% 1.97/2.16    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.97/2.16     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.97/2.16         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.97/2.16       ( m1_subset_1 @
% 1.97/2.16         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.97/2.16         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 1.97/2.16  thf('13', plain,
% 1.97/2.16      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 1.97/2.16         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 1.97/2.16          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 1.97/2.16          | (m1_subset_1 @ (k4_relset_1 @ X12 @ X13 @ X15 @ X16 @ X11 @ X14) @ 
% 1.97/2.16             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X16))))),
% 1.97/2.16      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 1.97/2.16  thf('14', plain,
% 1.97/2.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.97/2.16         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.97/2.16           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.97/2.16          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 1.97/2.16      inference('sup-', [status(thm)], ['12', '13'])).
% 1.97/2.16  thf('15', plain,
% 1.97/2.16      ((m1_subset_1 @ 
% 1.97/2.16        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.97/2.16        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.97/2.16      inference('sup-', [status(thm)], ['11', '14'])).
% 1.97/2.16  thf('16', plain,
% 1.97/2.16      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf('17', plain,
% 1.97/2.16      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf(redefinition_k4_relset_1, axiom,
% 1.97/2.16    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.97/2.16     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.97/2.16         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.97/2.16       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.97/2.16  thf('18', plain,
% 1.97/2.16      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.97/2.16         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 1.97/2.16          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 1.97/2.16          | ((k4_relset_1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26)
% 1.97/2.16              = (k5_relat_1 @ X23 @ X26)))),
% 1.97/2.16      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 1.97/2.16  thf('19', plain,
% 1.97/2.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.97/2.16         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.97/2.16            = (k5_relat_1 @ sk_C @ X0))
% 1.97/2.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 1.97/2.16      inference('sup-', [status(thm)], ['17', '18'])).
% 1.97/2.16  thf('20', plain,
% 1.97/2.16      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.97/2.16         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.97/2.16      inference('sup-', [status(thm)], ['16', '19'])).
% 1.97/2.16  thf('21', plain,
% 1.97/2.16      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.97/2.16        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.97/2.16      inference('demod', [status(thm)], ['15', '20'])).
% 1.97/2.16  thf(redefinition_r2_relset_1, axiom,
% 1.97/2.16    (![A:$i,B:$i,C:$i,D:$i]:
% 1.97/2.16     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.97/2.16         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.97/2.16       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.97/2.16  thf('22', plain,
% 1.97/2.16      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 1.97/2.16         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.97/2.16          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.97/2.16          | ((X29) = (X32))
% 1.97/2.16          | ~ (r2_relset_1 @ X30 @ X31 @ X29 @ X32))),
% 1.97/2.16      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.97/2.16  thf('23', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 1.97/2.16          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 1.97/2.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.97/2.16      inference('sup-', [status(thm)], ['21', '22'])).
% 1.97/2.16  thf('24', plain,
% 1.97/2.16      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.97/2.16           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.97/2.16        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 1.97/2.16      inference('sup-', [status(thm)], ['10', '23'])).
% 1.97/2.16  thf(dt_k6_partfun1, axiom,
% 1.97/2.16    (![A:$i]:
% 1.97/2.16     ( ( m1_subset_1 @
% 1.97/2.16         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 1.97/2.16       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 1.97/2.16  thf('25', plain,
% 1.97/2.16      (![X42 : $i]:
% 1.97/2.16         (m1_subset_1 @ (k6_partfun1 @ X42) @ 
% 1.97/2.16          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X42)))),
% 1.97/2.16      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.97/2.16  thf('26', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.97/2.16      inference('demod', [status(thm)], ['24', '25'])).
% 1.97/2.16  thf('27', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf(d1_funct_2, axiom,
% 1.97/2.16    (![A:$i,B:$i,C:$i]:
% 1.97/2.16     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.97/2.16       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.97/2.16           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.97/2.16             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.97/2.16         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.97/2.16           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.97/2.16             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.97/2.16  thf(zf_stmt_1, axiom,
% 1.97/2.16    (![C:$i,B:$i,A:$i]:
% 1.97/2.16     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.97/2.16       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.97/2.16  thf('28', plain,
% 1.97/2.16      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.97/2.16         (~ (v1_funct_2 @ X37 @ X35 @ X36)
% 1.97/2.16          | ((X35) = (k1_relset_1 @ X35 @ X36 @ X37))
% 1.97/2.16          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.97/2.16  thf('29', plain,
% 1.97/2.16      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 1.97/2.16        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 1.97/2.16      inference('sup-', [status(thm)], ['27', '28'])).
% 1.97/2.16  thf(zf_stmt_2, axiom,
% 1.97/2.16    (![B:$i,A:$i]:
% 1.97/2.16     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.97/2.16       ( zip_tseitin_0 @ B @ A ) ))).
% 1.97/2.16  thf('30', plain,
% 1.97/2.16      (![X33 : $i, X34 : $i]:
% 1.97/2.16         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.97/2.16  thf('31', plain,
% 1.97/2.16      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.97/2.16  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.97/2.16  thf(zf_stmt_5, axiom,
% 1.97/2.16    (![A:$i,B:$i,C:$i]:
% 1.97/2.16     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.97/2.16       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.97/2.16         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.97/2.16           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.97/2.16             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.97/2.16  thf('32', plain,
% 1.97/2.16      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.97/2.16         (~ (zip_tseitin_0 @ X38 @ X39)
% 1.97/2.16          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 1.97/2.16          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.97/2.16  thf('33', plain,
% 1.97/2.16      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 1.97/2.16      inference('sup-', [status(thm)], ['31', '32'])).
% 1.97/2.16  thf('34', plain,
% 1.97/2.16      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 1.97/2.16      inference('sup-', [status(thm)], ['30', '33'])).
% 1.97/2.16  thf('35', plain, (((sk_A) != (k1_xboole_0))),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf('36', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 1.97/2.16      inference('simplify_reflect-', [status(thm)], ['34', '35'])).
% 1.97/2.16  thf('37', plain,
% 1.97/2.16      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf(redefinition_k1_relset_1, axiom,
% 1.97/2.16    (![A:$i,B:$i,C:$i]:
% 1.97/2.16     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.97/2.16       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.97/2.16  thf('38', plain,
% 1.97/2.16      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.97/2.16         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 1.97/2.16          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.97/2.16      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.97/2.16  thf('39', plain,
% 1.97/2.16      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.97/2.16      inference('sup-', [status(thm)], ['37', '38'])).
% 1.97/2.16  thf('40', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.97/2.16      inference('demod', [status(thm)], ['29', '36', '39'])).
% 1.97/2.16  thf(fc6_funct_1, axiom,
% 1.97/2.16    (![A:$i]:
% 1.97/2.16     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 1.97/2.16       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.97/2.16         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 1.97/2.16         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.97/2.16  thf('41', plain,
% 1.97/2.16      (![X4 : $i]:
% 1.97/2.16         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 1.97/2.16          | ~ (v2_funct_1 @ X4)
% 1.97/2.16          | ~ (v1_funct_1 @ X4)
% 1.97/2.16          | ~ (v1_relat_1 @ X4))),
% 1.97/2.16      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.97/2.16  thf('42', plain,
% 1.97/2.16      (![X4 : $i]:
% 1.97/2.16         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 1.97/2.16          | ~ (v2_funct_1 @ X4)
% 1.97/2.16          | ~ (v1_funct_1 @ X4)
% 1.97/2.16          | ~ (v1_relat_1 @ X4))),
% 1.97/2.16      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.97/2.16  thf('43', plain,
% 1.97/2.16      (![X4 : $i]:
% 1.97/2.16         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 1.97/2.16          | ~ (v2_funct_1 @ X4)
% 1.97/2.16          | ~ (v1_funct_1 @ X4)
% 1.97/2.16          | ~ (v1_relat_1 @ X4))),
% 1.97/2.16      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.97/2.16  thf('44', plain,
% 1.97/2.16      (![X4 : $i]:
% 1.97/2.16         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 1.97/2.16          | ~ (v2_funct_1 @ X4)
% 1.97/2.16          | ~ (v1_funct_1 @ X4)
% 1.97/2.16          | ~ (v1_relat_1 @ X4))),
% 1.97/2.16      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.97/2.16  thf('45', plain,
% 1.97/2.16      (![X4 : $i]:
% 1.97/2.16         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 1.97/2.16          | ~ (v2_funct_1 @ X4)
% 1.97/2.16          | ~ (v1_funct_1 @ X4)
% 1.97/2.16          | ~ (v1_relat_1 @ X4))),
% 1.97/2.16      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.97/2.16  thf(t55_funct_1, axiom,
% 1.97/2.16    (![A:$i]:
% 1.97/2.16     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.97/2.16       ( ( v2_funct_1 @ A ) =>
% 1.97/2.16         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.97/2.16           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.97/2.16  thf('46', plain,
% 1.97/2.16      (![X9 : $i]:
% 1.97/2.16         (~ (v2_funct_1 @ X9)
% 1.97/2.16          | ((k2_relat_1 @ X9) = (k1_relat_1 @ (k2_funct_1 @ X9)))
% 1.97/2.16          | ~ (v1_funct_1 @ X9)
% 1.97/2.16          | ~ (v1_relat_1 @ X9))),
% 1.97/2.16      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.97/2.16  thf('47', plain,
% 1.97/2.16      (![X4 : $i]:
% 1.97/2.16         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 1.97/2.16          | ~ (v2_funct_1 @ X4)
% 1.97/2.16          | ~ (v1_funct_1 @ X4)
% 1.97/2.16          | ~ (v1_relat_1 @ X4))),
% 1.97/2.16      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.97/2.16  thf('48', plain,
% 1.97/2.16      (![X4 : $i]:
% 1.97/2.16         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 1.97/2.16          | ~ (v2_funct_1 @ X4)
% 1.97/2.16          | ~ (v1_funct_1 @ X4)
% 1.97/2.16          | ~ (v1_relat_1 @ X4))),
% 1.97/2.16      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.97/2.16  thf(t61_funct_1, axiom,
% 1.97/2.16    (![A:$i]:
% 1.97/2.16     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.97/2.16       ( ( v2_funct_1 @ A ) =>
% 1.97/2.16         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.97/2.16             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.97/2.16           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.97/2.16             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.97/2.16  thf('49', plain,
% 1.97/2.16      (![X10 : $i]:
% 1.97/2.16         (~ (v2_funct_1 @ X10)
% 1.97/2.16          | ((k5_relat_1 @ X10 @ (k2_funct_1 @ X10))
% 1.97/2.16              = (k6_relat_1 @ (k1_relat_1 @ X10)))
% 1.97/2.16          | ~ (v1_funct_1 @ X10)
% 1.97/2.16          | ~ (v1_relat_1 @ X10))),
% 1.97/2.16      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.97/2.16  thf(redefinition_k6_partfun1, axiom,
% 1.97/2.16    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.97/2.16  thf('50', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 1.97/2.16      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.97/2.16  thf('51', plain,
% 1.97/2.16      (![X10 : $i]:
% 1.97/2.16         (~ (v2_funct_1 @ X10)
% 1.97/2.16          | ((k5_relat_1 @ X10 @ (k2_funct_1 @ X10))
% 1.97/2.16              = (k6_partfun1 @ (k1_relat_1 @ X10)))
% 1.97/2.16          | ~ (v1_funct_1 @ X10)
% 1.97/2.16          | ~ (v1_relat_1 @ X10))),
% 1.97/2.16      inference('demod', [status(thm)], ['49', '50'])).
% 1.97/2.16  thf('52', plain,
% 1.97/2.16      (![X9 : $i]:
% 1.97/2.16         (~ (v2_funct_1 @ X9)
% 1.97/2.16          | ((k2_relat_1 @ X9) = (k1_relat_1 @ (k2_funct_1 @ X9)))
% 1.97/2.16          | ~ (v1_funct_1 @ X9)
% 1.97/2.16          | ~ (v1_relat_1 @ X9))),
% 1.97/2.16      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.97/2.16  thf('53', plain,
% 1.97/2.16      (![X4 : $i]:
% 1.97/2.16         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 1.97/2.16          | ~ (v2_funct_1 @ X4)
% 1.97/2.16          | ~ (v1_funct_1 @ X4)
% 1.97/2.16          | ~ (v1_relat_1 @ X4))),
% 1.97/2.16      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.97/2.16  thf('54', plain,
% 1.97/2.16      (![X4 : $i]:
% 1.97/2.16         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 1.97/2.16          | ~ (v2_funct_1 @ X4)
% 1.97/2.16          | ~ (v1_funct_1 @ X4)
% 1.97/2.16          | ~ (v1_relat_1 @ X4))),
% 1.97/2.16      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.97/2.16  thf('55', plain,
% 1.97/2.16      (![X4 : $i]:
% 1.97/2.16         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 1.97/2.16          | ~ (v2_funct_1 @ X4)
% 1.97/2.16          | ~ (v1_funct_1 @ X4)
% 1.97/2.16          | ~ (v1_relat_1 @ X4))),
% 1.97/2.16      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.97/2.16  thf('56', plain,
% 1.97/2.16      (![X4 : $i]:
% 1.97/2.16         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 1.97/2.16          | ~ (v2_funct_1 @ X4)
% 1.97/2.16          | ~ (v1_funct_1 @ X4)
% 1.97/2.16          | ~ (v1_relat_1 @ X4))),
% 1.97/2.16      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.97/2.16  thf('57', plain,
% 1.97/2.16      (![X4 : $i]:
% 1.97/2.16         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 1.97/2.16          | ~ (v2_funct_1 @ X4)
% 1.97/2.16          | ~ (v1_funct_1 @ X4)
% 1.97/2.16          | ~ (v1_relat_1 @ X4))),
% 1.97/2.16      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.97/2.16  thf('58', plain,
% 1.97/2.16      (![X4 : $i]:
% 1.97/2.16         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 1.97/2.16          | ~ (v2_funct_1 @ X4)
% 1.97/2.16          | ~ (v1_funct_1 @ X4)
% 1.97/2.16          | ~ (v1_relat_1 @ X4))),
% 1.97/2.16      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.97/2.16  thf('59', plain,
% 1.97/2.16      (![X4 : $i]:
% 1.97/2.16         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 1.97/2.16          | ~ (v2_funct_1 @ X4)
% 1.97/2.16          | ~ (v1_funct_1 @ X4)
% 1.97/2.16          | ~ (v1_relat_1 @ X4))),
% 1.97/2.16      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.97/2.16  thf('60', plain,
% 1.97/2.16      (![X4 : $i]:
% 1.97/2.16         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 1.97/2.16          | ~ (v2_funct_1 @ X4)
% 1.97/2.16          | ~ (v1_funct_1 @ X4)
% 1.97/2.16          | ~ (v1_relat_1 @ X4))),
% 1.97/2.16      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.97/2.16  thf('61', plain,
% 1.97/2.16      (![X9 : $i]:
% 1.97/2.16         (~ (v2_funct_1 @ X9)
% 1.97/2.16          | ((k1_relat_1 @ X9) = (k2_relat_1 @ (k2_funct_1 @ X9)))
% 1.97/2.16          | ~ (v1_funct_1 @ X9)
% 1.97/2.16          | ~ (v1_relat_1 @ X9))),
% 1.97/2.16      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.97/2.16  thf('62', plain,
% 1.97/2.16      (![X9 : $i]:
% 1.97/2.16         (~ (v2_funct_1 @ X9)
% 1.97/2.16          | ((k2_relat_1 @ X9) = (k1_relat_1 @ (k2_funct_1 @ X9)))
% 1.97/2.16          | ~ (v1_funct_1 @ X9)
% 1.97/2.16          | ~ (v1_relat_1 @ X9))),
% 1.97/2.16      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.97/2.16  thf('63', plain,
% 1.97/2.16      (![X4 : $i]:
% 1.97/2.16         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 1.97/2.16          | ~ (v2_funct_1 @ X4)
% 1.97/2.16          | ~ (v1_funct_1 @ X4)
% 1.97/2.16          | ~ (v1_relat_1 @ X4))),
% 1.97/2.16      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.97/2.16  thf('64', plain,
% 1.97/2.16      (![X4 : $i]:
% 1.97/2.16         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 1.97/2.16          | ~ (v2_funct_1 @ X4)
% 1.97/2.16          | ~ (v1_funct_1 @ X4)
% 1.97/2.16          | ~ (v1_relat_1 @ X4))),
% 1.97/2.16      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.97/2.16  thf('65', plain,
% 1.97/2.16      (![X9 : $i]:
% 1.97/2.16         (~ (v2_funct_1 @ X9)
% 1.97/2.16          | ((k2_relat_1 @ X9) = (k1_relat_1 @ (k2_funct_1 @ X9)))
% 1.97/2.16          | ~ (v1_funct_1 @ X9)
% 1.97/2.16          | ~ (v1_relat_1 @ X9))),
% 1.97/2.16      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.97/2.16  thf('66', plain,
% 1.97/2.16      (![X10 : $i]:
% 1.97/2.16         (~ (v2_funct_1 @ X10)
% 1.97/2.16          | ((k5_relat_1 @ X10 @ (k2_funct_1 @ X10))
% 1.97/2.16              = (k6_partfun1 @ (k1_relat_1 @ X10)))
% 1.97/2.16          | ~ (v1_funct_1 @ X10)
% 1.97/2.16          | ~ (v1_relat_1 @ X10))),
% 1.97/2.16      inference('demod', [status(thm)], ['49', '50'])).
% 1.97/2.16  thf('67', plain,
% 1.97/2.16      (![X10 : $i]:
% 1.97/2.16         (~ (v2_funct_1 @ X10)
% 1.97/2.16          | ((k5_relat_1 @ X10 @ (k2_funct_1 @ X10))
% 1.97/2.16              = (k6_partfun1 @ (k1_relat_1 @ X10)))
% 1.97/2.16          | ~ (v1_funct_1 @ X10)
% 1.97/2.16          | ~ (v1_relat_1 @ X10))),
% 1.97/2.16      inference('demod', [status(thm)], ['49', '50'])).
% 1.97/2.16  thf(l72_funct_1, axiom,
% 1.97/2.16    (![A:$i,B:$i]:
% 1.97/2.16     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.97/2.16       ( ![C:$i]:
% 1.97/2.16         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.97/2.16           ( ![D:$i]:
% 1.97/2.16             ( ( ( v1_relat_1 @ D ) & ( v1_funct_1 @ D ) ) =>
% 1.97/2.16               ( ( ( ( k2_relat_1 @ B ) = ( A ) ) & 
% 1.97/2.16                   ( ( k5_relat_1 @ B @ C ) =
% 1.97/2.16                     ( k6_relat_1 @ ( k1_relat_1 @ D ) ) ) & 
% 1.97/2.16                   ( ( k5_relat_1 @ C @ D ) = ( k6_relat_1 @ A ) ) ) =>
% 1.97/2.16                 ( ( D ) = ( B ) ) ) ) ) ) ) ))).
% 1.97/2.16  thf('68', plain,
% 1.97/2.16      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.97/2.16         (~ (v1_relat_1 @ X5)
% 1.97/2.16          | ~ (v1_funct_1 @ X5)
% 1.97/2.16          | ((k2_relat_1 @ X7) != (X6))
% 1.97/2.16          | ((k5_relat_1 @ X7 @ X5) != (k6_relat_1 @ (k1_relat_1 @ X8)))
% 1.97/2.16          | ((k5_relat_1 @ X5 @ X8) != (k6_relat_1 @ X6))
% 1.97/2.16          | ((X8) = (X7))
% 1.97/2.16          | ~ (v1_funct_1 @ X8)
% 1.97/2.16          | ~ (v1_relat_1 @ X8)
% 1.97/2.16          | ~ (v1_funct_1 @ X7)
% 1.97/2.16          | ~ (v1_relat_1 @ X7))),
% 1.97/2.16      inference('cnf', [status(esa)], [l72_funct_1])).
% 1.97/2.16  thf('69', plain,
% 1.97/2.16      (![X5 : $i, X7 : $i, X8 : $i]:
% 1.97/2.16         (~ (v1_relat_1 @ X7)
% 1.97/2.16          | ~ (v1_funct_1 @ X7)
% 1.97/2.16          | ~ (v1_relat_1 @ X8)
% 1.97/2.16          | ~ (v1_funct_1 @ X8)
% 1.97/2.16          | ((X8) = (X7))
% 1.97/2.16          | ((k5_relat_1 @ X5 @ X8) != (k6_relat_1 @ (k2_relat_1 @ X7)))
% 1.97/2.16          | ((k5_relat_1 @ X7 @ X5) != (k6_relat_1 @ (k1_relat_1 @ X8)))
% 1.97/2.16          | ~ (v1_funct_1 @ X5)
% 1.97/2.16          | ~ (v1_relat_1 @ X5))),
% 1.97/2.16      inference('simplify', [status(thm)], ['68'])).
% 1.97/2.16  thf('70', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 1.97/2.16      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.97/2.16  thf('71', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 1.97/2.16      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.97/2.16  thf('72', plain,
% 1.97/2.16      (![X5 : $i, X7 : $i, X8 : $i]:
% 1.97/2.16         (~ (v1_relat_1 @ X7)
% 1.97/2.16          | ~ (v1_funct_1 @ X7)
% 1.97/2.16          | ~ (v1_relat_1 @ X8)
% 1.97/2.16          | ~ (v1_funct_1 @ X8)
% 1.97/2.16          | ((X8) = (X7))
% 1.97/2.16          | ((k5_relat_1 @ X5 @ X8) != (k6_partfun1 @ (k2_relat_1 @ X7)))
% 1.97/2.16          | ((k5_relat_1 @ X7 @ X5) != (k6_partfun1 @ (k1_relat_1 @ X8)))
% 1.97/2.16          | ~ (v1_funct_1 @ X5)
% 1.97/2.16          | ~ (v1_relat_1 @ X5))),
% 1.97/2.16      inference('demod', [status(thm)], ['69', '70', '71'])).
% 1.97/2.16  thf('73', plain,
% 1.97/2.16      (![X0 : $i, X1 : $i]:
% 1.97/2.16         (((k6_partfun1 @ (k1_relat_1 @ X0))
% 1.97/2.16            != (k6_partfun1 @ (k2_relat_1 @ X1)))
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ((k5_relat_1 @ X1 @ X0)
% 1.97/2.16              != (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 1.97/2.16          | ((k2_funct_1 @ X0) = (X1))
% 1.97/2.16          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v1_funct_1 @ X1)
% 1.97/2.16          | ~ (v1_relat_1 @ X1))),
% 1.97/2.16      inference('sup-', [status(thm)], ['67', '72'])).
% 1.97/2.16  thf('74', plain,
% 1.97/2.16      (![X0 : $i, X1 : $i]:
% 1.97/2.16         (~ (v1_relat_1 @ X1)
% 1.97/2.16          | ~ (v1_funct_1 @ X1)
% 1.97/2.16          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ((k2_funct_1 @ X0) = (X1))
% 1.97/2.16          | ((k5_relat_1 @ X1 @ X0)
% 1.97/2.16              != (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ((k6_partfun1 @ (k1_relat_1 @ X0))
% 1.97/2.16              != (k6_partfun1 @ (k2_relat_1 @ X1))))),
% 1.97/2.16      inference('simplify', [status(thm)], ['73'])).
% 1.97/2.16  thf('75', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (((k6_partfun1 @ (k1_relat_1 @ X0))
% 1.97/2.16            != (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ((k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.97/2.16              != (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.97/2.16          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0))
% 1.97/2.16          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.97/2.16          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ X0))),
% 1.97/2.16      inference('sup-', [status(thm)], ['66', '74'])).
% 1.97/2.16  thf('76', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.97/2.16          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.97/2.16          | ((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0))
% 1.97/2.16          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ((k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.97/2.16              != (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ((k6_partfun1 @ (k1_relat_1 @ X0))
% 1.97/2.16              != (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))),
% 1.97/2.16      inference('simplify', [status(thm)], ['75'])).
% 1.97/2.16  thf('77', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (((k6_partfun1 @ (k1_relat_1 @ X0))
% 1.97/2.16            != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 1.97/2.16          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ((k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.97/2.16              != (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.97/2.16          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0))
% 1.97/2.16          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.97/2.16          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 1.97/2.16      inference('sup-', [status(thm)], ['65', '76'])).
% 1.97/2.16  thf('78', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.97/2.16          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.97/2.16          | ((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0))
% 1.97/2.16          | ((k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.97/2.16              != (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ((k6_partfun1 @ (k1_relat_1 @ X0))
% 1.97/2.16              != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 1.97/2.16      inference('simplify', [status(thm)], ['77'])).
% 1.97/2.16  thf('79', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ((k6_partfun1 @ (k1_relat_1 @ X0))
% 1.97/2.16              != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 1.97/2.16          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ((k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.97/2.16              != (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.97/2.16          | ((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0))
% 1.97/2.16          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 1.97/2.16      inference('sup-', [status(thm)], ['64', '78'])).
% 1.97/2.16  thf('80', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.97/2.16          | ((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0))
% 1.97/2.16          | ((k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.97/2.16              != (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ((k6_partfun1 @ (k1_relat_1 @ X0))
% 1.97/2.16              != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 1.97/2.16          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.97/2.16      inference('simplify', [status(thm)], ['79'])).
% 1.97/2.16  thf('81', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ((k6_partfun1 @ (k1_relat_1 @ X0))
% 1.97/2.16              != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ((k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.97/2.16              != (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.97/2.16          | ((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0)))),
% 1.97/2.16      inference('sup-', [status(thm)], ['63', '80'])).
% 1.97/2.16  thf('82', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0))
% 1.97/2.16          | ((k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.97/2.16              != (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ((k6_partfun1 @ (k1_relat_1 @ X0))
% 1.97/2.16              != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 1.97/2.16          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.97/2.16      inference('simplify', [status(thm)], ['81'])).
% 1.97/2.16  thf('83', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (((k6_partfun1 @ (k2_relat_1 @ X0))
% 1.97/2.16            != (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ((k6_partfun1 @ (k1_relat_1 @ X0))
% 1.97/2.16              != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0)))),
% 1.97/2.16      inference('sup-', [status(thm)], ['62', '82'])).
% 1.97/2.16  thf('84', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0))
% 1.97/2.16          | ((k6_partfun1 @ (k1_relat_1 @ X0))
% 1.97/2.16              != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 1.97/2.16          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ X0))),
% 1.97/2.16      inference('simplify', [status(thm)], ['83'])).
% 1.97/2.16  thf('85', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (((k6_partfun1 @ (k1_relat_1 @ X0))
% 1.97/2.16            != (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0)))),
% 1.97/2.16      inference('sup-', [status(thm)], ['61', '84'])).
% 1.97/2.16  thf('86', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0))
% 1.97/2.16          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ X0))),
% 1.97/2.16      inference('simplify', [status(thm)], ['85'])).
% 1.97/2.16  thf('87', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0)))),
% 1.97/2.16      inference('sup-', [status(thm)], ['60', '86'])).
% 1.97/2.16  thf('88', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0))
% 1.97/2.16          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ X0))),
% 1.97/2.16      inference('simplify', [status(thm)], ['87'])).
% 1.97/2.16  thf('89', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0)))),
% 1.97/2.16      inference('sup-', [status(thm)], ['59', '88'])).
% 1.97/2.16  thf('90', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0))
% 1.97/2.16          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ X0))),
% 1.97/2.16      inference('simplify', [status(thm)], ['89'])).
% 1.97/2.16  thf('91', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0)))),
% 1.97/2.16      inference('sup-', [status(thm)], ['58', '90'])).
% 1.97/2.16  thf('92', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0))
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ X0))),
% 1.97/2.16      inference('simplify', [status(thm)], ['91'])).
% 1.97/2.16  thf('93', plain,
% 1.97/2.16      (![X10 : $i]:
% 1.97/2.16         (~ (v2_funct_1 @ X10)
% 1.97/2.16          | ((k5_relat_1 @ (k2_funct_1 @ X10) @ X10)
% 1.97/2.16              = (k6_relat_1 @ (k2_relat_1 @ X10)))
% 1.97/2.16          | ~ (v1_funct_1 @ X10)
% 1.97/2.16          | ~ (v1_relat_1 @ X10))),
% 1.97/2.16      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.97/2.16  thf('94', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 1.97/2.16      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.97/2.16  thf('95', plain,
% 1.97/2.16      (![X10 : $i]:
% 1.97/2.16         (~ (v2_funct_1 @ X10)
% 1.97/2.16          | ((k5_relat_1 @ (k2_funct_1 @ X10) @ X10)
% 1.97/2.16              = (k6_partfun1 @ (k2_relat_1 @ X10)))
% 1.97/2.16          | ~ (v1_funct_1 @ X10)
% 1.97/2.16          | ~ (v1_relat_1 @ X10))),
% 1.97/2.16      inference('demod', [status(thm)], ['93', '94'])).
% 1.97/2.16  thf('96', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.97/2.16            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 1.97/2.16      inference('sup+', [status(thm)], ['92', '95'])).
% 1.97/2.16  thf('97', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.97/2.16              = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 1.97/2.16      inference('sup-', [status(thm)], ['57', '96'])).
% 1.97/2.16  thf('98', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.97/2.16            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 1.97/2.16          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ X0))),
% 1.97/2.16      inference('simplify', [status(thm)], ['97'])).
% 1.97/2.16  thf('99', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.97/2.16              = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 1.97/2.16      inference('sup-', [status(thm)], ['56', '98'])).
% 1.97/2.16  thf('100', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.97/2.16            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 1.97/2.16          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ X0))),
% 1.97/2.16      inference('simplify', [status(thm)], ['99'])).
% 1.97/2.16  thf('101', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.97/2.16              = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 1.97/2.16      inference('sup-', [status(thm)], ['55', '100'])).
% 1.97/2.16  thf('102', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.97/2.16            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ X0))),
% 1.97/2.16      inference('simplify', [status(thm)], ['101'])).
% 1.97/2.16  thf('103', plain,
% 1.97/2.16      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf(redefinition_k2_relset_1, axiom,
% 1.97/2.16    (![A:$i,B:$i,C:$i]:
% 1.97/2.16     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.97/2.16       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.97/2.16  thf('104', plain,
% 1.97/2.16      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.97/2.16         (((k2_relset_1 @ X21 @ X22 @ X20) = (k2_relat_1 @ X20))
% 1.97/2.16          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.97/2.16      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.97/2.16  thf('105', plain,
% 1.97/2.16      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.97/2.16      inference('sup-', [status(thm)], ['103', '104'])).
% 1.97/2.16  thf('106', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf('107', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.97/2.16      inference('sup+', [status(thm)], ['105', '106'])).
% 1.97/2.16  thf('108', plain,
% 1.97/2.16      (![X5 : $i, X7 : $i, X8 : $i]:
% 1.97/2.16         (~ (v1_relat_1 @ X7)
% 1.97/2.16          | ~ (v1_funct_1 @ X7)
% 1.97/2.16          | ~ (v1_relat_1 @ X8)
% 1.97/2.16          | ~ (v1_funct_1 @ X8)
% 1.97/2.16          | ((X8) = (X7))
% 1.97/2.16          | ((k5_relat_1 @ X5 @ X8) != (k6_partfun1 @ (k2_relat_1 @ X7)))
% 1.97/2.16          | ((k5_relat_1 @ X7 @ X5) != (k6_partfun1 @ (k1_relat_1 @ X8)))
% 1.97/2.16          | ~ (v1_funct_1 @ X5)
% 1.97/2.16          | ~ (v1_relat_1 @ X5))),
% 1.97/2.16      inference('demod', [status(thm)], ['69', '70', '71'])).
% 1.97/2.16  thf('109', plain,
% 1.97/2.16      (![X0 : $i, X1 : $i]:
% 1.97/2.16         (((k5_relat_1 @ X1 @ X0) != (k6_partfun1 @ sk_B))
% 1.97/2.16          | ~ (v1_relat_1 @ X1)
% 1.97/2.16          | ~ (v1_funct_1 @ X1)
% 1.97/2.16          | ((k5_relat_1 @ sk_C @ X1) != (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.97/2.16          | ((X0) = (sk_C))
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ sk_C)
% 1.97/2.16          | ~ (v1_relat_1 @ sk_C))),
% 1.97/2.16      inference('sup-', [status(thm)], ['107', '108'])).
% 1.97/2.16  thf('110', plain, ((v1_funct_1 @ sk_C)),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf('111', plain,
% 1.97/2.16      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf(cc2_relat_1, axiom,
% 1.97/2.16    (![A:$i]:
% 1.97/2.16     ( ( v1_relat_1 @ A ) =>
% 1.97/2.16       ( ![B:$i]:
% 1.97/2.16         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.97/2.16  thf('112', plain,
% 1.97/2.16      (![X0 : $i, X1 : $i]:
% 1.97/2.16         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.97/2.16          | (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ X1))),
% 1.97/2.16      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.97/2.16  thf('113', plain,
% 1.97/2.16      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 1.97/2.16      inference('sup-', [status(thm)], ['111', '112'])).
% 1.97/2.16  thf(fc6_relat_1, axiom,
% 1.97/2.16    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.97/2.16  thf('114', plain,
% 1.97/2.16      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.97/2.16      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.97/2.16  thf('115', plain, ((v1_relat_1 @ sk_C)),
% 1.97/2.16      inference('demod', [status(thm)], ['113', '114'])).
% 1.97/2.16  thf('116', plain,
% 1.97/2.16      (![X0 : $i, X1 : $i]:
% 1.97/2.16         (((k5_relat_1 @ X1 @ X0) != (k6_partfun1 @ sk_B))
% 1.97/2.16          | ~ (v1_relat_1 @ X1)
% 1.97/2.16          | ~ (v1_funct_1 @ X1)
% 1.97/2.16          | ((k5_relat_1 @ sk_C @ X1) != (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.97/2.16          | ((X0) = (sk_C))
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ X0))),
% 1.97/2.16      inference('demod', [status(thm)], ['109', '110', '115'])).
% 1.97/2.16  thf('117', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (((k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.97/2.16            != (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.97/2.16          | ~ (v1_relat_1 @ sk_C)
% 1.97/2.16          | ~ (v1_funct_1 @ sk_C)
% 1.97/2.16          | ~ (v2_funct_1 @ sk_C)
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ((X0) = (sk_C))
% 1.97/2.16          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0) != (k6_partfun1 @ sk_B)))),
% 1.97/2.16      inference('sup-', [status(thm)], ['102', '116'])).
% 1.97/2.16  thf('118', plain, ((v1_relat_1 @ sk_C)),
% 1.97/2.16      inference('demod', [status(thm)], ['113', '114'])).
% 1.97/2.16  thf('119', plain, ((v1_funct_1 @ sk_C)),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf('120', plain, ((v2_funct_1 @ sk_C)),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf('121', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (((k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.97/2.16            != (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ((X0) = (sk_C))
% 1.97/2.16          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0) != (k6_partfun1 @ sk_B)))),
% 1.97/2.16      inference('demod', [status(thm)], ['117', '118', '119', '120'])).
% 1.97/2.16  thf('122', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (~ (v1_relat_1 @ sk_C)
% 1.97/2.16          | ~ (v1_funct_1 @ sk_C)
% 1.97/2.16          | ~ (v2_funct_1 @ sk_C)
% 1.97/2.16          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0) != (k6_partfun1 @ sk_B))
% 1.97/2.16          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16          | ((X0) = (sk_C))
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ((k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.97/2.16              != (k6_partfun1 @ (k1_relat_1 @ X0))))),
% 1.97/2.16      inference('sup-', [status(thm)], ['54', '121'])).
% 1.97/2.16  thf('123', plain, ((v1_relat_1 @ sk_C)),
% 1.97/2.16      inference('demod', [status(thm)], ['113', '114'])).
% 1.97/2.16  thf('124', plain, ((v1_funct_1 @ sk_C)),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf('125', plain, ((v2_funct_1 @ sk_C)),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf('126', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0) != (k6_partfun1 @ sk_B))
% 1.97/2.16          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16          | ((X0) = (sk_C))
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ((k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.97/2.16              != (k6_partfun1 @ (k1_relat_1 @ X0))))),
% 1.97/2.16      inference('demod', [status(thm)], ['122', '123', '124', '125'])).
% 1.97/2.16  thf('127', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (~ (v1_relat_1 @ sk_C)
% 1.97/2.16          | ~ (v1_funct_1 @ sk_C)
% 1.97/2.16          | ~ (v2_funct_1 @ sk_C)
% 1.97/2.16          | ((k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.97/2.16              != (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ((X0) = (sk_C))
% 1.97/2.16          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0) != (k6_partfun1 @ sk_B)))),
% 1.97/2.16      inference('sup-', [status(thm)], ['53', '126'])).
% 1.97/2.16  thf('128', plain, ((v1_relat_1 @ sk_C)),
% 1.97/2.16      inference('demod', [status(thm)], ['113', '114'])).
% 1.97/2.16  thf('129', plain, ((v1_funct_1 @ sk_C)),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf('130', plain, ((v2_funct_1 @ sk_C)),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf('131', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (((k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.97/2.16            != (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ((X0) = (sk_C))
% 1.97/2.16          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0) != (k6_partfun1 @ sk_B)))),
% 1.97/2.16      inference('demod', [status(thm)], ['127', '128', '129', '130'])).
% 1.97/2.16  thf('132', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (((k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.97/2.16            != (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_funct_1 @ X0))
% 1.97/2.16              != (k6_partfun1 @ sk_B))
% 1.97/2.16          | ((k2_funct_1 @ X0) = (sk_C))
% 1.97/2.16          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.97/2.16      inference('sup-', [status(thm)], ['52', '131'])).
% 1.97/2.16  thf('133', plain,
% 1.97/2.16      ((~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.97/2.16        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.97/2.16        | ((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (sk_C))
% 1.97/2.16        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 1.97/2.16            (k2_funct_1 @ (k2_funct_1 @ sk_C))) != (k6_partfun1 @ sk_B))
% 1.97/2.16        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.97/2.16      inference('eq_res', [status(thm)], ['132'])).
% 1.97/2.16  thf('134', plain,
% 1.97/2.16      ((((k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.97/2.16          != (k6_partfun1 @ sk_B))
% 1.97/2.16        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16        | ((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (sk_C))
% 1.97/2.16        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.97/2.16        | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.97/2.16      inference('sup-', [status(thm)], ['51', '133'])).
% 1.97/2.16  thf('135', plain,
% 1.97/2.16      ((~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.97/2.16        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.97/2.16        | ((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (sk_C))
% 1.97/2.16        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16        | ((k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.97/2.16            != (k6_partfun1 @ sk_B)))),
% 1.97/2.16      inference('simplify', [status(thm)], ['134'])).
% 1.97/2.16  thf('136', plain,
% 1.97/2.16      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16        | ((k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.97/2.16            != (k6_partfun1 @ sk_B))
% 1.97/2.16        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16        | ((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (sk_C))
% 1.97/2.16        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.97/2.16      inference('sup-', [status(thm)], ['48', '135'])).
% 1.97/2.16  thf('137', plain,
% 1.97/2.16      ((~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.97/2.16        | ((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (sk_C))
% 1.97/2.16        | ((k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.97/2.16            != (k6_partfun1 @ sk_B))
% 1.97/2.16        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.97/2.16      inference('simplify', [status(thm)], ['136'])).
% 1.97/2.16  thf('138', plain,
% 1.97/2.16      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16        | ((k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.97/2.16            != (k6_partfun1 @ sk_B))
% 1.97/2.16        | ((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (sk_C)))),
% 1.97/2.16      inference('sup-', [status(thm)], ['47', '137'])).
% 1.97/2.16  thf('139', plain,
% 1.97/2.16      ((((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (sk_C))
% 1.97/2.16        | ((k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.97/2.16            != (k6_partfun1 @ sk_B))
% 1.97/2.16        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.97/2.16      inference('simplify', [status(thm)], ['138'])).
% 1.97/2.16  thf('140', plain,
% 1.97/2.16      ((((k6_partfun1 @ (k2_relat_1 @ sk_C)) != (k6_partfun1 @ sk_B))
% 1.97/2.16        | ~ (v1_relat_1 @ sk_C)
% 1.97/2.16        | ~ (v1_funct_1 @ sk_C)
% 1.97/2.16        | ~ (v2_funct_1 @ sk_C)
% 1.97/2.16        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16        | ((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (sk_C)))),
% 1.97/2.16      inference('sup-', [status(thm)], ['46', '139'])).
% 1.97/2.16  thf('141', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.97/2.16      inference('sup+', [status(thm)], ['105', '106'])).
% 1.97/2.16  thf('142', plain, ((v1_relat_1 @ sk_C)),
% 1.97/2.16      inference('demod', [status(thm)], ['113', '114'])).
% 1.97/2.16  thf('143', plain, ((v1_funct_1 @ sk_C)),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf('144', plain, ((v2_funct_1 @ sk_C)),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf('145', plain,
% 1.97/2.16      ((((k6_partfun1 @ sk_B) != (k6_partfun1 @ sk_B))
% 1.97/2.16        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16        | ((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (sk_C)))),
% 1.97/2.16      inference('demod', [status(thm)], ['140', '141', '142', '143', '144'])).
% 1.97/2.16  thf('146', plain,
% 1.97/2.16      ((((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (sk_C))
% 1.97/2.16        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.97/2.16      inference('simplify', [status(thm)], ['145'])).
% 1.97/2.16  thf('147', plain,
% 1.97/2.16      ((~ (v1_relat_1 @ sk_C)
% 1.97/2.16        | ~ (v1_funct_1 @ sk_C)
% 1.97/2.16        | ~ (v2_funct_1 @ sk_C)
% 1.97/2.16        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16        | ((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (sk_C)))),
% 1.97/2.16      inference('sup-', [status(thm)], ['45', '146'])).
% 1.97/2.16  thf('148', plain, ((v1_relat_1 @ sk_C)),
% 1.97/2.16      inference('demod', [status(thm)], ['113', '114'])).
% 1.97/2.16  thf('149', plain, ((v1_funct_1 @ sk_C)),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf('150', plain, ((v2_funct_1 @ sk_C)),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf('151', plain,
% 1.97/2.16      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16        | ((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (sk_C)))),
% 1.97/2.16      inference('demod', [status(thm)], ['147', '148', '149', '150'])).
% 1.97/2.16  thf('152', plain,
% 1.97/2.16      ((~ (v1_relat_1 @ sk_C)
% 1.97/2.16        | ~ (v1_funct_1 @ sk_C)
% 1.97/2.16        | ~ (v2_funct_1 @ sk_C)
% 1.97/2.16        | ((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (sk_C))
% 1.97/2.16        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.97/2.16      inference('sup-', [status(thm)], ['44', '151'])).
% 1.97/2.16  thf('153', plain, ((v1_relat_1 @ sk_C)),
% 1.97/2.16      inference('demod', [status(thm)], ['113', '114'])).
% 1.97/2.16  thf('154', plain, ((v1_funct_1 @ sk_C)),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf('155', plain, ((v2_funct_1 @ sk_C)),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf('156', plain,
% 1.97/2.16      ((((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (sk_C))
% 1.97/2.16        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.97/2.16      inference('demod', [status(thm)], ['152', '153', '154', '155'])).
% 1.97/2.16  thf('157', plain,
% 1.97/2.16      ((~ (v1_relat_1 @ sk_C)
% 1.97/2.16        | ~ (v1_funct_1 @ sk_C)
% 1.97/2.16        | ~ (v2_funct_1 @ sk_C)
% 1.97/2.16        | ((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (sk_C)))),
% 1.97/2.16      inference('sup-', [status(thm)], ['43', '156'])).
% 1.97/2.16  thf('158', plain, ((v1_relat_1 @ sk_C)),
% 1.97/2.16      inference('demod', [status(thm)], ['113', '114'])).
% 1.97/2.16  thf('159', plain, ((v1_funct_1 @ sk_C)),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf('160', plain, ((v2_funct_1 @ sk_C)),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf('161', plain, (((k2_funct_1 @ (k2_funct_1 @ sk_C)) = (sk_C))),
% 1.97/2.16      inference('demod', [status(thm)], ['157', '158', '159', '160'])).
% 1.97/2.16  thf('162', plain,
% 1.97/2.16      (![X4 : $i]:
% 1.97/2.16         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 1.97/2.16          | ~ (v2_funct_1 @ X4)
% 1.97/2.16          | ~ (v1_funct_1 @ X4)
% 1.97/2.16          | ~ (v1_relat_1 @ X4))),
% 1.97/2.16      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.97/2.16  thf('163', plain,
% 1.97/2.16      (![X4 : $i]:
% 1.97/2.16         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 1.97/2.16          | ~ (v2_funct_1 @ X4)
% 1.97/2.16          | ~ (v1_funct_1 @ X4)
% 1.97/2.16          | ~ (v1_relat_1 @ X4))),
% 1.97/2.16      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.97/2.16  thf('164', plain,
% 1.97/2.16      (![X4 : $i]:
% 1.97/2.16         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 1.97/2.16          | ~ (v2_funct_1 @ X4)
% 1.97/2.16          | ~ (v1_funct_1 @ X4)
% 1.97/2.16          | ~ (v1_relat_1 @ X4))),
% 1.97/2.16      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.97/2.16  thf('165', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (((k2_funct_1 @ (k2_funct_1 @ X0)) = (X0))
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ X0))),
% 1.97/2.16      inference('simplify', [status(thm)], ['91'])).
% 1.97/2.16  thf('166', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.97/2.16            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ X0))),
% 1.97/2.16      inference('simplify', [status(thm)], ['101'])).
% 1.97/2.16  thf('167', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 1.97/2.16            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 1.97/2.16      inference('sup+', [status(thm)], ['165', '166'])).
% 1.97/2.16  thf('168', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 1.97/2.16              = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))),
% 1.97/2.16      inference('sup-', [status(thm)], ['164', '167'])).
% 1.97/2.16  thf('169', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 1.97/2.16            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 1.97/2.16          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ X0))),
% 1.97/2.16      inference('simplify', [status(thm)], ['168'])).
% 1.97/2.16  thf('170', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 1.97/2.16              = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))),
% 1.97/2.16      inference('sup-', [status(thm)], ['163', '169'])).
% 1.97/2.16  thf('171', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 1.97/2.16            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 1.97/2.16          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ X0))),
% 1.97/2.16      inference('simplify', [status(thm)], ['170'])).
% 1.97/2.16  thf('172', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 1.97/2.16              = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))),
% 1.97/2.16      inference('sup-', [status(thm)], ['162', '171'])).
% 1.97/2.16  thf('173', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 1.97/2.16            = (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ X0))),
% 1.97/2.16      inference('simplify', [status(thm)], ['172'])).
% 1.97/2.16  thf('174', plain,
% 1.97/2.16      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 1.97/2.16          = (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 1.97/2.16        | ~ (v1_relat_1 @ sk_C)
% 1.97/2.16        | ~ (v1_funct_1 @ sk_C)
% 1.97/2.16        | ~ (v2_funct_1 @ sk_C))),
% 1.97/2.16      inference('sup+', [status(thm)], ['161', '173'])).
% 1.97/2.16  thf('175', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.97/2.16      inference('sup+', [status(thm)], ['105', '106'])).
% 1.97/2.16  thf('176', plain, ((v1_relat_1 @ sk_C)),
% 1.97/2.16      inference('demod', [status(thm)], ['113', '114'])).
% 1.97/2.16  thf('177', plain, ((v1_funct_1 @ sk_C)),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf('178', plain, ((v2_funct_1 @ sk_C)),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf('179', plain,
% 1.97/2.16      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 1.97/2.16      inference('demod', [status(thm)], ['174', '175', '176', '177', '178'])).
% 1.97/2.16  thf('180', plain,
% 1.97/2.16      (![X9 : $i]:
% 1.97/2.16         (~ (v2_funct_1 @ X9)
% 1.97/2.16          | ((k1_relat_1 @ X9) = (k2_relat_1 @ (k2_funct_1 @ X9)))
% 1.97/2.16          | ~ (v1_funct_1 @ X9)
% 1.97/2.16          | ~ (v1_relat_1 @ X9))),
% 1.97/2.16      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.97/2.16  thf('181', plain,
% 1.97/2.16      (![X5 : $i, X7 : $i, X8 : $i]:
% 1.97/2.16         (~ (v1_relat_1 @ X7)
% 1.97/2.16          | ~ (v1_funct_1 @ X7)
% 1.97/2.16          | ~ (v1_relat_1 @ X8)
% 1.97/2.16          | ~ (v1_funct_1 @ X8)
% 1.97/2.16          | ((X8) = (X7))
% 1.97/2.16          | ((k5_relat_1 @ X5 @ X8) != (k6_partfun1 @ (k2_relat_1 @ X7)))
% 1.97/2.16          | ((k5_relat_1 @ X7 @ X5) != (k6_partfun1 @ (k1_relat_1 @ X8)))
% 1.97/2.16          | ~ (v1_funct_1 @ X5)
% 1.97/2.16          | ~ (v1_relat_1 @ X5))),
% 1.97/2.16      inference('demod', [status(thm)], ['69', '70', '71'])).
% 1.97/2.16  thf('182', plain,
% 1.97/2.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.97/2.16         (((k5_relat_1 @ X2 @ X1) != (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v2_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ X2)
% 1.97/2.16          | ~ (v1_funct_1 @ X2)
% 1.97/2.16          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X2)
% 1.97/2.16              != (k6_partfun1 @ (k1_relat_1 @ X1)))
% 1.97/2.16          | ((X1) = (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v1_funct_1 @ X1)
% 1.97/2.16          | ~ (v1_relat_1 @ X1)
% 1.97/2.16          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.97/2.16          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.97/2.16      inference('sup-', [status(thm)], ['180', '181'])).
% 1.97/2.16  thf('183', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (((k6_partfun1 @ sk_B) != (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.97/2.16          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ((X0) = (k2_funct_1 @ sk_C))
% 1.97/2.16          | ~ (v1_funct_1 @ sk_C)
% 1.97/2.16          | ~ (v1_relat_1 @ sk_C)
% 1.97/2.16          | ~ (v2_funct_1 @ sk_C)
% 1.97/2.16          | ~ (v1_funct_1 @ sk_C)
% 1.97/2.16          | ~ (v1_relat_1 @ sk_C)
% 1.97/2.16          | ((k5_relat_1 @ sk_C @ X0) != (k6_partfun1 @ (k1_relat_1 @ sk_C))))),
% 1.97/2.16      inference('sup-', [status(thm)], ['179', '182'])).
% 1.97/2.16  thf('184', plain, ((v1_funct_1 @ sk_C)),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf('185', plain, ((v1_relat_1 @ sk_C)),
% 1.97/2.16      inference('demod', [status(thm)], ['113', '114'])).
% 1.97/2.16  thf('186', plain, ((v2_funct_1 @ sk_C)),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf('187', plain, ((v1_funct_1 @ sk_C)),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf('188', plain, ((v1_relat_1 @ sk_C)),
% 1.97/2.16      inference('demod', [status(thm)], ['113', '114'])).
% 1.97/2.16  thf('189', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf('190', plain,
% 1.97/2.16      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.97/2.16         (~ (v1_funct_2 @ X37 @ X35 @ X36)
% 1.97/2.16          | ((X35) = (k1_relset_1 @ X35 @ X36 @ X37))
% 1.97/2.16          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.97/2.16  thf('191', plain,
% 1.97/2.16      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 1.97/2.16        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 1.97/2.16      inference('sup-', [status(thm)], ['189', '190'])).
% 1.97/2.16  thf('192', plain,
% 1.97/2.16      (![X33 : $i, X34 : $i]:
% 1.97/2.16         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.97/2.16  thf('193', plain,
% 1.97/2.16      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf('194', plain,
% 1.97/2.16      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.97/2.16         (~ (zip_tseitin_0 @ X38 @ X39)
% 1.97/2.16          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 1.97/2.16          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.97/2.16  thf('195', plain,
% 1.97/2.16      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.97/2.16      inference('sup-', [status(thm)], ['193', '194'])).
% 1.97/2.16  thf('196', plain,
% 1.97/2.16      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 1.97/2.16      inference('sup-', [status(thm)], ['192', '195'])).
% 1.97/2.16  thf('197', plain, (((sk_B) != (k1_xboole_0))),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf('198', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 1.97/2.16      inference('simplify_reflect-', [status(thm)], ['196', '197'])).
% 1.97/2.16  thf('199', plain,
% 1.97/2.16      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf('200', plain,
% 1.97/2.16      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.97/2.16         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 1.97/2.16          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.97/2.16      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.97/2.16  thf('201', plain,
% 1.97/2.16      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 1.97/2.16      inference('sup-', [status(thm)], ['199', '200'])).
% 1.97/2.16  thf('202', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 1.97/2.16      inference('demod', [status(thm)], ['191', '198', '201'])).
% 1.97/2.16  thf('203', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (((k6_partfun1 @ sk_B) != (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.97/2.16          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ((X0) = (k2_funct_1 @ sk_C))
% 1.97/2.16          | ((k5_relat_1 @ sk_C @ X0) != (k6_partfun1 @ sk_A)))),
% 1.97/2.16      inference('demod', [status(thm)],
% 1.97/2.16                ['183', '184', '185', '186', '187', '188', '202'])).
% 1.97/2.16  thf('204', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (~ (v1_relat_1 @ sk_C)
% 1.97/2.16          | ~ (v1_funct_1 @ sk_C)
% 1.97/2.16          | ~ (v2_funct_1 @ sk_C)
% 1.97/2.16          | ((k5_relat_1 @ sk_C @ X0) != (k6_partfun1 @ sk_A))
% 1.97/2.16          | ((X0) = (k2_funct_1 @ sk_C))
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16          | ((k6_partfun1 @ sk_B) != (k6_partfun1 @ (k1_relat_1 @ X0))))),
% 1.97/2.16      inference('sup-', [status(thm)], ['42', '203'])).
% 1.97/2.16  thf('205', plain, ((v1_relat_1 @ sk_C)),
% 1.97/2.16      inference('demod', [status(thm)], ['113', '114'])).
% 1.97/2.16  thf('206', plain, ((v1_funct_1 @ sk_C)),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf('207', plain, ((v2_funct_1 @ sk_C)),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf('208', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (((k5_relat_1 @ sk_C @ X0) != (k6_partfun1 @ sk_A))
% 1.97/2.16          | ((X0) = (k2_funct_1 @ sk_C))
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.97/2.16          | ((k6_partfun1 @ sk_B) != (k6_partfun1 @ (k1_relat_1 @ X0))))),
% 1.97/2.16      inference('demod', [status(thm)], ['204', '205', '206', '207'])).
% 1.97/2.16  thf('209', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (~ (v1_relat_1 @ sk_C)
% 1.97/2.16          | ~ (v1_funct_1 @ sk_C)
% 1.97/2.16          | ~ (v2_funct_1 @ sk_C)
% 1.97/2.16          | ((k6_partfun1 @ sk_B) != (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ((X0) = (k2_funct_1 @ sk_C))
% 1.97/2.16          | ((k5_relat_1 @ sk_C @ X0) != (k6_partfun1 @ sk_A)))),
% 1.97/2.16      inference('sup-', [status(thm)], ['41', '208'])).
% 1.97/2.16  thf('210', plain, ((v1_relat_1 @ sk_C)),
% 1.97/2.16      inference('demod', [status(thm)], ['113', '114'])).
% 1.97/2.16  thf('211', plain, ((v1_funct_1 @ sk_C)),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf('212', plain, ((v2_funct_1 @ sk_C)),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf('213', plain,
% 1.97/2.16      (![X0 : $i]:
% 1.97/2.16         (((k6_partfun1 @ sk_B) != (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.97/2.16          | ~ (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_funct_1 @ X0)
% 1.97/2.16          | ((X0) = (k2_funct_1 @ sk_C))
% 1.97/2.16          | ((k5_relat_1 @ sk_C @ X0) != (k6_partfun1 @ sk_A)))),
% 1.97/2.16      inference('demod', [status(thm)], ['209', '210', '211', '212'])).
% 1.97/2.16  thf('214', plain,
% 1.97/2.16      ((((k6_partfun1 @ sk_B) != (k6_partfun1 @ sk_B))
% 1.97/2.16        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_partfun1 @ sk_A))
% 1.97/2.16        | ((sk_D) = (k2_funct_1 @ sk_C))
% 1.97/2.16        | ~ (v1_funct_1 @ sk_D)
% 1.97/2.16        | ~ (v1_relat_1 @ sk_D))),
% 1.97/2.16      inference('sup-', [status(thm)], ['40', '213'])).
% 1.97/2.16  thf('215', plain, ((v1_funct_1 @ sk_D)),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf('216', plain,
% 1.97/2.16      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf('217', plain,
% 1.97/2.16      (![X0 : $i, X1 : $i]:
% 1.97/2.16         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.97/2.16          | (v1_relat_1 @ X0)
% 1.97/2.16          | ~ (v1_relat_1 @ X1))),
% 1.97/2.16      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.97/2.16  thf('218', plain,
% 1.97/2.16      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 1.97/2.16      inference('sup-', [status(thm)], ['216', '217'])).
% 1.97/2.16  thf('219', plain,
% 1.97/2.16      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.97/2.16      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.97/2.16  thf('220', plain, ((v1_relat_1 @ sk_D)),
% 1.97/2.16      inference('demod', [status(thm)], ['218', '219'])).
% 1.97/2.16  thf('221', plain,
% 1.97/2.16      ((((k6_partfun1 @ sk_B) != (k6_partfun1 @ sk_B))
% 1.97/2.16        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_partfun1 @ sk_A))
% 1.97/2.16        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 1.97/2.16      inference('demod', [status(thm)], ['214', '215', '220'])).
% 1.97/2.16  thf('222', plain,
% 1.97/2.16      ((((sk_D) = (k2_funct_1 @ sk_C))
% 1.97/2.16        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_partfun1 @ sk_A)))),
% 1.97/2.16      inference('simplify', [status(thm)], ['221'])).
% 1.97/2.16  thf('223', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.97/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.16  thf('224', plain, (((k5_relat_1 @ sk_C @ sk_D) != (k6_partfun1 @ sk_A))),
% 1.97/2.16      inference('simplify_reflect-', [status(thm)], ['222', '223'])).
% 1.97/2.16  thf('225', plain, ($false),
% 1.97/2.16      inference('simplify_reflect-', [status(thm)], ['26', '224'])).
% 1.97/2.16  
% 1.97/2.16  % SZS output end Refutation
% 1.97/2.16  
% 1.97/2.17  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

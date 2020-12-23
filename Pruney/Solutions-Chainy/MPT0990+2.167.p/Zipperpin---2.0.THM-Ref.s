%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.e0eTQJYv01

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:23 EST 2020

% Result     : Theorem 2.73s
% Output     : Refutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 229 expanded)
%              Number of leaves         :   43 (  87 expanded)
%              Depth                    :   14
%              Number of atoms          : 1348 (4846 expanded)
%              Number of equality atoms :  111 ( 374 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

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
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( ( k1_partfun1 @ X32 @ X33 @ X35 @ X36 @ X31 @ X34 )
        = ( k5_relat_1 @ X31 @ X34 ) ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X30 ) ) ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( X12 = X15 )
      | ~ ( r2_relset_1 @ X13 @ X14 @ X12 @ X15 ) ) ),
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

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('21',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X16 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('22',plain,(
    ! [X37: $i] :
      ( ( k6_partfun1 @ X37 )
      = ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('23',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X16 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X16 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['6','7','24'])).

thf('26',plain,(
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

thf('27',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('28',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('29',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('30',plain,(
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

thf('31',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('32',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('37',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('38',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['28','35','38'])).

thf('40',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('42',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('46',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('52',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['42','49','52'])).

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

thf('54',plain,(
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

thf('55',plain,(
    ! [X37: $i] :
      ( ( k6_partfun1 @ X37 )
      = ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('56',plain,(
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
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
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
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('60',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('61',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('62',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['60','61'])).

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
    inference(demod,[status(thm)],['57','62','63','64'])).

thf('66',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != sk_B )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
     != ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('69',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('71',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != sk_B )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
     != ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','71','72'])).

thf('74',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != sk_B )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
     != ( k6_partfun1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['73','74'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('76',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X6 ) @ X6 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('77',plain,(
    ! [X37: $i] :
      ( ( k6_partfun1 @ X37 )
      = ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('78',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X6 ) @ X6 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
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

thf('80',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( X38 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X38 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X39 ) @ X39 )
        = ( k6_partfun1 @ X38 ) )
      | ~ ( v2_funct_1 @ X39 )
      | ( ( k2_relset_1 @ X40 @ X38 @ X39 )
       != X38 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('81',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['81','82','83','84','85'])).

thf('87',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['78','89'])).

thf('91',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['60','61'])).

thf('92',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['90','91','92','93'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('95',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('96',plain,(
    ! [X37: $i] :
      ( ( k6_partfun1 @ X37 )
      = ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('97',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['94','97'])).

thf('99',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('100',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
     != ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','100'])).

thf('102',plain,(
    ( k5_relat_1 @ sk_C @ sk_D )
 != ( k6_partfun1 @ sk_A ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['25','102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.e0eTQJYv01
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:47:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.73/2.91  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.73/2.91  % Solved by: fo/fo7.sh
% 2.73/2.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.73/2.91  % done 867 iterations in 2.452s
% 2.73/2.91  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.73/2.91  % SZS output start Refutation
% 2.73/2.91  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.73/2.91  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.73/2.91  thf(sk_C_type, type, sk_C: $i).
% 2.73/2.91  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.73/2.91  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.73/2.91  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.73/2.91  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.73/2.91  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.73/2.91  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.73/2.91  thf(sk_D_type, type, sk_D: $i).
% 2.73/2.91  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.73/2.91  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.73/2.91  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.73/2.91  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.73/2.91  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.73/2.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.73/2.91  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.73/2.91  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.73/2.91  thf(sk_A_type, type, sk_A: $i).
% 2.73/2.91  thf(sk_B_type, type, sk_B: $i).
% 2.73/2.91  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.73/2.91  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.73/2.91  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.73/2.91  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.73/2.91  thf(t36_funct_2, conjecture,
% 2.73/2.91    (![A:$i,B:$i,C:$i]:
% 2.73/2.91     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.73/2.91         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.73/2.91       ( ![D:$i]:
% 2.73/2.91         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.73/2.91             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.73/2.91           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.73/2.91               ( r2_relset_1 @
% 2.73/2.91                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.73/2.91                 ( k6_partfun1 @ A ) ) & 
% 2.73/2.91               ( v2_funct_1 @ C ) ) =>
% 2.73/2.91             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.73/2.91               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 2.73/2.91  thf(zf_stmt_0, negated_conjecture,
% 2.73/2.91    (~( ![A:$i,B:$i,C:$i]:
% 2.73/2.91        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.73/2.91            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.73/2.91          ( ![D:$i]:
% 2.73/2.91            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.73/2.91                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.73/2.91              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.73/2.91                  ( r2_relset_1 @
% 2.73/2.91                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.73/2.91                    ( k6_partfun1 @ A ) ) & 
% 2.73/2.91                  ( v2_funct_1 @ C ) ) =>
% 2.73/2.91                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.73/2.91                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 2.73/2.91    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 2.73/2.91  thf('0', plain,
% 2.73/2.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.91  thf('1', plain,
% 2.73/2.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.91  thf(redefinition_k1_partfun1, axiom,
% 2.73/2.91    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.73/2.91     ( ( ( v1_funct_1 @ E ) & 
% 2.73/2.91         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.73/2.91         ( v1_funct_1 @ F ) & 
% 2.73/2.91         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.73/2.91       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.73/2.91  thf('2', plain,
% 2.73/2.91      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 2.73/2.91         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 2.73/2.91          | ~ (v1_funct_1 @ X31)
% 2.73/2.91          | ~ (v1_funct_1 @ X34)
% 2.73/2.91          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 2.73/2.91          | ((k1_partfun1 @ X32 @ X33 @ X35 @ X36 @ X31 @ X34)
% 2.73/2.91              = (k5_relat_1 @ X31 @ X34)))),
% 2.73/2.91      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 2.73/2.91  thf('3', plain,
% 2.73/2.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.73/2.91         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.73/2.91            = (k5_relat_1 @ sk_C @ X0))
% 2.73/2.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.73/2.91          | ~ (v1_funct_1 @ X0)
% 2.73/2.91          | ~ (v1_funct_1 @ sk_C))),
% 2.73/2.91      inference('sup-', [status(thm)], ['1', '2'])).
% 2.73/2.91  thf('4', plain, ((v1_funct_1 @ sk_C)),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.91  thf('5', plain,
% 2.73/2.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.73/2.91         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.73/2.91            = (k5_relat_1 @ sk_C @ X0))
% 2.73/2.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.73/2.91          | ~ (v1_funct_1 @ X0))),
% 2.73/2.91      inference('demod', [status(thm)], ['3', '4'])).
% 2.73/2.91  thf('6', plain,
% 2.73/2.91      ((~ (v1_funct_1 @ sk_D)
% 2.73/2.91        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.73/2.91            = (k5_relat_1 @ sk_C @ sk_D)))),
% 2.73/2.91      inference('sup-', [status(thm)], ['0', '5'])).
% 2.73/2.91  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.91  thf('8', plain,
% 2.73/2.91      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.73/2.91        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.73/2.91        (k6_partfun1 @ sk_A))),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.91  thf('9', plain,
% 2.73/2.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.91  thf('10', plain,
% 2.73/2.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.91  thf(dt_k1_partfun1, axiom,
% 2.73/2.91    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.73/2.91     ( ( ( v1_funct_1 @ E ) & 
% 2.73/2.91         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.73/2.91         ( v1_funct_1 @ F ) & 
% 2.73/2.91         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.73/2.91       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.73/2.91         ( m1_subset_1 @
% 2.73/2.91           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.73/2.91           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.73/2.91  thf('11', plain,
% 2.73/2.91      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 2.73/2.91         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 2.73/2.91          | ~ (v1_funct_1 @ X25)
% 2.73/2.91          | ~ (v1_funct_1 @ X28)
% 2.73/2.91          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 2.73/2.91          | (m1_subset_1 @ (k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28) @ 
% 2.73/2.91             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X30))))),
% 2.73/2.91      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.73/2.91  thf('12', plain,
% 2.73/2.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.73/2.91         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.73/2.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.73/2.91          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.73/2.91          | ~ (v1_funct_1 @ X1)
% 2.73/2.91          | ~ (v1_funct_1 @ sk_C))),
% 2.73/2.91      inference('sup-', [status(thm)], ['10', '11'])).
% 2.73/2.91  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.91  thf('14', plain,
% 2.73/2.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.73/2.91         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.73/2.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.73/2.91          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.73/2.91          | ~ (v1_funct_1 @ X1))),
% 2.73/2.91      inference('demod', [status(thm)], ['12', '13'])).
% 2.73/2.91  thf('15', plain,
% 2.73/2.91      ((~ (v1_funct_1 @ sk_D)
% 2.73/2.91        | (m1_subset_1 @ 
% 2.73/2.91           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.73/2.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.73/2.91      inference('sup-', [status(thm)], ['9', '14'])).
% 2.73/2.91  thf('16', plain, ((v1_funct_1 @ sk_D)),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.91  thf('17', plain,
% 2.73/2.91      ((m1_subset_1 @ 
% 2.73/2.91        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.73/2.91        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.73/2.91      inference('demod', [status(thm)], ['15', '16'])).
% 2.73/2.91  thf(redefinition_r2_relset_1, axiom,
% 2.73/2.91    (![A:$i,B:$i,C:$i,D:$i]:
% 2.73/2.91     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.73/2.91         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.73/2.91       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.73/2.91  thf('18', plain,
% 2.73/2.91      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 2.73/2.91         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 2.73/2.91          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 2.73/2.91          | ((X12) = (X15))
% 2.73/2.91          | ~ (r2_relset_1 @ X13 @ X14 @ X12 @ X15))),
% 2.73/2.91      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.73/2.91  thf('19', plain,
% 2.73/2.91      (![X0 : $i]:
% 2.73/2.91         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.73/2.91             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 2.73/2.91          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 2.73/2.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.73/2.91      inference('sup-', [status(thm)], ['17', '18'])).
% 2.73/2.91  thf('20', plain,
% 2.73/2.91      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 2.73/2.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.73/2.91        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.73/2.91            = (k6_partfun1 @ sk_A)))),
% 2.73/2.91      inference('sup-', [status(thm)], ['8', '19'])).
% 2.73/2.91  thf(t29_relset_1, axiom,
% 2.73/2.91    (![A:$i]:
% 2.73/2.91     ( m1_subset_1 @
% 2.73/2.91       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 2.73/2.91  thf('21', plain,
% 2.73/2.91      (![X16 : $i]:
% 2.73/2.91         (m1_subset_1 @ (k6_relat_1 @ X16) @ 
% 2.73/2.91          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X16)))),
% 2.73/2.91      inference('cnf', [status(esa)], [t29_relset_1])).
% 2.73/2.91  thf(redefinition_k6_partfun1, axiom,
% 2.73/2.91    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.73/2.91  thf('22', plain, (![X37 : $i]: ((k6_partfun1 @ X37) = (k6_relat_1 @ X37))),
% 2.73/2.91      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.73/2.91  thf('23', plain,
% 2.73/2.91      (![X16 : $i]:
% 2.73/2.91         (m1_subset_1 @ (k6_partfun1 @ X16) @ 
% 2.73/2.91          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X16)))),
% 2.73/2.91      inference('demod', [status(thm)], ['21', '22'])).
% 2.73/2.91  thf('24', plain,
% 2.73/2.91      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.73/2.91         = (k6_partfun1 @ sk_A))),
% 2.73/2.91      inference('demod', [status(thm)], ['20', '23'])).
% 2.73/2.91  thf('25', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 2.73/2.91      inference('demod', [status(thm)], ['6', '7', '24'])).
% 2.73/2.91  thf('26', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.91  thf(d1_funct_2, axiom,
% 2.73/2.91    (![A:$i,B:$i,C:$i]:
% 2.73/2.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.73/2.91       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.73/2.91           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.73/2.91             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.73/2.91         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.73/2.91           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.73/2.91             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.73/2.91  thf(zf_stmt_1, axiom,
% 2.73/2.91    (![C:$i,B:$i,A:$i]:
% 2.73/2.91     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.73/2.91       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.73/2.91  thf('27', plain,
% 2.73/2.91      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.73/2.91         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 2.73/2.91          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 2.73/2.91          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.73/2.91  thf('28', plain,
% 2.73/2.91      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 2.73/2.91        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 2.73/2.91      inference('sup-', [status(thm)], ['26', '27'])).
% 2.73/2.91  thf(zf_stmt_2, axiom,
% 2.73/2.91    (![B:$i,A:$i]:
% 2.73/2.91     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.73/2.91       ( zip_tseitin_0 @ B @ A ) ))).
% 2.73/2.91  thf('29', plain,
% 2.73/2.91      (![X17 : $i, X18 : $i]:
% 2.73/2.91         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.73/2.91  thf('30', plain,
% 2.73/2.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.91  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.73/2.91  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.73/2.91  thf(zf_stmt_5, axiom,
% 2.73/2.91    (![A:$i,B:$i,C:$i]:
% 2.73/2.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.73/2.91       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.73/2.91         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.73/2.91           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.73/2.91             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.73/2.91  thf('31', plain,
% 2.73/2.91      (![X22 : $i, X23 : $i, X24 : $i]:
% 2.73/2.91         (~ (zip_tseitin_0 @ X22 @ X23)
% 2.73/2.91          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 2.73/2.91          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.73/2.91  thf('32', plain,
% 2.73/2.91      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 2.73/2.91      inference('sup-', [status(thm)], ['30', '31'])).
% 2.73/2.91  thf('33', plain,
% 2.73/2.91      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 2.73/2.91      inference('sup-', [status(thm)], ['29', '32'])).
% 2.73/2.91  thf('34', plain, (((sk_A) != (k1_xboole_0))),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.91  thf('35', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 2.73/2.91      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 2.73/2.91  thf('36', plain,
% 2.73/2.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.91  thf(redefinition_k1_relset_1, axiom,
% 2.73/2.91    (![A:$i,B:$i,C:$i]:
% 2.73/2.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.73/2.91       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.73/2.91  thf('37', plain,
% 2.73/2.91      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.73/2.91         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 2.73/2.91          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 2.73/2.91      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.73/2.91  thf('38', plain,
% 2.73/2.91      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 2.73/2.91      inference('sup-', [status(thm)], ['36', '37'])).
% 2.73/2.91  thf('39', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 2.73/2.91      inference('demod', [status(thm)], ['28', '35', '38'])).
% 2.73/2.91  thf('40', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.91  thf('41', plain,
% 2.73/2.91      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.73/2.91         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 2.73/2.91          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 2.73/2.91          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.73/2.91  thf('42', plain,
% 2.73/2.91      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 2.73/2.91        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 2.73/2.91      inference('sup-', [status(thm)], ['40', '41'])).
% 2.73/2.91  thf('43', plain,
% 2.73/2.91      (![X17 : $i, X18 : $i]:
% 2.73/2.91         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.73/2.91  thf('44', plain,
% 2.73/2.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.91  thf('45', plain,
% 2.73/2.91      (![X22 : $i, X23 : $i, X24 : $i]:
% 2.73/2.91         (~ (zip_tseitin_0 @ X22 @ X23)
% 2.73/2.91          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 2.73/2.91          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.73/2.91  thf('46', plain,
% 2.73/2.91      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 2.73/2.91      inference('sup-', [status(thm)], ['44', '45'])).
% 2.73/2.91  thf('47', plain,
% 2.73/2.91      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 2.73/2.91      inference('sup-', [status(thm)], ['43', '46'])).
% 2.73/2.91  thf('48', plain, (((sk_B) != (k1_xboole_0))),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.91  thf('49', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 2.73/2.91      inference('simplify_reflect-', [status(thm)], ['47', '48'])).
% 2.73/2.91  thf('50', plain,
% 2.73/2.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.91  thf('51', plain,
% 2.73/2.91      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.73/2.91         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 2.73/2.91          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 2.73/2.91      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.73/2.91  thf('52', plain,
% 2.73/2.91      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 2.73/2.91      inference('sup-', [status(thm)], ['50', '51'])).
% 2.73/2.91  thf('53', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 2.73/2.91      inference('demod', [status(thm)], ['42', '49', '52'])).
% 2.73/2.91  thf(t63_funct_1, axiom,
% 2.73/2.91    (![A:$i]:
% 2.73/2.91     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.73/2.91       ( ![B:$i]:
% 2.73/2.91         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.73/2.91           ( ( ( v2_funct_1 @ A ) & 
% 2.73/2.91               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 2.73/2.91               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 2.73/2.91             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.73/2.91  thf('54', plain,
% 2.73/2.91      (![X7 : $i, X8 : $i]:
% 2.73/2.91         (~ (v1_relat_1 @ X7)
% 2.73/2.91          | ~ (v1_funct_1 @ X7)
% 2.73/2.91          | ((X7) = (k2_funct_1 @ X8))
% 2.73/2.91          | ((k5_relat_1 @ X8 @ X7) != (k6_relat_1 @ (k1_relat_1 @ X8)))
% 2.73/2.91          | ((k2_relat_1 @ X8) != (k1_relat_1 @ X7))
% 2.73/2.91          | ~ (v2_funct_1 @ X8)
% 2.73/2.91          | ~ (v1_funct_1 @ X8)
% 2.73/2.91          | ~ (v1_relat_1 @ X8))),
% 2.73/2.91      inference('cnf', [status(esa)], [t63_funct_1])).
% 2.73/2.91  thf('55', plain, (![X37 : $i]: ((k6_partfun1 @ X37) = (k6_relat_1 @ X37))),
% 2.73/2.91      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.73/2.91  thf('56', plain,
% 2.73/2.91      (![X7 : $i, X8 : $i]:
% 2.73/2.91         (~ (v1_relat_1 @ X7)
% 2.73/2.91          | ~ (v1_funct_1 @ X7)
% 2.73/2.91          | ((X7) = (k2_funct_1 @ X8))
% 2.73/2.91          | ((k5_relat_1 @ X8 @ X7) != (k6_partfun1 @ (k1_relat_1 @ X8)))
% 2.73/2.91          | ((k2_relat_1 @ X8) != (k1_relat_1 @ X7))
% 2.73/2.91          | ~ (v2_funct_1 @ X8)
% 2.73/2.91          | ~ (v1_funct_1 @ X8)
% 2.73/2.91          | ~ (v1_relat_1 @ X8))),
% 2.73/2.91      inference('demod', [status(thm)], ['54', '55'])).
% 2.73/2.91  thf('57', plain,
% 2.73/2.91      (![X0 : $i]:
% 2.73/2.91         (((k5_relat_1 @ sk_C @ X0) != (k6_partfun1 @ sk_A))
% 2.73/2.91          | ~ (v1_relat_1 @ sk_C)
% 2.73/2.91          | ~ (v1_funct_1 @ sk_C)
% 2.73/2.91          | ~ (v2_funct_1 @ sk_C)
% 2.73/2.91          | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ X0))
% 2.73/2.91          | ((X0) = (k2_funct_1 @ sk_C))
% 2.73/2.91          | ~ (v1_funct_1 @ X0)
% 2.73/2.91          | ~ (v1_relat_1 @ X0))),
% 2.73/2.91      inference('sup-', [status(thm)], ['53', '56'])).
% 2.73/2.91  thf('58', plain,
% 2.73/2.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.91  thf(cc2_relat_1, axiom,
% 2.73/2.91    (![A:$i]:
% 2.73/2.91     ( ( v1_relat_1 @ A ) =>
% 2.73/2.91       ( ![B:$i]:
% 2.73/2.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.73/2.91  thf('59', plain,
% 2.73/2.91      (![X0 : $i, X1 : $i]:
% 2.73/2.91         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 2.73/2.91          | (v1_relat_1 @ X0)
% 2.73/2.91          | ~ (v1_relat_1 @ X1))),
% 2.73/2.91      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.73/2.91  thf('60', plain,
% 2.73/2.91      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 2.73/2.91      inference('sup-', [status(thm)], ['58', '59'])).
% 2.73/2.91  thf(fc6_relat_1, axiom,
% 2.73/2.91    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.73/2.91  thf('61', plain,
% 2.73/2.91      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 2.73/2.91      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.73/2.91  thf('62', plain, ((v1_relat_1 @ sk_C)),
% 2.73/2.91      inference('demod', [status(thm)], ['60', '61'])).
% 2.73/2.91  thf('63', plain, ((v1_funct_1 @ sk_C)),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.91  thf('64', plain, ((v2_funct_1 @ sk_C)),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.91  thf('65', plain,
% 2.73/2.91      (![X0 : $i]:
% 2.73/2.91         (((k5_relat_1 @ sk_C @ X0) != (k6_partfun1 @ sk_A))
% 2.73/2.91          | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ X0))
% 2.73/2.91          | ((X0) = (k2_funct_1 @ sk_C))
% 2.73/2.91          | ~ (v1_funct_1 @ X0)
% 2.73/2.91          | ~ (v1_relat_1 @ X0))),
% 2.73/2.91      inference('demod', [status(thm)], ['57', '62', '63', '64'])).
% 2.73/2.91  thf('66', plain,
% 2.73/2.91      ((((k2_relat_1 @ sk_C) != (sk_B))
% 2.73/2.91        | ~ (v1_relat_1 @ sk_D)
% 2.73/2.91        | ~ (v1_funct_1 @ sk_D)
% 2.73/2.91        | ((sk_D) = (k2_funct_1 @ sk_C))
% 2.73/2.91        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_partfun1 @ sk_A)))),
% 2.73/2.91      inference('sup-', [status(thm)], ['39', '65'])).
% 2.73/2.91  thf('67', plain,
% 2.73/2.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.91  thf('68', plain,
% 2.73/2.91      (![X0 : $i, X1 : $i]:
% 2.73/2.91         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 2.73/2.91          | (v1_relat_1 @ X0)
% 2.73/2.91          | ~ (v1_relat_1 @ X1))),
% 2.73/2.91      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.73/2.91  thf('69', plain,
% 2.73/2.91      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 2.73/2.91      inference('sup-', [status(thm)], ['67', '68'])).
% 2.73/2.91  thf('70', plain,
% 2.73/2.91      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 2.73/2.91      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.73/2.91  thf('71', plain, ((v1_relat_1 @ sk_D)),
% 2.73/2.91      inference('demod', [status(thm)], ['69', '70'])).
% 2.73/2.91  thf('72', plain, ((v1_funct_1 @ sk_D)),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.91  thf('73', plain,
% 2.73/2.91      ((((k2_relat_1 @ sk_C) != (sk_B))
% 2.73/2.91        | ((sk_D) = (k2_funct_1 @ sk_C))
% 2.73/2.91        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_partfun1 @ sk_A)))),
% 2.73/2.91      inference('demod', [status(thm)], ['66', '71', '72'])).
% 2.73/2.91  thf('74', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.91  thf('75', plain,
% 2.73/2.91      ((((k2_relat_1 @ sk_C) != (sk_B))
% 2.73/2.91        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_partfun1 @ sk_A)))),
% 2.73/2.91      inference('simplify_reflect-', [status(thm)], ['73', '74'])).
% 2.73/2.91  thf(t61_funct_1, axiom,
% 2.73/2.91    (![A:$i]:
% 2.73/2.91     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.73/2.91       ( ( v2_funct_1 @ A ) =>
% 2.73/2.91         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 2.73/2.91             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 2.73/2.91           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 2.73/2.91             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 2.73/2.91  thf('76', plain,
% 2.73/2.91      (![X6 : $i]:
% 2.73/2.91         (~ (v2_funct_1 @ X6)
% 2.73/2.91          | ((k5_relat_1 @ (k2_funct_1 @ X6) @ X6)
% 2.73/2.91              = (k6_relat_1 @ (k2_relat_1 @ X6)))
% 2.73/2.91          | ~ (v1_funct_1 @ X6)
% 2.73/2.91          | ~ (v1_relat_1 @ X6))),
% 2.73/2.91      inference('cnf', [status(esa)], [t61_funct_1])).
% 2.73/2.91  thf('77', plain, (![X37 : $i]: ((k6_partfun1 @ X37) = (k6_relat_1 @ X37))),
% 2.73/2.91      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.73/2.91  thf('78', plain,
% 2.73/2.91      (![X6 : $i]:
% 2.73/2.91         (~ (v2_funct_1 @ X6)
% 2.73/2.91          | ((k5_relat_1 @ (k2_funct_1 @ X6) @ X6)
% 2.73/2.91              = (k6_partfun1 @ (k2_relat_1 @ X6)))
% 2.73/2.91          | ~ (v1_funct_1 @ X6)
% 2.73/2.91          | ~ (v1_relat_1 @ X6))),
% 2.73/2.91      inference('demod', [status(thm)], ['76', '77'])).
% 2.73/2.91  thf('79', plain,
% 2.73/2.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.91  thf(t35_funct_2, axiom,
% 2.73/2.91    (![A:$i,B:$i,C:$i]:
% 2.73/2.91     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.73/2.91         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.73/2.91       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 2.73/2.91         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.73/2.91           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 2.73/2.91             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 2.73/2.91  thf('80', plain,
% 2.73/2.91      (![X38 : $i, X39 : $i, X40 : $i]:
% 2.73/2.91         (((X38) = (k1_xboole_0))
% 2.73/2.91          | ~ (v1_funct_1 @ X39)
% 2.73/2.91          | ~ (v1_funct_2 @ X39 @ X40 @ X38)
% 2.73/2.91          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X38)))
% 2.73/2.91          | ((k5_relat_1 @ (k2_funct_1 @ X39) @ X39) = (k6_partfun1 @ X38))
% 2.73/2.91          | ~ (v2_funct_1 @ X39)
% 2.73/2.91          | ((k2_relset_1 @ X40 @ X38 @ X39) != (X38)))),
% 2.73/2.91      inference('cnf', [status(esa)], [t35_funct_2])).
% 2.73/2.91  thf('81', plain,
% 2.73/2.91      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 2.73/2.91        | ~ (v2_funct_1 @ sk_C)
% 2.73/2.91        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 2.73/2.91        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.73/2.91        | ~ (v1_funct_1 @ sk_C)
% 2.73/2.91        | ((sk_B) = (k1_xboole_0)))),
% 2.73/2.91      inference('sup-', [status(thm)], ['79', '80'])).
% 2.73/2.91  thf('82', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.91  thf('83', plain, ((v2_funct_1 @ sk_C)),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.91  thf('84', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.91  thf('85', plain, ((v1_funct_1 @ sk_C)),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.91  thf('86', plain,
% 2.73/2.91      ((((sk_B) != (sk_B))
% 2.73/2.91        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 2.73/2.91        | ((sk_B) = (k1_xboole_0)))),
% 2.73/2.91      inference('demod', [status(thm)], ['81', '82', '83', '84', '85'])).
% 2.73/2.91  thf('87', plain,
% 2.73/2.91      ((((sk_B) = (k1_xboole_0))
% 2.73/2.91        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 2.73/2.91      inference('simplify', [status(thm)], ['86'])).
% 2.73/2.91  thf('88', plain, (((sk_B) != (k1_xboole_0))),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.91  thf('89', plain,
% 2.73/2.91      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 2.73/2.91      inference('simplify_reflect-', [status(thm)], ['87', '88'])).
% 2.73/2.91  thf('90', plain,
% 2.73/2.91      ((((k6_partfun1 @ (k2_relat_1 @ sk_C)) = (k6_partfun1 @ sk_B))
% 2.73/2.91        | ~ (v1_relat_1 @ sk_C)
% 2.73/2.91        | ~ (v1_funct_1 @ sk_C)
% 2.73/2.91        | ~ (v2_funct_1 @ sk_C))),
% 2.73/2.91      inference('sup+', [status(thm)], ['78', '89'])).
% 2.73/2.91  thf('91', plain, ((v1_relat_1 @ sk_C)),
% 2.73/2.91      inference('demod', [status(thm)], ['60', '61'])).
% 2.73/2.91  thf('92', plain, ((v1_funct_1 @ sk_C)),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.91  thf('93', plain, ((v2_funct_1 @ sk_C)),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.91  thf('94', plain,
% 2.73/2.91      (((k6_partfun1 @ (k2_relat_1 @ sk_C)) = (k6_partfun1 @ sk_B))),
% 2.73/2.91      inference('demod', [status(thm)], ['90', '91', '92', '93'])).
% 2.73/2.91  thf(t71_relat_1, axiom,
% 2.73/2.91    (![A:$i]:
% 2.73/2.91     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 2.73/2.91       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 2.73/2.91  thf('95', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 2.73/2.91      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.73/2.91  thf('96', plain, (![X37 : $i]: ((k6_partfun1 @ X37) = (k6_relat_1 @ X37))),
% 2.73/2.91      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.73/2.91  thf('97', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 2.73/2.91      inference('demod', [status(thm)], ['95', '96'])).
% 2.73/2.91  thf('98', plain,
% 2.73/2.91      (((k1_relat_1 @ (k6_partfun1 @ sk_B)) = (k2_relat_1 @ sk_C))),
% 2.73/2.91      inference('sup+', [status(thm)], ['94', '97'])).
% 2.73/2.91  thf('99', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 2.73/2.91      inference('demod', [status(thm)], ['95', '96'])).
% 2.73/2.91  thf('100', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 2.73/2.91      inference('demod', [status(thm)], ['98', '99'])).
% 2.73/2.91  thf('101', plain,
% 2.73/2.91      ((((sk_B) != (sk_B))
% 2.73/2.91        | ((k5_relat_1 @ sk_C @ sk_D) != (k6_partfun1 @ sk_A)))),
% 2.73/2.91      inference('demod', [status(thm)], ['75', '100'])).
% 2.73/2.91  thf('102', plain, (((k5_relat_1 @ sk_C @ sk_D) != (k6_partfun1 @ sk_A))),
% 2.73/2.91      inference('simplify', [status(thm)], ['101'])).
% 2.73/2.91  thf('103', plain, ($false),
% 2.73/2.91      inference('simplify_reflect-', [status(thm)], ['25', '102'])).
% 2.73/2.91  
% 2.73/2.91  % SZS output end Refutation
% 2.73/2.91  
% 2.73/2.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

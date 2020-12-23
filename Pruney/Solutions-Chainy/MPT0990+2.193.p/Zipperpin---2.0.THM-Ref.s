%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.F7Bhc3tZak

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:28 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  199 ( 480 expanded)
%              Number of leaves         :   44 ( 162 expanded)
%              Depth                    :   21
%              Number of atoms          : 1962 (11584 expanded)
%              Number of equality atoms :  144 ( 816 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('0',plain,(
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

thf('1',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k5_relat_1 @ X10 @ ( k2_funct_1 @ X10 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

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

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
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

thf('4',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( X45 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X45 ) ) )
      | ( ( k5_relat_1 @ X46 @ ( k2_funct_1 @ X46 ) )
        = ( k6_partfun1 @ X47 ) )
      | ~ ( v2_funct_1 @ X46 )
      | ( ( k2_relset_1 @ X47 @ X45 @ X46 )
       != X45 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('5',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
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

thf('14',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X18 @ X19 @ X21 @ X22 @ X17 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('21',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( X13 = X16 )
      | ~ ( r2_relset_1 @ X14 @ X15 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','22'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('24',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('25',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ ( k6_partfun1 @ B ) )
           => ( ( k2_relset_1 @ A @ B @ C )
              = B ) ) ) ) )).

thf('27',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( r2_relset_1 @ X33 @ X33 @ ( k1_partfun1 @ X33 @ X34 @ X34 @ X33 @ X32 @ X35 ) @ ( k6_partfun1 @ X33 ) )
      | ( ( k2_relset_1 @ X34 @ X33 @ X35 )
        = X33 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('34',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( r2_relset_1 @ X14 @ X15 @ X13 @ X16 )
      | ( X13 != X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('35',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_relset_1 @ X14 @ X15 @ X16 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['32','36','37','38','39'])).

thf('41',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','40'])).

thf('42',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('44',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_2 @ D @ A @ B )
        & ( v1_funct_1 @ D ) )
     => ! [E: $i] :
          ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
            & ( v1_funct_2 @ E @ B @ C )
            & ( v1_funct_1 @ E ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ D )
                = B )
              & ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) )
           => ( ( ( v2_funct_1 @ E )
                & ( v2_funct_1 @ D ) )
              | ( ( B != k1_xboole_0 )
                & ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i] :
      ( ( zip_tseitin_1 @ C @ B )
     => ( ( C = k1_xboole_0 )
        & ( B != k1_xboole_0 ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [E: $i,D: $i] :
      ( ( zip_tseitin_0 @ E @ D )
     => ( ( v2_funct_1 @ D )
        & ( v2_funct_1 @ E ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
              & ( ( k2_relset_1 @ A @ B @ D )
                = B ) )
           => ( ( zip_tseitin_1 @ C @ B )
              | ( zip_tseitin_0 @ E @ D ) ) ) ) ) )).

thf('45',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( zip_tseitin_0 @ X40 @ X43 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X44 @ X41 @ X41 @ X42 @ X43 @ X40 ) )
      | ( zip_tseitin_1 @ X42 @ X41 )
      | ( ( k2_relset_1 @ X44 @ X41 @ X43 )
       != X41 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X41 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X41 )
      | ~ ( v1_funct_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['43','49'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('51',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('52',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('53',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X7 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['50','53','54','55','56','57'])).

thf('59',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X38: $i,X39: $i] :
      ( ( X38 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('61',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X36: $i,X37: $i] :
      ( ( v2_funct_1 @ X37 )
      | ~ ( zip_tseitin_0 @ X37 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('65',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['42','65'])).

thf('67',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['2','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('70',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('71',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('72',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['63','64'])).

thf('75',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['67','72','73','74'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('76',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('77',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('78',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['75','78'])).

thf('80',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('81',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
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

thf('84',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( ( k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28 )
        = ( k5_relat_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['82','87'])).

thf('89',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('91',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['88','89','90'])).

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

thf('92',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X11
        = ( k2_funct_1 @ X12 ) )
      | ( ( k5_relat_1 @ X12 @ X11 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X12 ) ) )
      | ( ( k2_relat_1 @ X12 )
       != ( k1_relat_1 @ X11 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t63_funct_1])).

thf('93',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('94',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X11
        = ( k2_funct_1 @ X12 ) )
      | ( ( k5_relat_1 @ X12 @ X11 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X12 ) ) )
      | ( ( k2_relat_1 @ X12 )
       != ( k1_relat_1 @ X11 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('96',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k5_relat_1 @ X10 @ ( k2_funct_1 @ X10 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('97',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( X45 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X45 ) ) )
      | ( ( k5_relat_1 @ X46 @ ( k2_funct_1 @ X46 ) )
        = ( k6_partfun1 @ X47 ) )
      | ~ ( v2_funct_1 @ X46 )
      | ( ( k2_relset_1 @ X47 @ X45 @ X46 )
       != X45 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('99',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['99','100','101','102','103'])).

thf('105',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['96','107'])).

thf('109',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('111',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('113',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['108','113','114','115'])).

thf('117',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('118',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('120',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['111','112'])).

thf('122',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X10 ) @ X10 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('125',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('126',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X10 ) @ X10 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
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

thf('129',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['129','130','131','132','133'])).

thf('135',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['126','137'])).

thf('139',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['111','112'])).

thf('140',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['138','139','140','141'])).

thf('143',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('144',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('146',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['70','71'])).

thf('149',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['95','120','121','122','123','146','147','148'])).

thf('150',plain,
    ( ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    sk_B
 != ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['150','151'])).

thf('153',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['81','152'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.F7Bhc3tZak
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:20:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.90/1.17  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.90/1.17  % Solved by: fo/fo7.sh
% 0.90/1.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.17  % done 986 iterations in 0.700s
% 0.90/1.17  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.90/1.17  % SZS output start Refutation
% 0.90/1.17  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.17  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.90/1.17  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.17  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.17  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.90/1.17  thf(sk_D_type, type, sk_D: $i).
% 0.90/1.17  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.90/1.17  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.90/1.17  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.90/1.17  thf(sk_C_type, type, sk_C: $i).
% 0.90/1.17  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.90/1.17  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.90/1.17  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.90/1.17  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.90/1.17  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.90/1.17  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.90/1.17  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.90/1.17  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.17  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.90/1.17  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.90/1.17  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.90/1.17  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.90/1.17  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.90/1.17  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.90/1.17  thf(t61_funct_1, axiom,
% 0.90/1.17    (![A:$i]:
% 0.90/1.17     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.90/1.17       ( ( v2_funct_1 @ A ) =>
% 0.90/1.17         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.90/1.17             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.90/1.17           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.90/1.17             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.90/1.17  thf('0', plain,
% 0.90/1.17      (![X10 : $i]:
% 0.90/1.17         (~ (v2_funct_1 @ X10)
% 0.90/1.17          | ((k5_relat_1 @ X10 @ (k2_funct_1 @ X10))
% 0.90/1.17              = (k6_relat_1 @ (k1_relat_1 @ X10)))
% 0.90/1.17          | ~ (v1_funct_1 @ X10)
% 0.90/1.17          | ~ (v1_relat_1 @ X10))),
% 0.90/1.17      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.90/1.17  thf(redefinition_k6_partfun1, axiom,
% 0.90/1.17    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.90/1.17  thf('1', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.90/1.17      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.90/1.17  thf('2', plain,
% 0.90/1.17      (![X10 : $i]:
% 0.90/1.17         (~ (v2_funct_1 @ X10)
% 0.90/1.17          | ((k5_relat_1 @ X10 @ (k2_funct_1 @ X10))
% 0.90/1.17              = (k6_partfun1 @ (k1_relat_1 @ X10)))
% 0.90/1.17          | ~ (v1_funct_1 @ X10)
% 0.90/1.17          | ~ (v1_relat_1 @ X10))),
% 0.90/1.17      inference('demod', [status(thm)], ['0', '1'])).
% 0.90/1.17  thf(t36_funct_2, conjecture,
% 0.90/1.17    (![A:$i,B:$i,C:$i]:
% 0.90/1.17     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.90/1.17         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.90/1.17       ( ![D:$i]:
% 0.90/1.17         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.90/1.17             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.90/1.17           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.90/1.17               ( r2_relset_1 @
% 0.90/1.17                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.90/1.17                 ( k6_partfun1 @ A ) ) & 
% 0.90/1.17               ( v2_funct_1 @ C ) ) =>
% 0.90/1.17             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.90/1.17               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.90/1.17  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.17    (~( ![A:$i,B:$i,C:$i]:
% 0.90/1.17        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.90/1.17            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.90/1.17          ( ![D:$i]:
% 0.90/1.17            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.90/1.17                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.90/1.17              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.90/1.17                  ( r2_relset_1 @
% 0.90/1.17                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.90/1.17                    ( k6_partfun1 @ A ) ) & 
% 0.90/1.17                  ( v2_funct_1 @ C ) ) =>
% 0.90/1.17                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.90/1.17                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.90/1.17    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.90/1.17  thf('3', plain,
% 0.90/1.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf(t35_funct_2, axiom,
% 0.90/1.17    (![A:$i,B:$i,C:$i]:
% 0.90/1.17     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.90/1.17         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.90/1.17       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.90/1.17         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.90/1.17           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.90/1.17             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.90/1.17  thf('4', plain,
% 0.90/1.17      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.90/1.17         (((X45) = (k1_xboole_0))
% 0.90/1.17          | ~ (v1_funct_1 @ X46)
% 0.90/1.17          | ~ (v1_funct_2 @ X46 @ X47 @ X45)
% 0.90/1.17          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X45)))
% 0.90/1.17          | ((k5_relat_1 @ X46 @ (k2_funct_1 @ X46)) = (k6_partfun1 @ X47))
% 0.90/1.17          | ~ (v2_funct_1 @ X46)
% 0.90/1.17          | ((k2_relset_1 @ X47 @ X45 @ X46) != (X45)))),
% 0.90/1.17      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.90/1.17  thf('5', plain,
% 0.90/1.17      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 0.90/1.17        | ~ (v2_funct_1 @ sk_D)
% 0.90/1.17        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.90/1.17        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.90/1.17        | ~ (v1_funct_1 @ sk_D)
% 0.90/1.17        | ((sk_A) = (k1_xboole_0)))),
% 0.90/1.17      inference('sup-', [status(thm)], ['3', '4'])).
% 0.90/1.17  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('8', plain,
% 0.90/1.17      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 0.90/1.17        | ~ (v2_funct_1 @ sk_D)
% 0.90/1.17        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.90/1.17        | ((sk_A) = (k1_xboole_0)))),
% 0.90/1.17      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.90/1.17  thf('9', plain, (((sk_A) != (k1_xboole_0))),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('10', plain,
% 0.90/1.17      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 0.90/1.17        | ~ (v2_funct_1 @ sk_D)
% 0.90/1.17        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 0.90/1.17      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.90/1.17  thf('11', plain,
% 0.90/1.17      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.17        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.90/1.17        (k6_partfun1 @ sk_A))),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('12', plain,
% 0.90/1.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('13', plain,
% 0.90/1.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf(dt_k1_partfun1, axiom,
% 0.90/1.17    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.90/1.17     ( ( ( v1_funct_1 @ E ) & 
% 0.90/1.17         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.90/1.17         ( v1_funct_1 @ F ) & 
% 0.90/1.17         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.90/1.17       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.90/1.17         ( m1_subset_1 @
% 0.90/1.17           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.90/1.17           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.90/1.17  thf('14', plain,
% 0.90/1.17      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.90/1.17         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.90/1.17          | ~ (v1_funct_1 @ X17)
% 0.90/1.17          | ~ (v1_funct_1 @ X20)
% 0.90/1.17          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.90/1.17          | (m1_subset_1 @ (k1_partfun1 @ X18 @ X19 @ X21 @ X22 @ X17 @ X20) @ 
% 0.90/1.17             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X22))))),
% 0.90/1.17      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.90/1.17  thf('15', plain,
% 0.90/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.17         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.90/1.17           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.90/1.17          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.90/1.17          | ~ (v1_funct_1 @ X1)
% 0.90/1.17          | ~ (v1_funct_1 @ sk_C))),
% 0.90/1.17      inference('sup-', [status(thm)], ['13', '14'])).
% 0.90/1.17  thf('16', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('17', plain,
% 0.90/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.17         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.90/1.17           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.90/1.17          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.90/1.17          | ~ (v1_funct_1 @ X1))),
% 0.90/1.17      inference('demod', [status(thm)], ['15', '16'])).
% 0.90/1.17  thf('18', plain,
% 0.90/1.17      ((~ (v1_funct_1 @ sk_D)
% 0.90/1.17        | (m1_subset_1 @ 
% 0.90/1.17           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.90/1.17           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.90/1.17      inference('sup-', [status(thm)], ['12', '17'])).
% 0.90/1.17  thf('19', plain, ((v1_funct_1 @ sk_D)),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('20', plain,
% 0.90/1.17      ((m1_subset_1 @ 
% 0.90/1.17        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.90/1.17        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.17      inference('demod', [status(thm)], ['18', '19'])).
% 0.90/1.17  thf(redefinition_r2_relset_1, axiom,
% 0.90/1.17    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.17     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.90/1.17         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.90/1.17       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.90/1.17  thf('21', plain,
% 0.90/1.17      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.90/1.17         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.90/1.17          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.90/1.17          | ((X13) = (X16))
% 0.90/1.17          | ~ (r2_relset_1 @ X14 @ X15 @ X13 @ X16))),
% 0.90/1.17      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.90/1.17  thf('22', plain,
% 0.90/1.17      (![X0 : $i]:
% 0.90/1.17         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.17             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.90/1.17          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.90/1.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.90/1.17      inference('sup-', [status(thm)], ['20', '21'])).
% 0.90/1.17  thf('23', plain,
% 0.90/1.17      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.90/1.17           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.90/1.17        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.90/1.17            = (k6_partfun1 @ sk_A)))),
% 0.90/1.17      inference('sup-', [status(thm)], ['11', '22'])).
% 0.90/1.17  thf(dt_k6_partfun1, axiom,
% 0.90/1.17    (![A:$i]:
% 0.90/1.17     ( ( m1_subset_1 @
% 0.90/1.17         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.90/1.17       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.90/1.17  thf('24', plain,
% 0.90/1.17      (![X24 : $i]:
% 0.90/1.17         (m1_subset_1 @ (k6_partfun1 @ X24) @ 
% 0.90/1.17          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))),
% 0.90/1.17      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.90/1.17  thf('25', plain,
% 0.90/1.17      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.90/1.17         = (k6_partfun1 @ sk_A))),
% 0.90/1.17      inference('demod', [status(thm)], ['23', '24'])).
% 0.90/1.17  thf('26', plain,
% 0.90/1.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf(t24_funct_2, axiom,
% 0.90/1.17    (![A:$i,B:$i,C:$i]:
% 0.90/1.17     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.90/1.17         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.90/1.17       ( ![D:$i]:
% 0.90/1.17         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.90/1.17             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.90/1.17           ( ( r2_relset_1 @
% 0.90/1.17               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.90/1.17               ( k6_partfun1 @ B ) ) =>
% 0.90/1.17             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.90/1.17  thf('27', plain,
% 0.90/1.17      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.90/1.17         (~ (v1_funct_1 @ X32)
% 0.90/1.17          | ~ (v1_funct_2 @ X32 @ X33 @ X34)
% 0.90/1.17          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.90/1.17          | ~ (r2_relset_1 @ X33 @ X33 @ 
% 0.90/1.17               (k1_partfun1 @ X33 @ X34 @ X34 @ X33 @ X32 @ X35) @ 
% 0.90/1.17               (k6_partfun1 @ X33))
% 0.90/1.17          | ((k2_relset_1 @ X34 @ X33 @ X35) = (X33))
% 0.90/1.17          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.90/1.17          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 0.90/1.17          | ~ (v1_funct_1 @ X35))),
% 0.90/1.17      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.90/1.17  thf('28', plain,
% 0.90/1.17      (![X0 : $i]:
% 0.90/1.17         (~ (v1_funct_1 @ X0)
% 0.90/1.17          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.90/1.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.90/1.17          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.90/1.17          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.17               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.90/1.17               (k6_partfun1 @ sk_A))
% 0.90/1.17          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.90/1.17          | ~ (v1_funct_1 @ sk_C))),
% 0.90/1.17      inference('sup-', [status(thm)], ['26', '27'])).
% 0.90/1.17  thf('29', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('30', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('31', plain,
% 0.90/1.17      (![X0 : $i]:
% 0.90/1.17         (~ (v1_funct_1 @ X0)
% 0.90/1.17          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.90/1.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.90/1.17          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.90/1.17          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.17               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.90/1.17               (k6_partfun1 @ sk_A)))),
% 0.90/1.17      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.90/1.17  thf('32', plain,
% 0.90/1.17      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 0.90/1.17           (k6_partfun1 @ sk_A))
% 0.90/1.17        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.90/1.17        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.90/1.17        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.90/1.17        | ~ (v1_funct_1 @ sk_D))),
% 0.90/1.17      inference('sup-', [status(thm)], ['25', '31'])).
% 0.90/1.17  thf('33', plain,
% 0.90/1.17      (![X24 : $i]:
% 0.90/1.17         (m1_subset_1 @ (k6_partfun1 @ X24) @ 
% 0.90/1.17          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))),
% 0.90/1.17      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.90/1.17  thf('34', plain,
% 0.90/1.17      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.90/1.17         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.90/1.17          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.90/1.17          | (r2_relset_1 @ X14 @ X15 @ X13 @ X16)
% 0.90/1.17          | ((X13) != (X16)))),
% 0.90/1.17      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.90/1.17  thf('35', plain,
% 0.90/1.17      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.90/1.17         ((r2_relset_1 @ X14 @ X15 @ X16 @ X16)
% 0.90/1.17          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.90/1.17      inference('simplify', [status(thm)], ['34'])).
% 0.90/1.17  thf('36', plain,
% 0.90/1.17      (![X0 : $i]:
% 0.90/1.17         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 0.90/1.17      inference('sup-', [status(thm)], ['33', '35'])).
% 0.90/1.17  thf('37', plain,
% 0.90/1.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('38', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('39', plain, ((v1_funct_1 @ sk_D)),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('40', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))),
% 0.90/1.17      inference('demod', [status(thm)], ['32', '36', '37', '38', '39'])).
% 0.90/1.17  thf('41', plain,
% 0.90/1.17      ((((sk_A) != (sk_A))
% 0.90/1.17        | ~ (v2_funct_1 @ sk_D)
% 0.90/1.17        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 0.90/1.17      inference('demod', [status(thm)], ['10', '40'])).
% 0.90/1.17  thf('42', plain,
% 0.90/1.17      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.90/1.17        | ~ (v2_funct_1 @ sk_D))),
% 0.90/1.17      inference('simplify', [status(thm)], ['41'])).
% 0.90/1.17  thf('43', plain,
% 0.90/1.17      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.90/1.17         = (k6_partfun1 @ sk_A))),
% 0.90/1.17      inference('demod', [status(thm)], ['23', '24'])).
% 0.90/1.17  thf('44', plain,
% 0.90/1.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf(t30_funct_2, axiom,
% 0.90/1.17    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.17     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.90/1.17         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 0.90/1.17       ( ![E:$i]:
% 0.90/1.17         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 0.90/1.17             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 0.90/1.17           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 0.90/1.17               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 0.90/1.17             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 0.90/1.17               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 0.90/1.17  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 0.90/1.17  thf(zf_stmt_2, axiom,
% 0.90/1.17    (![C:$i,B:$i]:
% 0.90/1.17     ( ( zip_tseitin_1 @ C @ B ) =>
% 0.90/1.17       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 0.90/1.17  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.90/1.17  thf(zf_stmt_4, axiom,
% 0.90/1.17    (![E:$i,D:$i]:
% 0.90/1.17     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 0.90/1.17  thf(zf_stmt_5, axiom,
% 0.90/1.17    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.17     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.90/1.17         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.90/1.17       ( ![E:$i]:
% 0.90/1.17         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.90/1.17             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.90/1.17           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 0.90/1.17               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 0.90/1.17             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 0.90/1.17  thf('45', plain,
% 0.90/1.17      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.90/1.17         (~ (v1_funct_1 @ X40)
% 0.90/1.17          | ~ (v1_funct_2 @ X40 @ X41 @ X42)
% 0.90/1.17          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.90/1.17          | (zip_tseitin_0 @ X40 @ X43)
% 0.90/1.17          | ~ (v2_funct_1 @ (k1_partfun1 @ X44 @ X41 @ X41 @ X42 @ X43 @ X40))
% 0.90/1.17          | (zip_tseitin_1 @ X42 @ X41)
% 0.90/1.17          | ((k2_relset_1 @ X44 @ X41 @ X43) != (X41))
% 0.90/1.17          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X41)))
% 0.90/1.17          | ~ (v1_funct_2 @ X43 @ X44 @ X41)
% 0.90/1.17          | ~ (v1_funct_1 @ X43))),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.90/1.17  thf('46', plain,
% 0.90/1.17      (![X0 : $i, X1 : $i]:
% 0.90/1.17         (~ (v1_funct_1 @ X0)
% 0.90/1.17          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.90/1.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.90/1.17          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 0.90/1.17          | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.90/1.17          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.90/1.17          | (zip_tseitin_0 @ sk_D @ X0)
% 0.90/1.17          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.90/1.17          | ~ (v1_funct_1 @ sk_D))),
% 0.90/1.17      inference('sup-', [status(thm)], ['44', '45'])).
% 0.90/1.17  thf('47', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('48', plain, ((v1_funct_1 @ sk_D)),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('49', plain,
% 0.90/1.17      (![X0 : $i, X1 : $i]:
% 0.90/1.17         (~ (v1_funct_1 @ X0)
% 0.90/1.17          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.90/1.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.90/1.17          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 0.90/1.17          | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.90/1.17          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.90/1.17          | (zip_tseitin_0 @ sk_D @ X0))),
% 0.90/1.17      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.90/1.17  thf('50', plain,
% 0.90/1.17      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.90/1.17        | (zip_tseitin_0 @ sk_D @ sk_C)
% 0.90/1.17        | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.90/1.17        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.90/1.17        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.90/1.17        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.90/1.17        | ~ (v1_funct_1 @ sk_C))),
% 0.90/1.17      inference('sup-', [status(thm)], ['43', '49'])).
% 0.90/1.17  thf(fc4_funct_1, axiom,
% 0.90/1.17    (![A:$i]:
% 0.90/1.17     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.90/1.17       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.90/1.17  thf('51', plain, (![X7 : $i]: (v2_funct_1 @ (k6_relat_1 @ X7))),
% 0.90/1.17      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.90/1.17  thf('52', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.90/1.17      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.90/1.17  thf('53', plain, (![X7 : $i]: (v2_funct_1 @ (k6_partfun1 @ X7))),
% 0.90/1.17      inference('demod', [status(thm)], ['51', '52'])).
% 0.90/1.17  thf('54', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('55', plain,
% 0.90/1.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('56', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('57', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('58', plain,
% 0.90/1.17      (((zip_tseitin_0 @ sk_D @ sk_C)
% 0.90/1.17        | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.90/1.17        | ((sk_B) != (sk_B)))),
% 0.90/1.17      inference('demod', [status(thm)], ['50', '53', '54', '55', '56', '57'])).
% 0.90/1.17  thf('59', plain,
% 0.90/1.17      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 0.90/1.17      inference('simplify', [status(thm)], ['58'])).
% 0.90/1.17  thf('60', plain,
% 0.90/1.17      (![X38 : $i, X39 : $i]:
% 0.90/1.17         (((X38) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X38 @ X39))),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.90/1.17  thf('61', plain,
% 0.90/1.17      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.90/1.17      inference('sup-', [status(thm)], ['59', '60'])).
% 0.90/1.17  thf('62', plain, (((sk_A) != (k1_xboole_0))),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('63', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 0.90/1.17      inference('simplify_reflect-', [status(thm)], ['61', '62'])).
% 0.90/1.17  thf('64', plain,
% 0.90/1.17      (![X36 : $i, X37 : $i]:
% 0.90/1.17         ((v2_funct_1 @ X37) | ~ (zip_tseitin_0 @ X37 @ X36))),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.90/1.17  thf('65', plain, ((v2_funct_1 @ sk_D)),
% 0.90/1.17      inference('sup-', [status(thm)], ['63', '64'])).
% 0.90/1.17  thf('66', plain,
% 0.90/1.17      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 0.90/1.17      inference('demod', [status(thm)], ['42', '65'])).
% 0.90/1.17  thf('67', plain,
% 0.90/1.17      ((((k6_partfun1 @ (k1_relat_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.90/1.17        | ~ (v1_relat_1 @ sk_D)
% 0.90/1.17        | ~ (v1_funct_1 @ sk_D)
% 0.90/1.17        | ~ (v2_funct_1 @ sk_D))),
% 0.90/1.17      inference('sup+', [status(thm)], ['2', '66'])).
% 0.90/1.17  thf('68', plain,
% 0.90/1.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf(cc2_relat_1, axiom,
% 0.90/1.17    (![A:$i]:
% 0.90/1.17     ( ( v1_relat_1 @ A ) =>
% 0.90/1.17       ( ![B:$i]:
% 0.90/1.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.90/1.17  thf('69', plain,
% 0.90/1.17      (![X0 : $i, X1 : $i]:
% 0.90/1.17         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.90/1.17          | (v1_relat_1 @ X0)
% 0.90/1.17          | ~ (v1_relat_1 @ X1))),
% 0.90/1.17      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.90/1.17  thf('70', plain,
% 0.90/1.17      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.90/1.17      inference('sup-', [status(thm)], ['68', '69'])).
% 0.90/1.17  thf(fc6_relat_1, axiom,
% 0.90/1.17    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.90/1.17  thf('71', plain,
% 0.90/1.17      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.90/1.17      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.90/1.17  thf('72', plain, ((v1_relat_1 @ sk_D)),
% 0.90/1.17      inference('demod', [status(thm)], ['70', '71'])).
% 0.90/1.17  thf('73', plain, ((v1_funct_1 @ sk_D)),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('74', plain, ((v2_funct_1 @ sk_D)),
% 0.90/1.17      inference('sup-', [status(thm)], ['63', '64'])).
% 0.90/1.17  thf('75', plain,
% 0.90/1.17      (((k6_partfun1 @ (k1_relat_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 0.90/1.17      inference('demod', [status(thm)], ['67', '72', '73', '74'])).
% 0.90/1.17  thf(t71_relat_1, axiom,
% 0.90/1.17    (![A:$i]:
% 0.90/1.17     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.90/1.17       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.90/1.17  thf('76', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 0.90/1.17      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.90/1.17  thf('77', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.90/1.17      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.90/1.17  thf('78', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 0.90/1.17      inference('demod', [status(thm)], ['76', '77'])).
% 0.90/1.17  thf('79', plain,
% 0.90/1.17      (((k1_relat_1 @ (k6_partfun1 @ sk_B)) = (k1_relat_1 @ sk_D))),
% 0.90/1.17      inference('sup+', [status(thm)], ['75', '78'])).
% 0.90/1.17  thf('80', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 0.90/1.17      inference('demod', [status(thm)], ['76', '77'])).
% 0.90/1.17  thf('81', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.90/1.17      inference('demod', [status(thm)], ['79', '80'])).
% 0.90/1.17  thf('82', plain,
% 0.90/1.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('83', plain,
% 0.90/1.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf(redefinition_k1_partfun1, axiom,
% 0.90/1.17    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.90/1.17     ( ( ( v1_funct_1 @ E ) & 
% 0.90/1.17         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.90/1.17         ( v1_funct_1 @ F ) & 
% 0.90/1.17         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.90/1.17       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.90/1.17  thf('84', plain,
% 0.90/1.17      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.90/1.17         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.90/1.17          | ~ (v1_funct_1 @ X25)
% 0.90/1.17          | ~ (v1_funct_1 @ X28)
% 0.90/1.17          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.90/1.17          | ((k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28)
% 0.90/1.17              = (k5_relat_1 @ X25 @ X28)))),
% 0.90/1.17      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.90/1.17  thf('85', plain,
% 0.90/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.17         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.90/1.17            = (k5_relat_1 @ sk_C @ X0))
% 0.90/1.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.90/1.17          | ~ (v1_funct_1 @ X0)
% 0.90/1.17          | ~ (v1_funct_1 @ sk_C))),
% 0.90/1.17      inference('sup-', [status(thm)], ['83', '84'])).
% 0.90/1.17  thf('86', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('87', plain,
% 0.90/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.17         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.90/1.17            = (k5_relat_1 @ sk_C @ X0))
% 0.90/1.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.90/1.17          | ~ (v1_funct_1 @ X0))),
% 0.90/1.17      inference('demod', [status(thm)], ['85', '86'])).
% 0.90/1.17  thf('88', plain,
% 0.90/1.17      ((~ (v1_funct_1 @ sk_D)
% 0.90/1.17        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.90/1.17            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.90/1.17      inference('sup-', [status(thm)], ['82', '87'])).
% 0.90/1.17  thf('89', plain, ((v1_funct_1 @ sk_D)),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('90', plain,
% 0.90/1.17      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.90/1.17         = (k6_partfun1 @ sk_A))),
% 0.90/1.17      inference('demod', [status(thm)], ['23', '24'])).
% 0.90/1.17  thf('91', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.90/1.17      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.90/1.17  thf(t63_funct_1, axiom,
% 0.90/1.17    (![A:$i]:
% 0.90/1.17     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.90/1.17       ( ![B:$i]:
% 0.90/1.17         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.90/1.17           ( ( ( v2_funct_1 @ A ) & 
% 0.90/1.17               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.90/1.17               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.90/1.17             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.90/1.17  thf('92', plain,
% 0.90/1.17      (![X11 : $i, X12 : $i]:
% 0.90/1.17         (~ (v1_relat_1 @ X11)
% 0.90/1.17          | ~ (v1_funct_1 @ X11)
% 0.90/1.17          | ((X11) = (k2_funct_1 @ X12))
% 0.90/1.17          | ((k5_relat_1 @ X12 @ X11) != (k6_relat_1 @ (k1_relat_1 @ X12)))
% 0.90/1.17          | ((k2_relat_1 @ X12) != (k1_relat_1 @ X11))
% 0.90/1.17          | ~ (v2_funct_1 @ X12)
% 0.90/1.17          | ~ (v1_funct_1 @ X12)
% 0.90/1.17          | ~ (v1_relat_1 @ X12))),
% 0.90/1.17      inference('cnf', [status(esa)], [t63_funct_1])).
% 0.90/1.17  thf('93', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.90/1.17      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.90/1.17  thf('94', plain,
% 0.90/1.17      (![X11 : $i, X12 : $i]:
% 0.90/1.17         (~ (v1_relat_1 @ X11)
% 0.90/1.17          | ~ (v1_funct_1 @ X11)
% 0.90/1.17          | ((X11) = (k2_funct_1 @ X12))
% 0.90/1.17          | ((k5_relat_1 @ X12 @ X11) != (k6_partfun1 @ (k1_relat_1 @ X12)))
% 0.90/1.17          | ((k2_relat_1 @ X12) != (k1_relat_1 @ X11))
% 0.90/1.17          | ~ (v2_funct_1 @ X12)
% 0.90/1.17          | ~ (v1_funct_1 @ X12)
% 0.90/1.17          | ~ (v1_relat_1 @ X12))),
% 0.90/1.17      inference('demod', [status(thm)], ['92', '93'])).
% 0.90/1.17  thf('95', plain,
% 0.90/1.17      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 0.90/1.17        | ~ (v1_relat_1 @ sk_C)
% 0.90/1.17        | ~ (v1_funct_1 @ sk_C)
% 0.90/1.17        | ~ (v2_funct_1 @ sk_C)
% 0.90/1.17        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.90/1.17        | ((sk_D) = (k2_funct_1 @ sk_C))
% 0.90/1.17        | ~ (v1_funct_1 @ sk_D)
% 0.90/1.17        | ~ (v1_relat_1 @ sk_D))),
% 0.90/1.17      inference('sup-', [status(thm)], ['91', '94'])).
% 0.90/1.17  thf('96', plain,
% 0.90/1.17      (![X10 : $i]:
% 0.90/1.17         (~ (v2_funct_1 @ X10)
% 0.90/1.17          | ((k5_relat_1 @ X10 @ (k2_funct_1 @ X10))
% 0.90/1.17              = (k6_partfun1 @ (k1_relat_1 @ X10)))
% 0.90/1.17          | ~ (v1_funct_1 @ X10)
% 0.90/1.17          | ~ (v1_relat_1 @ X10))),
% 0.90/1.17      inference('demod', [status(thm)], ['0', '1'])).
% 0.90/1.17  thf('97', plain,
% 0.90/1.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('98', plain,
% 0.90/1.17      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.90/1.17         (((X45) = (k1_xboole_0))
% 0.90/1.17          | ~ (v1_funct_1 @ X46)
% 0.90/1.17          | ~ (v1_funct_2 @ X46 @ X47 @ X45)
% 0.90/1.17          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X45)))
% 0.90/1.17          | ((k5_relat_1 @ X46 @ (k2_funct_1 @ X46)) = (k6_partfun1 @ X47))
% 0.90/1.17          | ~ (v2_funct_1 @ X46)
% 0.90/1.17          | ((k2_relset_1 @ X47 @ X45 @ X46) != (X45)))),
% 0.90/1.17      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.90/1.17  thf('99', plain,
% 0.90/1.17      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.90/1.17        | ~ (v2_funct_1 @ sk_C)
% 0.90/1.17        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.90/1.17        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.90/1.17        | ~ (v1_funct_1 @ sk_C)
% 0.90/1.17        | ((sk_B) = (k1_xboole_0)))),
% 0.90/1.17      inference('sup-', [status(thm)], ['97', '98'])).
% 0.90/1.17  thf('100', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('101', plain, ((v2_funct_1 @ sk_C)),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('102', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('103', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('104', plain,
% 0.90/1.17      ((((sk_B) != (sk_B))
% 0.90/1.17        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.90/1.17        | ((sk_B) = (k1_xboole_0)))),
% 0.90/1.17      inference('demod', [status(thm)], ['99', '100', '101', '102', '103'])).
% 0.90/1.17  thf('105', plain,
% 0.90/1.17      ((((sk_B) = (k1_xboole_0))
% 0.90/1.17        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 0.90/1.17      inference('simplify', [status(thm)], ['104'])).
% 0.90/1.17  thf('106', plain, (((sk_B) != (k1_xboole_0))),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('107', plain,
% 0.90/1.17      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 0.90/1.17      inference('simplify_reflect-', [status(thm)], ['105', '106'])).
% 0.90/1.17  thf('108', plain,
% 0.90/1.17      ((((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.90/1.17        | ~ (v1_relat_1 @ sk_C)
% 0.90/1.17        | ~ (v1_funct_1 @ sk_C)
% 0.90/1.17        | ~ (v2_funct_1 @ sk_C))),
% 0.90/1.17      inference('sup+', [status(thm)], ['96', '107'])).
% 0.90/1.17  thf('109', plain,
% 0.90/1.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('110', plain,
% 0.90/1.17      (![X0 : $i, X1 : $i]:
% 0.90/1.17         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.90/1.17          | (v1_relat_1 @ X0)
% 0.90/1.17          | ~ (v1_relat_1 @ X1))),
% 0.90/1.17      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.90/1.17  thf('111', plain,
% 0.90/1.17      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.90/1.17      inference('sup-', [status(thm)], ['109', '110'])).
% 0.90/1.17  thf('112', plain,
% 0.90/1.17      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.90/1.17      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.90/1.17  thf('113', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.17      inference('demod', [status(thm)], ['111', '112'])).
% 0.90/1.17  thf('114', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('115', plain, ((v2_funct_1 @ sk_C)),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('116', plain,
% 0.90/1.17      (((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 0.90/1.17      inference('demod', [status(thm)], ['108', '113', '114', '115'])).
% 0.90/1.17  thf('117', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 0.90/1.17      inference('demod', [status(thm)], ['76', '77'])).
% 0.90/1.17  thf('118', plain,
% 0.90/1.17      (((k1_relat_1 @ (k6_partfun1 @ sk_A)) = (k1_relat_1 @ sk_C))),
% 0.90/1.17      inference('sup+', [status(thm)], ['116', '117'])).
% 0.90/1.17  thf('119', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 0.90/1.17      inference('demod', [status(thm)], ['76', '77'])).
% 0.90/1.17  thf('120', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.90/1.17      inference('demod', [status(thm)], ['118', '119'])).
% 0.90/1.17  thf('121', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.17      inference('demod', [status(thm)], ['111', '112'])).
% 0.90/1.17  thf('122', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('123', plain, ((v2_funct_1 @ sk_C)),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('124', plain,
% 0.90/1.17      (![X10 : $i]:
% 0.90/1.17         (~ (v2_funct_1 @ X10)
% 0.90/1.17          | ((k5_relat_1 @ (k2_funct_1 @ X10) @ X10)
% 0.90/1.17              = (k6_relat_1 @ (k2_relat_1 @ X10)))
% 0.90/1.17          | ~ (v1_funct_1 @ X10)
% 0.90/1.17          | ~ (v1_relat_1 @ X10))),
% 0.90/1.17      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.90/1.17  thf('125', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.90/1.17      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.90/1.17  thf('126', plain,
% 0.90/1.17      (![X10 : $i]:
% 0.90/1.17         (~ (v2_funct_1 @ X10)
% 0.90/1.17          | ((k5_relat_1 @ (k2_funct_1 @ X10) @ X10)
% 0.90/1.17              = (k6_partfun1 @ (k2_relat_1 @ X10)))
% 0.90/1.17          | ~ (v1_funct_1 @ X10)
% 0.90/1.17          | ~ (v1_relat_1 @ X10))),
% 0.90/1.17      inference('demod', [status(thm)], ['124', '125'])).
% 0.90/1.17  thf('127', plain,
% 0.90/1.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('128', plain,
% 0.90/1.17      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.90/1.17         (((X45) = (k1_xboole_0))
% 0.90/1.17          | ~ (v1_funct_1 @ X46)
% 0.90/1.17          | ~ (v1_funct_2 @ X46 @ X47 @ X45)
% 0.90/1.17          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X45)))
% 0.90/1.17          | ((k5_relat_1 @ (k2_funct_1 @ X46) @ X46) = (k6_partfun1 @ X45))
% 0.90/1.17          | ~ (v2_funct_1 @ X46)
% 0.90/1.17          | ((k2_relset_1 @ X47 @ X45 @ X46) != (X45)))),
% 0.90/1.17      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.90/1.17  thf('129', plain,
% 0.90/1.17      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.90/1.17        | ~ (v2_funct_1 @ sk_C)
% 0.90/1.17        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 0.90/1.17        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.90/1.17        | ~ (v1_funct_1 @ sk_C)
% 0.90/1.17        | ((sk_B) = (k1_xboole_0)))),
% 0.90/1.17      inference('sup-', [status(thm)], ['127', '128'])).
% 0.90/1.17  thf('130', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('131', plain, ((v2_funct_1 @ sk_C)),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('132', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('133', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('134', plain,
% 0.90/1.17      ((((sk_B) != (sk_B))
% 0.90/1.17        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 0.90/1.17        | ((sk_B) = (k1_xboole_0)))),
% 0.90/1.17      inference('demod', [status(thm)], ['129', '130', '131', '132', '133'])).
% 0.90/1.17  thf('135', plain,
% 0.90/1.17      ((((sk_B) = (k1_xboole_0))
% 0.90/1.17        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 0.90/1.17      inference('simplify', [status(thm)], ['134'])).
% 0.90/1.17  thf('136', plain, (((sk_B) != (k1_xboole_0))),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('137', plain,
% 0.90/1.17      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 0.90/1.17      inference('simplify_reflect-', [status(thm)], ['135', '136'])).
% 0.90/1.17  thf('138', plain,
% 0.90/1.17      ((((k6_partfun1 @ (k2_relat_1 @ sk_C)) = (k6_partfun1 @ sk_B))
% 0.90/1.17        | ~ (v1_relat_1 @ sk_C)
% 0.90/1.17        | ~ (v1_funct_1 @ sk_C)
% 0.90/1.17        | ~ (v2_funct_1 @ sk_C))),
% 0.90/1.17      inference('sup+', [status(thm)], ['126', '137'])).
% 0.90/1.17  thf('139', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.17      inference('demod', [status(thm)], ['111', '112'])).
% 0.90/1.17  thf('140', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('141', plain, ((v2_funct_1 @ sk_C)),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('142', plain,
% 0.90/1.17      (((k6_partfun1 @ (k2_relat_1 @ sk_C)) = (k6_partfun1 @ sk_B))),
% 0.90/1.17      inference('demod', [status(thm)], ['138', '139', '140', '141'])).
% 0.90/1.17  thf('143', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 0.90/1.17      inference('demod', [status(thm)], ['76', '77'])).
% 0.90/1.17  thf('144', plain,
% 0.90/1.17      (((k1_relat_1 @ (k6_partfun1 @ sk_B)) = (k2_relat_1 @ sk_C))),
% 0.90/1.17      inference('sup+', [status(thm)], ['142', '143'])).
% 0.90/1.17  thf('145', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 0.90/1.17      inference('demod', [status(thm)], ['76', '77'])).
% 0.90/1.17  thf('146', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 0.90/1.17      inference('demod', [status(thm)], ['144', '145'])).
% 0.90/1.17  thf('147', plain, ((v1_funct_1 @ sk_D)),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('148', plain, ((v1_relat_1 @ sk_D)),
% 0.90/1.17      inference('demod', [status(thm)], ['70', '71'])).
% 0.90/1.17  thf('149', plain,
% 0.90/1.17      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 0.90/1.17        | ((sk_B) != (k1_relat_1 @ sk_D))
% 0.90/1.17        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 0.90/1.17      inference('demod', [status(thm)],
% 0.90/1.17                ['95', '120', '121', '122', '123', '146', '147', '148'])).
% 0.90/1.17  thf('150', plain,
% 0.90/1.17      ((((sk_D) = (k2_funct_1 @ sk_C)) | ((sk_B) != (k1_relat_1 @ sk_D)))),
% 0.90/1.17      inference('simplify', [status(thm)], ['149'])).
% 0.90/1.17  thf('151', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('152', plain, (((sk_B) != (k1_relat_1 @ sk_D))),
% 0.90/1.17      inference('simplify_reflect-', [status(thm)], ['150', '151'])).
% 0.90/1.17  thf('153', plain, ($false),
% 0.90/1.17      inference('simplify_reflect-', [status(thm)], ['81', '152'])).
% 0.90/1.17  
% 0.90/1.17  % SZS output end Refutation
% 0.90/1.17  
% 0.90/1.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

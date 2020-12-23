%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zWwzmCCh7P

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:29 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  200 ( 494 expanded)
%              Number of leaves         :   43 ( 166 expanded)
%              Depth                    :   21
%              Number of atoms          : 1970 (11649 expanded)
%              Number of equality atoms :  145 ( 826 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

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
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
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
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( X44 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X44 ) ) )
      | ( ( k5_relat_1 @ X45 @ ( k2_funct_1 @ X45 ) )
        = ( k6_partfun1 @ X46 ) )
      | ~ ( v2_funct_1 @ X45 )
      | ( ( k2_relset_1 @ X46 @ X44 @ X45 )
       != X44 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X19 @ X20 @ X22 @ X23 @ X18 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X23 ) ) ) ) ),
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

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('24',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('25',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('26',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
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

thf('29',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( r2_relset_1 @ X32 @ X32 @ ( k1_partfun1 @ X32 @ X33 @ X33 @ X32 @ X31 @ X34 ) @ ( k6_partfun1 @ X32 ) )
      | ( ( k2_relset_1 @ X33 @ X32 @ X34 )
        = X32 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X33 @ X32 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['27','33'])).

thf('35',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('36',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( r2_relset_1 @ X14 @ X15 @ X13 @ X16 )
      | ( X13 != X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('37',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_relset_1 @ X14 @ X15 @ X16 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['34','38','39','40','41'])).

thf('43',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','42'])).

thf('44',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('46',plain,(
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

thf('47',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( zip_tseitin_0 @ X39 @ X42 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X43 @ X40 @ X40 @ X41 @ X42 @ X39 ) )
      | ( zip_tseitin_1 @ X41 @ X40 )
      | ( ( k2_relset_1 @ X43 @ X40 @ X42 )
       != X40 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X40 ) ) )
      | ~ ( v1_funct_2 @ X42 @ X43 @ X40 )
      | ~ ( v1_funct_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('48',plain,(
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
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['45','51'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('53',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('54',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('55',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X7 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['52','55','56','57','58','59'])).

thf('61',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X37 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('63',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X35: $i,X36: $i] :
      ( ( v2_funct_1 @ X36 )
      | ~ ( zip_tseitin_0 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('67',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['44','67'])).

thf('69',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['2','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

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

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

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

thf('76',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['65','66'])).

thf('77',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['69','74','75','76'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('78',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('79',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('80',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['77','80'])).

thf('82',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('83',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
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

thf('86',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 )
        = ( k5_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['84','89'])).

thf('91',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('93',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['90','91','92'])).

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

thf('94',plain,(
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

thf('95',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('96',plain,(
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
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
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
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k5_relat_1 @ X10 @ ( k2_funct_1 @ X10 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('99',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( X44 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X44 ) ) )
      | ( ( k5_relat_1 @ X45 @ ( k2_funct_1 @ X45 ) )
        = ( k6_partfun1 @ X46 ) )
      | ~ ( v2_funct_1 @ X45 )
      | ( ( k2_relset_1 @ X46 @ X44 @ X45 )
       != X44 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('101',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['101','102','103','104','105'])).

thf('107',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['98','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('114',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('115',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['110','115','116','117'])).

thf('119',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('120',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('122',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['120','121'])).

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
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X10 ) @ X10 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('127',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('128',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X10 ) @ X10 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( X44 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X44 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X45 ) @ X45 )
        = ( k6_partfun1 @ X44 ) )
      | ~ ( v2_funct_1 @ X45 )
      | ( ( k2_relset_1 @ X46 @ X44 @ X45 )
       != X44 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('131',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['131','132','133','134','135'])).

thf('137',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['137','138'])).

thf('140',plain,
    ( ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['128','139'])).

thf('141',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['113','114'])).

thf('142',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['140','141','142','143'])).

thf('145',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('146',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('148',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['72','73'])).

thf('151',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['97','122','123','124','125','148','149','150'])).

thf('152',plain,
    ( ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    sk_B
 != ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['152','153'])).

thf('155',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['83','154'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zWwzmCCh7P
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:48:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.90/1.14  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.90/1.14  % Solved by: fo/fo7.sh
% 0.90/1.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.14  % done 834 iterations in 0.686s
% 0.90/1.14  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.90/1.14  % SZS output start Refutation
% 0.90/1.14  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.90/1.14  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.90/1.14  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.14  thf(sk_C_type, type, sk_C: $i).
% 0.90/1.14  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.90/1.14  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.90/1.14  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.90/1.14  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.90/1.14  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.90/1.14  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.90/1.14  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.90/1.14  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.90/1.14  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.14  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.14  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.14  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.90/1.14  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.90/1.14  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.90/1.14  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.90/1.14  thf(sk_D_type, type, sk_D: $i).
% 0.90/1.14  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.90/1.14  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.90/1.14  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.90/1.14  thf(t61_funct_1, axiom,
% 0.90/1.14    (![A:$i]:
% 0.90/1.14     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.90/1.14       ( ( v2_funct_1 @ A ) =>
% 0.90/1.14         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.90/1.14             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.90/1.14           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.90/1.14             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.90/1.14  thf('0', plain,
% 0.90/1.14      (![X10 : $i]:
% 0.90/1.14         (~ (v2_funct_1 @ X10)
% 0.90/1.14          | ((k5_relat_1 @ X10 @ (k2_funct_1 @ X10))
% 0.90/1.14              = (k6_relat_1 @ (k1_relat_1 @ X10)))
% 0.90/1.14          | ~ (v1_funct_1 @ X10)
% 0.90/1.14          | ~ (v1_relat_1 @ X10))),
% 0.90/1.14      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.90/1.14  thf(redefinition_k6_partfun1, axiom,
% 0.90/1.14    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.90/1.14  thf('1', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.90/1.14      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.90/1.14  thf('2', plain,
% 0.90/1.14      (![X10 : $i]:
% 0.90/1.14         (~ (v2_funct_1 @ X10)
% 0.90/1.14          | ((k5_relat_1 @ X10 @ (k2_funct_1 @ X10))
% 0.90/1.14              = (k6_partfun1 @ (k1_relat_1 @ X10)))
% 0.90/1.14          | ~ (v1_funct_1 @ X10)
% 0.90/1.14          | ~ (v1_relat_1 @ X10))),
% 0.90/1.14      inference('demod', [status(thm)], ['0', '1'])).
% 0.90/1.14  thf(t36_funct_2, conjecture,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.90/1.14         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.90/1.14       ( ![D:$i]:
% 0.90/1.14         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.90/1.14             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.90/1.14           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.90/1.14               ( r2_relset_1 @
% 0.90/1.14                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.90/1.14                 ( k6_partfun1 @ A ) ) & 
% 0.90/1.14               ( v2_funct_1 @ C ) ) =>
% 0.90/1.14             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.90/1.14               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.90/1.14  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.14    (~( ![A:$i,B:$i,C:$i]:
% 0.90/1.14        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.90/1.14            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.90/1.14          ( ![D:$i]:
% 0.90/1.14            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.90/1.14                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.90/1.14              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.90/1.14                  ( r2_relset_1 @
% 0.90/1.14                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.90/1.14                    ( k6_partfun1 @ A ) ) & 
% 0.90/1.14                  ( v2_funct_1 @ C ) ) =>
% 0.90/1.14                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.90/1.14                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.90/1.14    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.90/1.14  thf('3', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(t35_funct_2, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.90/1.14         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.90/1.14       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.90/1.14         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.90/1.14           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.90/1.14             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.90/1.14  thf('4', plain,
% 0.90/1.14      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.90/1.14         (((X44) = (k1_xboole_0))
% 0.90/1.14          | ~ (v1_funct_1 @ X45)
% 0.90/1.14          | ~ (v1_funct_2 @ X45 @ X46 @ X44)
% 0.90/1.14          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X44)))
% 0.90/1.14          | ((k5_relat_1 @ X45 @ (k2_funct_1 @ X45)) = (k6_partfun1 @ X46))
% 0.90/1.14          | ~ (v2_funct_1 @ X45)
% 0.90/1.14          | ((k2_relset_1 @ X46 @ X44 @ X45) != (X44)))),
% 0.90/1.14      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.90/1.14  thf('5', plain,
% 0.90/1.14      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 0.90/1.14        | ~ (v2_funct_1 @ sk_D)
% 0.90/1.14        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.90/1.14        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.90/1.14        | ~ (v1_funct_1 @ sk_D)
% 0.90/1.14        | ((sk_A) = (k1_xboole_0)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['3', '4'])).
% 0.90/1.14  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('8', plain,
% 0.90/1.14      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 0.90/1.14        | ~ (v2_funct_1 @ sk_D)
% 0.90/1.14        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.90/1.14        | ((sk_A) = (k1_xboole_0)))),
% 0.90/1.14      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.90/1.14  thf('9', plain, (((sk_A) != (k1_xboole_0))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('10', plain,
% 0.90/1.14      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 0.90/1.14        | ~ (v2_funct_1 @ sk_D)
% 0.90/1.14        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 0.90/1.14      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.90/1.14  thf('11', plain,
% 0.90/1.14      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.14        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.90/1.14        (k6_partfun1 @ sk_A))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('12', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('13', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(dt_k1_partfun1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.90/1.14     ( ( ( v1_funct_1 @ E ) & 
% 0.90/1.14         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.90/1.14         ( v1_funct_1 @ F ) & 
% 0.90/1.14         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.90/1.14       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.90/1.14         ( m1_subset_1 @
% 0.90/1.14           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.90/1.14           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.90/1.14  thf('14', plain,
% 0.90/1.14      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.90/1.14         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.90/1.14          | ~ (v1_funct_1 @ X18)
% 0.90/1.14          | ~ (v1_funct_1 @ X21)
% 0.90/1.14          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.90/1.14          | (m1_subset_1 @ (k1_partfun1 @ X19 @ X20 @ X22 @ X23 @ X18 @ X21) @ 
% 0.90/1.14             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X23))))),
% 0.90/1.14      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.90/1.14  thf('15', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.14         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.90/1.14           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.90/1.14          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.90/1.14          | ~ (v1_funct_1 @ X1)
% 0.90/1.14          | ~ (v1_funct_1 @ sk_C))),
% 0.90/1.14      inference('sup-', [status(thm)], ['13', '14'])).
% 0.90/1.14  thf('16', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('17', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.14         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.90/1.14           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.90/1.14          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.90/1.14          | ~ (v1_funct_1 @ X1))),
% 0.90/1.14      inference('demod', [status(thm)], ['15', '16'])).
% 0.90/1.14  thf('18', plain,
% 0.90/1.14      ((~ (v1_funct_1 @ sk_D)
% 0.90/1.14        | (m1_subset_1 @ 
% 0.90/1.14           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.90/1.14           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['12', '17'])).
% 0.90/1.14  thf('19', plain, ((v1_funct_1 @ sk_D)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('20', plain,
% 0.90/1.14      ((m1_subset_1 @ 
% 0.90/1.14        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.90/1.14        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.14      inference('demod', [status(thm)], ['18', '19'])).
% 0.90/1.14  thf(redefinition_r2_relset_1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.14     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.90/1.14         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.90/1.14       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.90/1.14  thf('21', plain,
% 0.90/1.14      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.90/1.14         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.90/1.14          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.90/1.14          | ((X13) = (X16))
% 0.90/1.14          | ~ (r2_relset_1 @ X14 @ X15 @ X13 @ X16))),
% 0.90/1.14      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.90/1.14  thf('22', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.14             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.90/1.14          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.90/1.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.90/1.14      inference('sup-', [status(thm)], ['20', '21'])).
% 0.90/1.14  thf('23', plain,
% 0.90/1.14      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.90/1.14           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.90/1.14        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.90/1.14            = (k6_partfun1 @ sk_A)))),
% 0.90/1.14      inference('sup-', [status(thm)], ['11', '22'])).
% 0.90/1.14  thf(t29_relset_1, axiom,
% 0.90/1.14    (![A:$i]:
% 0.90/1.14     ( m1_subset_1 @
% 0.90/1.14       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.90/1.14  thf('24', plain,
% 0.90/1.14      (![X17 : $i]:
% 0.90/1.14         (m1_subset_1 @ (k6_relat_1 @ X17) @ 
% 0.90/1.14          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))),
% 0.90/1.14      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.90/1.14  thf('25', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.90/1.14      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.90/1.14  thf('26', plain,
% 0.90/1.14      (![X17 : $i]:
% 0.90/1.14         (m1_subset_1 @ (k6_partfun1 @ X17) @ 
% 0.90/1.14          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))),
% 0.90/1.14      inference('demod', [status(thm)], ['24', '25'])).
% 0.90/1.14  thf('27', plain,
% 0.90/1.14      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.90/1.14         = (k6_partfun1 @ sk_A))),
% 0.90/1.14      inference('demod', [status(thm)], ['23', '26'])).
% 0.90/1.14  thf('28', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(t24_funct_2, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.90/1.14         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.90/1.14       ( ![D:$i]:
% 0.90/1.14         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.90/1.14             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.90/1.14           ( ( r2_relset_1 @
% 0.90/1.14               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.90/1.14               ( k6_partfun1 @ B ) ) =>
% 0.90/1.14             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.90/1.14  thf('29', plain,
% 0.90/1.14      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.90/1.14         (~ (v1_funct_1 @ X31)
% 0.90/1.14          | ~ (v1_funct_2 @ X31 @ X32 @ X33)
% 0.90/1.14          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.90/1.14          | ~ (r2_relset_1 @ X32 @ X32 @ 
% 0.90/1.14               (k1_partfun1 @ X32 @ X33 @ X33 @ X32 @ X31 @ X34) @ 
% 0.90/1.14               (k6_partfun1 @ X32))
% 0.90/1.14          | ((k2_relset_1 @ X33 @ X32 @ X34) = (X32))
% 0.90/1.14          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 0.90/1.14          | ~ (v1_funct_2 @ X34 @ X33 @ X32)
% 0.90/1.14          | ~ (v1_funct_1 @ X34))),
% 0.90/1.14      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.90/1.14  thf('30', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (~ (v1_funct_1 @ X0)
% 0.90/1.14          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.90/1.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.90/1.14          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.90/1.14          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.14               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.90/1.14               (k6_partfun1 @ sk_A))
% 0.90/1.14          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.90/1.14          | ~ (v1_funct_1 @ sk_C))),
% 0.90/1.14      inference('sup-', [status(thm)], ['28', '29'])).
% 0.90/1.14  thf('31', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('33', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (~ (v1_funct_1 @ X0)
% 0.90/1.14          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.90/1.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.90/1.14          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.90/1.14          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.14               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.90/1.14               (k6_partfun1 @ sk_A)))),
% 0.90/1.14      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.90/1.14  thf('34', plain,
% 0.90/1.14      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 0.90/1.14           (k6_partfun1 @ sk_A))
% 0.90/1.14        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.90/1.14        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.90/1.14        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.90/1.14        | ~ (v1_funct_1 @ sk_D))),
% 0.90/1.14      inference('sup-', [status(thm)], ['27', '33'])).
% 0.90/1.14  thf('35', plain,
% 0.90/1.14      (![X17 : $i]:
% 0.90/1.14         (m1_subset_1 @ (k6_partfun1 @ X17) @ 
% 0.90/1.14          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))),
% 0.90/1.14      inference('demod', [status(thm)], ['24', '25'])).
% 0.90/1.14  thf('36', plain,
% 0.90/1.14      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.90/1.14         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.90/1.14          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.90/1.14          | (r2_relset_1 @ X14 @ X15 @ X13 @ X16)
% 0.90/1.14          | ((X13) != (X16)))),
% 0.90/1.14      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.90/1.14  thf('37', plain,
% 0.90/1.14      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.90/1.14         ((r2_relset_1 @ X14 @ X15 @ X16 @ X16)
% 0.90/1.14          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.90/1.14      inference('simplify', [status(thm)], ['36'])).
% 0.90/1.14  thf('38', plain,
% 0.90/1.14      (![X0 : $i]:
% 0.90/1.14         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 0.90/1.14      inference('sup-', [status(thm)], ['35', '37'])).
% 0.90/1.14  thf('39', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('40', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('41', plain, ((v1_funct_1 @ sk_D)),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf('42', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))),
% 0.90/1.14      inference('demod', [status(thm)], ['34', '38', '39', '40', '41'])).
% 0.90/1.14  thf('43', plain,
% 0.90/1.14      ((((sk_A) != (sk_A))
% 0.90/1.14        | ~ (v2_funct_1 @ sk_D)
% 0.90/1.14        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 0.90/1.14      inference('demod', [status(thm)], ['10', '42'])).
% 0.90/1.14  thf('44', plain,
% 0.90/1.14      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.90/1.14        | ~ (v2_funct_1 @ sk_D))),
% 0.90/1.14      inference('simplify', [status(thm)], ['43'])).
% 0.90/1.14  thf('45', plain,
% 0.90/1.14      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.90/1.14         = (k6_partfun1 @ sk_A))),
% 0.90/1.14      inference('demod', [status(thm)], ['23', '26'])).
% 0.90/1.14  thf('46', plain,
% 0.90/1.14      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(t30_funct_2, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.14     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.90/1.14         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 0.90/1.14       ( ![E:$i]:
% 0.90/1.14         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 0.90/1.14             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 0.90/1.14           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 0.90/1.14               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 0.90/1.14             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 0.90/1.14               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 0.90/1.14  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 0.90/1.14  thf(zf_stmt_2, axiom,
% 0.90/1.14    (![C:$i,B:$i]:
% 0.90/1.14     ( ( zip_tseitin_1 @ C @ B ) =>
% 0.90/1.14       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 0.90/1.14  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.90/1.14  thf(zf_stmt_4, axiom,
% 0.90/1.14    (![E:$i,D:$i]:
% 0.90/1.14     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 0.90/1.14  thf(zf_stmt_5, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.14     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.90/1.14         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.90/1.14       ( ![E:$i]:
% 0.90/1.14         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.90/1.14             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.90/1.14           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 0.90/1.14               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 0.90/1.14             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 0.90/1.14  thf('47', plain,
% 0.90/1.14      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.90/1.14         (~ (v1_funct_1 @ X39)
% 0.90/1.14          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 0.90/1.14          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.90/1.14          | (zip_tseitin_0 @ X39 @ X42)
% 0.90/1.14          | ~ (v2_funct_1 @ (k1_partfun1 @ X43 @ X40 @ X40 @ X41 @ X42 @ X39))
% 0.90/1.14          | (zip_tseitin_1 @ X41 @ X40)
% 0.90/1.14          | ((k2_relset_1 @ X43 @ X40 @ X42) != (X40))
% 0.90/1.14          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X40)))
% 0.90/1.14          | ~ (v1_funct_2 @ X42 @ X43 @ X40)
% 0.90/1.14          | ~ (v1_funct_1 @ X42))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.90/1.14  thf('48', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         (~ (v1_funct_1 @ X0)
% 0.90/1.14          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.90/1.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.90/1.15          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 0.90/1.15          | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.90/1.15          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.90/1.15          | (zip_tseitin_0 @ sk_D @ X0)
% 0.90/1.15          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.90/1.15          | ~ (v1_funct_1 @ sk_D))),
% 0.90/1.15      inference('sup-', [status(thm)], ['46', '47'])).
% 0.90/1.15  thf('49', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf('50', plain, ((v1_funct_1 @ sk_D)),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf('51', plain,
% 0.90/1.15      (![X0 : $i, X1 : $i]:
% 0.90/1.15         (~ (v1_funct_1 @ X0)
% 0.90/1.15          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.90/1.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.90/1.15          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 0.90/1.15          | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.90/1.15          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.90/1.15          | (zip_tseitin_0 @ sk_D @ X0))),
% 0.90/1.15      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.90/1.15  thf('52', plain,
% 0.90/1.15      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.90/1.15        | (zip_tseitin_0 @ sk_D @ sk_C)
% 0.90/1.15        | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.90/1.15        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.90/1.15        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.90/1.15        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.90/1.15        | ~ (v1_funct_1 @ sk_C))),
% 0.90/1.15      inference('sup-', [status(thm)], ['45', '51'])).
% 0.90/1.15  thf(fc4_funct_1, axiom,
% 0.90/1.15    (![A:$i]:
% 0.90/1.15     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.90/1.15       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.90/1.15  thf('53', plain, (![X7 : $i]: (v2_funct_1 @ (k6_relat_1 @ X7))),
% 0.90/1.15      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.90/1.15  thf('54', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.90/1.15      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.90/1.15  thf('55', plain, (![X7 : $i]: (v2_funct_1 @ (k6_partfun1 @ X7))),
% 0.90/1.15      inference('demod', [status(thm)], ['53', '54'])).
% 0.90/1.15  thf('56', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf('57', plain,
% 0.90/1.15      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf('58', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf('59', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf('60', plain,
% 0.90/1.15      (((zip_tseitin_0 @ sk_D @ sk_C)
% 0.90/1.15        | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.90/1.15        | ((sk_B) != (sk_B)))),
% 0.90/1.15      inference('demod', [status(thm)], ['52', '55', '56', '57', '58', '59'])).
% 0.90/1.15  thf('61', plain,
% 0.90/1.15      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 0.90/1.15      inference('simplify', [status(thm)], ['60'])).
% 0.90/1.15  thf('62', plain,
% 0.90/1.15      (![X37 : $i, X38 : $i]:
% 0.90/1.15         (((X37) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X37 @ X38))),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.90/1.15  thf('63', plain,
% 0.90/1.15      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.90/1.15      inference('sup-', [status(thm)], ['61', '62'])).
% 0.90/1.15  thf('64', plain, (((sk_A) != (k1_xboole_0))),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf('65', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 0.90/1.15      inference('simplify_reflect-', [status(thm)], ['63', '64'])).
% 0.90/1.15  thf('66', plain,
% 0.90/1.15      (![X35 : $i, X36 : $i]:
% 0.90/1.15         ((v2_funct_1 @ X36) | ~ (zip_tseitin_0 @ X36 @ X35))),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.90/1.15  thf('67', plain, ((v2_funct_1 @ sk_D)),
% 0.90/1.15      inference('sup-', [status(thm)], ['65', '66'])).
% 0.90/1.15  thf('68', plain,
% 0.90/1.15      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 0.90/1.15      inference('demod', [status(thm)], ['44', '67'])).
% 0.90/1.15  thf('69', plain,
% 0.90/1.15      ((((k6_partfun1 @ (k1_relat_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.90/1.15        | ~ (v1_relat_1 @ sk_D)
% 0.90/1.15        | ~ (v1_funct_1 @ sk_D)
% 0.90/1.15        | ~ (v2_funct_1 @ sk_D))),
% 0.90/1.15      inference('sup+', [status(thm)], ['2', '68'])).
% 0.90/1.15  thf('70', plain,
% 0.90/1.15      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf(cc2_relat_1, axiom,
% 0.90/1.15    (![A:$i]:
% 0.90/1.15     ( ( v1_relat_1 @ A ) =>
% 0.90/1.15       ( ![B:$i]:
% 0.90/1.15         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.90/1.15  thf('71', plain,
% 0.90/1.15      (![X0 : $i, X1 : $i]:
% 0.90/1.15         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.90/1.15          | (v1_relat_1 @ X0)
% 0.90/1.15          | ~ (v1_relat_1 @ X1))),
% 0.90/1.15      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.90/1.15  thf('72', plain,
% 0.90/1.15      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.90/1.15      inference('sup-', [status(thm)], ['70', '71'])).
% 0.90/1.15  thf(fc6_relat_1, axiom,
% 0.90/1.15    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.90/1.15  thf('73', plain,
% 0.90/1.15      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.90/1.15      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.90/1.15  thf('74', plain, ((v1_relat_1 @ sk_D)),
% 0.90/1.15      inference('demod', [status(thm)], ['72', '73'])).
% 0.90/1.15  thf('75', plain, ((v1_funct_1 @ sk_D)),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf('76', plain, ((v2_funct_1 @ sk_D)),
% 0.90/1.15      inference('sup-', [status(thm)], ['65', '66'])).
% 0.90/1.15  thf('77', plain,
% 0.90/1.15      (((k6_partfun1 @ (k1_relat_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 0.90/1.15      inference('demod', [status(thm)], ['69', '74', '75', '76'])).
% 0.90/1.15  thf(t71_relat_1, axiom,
% 0.90/1.15    (![A:$i]:
% 0.90/1.15     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.90/1.15       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.90/1.15  thf('78', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 0.90/1.15      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.90/1.15  thf('79', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.90/1.15      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.90/1.15  thf('80', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 0.90/1.15      inference('demod', [status(thm)], ['78', '79'])).
% 0.90/1.15  thf('81', plain,
% 0.90/1.15      (((k1_relat_1 @ (k6_partfun1 @ sk_B)) = (k1_relat_1 @ sk_D))),
% 0.90/1.15      inference('sup+', [status(thm)], ['77', '80'])).
% 0.90/1.15  thf('82', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 0.90/1.15      inference('demod', [status(thm)], ['78', '79'])).
% 0.90/1.15  thf('83', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.90/1.15      inference('demod', [status(thm)], ['81', '82'])).
% 0.90/1.15  thf('84', plain,
% 0.90/1.15      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf('85', plain,
% 0.90/1.15      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf(redefinition_k1_partfun1, axiom,
% 0.90/1.15    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.90/1.15     ( ( ( v1_funct_1 @ E ) & 
% 0.90/1.15         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.90/1.15         ( v1_funct_1 @ F ) & 
% 0.90/1.15         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.90/1.15       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.90/1.15  thf('86', plain,
% 0.90/1.15      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.90/1.15         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.90/1.15          | ~ (v1_funct_1 @ X24)
% 0.90/1.15          | ~ (v1_funct_1 @ X27)
% 0.90/1.15          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.90/1.15          | ((k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27)
% 0.90/1.15              = (k5_relat_1 @ X24 @ X27)))),
% 0.90/1.15      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.90/1.15  thf('87', plain,
% 0.90/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.15         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.90/1.15            = (k5_relat_1 @ sk_C @ X0))
% 0.90/1.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.90/1.15          | ~ (v1_funct_1 @ X0)
% 0.90/1.15          | ~ (v1_funct_1 @ sk_C))),
% 0.90/1.15      inference('sup-', [status(thm)], ['85', '86'])).
% 0.90/1.15  thf('88', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf('89', plain,
% 0.90/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.15         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.90/1.15            = (k5_relat_1 @ sk_C @ X0))
% 0.90/1.15          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.90/1.15          | ~ (v1_funct_1 @ X0))),
% 0.90/1.15      inference('demod', [status(thm)], ['87', '88'])).
% 0.90/1.15  thf('90', plain,
% 0.90/1.15      ((~ (v1_funct_1 @ sk_D)
% 0.90/1.15        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.90/1.15            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.90/1.15      inference('sup-', [status(thm)], ['84', '89'])).
% 0.90/1.15  thf('91', plain, ((v1_funct_1 @ sk_D)),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf('92', plain,
% 0.90/1.15      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.90/1.15         = (k6_partfun1 @ sk_A))),
% 0.90/1.15      inference('demod', [status(thm)], ['23', '26'])).
% 0.90/1.15  thf('93', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.90/1.15      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.90/1.15  thf(t63_funct_1, axiom,
% 0.90/1.15    (![A:$i]:
% 0.90/1.15     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.90/1.15       ( ![B:$i]:
% 0.90/1.15         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.90/1.15           ( ( ( v2_funct_1 @ A ) & 
% 0.90/1.15               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.90/1.15               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.90/1.15             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.90/1.15  thf('94', plain,
% 0.90/1.15      (![X11 : $i, X12 : $i]:
% 0.90/1.15         (~ (v1_relat_1 @ X11)
% 0.90/1.15          | ~ (v1_funct_1 @ X11)
% 0.90/1.15          | ((X11) = (k2_funct_1 @ X12))
% 0.90/1.15          | ((k5_relat_1 @ X12 @ X11) != (k6_relat_1 @ (k1_relat_1 @ X12)))
% 0.90/1.15          | ((k2_relat_1 @ X12) != (k1_relat_1 @ X11))
% 0.90/1.15          | ~ (v2_funct_1 @ X12)
% 0.90/1.15          | ~ (v1_funct_1 @ X12)
% 0.90/1.15          | ~ (v1_relat_1 @ X12))),
% 0.90/1.15      inference('cnf', [status(esa)], [t63_funct_1])).
% 0.90/1.15  thf('95', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.90/1.15      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.90/1.15  thf('96', plain,
% 0.90/1.15      (![X11 : $i, X12 : $i]:
% 0.90/1.15         (~ (v1_relat_1 @ X11)
% 0.90/1.15          | ~ (v1_funct_1 @ X11)
% 0.90/1.15          | ((X11) = (k2_funct_1 @ X12))
% 0.90/1.15          | ((k5_relat_1 @ X12 @ X11) != (k6_partfun1 @ (k1_relat_1 @ X12)))
% 0.90/1.15          | ((k2_relat_1 @ X12) != (k1_relat_1 @ X11))
% 0.90/1.15          | ~ (v2_funct_1 @ X12)
% 0.90/1.15          | ~ (v1_funct_1 @ X12)
% 0.90/1.15          | ~ (v1_relat_1 @ X12))),
% 0.90/1.15      inference('demod', [status(thm)], ['94', '95'])).
% 0.90/1.15  thf('97', plain,
% 0.90/1.15      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 0.90/1.15        | ~ (v1_relat_1 @ sk_C)
% 0.90/1.15        | ~ (v1_funct_1 @ sk_C)
% 0.90/1.15        | ~ (v2_funct_1 @ sk_C)
% 0.90/1.15        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.90/1.15        | ((sk_D) = (k2_funct_1 @ sk_C))
% 0.90/1.15        | ~ (v1_funct_1 @ sk_D)
% 0.90/1.15        | ~ (v1_relat_1 @ sk_D))),
% 0.90/1.15      inference('sup-', [status(thm)], ['93', '96'])).
% 0.90/1.15  thf('98', plain,
% 0.90/1.15      (![X10 : $i]:
% 0.90/1.15         (~ (v2_funct_1 @ X10)
% 0.90/1.15          | ((k5_relat_1 @ X10 @ (k2_funct_1 @ X10))
% 0.90/1.15              = (k6_partfun1 @ (k1_relat_1 @ X10)))
% 0.90/1.15          | ~ (v1_funct_1 @ X10)
% 0.90/1.15          | ~ (v1_relat_1 @ X10))),
% 0.90/1.15      inference('demod', [status(thm)], ['0', '1'])).
% 0.90/1.15  thf('99', plain,
% 0.90/1.15      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf('100', plain,
% 0.90/1.15      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.90/1.15         (((X44) = (k1_xboole_0))
% 0.90/1.15          | ~ (v1_funct_1 @ X45)
% 0.90/1.15          | ~ (v1_funct_2 @ X45 @ X46 @ X44)
% 0.90/1.15          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X44)))
% 0.90/1.15          | ((k5_relat_1 @ X45 @ (k2_funct_1 @ X45)) = (k6_partfun1 @ X46))
% 0.90/1.15          | ~ (v2_funct_1 @ X45)
% 0.90/1.15          | ((k2_relset_1 @ X46 @ X44 @ X45) != (X44)))),
% 0.90/1.15      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.90/1.15  thf('101', plain,
% 0.90/1.15      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.90/1.15        | ~ (v2_funct_1 @ sk_C)
% 0.90/1.15        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.90/1.15        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.90/1.15        | ~ (v1_funct_1 @ sk_C)
% 0.90/1.15        | ((sk_B) = (k1_xboole_0)))),
% 0.90/1.15      inference('sup-', [status(thm)], ['99', '100'])).
% 0.90/1.15  thf('102', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf('103', plain, ((v2_funct_1 @ sk_C)),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf('104', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf('105', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf('106', plain,
% 0.90/1.15      ((((sk_B) != (sk_B))
% 0.90/1.15        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.90/1.15        | ((sk_B) = (k1_xboole_0)))),
% 0.90/1.15      inference('demod', [status(thm)], ['101', '102', '103', '104', '105'])).
% 0.90/1.15  thf('107', plain,
% 0.90/1.15      ((((sk_B) = (k1_xboole_0))
% 0.90/1.15        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 0.90/1.15      inference('simplify', [status(thm)], ['106'])).
% 0.90/1.15  thf('108', plain, (((sk_B) != (k1_xboole_0))),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf('109', plain,
% 0.90/1.15      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 0.90/1.15      inference('simplify_reflect-', [status(thm)], ['107', '108'])).
% 0.90/1.15  thf('110', plain,
% 0.90/1.15      ((((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.90/1.15        | ~ (v1_relat_1 @ sk_C)
% 0.90/1.15        | ~ (v1_funct_1 @ sk_C)
% 0.90/1.15        | ~ (v2_funct_1 @ sk_C))),
% 0.90/1.15      inference('sup+', [status(thm)], ['98', '109'])).
% 0.90/1.15  thf('111', plain,
% 0.90/1.15      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf('112', plain,
% 0.90/1.15      (![X0 : $i, X1 : $i]:
% 0.90/1.15         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.90/1.15          | (v1_relat_1 @ X0)
% 0.90/1.15          | ~ (v1_relat_1 @ X1))),
% 0.90/1.15      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.90/1.15  thf('113', plain,
% 0.90/1.15      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.90/1.15      inference('sup-', [status(thm)], ['111', '112'])).
% 0.90/1.15  thf('114', plain,
% 0.90/1.15      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.90/1.15      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.90/1.15  thf('115', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.15      inference('demod', [status(thm)], ['113', '114'])).
% 0.90/1.15  thf('116', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf('117', plain, ((v2_funct_1 @ sk_C)),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf('118', plain,
% 0.90/1.15      (((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 0.90/1.15      inference('demod', [status(thm)], ['110', '115', '116', '117'])).
% 0.90/1.15  thf('119', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 0.90/1.15      inference('demod', [status(thm)], ['78', '79'])).
% 0.90/1.15  thf('120', plain,
% 0.90/1.15      (((k1_relat_1 @ (k6_partfun1 @ sk_A)) = (k1_relat_1 @ sk_C))),
% 0.90/1.15      inference('sup+', [status(thm)], ['118', '119'])).
% 0.90/1.15  thf('121', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 0.90/1.15      inference('demod', [status(thm)], ['78', '79'])).
% 0.90/1.15  thf('122', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.90/1.15      inference('demod', [status(thm)], ['120', '121'])).
% 0.90/1.15  thf('123', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.15      inference('demod', [status(thm)], ['113', '114'])).
% 0.90/1.15  thf('124', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf('125', plain, ((v2_funct_1 @ sk_C)),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf('126', plain,
% 0.90/1.15      (![X10 : $i]:
% 0.90/1.15         (~ (v2_funct_1 @ X10)
% 0.90/1.15          | ((k5_relat_1 @ (k2_funct_1 @ X10) @ X10)
% 0.90/1.15              = (k6_relat_1 @ (k2_relat_1 @ X10)))
% 0.90/1.15          | ~ (v1_funct_1 @ X10)
% 0.90/1.15          | ~ (v1_relat_1 @ X10))),
% 0.90/1.15      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.90/1.15  thf('127', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.90/1.15      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.90/1.15  thf('128', plain,
% 0.90/1.15      (![X10 : $i]:
% 0.90/1.15         (~ (v2_funct_1 @ X10)
% 0.90/1.15          | ((k5_relat_1 @ (k2_funct_1 @ X10) @ X10)
% 0.90/1.15              = (k6_partfun1 @ (k2_relat_1 @ X10)))
% 0.90/1.15          | ~ (v1_funct_1 @ X10)
% 0.90/1.15          | ~ (v1_relat_1 @ X10))),
% 0.90/1.15      inference('demod', [status(thm)], ['126', '127'])).
% 0.90/1.15  thf('129', plain,
% 0.90/1.15      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf('130', plain,
% 0.90/1.15      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.90/1.15         (((X44) = (k1_xboole_0))
% 0.90/1.15          | ~ (v1_funct_1 @ X45)
% 0.90/1.15          | ~ (v1_funct_2 @ X45 @ X46 @ X44)
% 0.90/1.15          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X44)))
% 0.90/1.15          | ((k5_relat_1 @ (k2_funct_1 @ X45) @ X45) = (k6_partfun1 @ X44))
% 0.90/1.15          | ~ (v2_funct_1 @ X45)
% 0.90/1.15          | ((k2_relset_1 @ X46 @ X44 @ X45) != (X44)))),
% 0.90/1.15      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.90/1.15  thf('131', plain,
% 0.90/1.15      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.90/1.15        | ~ (v2_funct_1 @ sk_C)
% 0.90/1.15        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 0.90/1.15        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.90/1.15        | ~ (v1_funct_1 @ sk_C)
% 0.90/1.15        | ((sk_B) = (k1_xboole_0)))),
% 0.90/1.15      inference('sup-', [status(thm)], ['129', '130'])).
% 0.90/1.15  thf('132', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf('133', plain, ((v2_funct_1 @ sk_C)),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf('134', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf('135', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf('136', plain,
% 0.90/1.15      ((((sk_B) != (sk_B))
% 0.90/1.15        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 0.90/1.15        | ((sk_B) = (k1_xboole_0)))),
% 0.90/1.15      inference('demod', [status(thm)], ['131', '132', '133', '134', '135'])).
% 0.90/1.15  thf('137', plain,
% 0.90/1.15      ((((sk_B) = (k1_xboole_0))
% 0.90/1.15        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 0.90/1.15      inference('simplify', [status(thm)], ['136'])).
% 0.90/1.15  thf('138', plain, (((sk_B) != (k1_xboole_0))),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf('139', plain,
% 0.90/1.15      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 0.90/1.15      inference('simplify_reflect-', [status(thm)], ['137', '138'])).
% 0.90/1.15  thf('140', plain,
% 0.90/1.15      ((((k6_partfun1 @ (k2_relat_1 @ sk_C)) = (k6_partfun1 @ sk_B))
% 0.90/1.15        | ~ (v1_relat_1 @ sk_C)
% 0.90/1.15        | ~ (v1_funct_1 @ sk_C)
% 0.90/1.15        | ~ (v2_funct_1 @ sk_C))),
% 0.90/1.15      inference('sup+', [status(thm)], ['128', '139'])).
% 0.90/1.15  thf('141', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.15      inference('demod', [status(thm)], ['113', '114'])).
% 0.90/1.15  thf('142', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf('143', plain, ((v2_funct_1 @ sk_C)),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf('144', plain,
% 0.90/1.15      (((k6_partfun1 @ (k2_relat_1 @ sk_C)) = (k6_partfun1 @ sk_B))),
% 0.90/1.15      inference('demod', [status(thm)], ['140', '141', '142', '143'])).
% 0.90/1.15  thf('145', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 0.90/1.15      inference('demod', [status(thm)], ['78', '79'])).
% 0.90/1.15  thf('146', plain,
% 0.90/1.15      (((k1_relat_1 @ (k6_partfun1 @ sk_B)) = (k2_relat_1 @ sk_C))),
% 0.90/1.15      inference('sup+', [status(thm)], ['144', '145'])).
% 0.90/1.15  thf('147', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 0.90/1.15      inference('demod', [status(thm)], ['78', '79'])).
% 0.90/1.15  thf('148', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 0.90/1.15      inference('demod', [status(thm)], ['146', '147'])).
% 0.90/1.15  thf('149', plain, ((v1_funct_1 @ sk_D)),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf('150', plain, ((v1_relat_1 @ sk_D)),
% 0.90/1.15      inference('demod', [status(thm)], ['72', '73'])).
% 0.90/1.15  thf('151', plain,
% 0.90/1.15      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 0.90/1.15        | ((sk_B) != (k1_relat_1 @ sk_D))
% 0.90/1.15        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 0.90/1.15      inference('demod', [status(thm)],
% 0.90/1.15                ['97', '122', '123', '124', '125', '148', '149', '150'])).
% 0.90/1.15  thf('152', plain,
% 0.90/1.15      ((((sk_D) = (k2_funct_1 @ sk_C)) | ((sk_B) != (k1_relat_1 @ sk_D)))),
% 0.90/1.15      inference('simplify', [status(thm)], ['151'])).
% 0.90/1.15  thf('153', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.90/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.15  thf('154', plain, (((sk_B) != (k1_relat_1 @ sk_D))),
% 0.90/1.15      inference('simplify_reflect-', [status(thm)], ['152', '153'])).
% 0.90/1.15  thf('155', plain, ($false),
% 0.90/1.15      inference('simplify_reflect-', [status(thm)], ['83', '154'])).
% 0.90/1.15  
% 0.90/1.15  % SZS output end Refutation
% 0.90/1.15  
% 0.90/1.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

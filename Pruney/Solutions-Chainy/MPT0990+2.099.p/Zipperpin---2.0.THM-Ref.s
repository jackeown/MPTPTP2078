%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JXJBzjTaKt

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:11 EST 2020

% Result     : Theorem 0.79s
% Output     : Refutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :  195 ( 479 expanded)
%              Number of leaves         :   42 ( 161 expanded)
%              Depth                    :   21
%              Number of atoms          : 1946 (11579 expanded)
%              Number of equality atoms :  145 ( 826 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k5_relat_1 @ X6 @ ( k2_funct_1 @ X6 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X29: $i] :
      ( ( k6_partfun1 @ X29 )
      = ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k5_relat_1 @ X6 @ ( k2_funct_1 @ X6 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
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
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( X43 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ X45 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X43 ) ) )
      | ( ( k5_relat_1 @ X44 @ ( k2_funct_1 @ X44 ) )
        = ( k6_partfun1 @ X45 ) )
      | ~ ( v2_funct_1 @ X44 )
      | ( ( k2_relset_1 @ X45 @ X43 @ X44 )
       != X43 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( X12 = X15 )
      | ~ ( r2_relset_1 @ X13 @ X14 @ X12 @ X15 ) ) ),
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
    ! [X16: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X16 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('25',plain,(
    ! [X29: $i] :
      ( ( k6_partfun1 @ X29 )
      = ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('26',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X16 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X16 ) ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_2 @ X30 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( r2_relset_1 @ X31 @ X31 @ ( k1_partfun1 @ X31 @ X32 @ X32 @ X31 @ X30 @ X33 ) @ ( k6_partfun1 @ X31 ) )
      | ( ( k2_relset_1 @ X32 @ X31 @ X33 )
        = X31 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X32 @ X31 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
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
    ! [X16: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X16 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X16 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('36',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( r2_relset_1 @ X13 @ X14 @ X12 @ X15 )
      | ( X12 != X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('37',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_relset_1 @ X13 @ X14 @ X15 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
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
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( zip_tseitin_0 @ X38 @ X41 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X42 @ X39 @ X39 @ X40 @ X41 @ X38 ) )
      | ( zip_tseitin_1 @ X40 @ X39 )
      | ( ( k2_relset_1 @ X42 @ X39 @ X41 )
       != X39 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X39 ) ) )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X39 )
      | ~ ( v1_funct_1 @ X41 ) ) ),
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
    ! [X3: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('54',plain,(
    ! [X29: $i] :
      ( ( k6_partfun1 @ X29 )
      = ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('55',plain,(
    ! [X3: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X3 ) ) ),
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
    ! [X36: $i,X37: $i] :
      ( ( X36 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X36 @ X37 ) ) ),
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
    ! [X34: $i,X35: $i] :
      ( ( v2_funct_1 @ X35 )
      | ~ ( zip_tseitin_0 @ X35 @ X34 ) ) ),
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

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('71',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('72',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['65','66'])).

thf('75',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['69','72','73','74'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('77',plain,(
    ! [X29: $i] :
      ( ( k6_partfun1 @ X29 )
      = ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['75','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
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
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 )
        = ( k5_relat_1 @ X23 @ X26 ) ) ) ),
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
    inference(demod,[status(thm)],['23','26'])).

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

thf('93',plain,(
    ! [X29: $i] :
      ( ( k6_partfun1 @ X29 )
      = ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('94',plain,(
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
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k5_relat_1 @ X6 @ ( k2_funct_1 @ X6 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('97',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( X43 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ X45 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X43 ) ) )
      | ( ( k5_relat_1 @ X44 @ ( k2_funct_1 @ X44 ) )
        = ( k6_partfun1 @ X45 ) )
      | ~ ( v2_funct_1 @ X44 )
      | ( ( k2_relset_1 @ X45 @ X43 @ X44 )
       != X43 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('111',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['108','111','112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('116',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('118',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['109','110'])).

thf('120',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X6 ) @ X6 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('123',plain,(
    ! [X29: $i] :
      ( ( k6_partfun1 @ X29 )
      = ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('124',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X6 ) @ X6 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( X43 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ X45 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X43 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X44 ) @ X44 )
        = ( k6_partfun1 @ X43 ) )
      | ~ ( v2_funct_1 @ X44 )
      | ( ( k2_relset_1 @ X45 @ X43 @ X44 )
       != X43 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('127',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['127','128','129','130','131'])).

thf('133',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['133','134'])).

thf('136',plain,
    ( ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['124','135'])).

thf('137',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['109','110'])).

thf('138',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['136','137','138','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('142',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('144',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['70','71'])).

thf('147',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['95','118','119','120','121','144','145','146'])).

thf('148',plain,
    ( ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    sk_B
 != ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['148','149'])).

thf('151',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['81','150'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JXJBzjTaKt
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:19:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.79/1.01  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.79/1.01  % Solved by: fo/fo7.sh
% 0.79/1.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.79/1.01  % done 834 iterations in 0.575s
% 0.79/1.01  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.79/1.01  % SZS output start Refutation
% 0.79/1.01  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.79/1.01  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.79/1.01  thf(sk_C_type, type, sk_C: $i).
% 0.79/1.01  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.79/1.01  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.79/1.01  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.79/1.01  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.79/1.01  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.79/1.01  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.79/1.01  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.79/1.01  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.79/1.01  thf(sk_A_type, type, sk_A: $i).
% 0.79/1.01  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.79/1.01  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.79/1.01  thf(sk_D_type, type, sk_D: $i).
% 0.79/1.01  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.79/1.01  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.79/1.01  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.79/1.01  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.79/1.01  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.79/1.01  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.79/1.01  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.79/1.01  thf(sk_B_type, type, sk_B: $i).
% 0.79/1.01  thf(t61_funct_1, axiom,
% 0.79/1.01    (![A:$i]:
% 0.79/1.01     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.79/1.01       ( ( v2_funct_1 @ A ) =>
% 0.79/1.01         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.79/1.01             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.79/1.01           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.79/1.01             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.79/1.01  thf('0', plain,
% 0.79/1.01      (![X6 : $i]:
% 0.79/1.01         (~ (v2_funct_1 @ X6)
% 0.79/1.01          | ((k5_relat_1 @ X6 @ (k2_funct_1 @ X6))
% 0.79/1.01              = (k6_relat_1 @ (k1_relat_1 @ X6)))
% 0.79/1.01          | ~ (v1_funct_1 @ X6)
% 0.79/1.01          | ~ (v1_relat_1 @ X6))),
% 0.79/1.01      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.79/1.01  thf(redefinition_k6_partfun1, axiom,
% 0.79/1.01    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.79/1.01  thf('1', plain, (![X29 : $i]: ((k6_partfun1 @ X29) = (k6_relat_1 @ X29))),
% 0.79/1.01      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.79/1.01  thf('2', plain,
% 0.79/1.01      (![X6 : $i]:
% 0.79/1.01         (~ (v2_funct_1 @ X6)
% 0.79/1.01          | ((k5_relat_1 @ X6 @ (k2_funct_1 @ X6))
% 0.79/1.01              = (k6_partfun1 @ (k1_relat_1 @ X6)))
% 0.79/1.01          | ~ (v1_funct_1 @ X6)
% 0.79/1.01          | ~ (v1_relat_1 @ X6))),
% 0.79/1.01      inference('demod', [status(thm)], ['0', '1'])).
% 0.79/1.01  thf(t36_funct_2, conjecture,
% 0.79/1.01    (![A:$i,B:$i,C:$i]:
% 0.79/1.01     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.79/1.01         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.79/1.01       ( ![D:$i]:
% 0.79/1.01         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.79/1.01             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.79/1.01           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.79/1.01               ( r2_relset_1 @
% 0.79/1.01                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.79/1.01                 ( k6_partfun1 @ A ) ) & 
% 0.79/1.01               ( v2_funct_1 @ C ) ) =>
% 0.79/1.01             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.79/1.01               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.79/1.01  thf(zf_stmt_0, negated_conjecture,
% 0.79/1.01    (~( ![A:$i,B:$i,C:$i]:
% 0.79/1.01        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.79/1.01            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.79/1.01          ( ![D:$i]:
% 0.79/1.01            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.79/1.01                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.79/1.01              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.79/1.01                  ( r2_relset_1 @
% 0.79/1.01                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.79/1.01                    ( k6_partfun1 @ A ) ) & 
% 0.79/1.01                  ( v2_funct_1 @ C ) ) =>
% 0.79/1.01                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.79/1.01                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.79/1.01    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.79/1.01  thf('3', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf(t35_funct_2, axiom,
% 0.79/1.01    (![A:$i,B:$i,C:$i]:
% 0.79/1.01     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.79/1.01         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.79/1.01       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.79/1.01         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.79/1.01           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.79/1.01             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.79/1.01  thf('4', plain,
% 0.79/1.01      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.79/1.01         (((X43) = (k1_xboole_0))
% 0.79/1.01          | ~ (v1_funct_1 @ X44)
% 0.79/1.01          | ~ (v1_funct_2 @ X44 @ X45 @ X43)
% 0.79/1.01          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X43)))
% 0.79/1.01          | ((k5_relat_1 @ X44 @ (k2_funct_1 @ X44)) = (k6_partfun1 @ X45))
% 0.79/1.01          | ~ (v2_funct_1 @ X44)
% 0.79/1.01          | ((k2_relset_1 @ X45 @ X43 @ X44) != (X43)))),
% 0.79/1.01      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.79/1.01  thf('5', plain,
% 0.79/1.01      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 0.79/1.01        | ~ (v2_funct_1 @ sk_D)
% 0.79/1.01        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.79/1.01        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.79/1.01        | ~ (v1_funct_1 @ sk_D)
% 0.79/1.01        | ((sk_A) = (k1_xboole_0)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['3', '4'])).
% 0.79/1.01  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('8', plain,
% 0.79/1.01      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 0.79/1.01        | ~ (v2_funct_1 @ sk_D)
% 0.79/1.01        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.79/1.01        | ((sk_A) = (k1_xboole_0)))),
% 0.79/1.01      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.79/1.01  thf('9', plain, (((sk_A) != (k1_xboole_0))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('10', plain,
% 0.79/1.01      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 0.79/1.01        | ~ (v2_funct_1 @ sk_D)
% 0.79/1.01        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 0.79/1.01      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.79/1.01  thf('11', plain,
% 0.79/1.01      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.79/1.01        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.79/1.01        (k6_partfun1 @ sk_A))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('12', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('13', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf(dt_k1_partfun1, axiom,
% 0.79/1.01    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.79/1.01     ( ( ( v1_funct_1 @ E ) & 
% 0.79/1.01         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.79/1.01         ( v1_funct_1 @ F ) & 
% 0.79/1.01         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.79/1.01       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.79/1.01         ( m1_subset_1 @
% 0.79/1.01           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.79/1.01           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.79/1.01  thf('14', plain,
% 0.79/1.01      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.79/1.01         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.79/1.01          | ~ (v1_funct_1 @ X17)
% 0.79/1.01          | ~ (v1_funct_1 @ X20)
% 0.79/1.01          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.79/1.01          | (m1_subset_1 @ (k1_partfun1 @ X18 @ X19 @ X21 @ X22 @ X17 @ X20) @ 
% 0.79/1.01             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X22))))),
% 0.79/1.01      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.79/1.01  thf('15', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/1.01         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.79/1.01           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.79/1.01          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.79/1.01          | ~ (v1_funct_1 @ X1)
% 0.79/1.01          | ~ (v1_funct_1 @ sk_C))),
% 0.79/1.01      inference('sup-', [status(thm)], ['13', '14'])).
% 0.79/1.01  thf('16', plain, ((v1_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('17', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/1.01         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.79/1.01           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.79/1.01          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.79/1.01          | ~ (v1_funct_1 @ X1))),
% 0.79/1.01      inference('demod', [status(thm)], ['15', '16'])).
% 0.79/1.01  thf('18', plain,
% 0.79/1.01      ((~ (v1_funct_1 @ sk_D)
% 0.79/1.01        | (m1_subset_1 @ 
% 0.79/1.01           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.79/1.01           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.79/1.01      inference('sup-', [status(thm)], ['12', '17'])).
% 0.79/1.01  thf('19', plain, ((v1_funct_1 @ sk_D)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('20', plain,
% 0.79/1.01      ((m1_subset_1 @ 
% 0.79/1.01        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.79/1.01        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.79/1.01      inference('demod', [status(thm)], ['18', '19'])).
% 0.79/1.01  thf(redefinition_r2_relset_1, axiom,
% 0.79/1.01    (![A:$i,B:$i,C:$i,D:$i]:
% 0.79/1.01     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.79/1.01         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.79/1.01       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.79/1.01  thf('21', plain,
% 0.79/1.01      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.79/1.01         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.79/1.01          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.79/1.01          | ((X12) = (X15))
% 0.79/1.01          | ~ (r2_relset_1 @ X13 @ X14 @ X12 @ X15))),
% 0.79/1.01      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.79/1.01  thf('22', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.79/1.01             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.79/1.01          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.79/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.79/1.01      inference('sup-', [status(thm)], ['20', '21'])).
% 0.79/1.01  thf('23', plain,
% 0.79/1.01      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.79/1.01           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.79/1.01        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.79/1.01            = (k6_partfun1 @ sk_A)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['11', '22'])).
% 0.79/1.01  thf(t29_relset_1, axiom,
% 0.79/1.01    (![A:$i]:
% 0.79/1.01     ( m1_subset_1 @
% 0.79/1.01       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.79/1.01  thf('24', plain,
% 0.79/1.01      (![X16 : $i]:
% 0.79/1.01         (m1_subset_1 @ (k6_relat_1 @ X16) @ 
% 0.79/1.01          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X16)))),
% 0.79/1.01      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.79/1.01  thf('25', plain, (![X29 : $i]: ((k6_partfun1 @ X29) = (k6_relat_1 @ X29))),
% 0.79/1.01      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.79/1.01  thf('26', plain,
% 0.79/1.01      (![X16 : $i]:
% 0.79/1.01         (m1_subset_1 @ (k6_partfun1 @ X16) @ 
% 0.79/1.01          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X16)))),
% 0.79/1.01      inference('demod', [status(thm)], ['24', '25'])).
% 0.79/1.01  thf('27', plain,
% 0.79/1.01      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.79/1.01         = (k6_partfun1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['23', '26'])).
% 0.79/1.01  thf('28', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf(t24_funct_2, axiom,
% 0.79/1.01    (![A:$i,B:$i,C:$i]:
% 0.79/1.01     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.79/1.01         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.79/1.01       ( ![D:$i]:
% 0.79/1.01         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.79/1.01             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.79/1.01           ( ( r2_relset_1 @
% 0.79/1.01               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.79/1.01               ( k6_partfun1 @ B ) ) =>
% 0.79/1.01             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.79/1.01  thf('29', plain,
% 0.79/1.01      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.79/1.01         (~ (v1_funct_1 @ X30)
% 0.79/1.01          | ~ (v1_funct_2 @ X30 @ X31 @ X32)
% 0.79/1.01          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.79/1.01          | ~ (r2_relset_1 @ X31 @ X31 @ 
% 0.79/1.01               (k1_partfun1 @ X31 @ X32 @ X32 @ X31 @ X30 @ X33) @ 
% 0.79/1.01               (k6_partfun1 @ X31))
% 0.79/1.01          | ((k2_relset_1 @ X32 @ X31 @ X33) = (X31))
% 0.79/1.01          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 0.79/1.01          | ~ (v1_funct_2 @ X33 @ X32 @ X31)
% 0.79/1.01          | ~ (v1_funct_1 @ X33))),
% 0.79/1.01      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.79/1.01  thf('30', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.79/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.79/1.01          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.79/1.01          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.79/1.01               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.79/1.01               (k6_partfun1 @ sk_A))
% 0.79/1.01          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.79/1.01          | ~ (v1_funct_1 @ sk_C))),
% 0.79/1.01      inference('sup-', [status(thm)], ['28', '29'])).
% 0.79/1.01  thf('31', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('33', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.79/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.79/1.01          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.79/1.01          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.79/1.01               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.79/1.01               (k6_partfun1 @ sk_A)))),
% 0.79/1.01      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.79/1.01  thf('34', plain,
% 0.79/1.01      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 0.79/1.01           (k6_partfun1 @ sk_A))
% 0.79/1.01        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.79/1.01        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.79/1.01        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.79/1.01        | ~ (v1_funct_1 @ sk_D))),
% 0.79/1.01      inference('sup-', [status(thm)], ['27', '33'])).
% 0.79/1.01  thf('35', plain,
% 0.79/1.01      (![X16 : $i]:
% 0.79/1.01         (m1_subset_1 @ (k6_partfun1 @ X16) @ 
% 0.79/1.01          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X16)))),
% 0.79/1.01      inference('demod', [status(thm)], ['24', '25'])).
% 0.79/1.01  thf('36', plain,
% 0.79/1.01      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.79/1.01         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.79/1.01          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.79/1.01          | (r2_relset_1 @ X13 @ X14 @ X12 @ X15)
% 0.79/1.01          | ((X12) != (X15)))),
% 0.79/1.01      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.79/1.01  thf('37', plain,
% 0.79/1.01      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.79/1.01         ((r2_relset_1 @ X13 @ X14 @ X15 @ X15)
% 0.79/1.01          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.79/1.01      inference('simplify', [status(thm)], ['36'])).
% 0.79/1.01  thf('38', plain,
% 0.79/1.01      (![X0 : $i]:
% 0.79/1.01         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 0.79/1.01      inference('sup-', [status(thm)], ['35', '37'])).
% 0.79/1.01  thf('39', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('40', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('41', plain, ((v1_funct_1 @ sk_D)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('42', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['34', '38', '39', '40', '41'])).
% 0.79/1.01  thf('43', plain,
% 0.79/1.01      ((((sk_A) != (sk_A))
% 0.79/1.01        | ~ (v2_funct_1 @ sk_D)
% 0.79/1.01        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 0.79/1.01      inference('demod', [status(thm)], ['10', '42'])).
% 0.79/1.01  thf('44', plain,
% 0.79/1.01      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.79/1.01        | ~ (v2_funct_1 @ sk_D))),
% 0.79/1.01      inference('simplify', [status(thm)], ['43'])).
% 0.79/1.01  thf('45', plain,
% 0.79/1.01      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.79/1.01         = (k6_partfun1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['23', '26'])).
% 0.79/1.01  thf('46', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf(t30_funct_2, axiom,
% 0.79/1.01    (![A:$i,B:$i,C:$i,D:$i]:
% 0.79/1.01     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.79/1.01         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 0.79/1.01       ( ![E:$i]:
% 0.79/1.01         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 0.79/1.01             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 0.79/1.01           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 0.79/1.01               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 0.79/1.01             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 0.79/1.01               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 0.79/1.01  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 0.79/1.01  thf(zf_stmt_2, axiom,
% 0.79/1.01    (![C:$i,B:$i]:
% 0.79/1.01     ( ( zip_tseitin_1 @ C @ B ) =>
% 0.79/1.01       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 0.79/1.01  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.79/1.01  thf(zf_stmt_4, axiom,
% 0.79/1.01    (![E:$i,D:$i]:
% 0.79/1.01     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 0.79/1.01  thf(zf_stmt_5, axiom,
% 0.79/1.01    (![A:$i,B:$i,C:$i,D:$i]:
% 0.79/1.01     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.79/1.01         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.79/1.01       ( ![E:$i]:
% 0.79/1.01         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.79/1.01             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.79/1.01           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 0.79/1.01               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 0.79/1.01             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 0.79/1.01  thf('47', plain,
% 0.79/1.01      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.79/1.01         (~ (v1_funct_1 @ X38)
% 0.79/1.01          | ~ (v1_funct_2 @ X38 @ X39 @ X40)
% 0.79/1.01          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.79/1.01          | (zip_tseitin_0 @ X38 @ X41)
% 0.79/1.01          | ~ (v2_funct_1 @ (k1_partfun1 @ X42 @ X39 @ X39 @ X40 @ X41 @ X38))
% 0.79/1.01          | (zip_tseitin_1 @ X40 @ X39)
% 0.79/1.01          | ((k2_relset_1 @ X42 @ X39 @ X41) != (X39))
% 0.79/1.01          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X39)))
% 0.79/1.01          | ~ (v1_funct_2 @ X41 @ X42 @ X39)
% 0.79/1.01          | ~ (v1_funct_1 @ X41))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.79/1.01  thf('48', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i]:
% 0.79/1.01         (~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.79/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.79/1.01          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 0.79/1.01          | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.79/1.01          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.79/1.01          | (zip_tseitin_0 @ sk_D @ X0)
% 0.79/1.01          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.79/1.01          | ~ (v1_funct_1 @ sk_D))),
% 0.79/1.01      inference('sup-', [status(thm)], ['46', '47'])).
% 0.79/1.01  thf('49', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('50', plain, ((v1_funct_1 @ sk_D)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('51', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i]:
% 0.79/1.01         (~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.79/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.79/1.01          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 0.79/1.01          | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.79/1.01          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.79/1.01          | (zip_tseitin_0 @ sk_D @ X0))),
% 0.79/1.01      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.79/1.01  thf('52', plain,
% 0.79/1.01      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.79/1.01        | (zip_tseitin_0 @ sk_D @ sk_C)
% 0.79/1.01        | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.79/1.01        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.79/1.01        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.79/1.01        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.79/1.01        | ~ (v1_funct_1 @ sk_C))),
% 0.79/1.01      inference('sup-', [status(thm)], ['45', '51'])).
% 0.79/1.01  thf(fc4_funct_1, axiom,
% 0.79/1.01    (![A:$i]:
% 0.79/1.01     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.79/1.01       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.79/1.01  thf('53', plain, (![X3 : $i]: (v2_funct_1 @ (k6_relat_1 @ X3))),
% 0.79/1.01      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.79/1.01  thf('54', plain, (![X29 : $i]: ((k6_partfun1 @ X29) = (k6_relat_1 @ X29))),
% 0.79/1.01      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.79/1.01  thf('55', plain, (![X3 : $i]: (v2_funct_1 @ (k6_partfun1 @ X3))),
% 0.79/1.01      inference('demod', [status(thm)], ['53', '54'])).
% 0.79/1.01  thf('56', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('57', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('58', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('59', plain, ((v1_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('60', plain,
% 0.79/1.01      (((zip_tseitin_0 @ sk_D @ sk_C)
% 0.79/1.01        | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.79/1.01        | ((sk_B) != (sk_B)))),
% 0.79/1.01      inference('demod', [status(thm)], ['52', '55', '56', '57', '58', '59'])).
% 0.79/1.01  thf('61', plain,
% 0.79/1.01      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 0.79/1.01      inference('simplify', [status(thm)], ['60'])).
% 0.79/1.01  thf('62', plain,
% 0.79/1.01      (![X36 : $i, X37 : $i]:
% 0.79/1.01         (((X36) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X36 @ X37))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.79/1.01  thf('63', plain,
% 0.79/1.01      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['61', '62'])).
% 0.79/1.01  thf('64', plain, (((sk_A) != (k1_xboole_0))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('65', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 0.79/1.01      inference('simplify_reflect-', [status(thm)], ['63', '64'])).
% 0.79/1.01  thf('66', plain,
% 0.79/1.01      (![X34 : $i, X35 : $i]:
% 0.79/1.01         ((v2_funct_1 @ X35) | ~ (zip_tseitin_0 @ X35 @ X34))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.79/1.01  thf('67', plain, ((v2_funct_1 @ sk_D)),
% 0.79/1.01      inference('sup-', [status(thm)], ['65', '66'])).
% 0.79/1.01  thf('68', plain,
% 0.79/1.01      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 0.79/1.01      inference('demod', [status(thm)], ['44', '67'])).
% 0.79/1.01  thf('69', plain,
% 0.79/1.01      ((((k6_partfun1 @ (k1_relat_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.79/1.01        | ~ (v1_relat_1 @ sk_D)
% 0.79/1.01        | ~ (v1_funct_1 @ sk_D)
% 0.79/1.01        | ~ (v2_funct_1 @ sk_D))),
% 0.79/1.01      inference('sup+', [status(thm)], ['2', '68'])).
% 0.79/1.01  thf('70', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf(cc1_relset_1, axiom,
% 0.79/1.01    (![A:$i,B:$i,C:$i]:
% 0.79/1.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.79/1.01       ( v1_relat_1 @ C ) ))).
% 0.79/1.01  thf('71', plain,
% 0.79/1.01      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.79/1.01         ((v1_relat_1 @ X9)
% 0.79/1.01          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.79/1.01      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.79/1.01  thf('72', plain, ((v1_relat_1 @ sk_D)),
% 0.79/1.01      inference('sup-', [status(thm)], ['70', '71'])).
% 0.79/1.01  thf('73', plain, ((v1_funct_1 @ sk_D)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('74', plain, ((v2_funct_1 @ sk_D)),
% 0.79/1.01      inference('sup-', [status(thm)], ['65', '66'])).
% 0.79/1.01  thf('75', plain,
% 0.79/1.01      (((k6_partfun1 @ (k1_relat_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 0.79/1.01      inference('demod', [status(thm)], ['69', '72', '73', '74'])).
% 0.79/1.01  thf(t71_relat_1, axiom,
% 0.79/1.01    (![A:$i]:
% 0.79/1.01     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.79/1.01       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.79/1.01  thf('76', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 0.79/1.01      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.79/1.01  thf('77', plain, (![X29 : $i]: ((k6_partfun1 @ X29) = (k6_relat_1 @ X29))),
% 0.79/1.01      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.79/1.01  thf('78', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 0.79/1.01      inference('demod', [status(thm)], ['76', '77'])).
% 0.79/1.01  thf('79', plain,
% 0.79/1.01      (((k1_relat_1 @ (k6_partfun1 @ sk_B)) = (k1_relat_1 @ sk_D))),
% 0.79/1.01      inference('sup+', [status(thm)], ['75', '78'])).
% 0.79/1.01  thf('80', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 0.79/1.01      inference('demod', [status(thm)], ['76', '77'])).
% 0.79/1.01  thf('81', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.79/1.01      inference('demod', [status(thm)], ['79', '80'])).
% 0.79/1.01  thf('82', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('83', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf(redefinition_k1_partfun1, axiom,
% 0.79/1.01    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.79/1.01     ( ( ( v1_funct_1 @ E ) & 
% 0.79/1.01         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.79/1.01         ( v1_funct_1 @ F ) & 
% 0.79/1.01         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.79/1.01       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.79/1.01  thf('84', plain,
% 0.79/1.01      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.79/1.01         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.79/1.01          | ~ (v1_funct_1 @ X23)
% 0.79/1.01          | ~ (v1_funct_1 @ X26)
% 0.79/1.01          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.79/1.01          | ((k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26)
% 0.79/1.01              = (k5_relat_1 @ X23 @ X26)))),
% 0.79/1.01      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.79/1.01  thf('85', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/1.01         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.79/1.01            = (k5_relat_1 @ sk_C @ X0))
% 0.79/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.79/1.01          | ~ (v1_funct_1 @ X0)
% 0.79/1.01          | ~ (v1_funct_1 @ sk_C))),
% 0.79/1.01      inference('sup-', [status(thm)], ['83', '84'])).
% 0.79/1.01  thf('86', plain, ((v1_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('87', plain,
% 0.79/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/1.01         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.79/1.01            = (k5_relat_1 @ sk_C @ X0))
% 0.79/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.79/1.01          | ~ (v1_funct_1 @ X0))),
% 0.79/1.01      inference('demod', [status(thm)], ['85', '86'])).
% 0.79/1.01  thf('88', plain,
% 0.79/1.01      ((~ (v1_funct_1 @ sk_D)
% 0.79/1.01        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.79/1.01            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['82', '87'])).
% 0.79/1.01  thf('89', plain, ((v1_funct_1 @ sk_D)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('90', plain,
% 0.79/1.01      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.79/1.01         = (k6_partfun1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['23', '26'])).
% 0.79/1.01  thf('91', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.79/1.01      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.79/1.01  thf(t63_funct_1, axiom,
% 0.79/1.01    (![A:$i]:
% 0.79/1.01     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.79/1.01       ( ![B:$i]:
% 0.79/1.01         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.79/1.01           ( ( ( v2_funct_1 @ A ) & 
% 0.79/1.01               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.79/1.01               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.79/1.01             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.79/1.01  thf('92', plain,
% 0.79/1.01      (![X7 : $i, X8 : $i]:
% 0.79/1.01         (~ (v1_relat_1 @ X7)
% 0.79/1.01          | ~ (v1_funct_1 @ X7)
% 0.79/1.01          | ((X7) = (k2_funct_1 @ X8))
% 0.79/1.01          | ((k5_relat_1 @ X8 @ X7) != (k6_relat_1 @ (k1_relat_1 @ X8)))
% 0.79/1.01          | ((k2_relat_1 @ X8) != (k1_relat_1 @ X7))
% 0.79/1.01          | ~ (v2_funct_1 @ X8)
% 0.79/1.01          | ~ (v1_funct_1 @ X8)
% 0.79/1.01          | ~ (v1_relat_1 @ X8))),
% 0.79/1.01      inference('cnf', [status(esa)], [t63_funct_1])).
% 0.79/1.01  thf('93', plain, (![X29 : $i]: ((k6_partfun1 @ X29) = (k6_relat_1 @ X29))),
% 0.79/1.01      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.79/1.01  thf('94', plain,
% 0.79/1.01      (![X7 : $i, X8 : $i]:
% 0.79/1.01         (~ (v1_relat_1 @ X7)
% 0.79/1.01          | ~ (v1_funct_1 @ X7)
% 0.79/1.01          | ((X7) = (k2_funct_1 @ X8))
% 0.79/1.01          | ((k5_relat_1 @ X8 @ X7) != (k6_partfun1 @ (k1_relat_1 @ X8)))
% 0.79/1.01          | ((k2_relat_1 @ X8) != (k1_relat_1 @ X7))
% 0.79/1.01          | ~ (v2_funct_1 @ X8)
% 0.79/1.01          | ~ (v1_funct_1 @ X8)
% 0.79/1.01          | ~ (v1_relat_1 @ X8))),
% 0.79/1.01      inference('demod', [status(thm)], ['92', '93'])).
% 0.79/1.01  thf('95', plain,
% 0.79/1.01      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 0.79/1.01        | ~ (v1_relat_1 @ sk_C)
% 0.79/1.01        | ~ (v1_funct_1 @ sk_C)
% 0.79/1.01        | ~ (v2_funct_1 @ sk_C)
% 0.79/1.01        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.79/1.01        | ((sk_D) = (k2_funct_1 @ sk_C))
% 0.79/1.01        | ~ (v1_funct_1 @ sk_D)
% 0.79/1.01        | ~ (v1_relat_1 @ sk_D))),
% 0.79/1.01      inference('sup-', [status(thm)], ['91', '94'])).
% 0.79/1.01  thf('96', plain,
% 0.79/1.01      (![X6 : $i]:
% 0.79/1.01         (~ (v2_funct_1 @ X6)
% 0.79/1.01          | ((k5_relat_1 @ X6 @ (k2_funct_1 @ X6))
% 0.79/1.01              = (k6_partfun1 @ (k1_relat_1 @ X6)))
% 0.79/1.01          | ~ (v1_funct_1 @ X6)
% 0.79/1.01          | ~ (v1_relat_1 @ X6))),
% 0.79/1.01      inference('demod', [status(thm)], ['0', '1'])).
% 0.79/1.01  thf('97', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('98', plain,
% 0.79/1.01      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.79/1.01         (((X43) = (k1_xboole_0))
% 0.79/1.01          | ~ (v1_funct_1 @ X44)
% 0.79/1.01          | ~ (v1_funct_2 @ X44 @ X45 @ X43)
% 0.79/1.01          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X43)))
% 0.79/1.01          | ((k5_relat_1 @ X44 @ (k2_funct_1 @ X44)) = (k6_partfun1 @ X45))
% 0.79/1.01          | ~ (v2_funct_1 @ X44)
% 0.79/1.01          | ((k2_relset_1 @ X45 @ X43 @ X44) != (X43)))),
% 0.79/1.01      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.79/1.01  thf('99', plain,
% 0.79/1.01      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.79/1.01        | ~ (v2_funct_1 @ sk_C)
% 0.79/1.01        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.79/1.01        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.79/1.01        | ~ (v1_funct_1 @ sk_C)
% 0.79/1.01        | ((sk_B) = (k1_xboole_0)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['97', '98'])).
% 0.79/1.01  thf('100', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('101', plain, ((v2_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('102', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('103', plain, ((v1_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('104', plain,
% 0.79/1.01      ((((sk_B) != (sk_B))
% 0.79/1.01        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.79/1.01        | ((sk_B) = (k1_xboole_0)))),
% 0.79/1.01      inference('demod', [status(thm)], ['99', '100', '101', '102', '103'])).
% 0.79/1.01  thf('105', plain,
% 0.79/1.01      ((((sk_B) = (k1_xboole_0))
% 0.79/1.01        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 0.79/1.01      inference('simplify', [status(thm)], ['104'])).
% 0.79/1.01  thf('106', plain, (((sk_B) != (k1_xboole_0))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('107', plain,
% 0.79/1.01      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 0.79/1.01      inference('simplify_reflect-', [status(thm)], ['105', '106'])).
% 0.79/1.01  thf('108', plain,
% 0.79/1.01      ((((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.79/1.01        | ~ (v1_relat_1 @ sk_C)
% 0.79/1.01        | ~ (v1_funct_1 @ sk_C)
% 0.79/1.01        | ~ (v2_funct_1 @ sk_C))),
% 0.79/1.01      inference('sup+', [status(thm)], ['96', '107'])).
% 0.79/1.01  thf('109', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('110', plain,
% 0.79/1.01      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.79/1.01         ((v1_relat_1 @ X9)
% 0.79/1.01          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.79/1.01      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.79/1.01  thf('111', plain, ((v1_relat_1 @ sk_C)),
% 0.79/1.01      inference('sup-', [status(thm)], ['109', '110'])).
% 0.79/1.01  thf('112', plain, ((v1_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('113', plain, ((v2_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('114', plain,
% 0.79/1.01      (((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 0.79/1.01      inference('demod', [status(thm)], ['108', '111', '112', '113'])).
% 0.79/1.01  thf('115', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 0.79/1.01      inference('demod', [status(thm)], ['76', '77'])).
% 0.79/1.01  thf('116', plain,
% 0.79/1.01      (((k1_relat_1 @ (k6_partfun1 @ sk_A)) = (k1_relat_1 @ sk_C))),
% 0.79/1.01      inference('sup+', [status(thm)], ['114', '115'])).
% 0.79/1.01  thf('117', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 0.79/1.01      inference('demod', [status(thm)], ['76', '77'])).
% 0.79/1.01  thf('118', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.79/1.01      inference('demod', [status(thm)], ['116', '117'])).
% 0.79/1.01  thf('119', plain, ((v1_relat_1 @ sk_C)),
% 0.79/1.01      inference('sup-', [status(thm)], ['109', '110'])).
% 0.79/1.01  thf('120', plain, ((v1_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('121', plain, ((v2_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('122', plain,
% 0.79/1.01      (![X6 : $i]:
% 0.79/1.01         (~ (v2_funct_1 @ X6)
% 0.79/1.01          | ((k5_relat_1 @ (k2_funct_1 @ X6) @ X6)
% 0.79/1.01              = (k6_relat_1 @ (k2_relat_1 @ X6)))
% 0.79/1.01          | ~ (v1_funct_1 @ X6)
% 0.79/1.01          | ~ (v1_relat_1 @ X6))),
% 0.79/1.01      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.79/1.01  thf('123', plain, (![X29 : $i]: ((k6_partfun1 @ X29) = (k6_relat_1 @ X29))),
% 0.79/1.01      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.79/1.01  thf('124', plain,
% 0.79/1.01      (![X6 : $i]:
% 0.79/1.01         (~ (v2_funct_1 @ X6)
% 0.79/1.01          | ((k5_relat_1 @ (k2_funct_1 @ X6) @ X6)
% 0.79/1.01              = (k6_partfun1 @ (k2_relat_1 @ X6)))
% 0.79/1.01          | ~ (v1_funct_1 @ X6)
% 0.79/1.01          | ~ (v1_relat_1 @ X6))),
% 0.79/1.01      inference('demod', [status(thm)], ['122', '123'])).
% 0.79/1.01  thf('125', plain,
% 0.79/1.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('126', plain,
% 0.79/1.01      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.79/1.01         (((X43) = (k1_xboole_0))
% 0.79/1.01          | ~ (v1_funct_1 @ X44)
% 0.79/1.01          | ~ (v1_funct_2 @ X44 @ X45 @ X43)
% 0.79/1.01          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X43)))
% 0.79/1.01          | ((k5_relat_1 @ (k2_funct_1 @ X44) @ X44) = (k6_partfun1 @ X43))
% 0.79/1.01          | ~ (v2_funct_1 @ X44)
% 0.79/1.01          | ((k2_relset_1 @ X45 @ X43 @ X44) != (X43)))),
% 0.79/1.01      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.79/1.01  thf('127', plain,
% 0.79/1.01      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.79/1.01        | ~ (v2_funct_1 @ sk_C)
% 0.79/1.01        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 0.79/1.01        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.79/1.01        | ~ (v1_funct_1 @ sk_C)
% 0.79/1.01        | ((sk_B) = (k1_xboole_0)))),
% 0.79/1.01      inference('sup-', [status(thm)], ['125', '126'])).
% 0.79/1.01  thf('128', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('129', plain, ((v2_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('130', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('131', plain, ((v1_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('132', plain,
% 0.79/1.01      ((((sk_B) != (sk_B))
% 0.79/1.01        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 0.79/1.01        | ((sk_B) = (k1_xboole_0)))),
% 0.79/1.01      inference('demod', [status(thm)], ['127', '128', '129', '130', '131'])).
% 0.79/1.01  thf('133', plain,
% 0.79/1.01      ((((sk_B) = (k1_xboole_0))
% 0.79/1.01        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 0.79/1.01      inference('simplify', [status(thm)], ['132'])).
% 0.79/1.01  thf('134', plain, (((sk_B) != (k1_xboole_0))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('135', plain,
% 0.79/1.01      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 0.79/1.01      inference('simplify_reflect-', [status(thm)], ['133', '134'])).
% 0.79/1.01  thf('136', plain,
% 0.79/1.01      ((((k6_partfun1 @ (k2_relat_1 @ sk_C)) = (k6_partfun1 @ sk_B))
% 0.79/1.01        | ~ (v1_relat_1 @ sk_C)
% 0.79/1.01        | ~ (v1_funct_1 @ sk_C)
% 0.79/1.01        | ~ (v2_funct_1 @ sk_C))),
% 0.79/1.01      inference('sup+', [status(thm)], ['124', '135'])).
% 0.79/1.01  thf('137', plain, ((v1_relat_1 @ sk_C)),
% 0.79/1.01      inference('sup-', [status(thm)], ['109', '110'])).
% 0.79/1.01  thf('138', plain, ((v1_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('139', plain, ((v2_funct_1 @ sk_C)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('140', plain,
% 0.79/1.01      (((k6_partfun1 @ (k2_relat_1 @ sk_C)) = (k6_partfun1 @ sk_B))),
% 0.79/1.01      inference('demod', [status(thm)], ['136', '137', '138', '139'])).
% 0.79/1.01  thf('141', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 0.79/1.01      inference('demod', [status(thm)], ['76', '77'])).
% 0.79/1.01  thf('142', plain,
% 0.79/1.01      (((k1_relat_1 @ (k6_partfun1 @ sk_B)) = (k2_relat_1 @ sk_C))),
% 0.79/1.01      inference('sup+', [status(thm)], ['140', '141'])).
% 0.79/1.01  thf('143', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 0.79/1.01      inference('demod', [status(thm)], ['76', '77'])).
% 0.79/1.01  thf('144', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 0.79/1.01      inference('demod', [status(thm)], ['142', '143'])).
% 0.79/1.01  thf('145', plain, ((v1_funct_1 @ sk_D)),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('146', plain, ((v1_relat_1 @ sk_D)),
% 0.79/1.01      inference('sup-', [status(thm)], ['70', '71'])).
% 0.79/1.01  thf('147', plain,
% 0.79/1.01      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 0.79/1.01        | ((sk_B) != (k1_relat_1 @ sk_D))
% 0.79/1.01        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 0.79/1.01      inference('demod', [status(thm)],
% 0.79/1.01                ['95', '118', '119', '120', '121', '144', '145', '146'])).
% 0.79/1.01  thf('148', plain,
% 0.79/1.01      ((((sk_D) = (k2_funct_1 @ sk_C)) | ((sk_B) != (k1_relat_1 @ sk_D)))),
% 0.79/1.01      inference('simplify', [status(thm)], ['147'])).
% 0.79/1.01  thf('149', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.79/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/1.01  thf('150', plain, (((sk_B) != (k1_relat_1 @ sk_D))),
% 0.79/1.01      inference('simplify_reflect-', [status(thm)], ['148', '149'])).
% 0.79/1.01  thf('151', plain, ($false),
% 0.79/1.01      inference('simplify_reflect-', [status(thm)], ['81', '150'])).
% 0.79/1.01  
% 0.79/1.01  % SZS output end Refutation
% 0.79/1.01  
% 0.79/1.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

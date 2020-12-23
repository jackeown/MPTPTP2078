%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ghHr5OUoev

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:27 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :  311 (2575 expanded)
%              Number of leaves         :   48 ( 783 expanded)
%              Depth                    :   31
%              Number of atoms          : 3685 (61501 expanded)
%              Number of equality atoms :  262 (4193 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 )
        = ( k5_relat_1 @ X28 @ X31 ) ) ) ),
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

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('13',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('20',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('21',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( X17 = X20 )
      | ~ ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','22'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('24',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('25',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('26',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

thf(t64_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) )
              & ( ( k5_relat_1 @ B @ A )
                = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('28',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( X12
        = ( k2_funct_1 @ X13 ) )
      | ( ( k5_relat_1 @ X12 @ X13 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X13 ) ) )
      | ( ( k2_relat_1 @ X12 )
       != ( k1_relat_1 @ X13 ) )
      | ~ ( v2_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('29',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('30',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( X12
        = ( k2_funct_1 @ X13 ) )
      | ( ( k5_relat_1 @ X12 @ X13 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X13 ) ) )
      | ( ( k2_relat_1 @ X12 )
       != ( k1_relat_1 @ X13 ) )
      | ~ ( v2_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('35',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('36',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('39',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('40',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('48',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['31','36','37','42','43','48'])).

thf('50',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('51',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('52',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
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

thf('54',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( r2_relset_1 @ X36 @ X36 @ ( k1_partfun1 @ X36 @ X37 @ X37 @ X36 @ X35 @ X38 ) @ ( k6_partfun1 @ X36 ) )
      | ( ( k2_relset_1 @ X37 @ X36 @ X38 )
        = X36 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X36 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['52','58'])).

thf('60',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('61',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 )
      | ( X17 != X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('62',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_relset_1 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('66',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['59','63','66','67','68','69'])).

thf('71',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['49','70'])).

thf('72',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('74',plain,(
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

thf('75',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ( zip_tseitin_0 @ X43 @ X46 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X47 @ X44 @ X44 @ X45 @ X46 @ X43 ) )
      | ( zip_tseitin_1 @ X45 @ X44 )
      | ( ( k2_relset_1 @ X47 @ X44 @ X46 )
       != X44 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X44 )
      | ~ ( v1_funct_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('76',plain,(
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
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['73','79'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('81',plain,(
    ! [X7: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('82',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k1_relat_1 @ X10 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('83',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['40','41'])).

thf('84',plain,(
    ! [X7: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('85',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('86',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X10 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('87',plain,(
    ! [X51: $i] :
      ( ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X51 ) @ ( k2_relat_1 @ X51 ) ) ) )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['84','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['83','92'])).

thf('94',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['46','47'])).

thf('95',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['93','94','95','96'])).

thf('98',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['82','97'])).

thf('99',plain,(
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

thf('100',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( X48 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X48 ) ) )
      | ( ( k5_relat_1 @ X49 @ ( k2_funct_1 @ X49 ) )
        = ( k6_partfun1 @ X50 ) )
      | ~ ( v2_funct_1 @ X49 )
      | ( ( k2_relset_1 @ X50 @ X48 @ X49 )
       != X48 ) ) ),
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

thf(t58_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('110',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X11 @ ( k2_funct_1 @ X11 ) ) )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('111',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ sk_A ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('112',plain,(
    ! [X5: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('113',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('114',plain,(
    ! [X5: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X5 ) )
      = X5 ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['46','47'])).

thf('116',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['111','114','115','116','117'])).

thf('119',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['46','47'])).

thf('120',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','118','119','120','121'])).

thf('123',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( v1_funct_1 @ ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('125',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['122','127'])).

thf('129',plain,(
    ! [X7: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('130',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','118','119','120','121'])).

thf('131',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('132',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['107','108'])).

thf('134',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['129','134'])).

thf('136',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['46','47'])).

thf('137',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['135','136','137'])).

thf('139',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['128','138'])).

thf('140',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_funct_1 @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['81','139'])).

thf('141',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['46','47'])).

thf('142',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v1_funct_1 @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['140','141','142'])).

thf('144',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('145',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('146',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['144','145'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('147',plain,(
    ! [X6: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X6 ) ) @ X6 )
        = X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('148',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('149',plain,(
    ! [X6: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X6 ) ) @ X6 )
        = X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['146','149'])).

thf('151',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('155',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['150','155'])).

thf(t53_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ? [B: $i] :
            ( ( ( k5_relat_1 @ A @ B )
              = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
            & ( v1_funct_1 @ B )
            & ( v1_relat_1 @ B ) )
       => ( v2_funct_1 @ A ) ) ) )).

thf('157',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( ( k5_relat_1 @ X9 @ X8 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X9 ) ) )
      | ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t53_funct_1])).

thf('158',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('159',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( ( k5_relat_1 @ X9 @ X8 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X9 ) ) )
      | ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ X0 )
       != ( k6_partfun1 @ ( k1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ( v2_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['156','159'])).

thf('161',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('162',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('163',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ X0 )
       != ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ( v2_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['160','161','162','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,(
    v2_funct_1 @ ( k6_partfun1 @ sk_A ) ),
    inference('sup-',[status(thm)],['143','165'])).

thf('167',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['80','166','167','168','169','170'])).

thf('172',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,(
    ! [X41: $i,X42: $i] :
      ( ( X41 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('174',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X39: $i,X40: $i] :
      ( ( v2_funct_1 @ X40 )
      | ~ ( zip_tseitin_0 @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('178',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['72','178'])).

thf('180',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( X48 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X48 ) ) )
      | ( ( k5_relat_1 @ X49 @ ( k2_funct_1 @ X49 ) )
        = ( k6_partfun1 @ X50 ) )
      | ~ ( v2_funct_1 @ X49 )
      | ( ( k2_relset_1 @ X50 @ X48 @ X49 )
       != X48 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('182',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('184',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['182','183','184','185'])).

thf('187',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['186','187'])).

thf('189',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['59','63','66','67','68','69'])).

thf('190',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['176','177'])).

thf('193',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['191','192'])).

thf('194',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X11 @ ( k2_funct_1 @ X11 ) ) )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('195',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ sk_B ) )
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X5: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X5 ) )
      = X5 ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('197',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['34','35'])).

thf('198',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['176','177'])).

thf('200',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['195','196','197','198','199'])).

thf('201',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['179','200'])).

thf('202',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['201'])).

thf('203',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X10 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('204',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('205',plain,(
    ! [X7: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('206',plain,(
    ! [X51: $i] :
      ( ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X51 ) @ ( k2_relat_1 @ X51 ) ) ) )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('207',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('208',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,(
    ! [X51: $i] :
      ( ( v1_funct_2 @ X51 @ ( k1_relat_1 @ X51 ) @ ( k2_relat_1 @ X51 ) )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('210',plain,(
    ! [X51: $i] :
      ( ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X51 ) @ ( k2_relat_1 @ X51 ) ) ) )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('211',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( X48 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X48 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X49 ) @ X49 )
        = ( k6_partfun1 @ X48 ) )
      | ~ ( v2_funct_1 @ X49 )
      | ( ( k2_relset_1 @ X50 @ X48 @ X49 )
       != X48 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('212',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['212'])).

thf('214',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['209','213'])).

thf('215',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['214'])).

thf('216',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['208','215'])).

thf('217',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['216'])).

thf('218',plain,(
    ! [X7: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('219',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('220',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X10 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('221',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( ( k5_relat_1 @ X9 @ X8 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X9 ) ) )
      | ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('222',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['220','221'])).

thf('223',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['219','222'])).

thf('224',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['223'])).

thf('225',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['218','224'])).

thf('226',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['225'])).

thf('227',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ ( k2_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['217','226'])).

thf('228',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['227'])).

thf('229',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k1_relat_1 @ X10 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('230',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('231',plain,(
    ! [X51: $i] :
      ( ( v1_funct_2 @ X51 @ ( k1_relat_1 @ X51 ) @ ( k2_relat_1 @ X51 ) )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('232',plain,(
    ! [X51: $i] :
      ( ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X51 ) @ ( k2_relat_1 @ X51 ) ) ) )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('233',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( X48 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X48 ) ) )
      | ( ( k5_relat_1 @ X49 @ ( k2_funct_1 @ X49 ) )
        = ( k6_partfun1 @ X50 ) )
      | ~ ( v2_funct_1 @ X49 )
      | ( ( k2_relset_1 @ X50 @ X48 @ X49 )
       != X48 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('234',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['232','233'])).

thf('235',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['234'])).

thf('236',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['231','235'])).

thf('237',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['236'])).

thf('238',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['230','237'])).

thf('239',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['238'])).

thf('240',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( X12
        = ( k2_funct_1 @ X13 ) )
      | ( ( k5_relat_1 @ X12 @ X13 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X13 ) ) )
      | ( ( k2_relat_1 @ X12 )
       != ( k1_relat_1 @ X13 ) )
      | ~ ( v2_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('241',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['239','240'])).

thf('242',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['241'])).

thf('243',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['229','242'])).

thf('244',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['243'])).

thf('245',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['228','244'])).

thf('246',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['245'])).

thf('247',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['205','246'])).

thf('248',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['247'])).

thf('249',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['204','248'])).

thf('250',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['249'])).

thf('251',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['203','250'])).

thf('252',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['251'])).

thf('253',plain,
    ( ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['202','252'])).

thf('254',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['34','35'])).

thf('255',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['176','177'])).

thf('257',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['59','63','66','67','68','69'])).

thf('258',plain,
    ( ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['253','254','255','256','257'])).

thf('259',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('260',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['258','259','260'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ghHr5OUoev
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:18:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.59/1.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.59/1.80  % Solved by: fo/fo7.sh
% 1.59/1.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.59/1.80  % done 1606 iterations in 1.298s
% 1.59/1.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.59/1.80  % SZS output start Refutation
% 1.59/1.80  thf(sk_D_type, type, sk_D: $i).
% 1.59/1.80  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 1.59/1.80  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.59/1.80  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.59/1.80  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.59/1.80  thf(sk_B_type, type, sk_B: $i).
% 1.59/1.80  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.59/1.80  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.59/1.80  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.59/1.80  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.59/1.80  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.59/1.80  thf(sk_C_type, type, sk_C: $i).
% 1.59/1.80  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.59/1.80  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.59/1.80  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.59/1.80  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.59/1.80  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.59/1.80  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.59/1.80  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.59/1.80  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.59/1.80  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.59/1.80  thf(sk_A_type, type, sk_A: $i).
% 1.59/1.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.59/1.80  thf(t36_funct_2, conjecture,
% 1.59/1.80    (![A:$i,B:$i,C:$i]:
% 1.59/1.80     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.59/1.80         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.59/1.80       ( ![D:$i]:
% 1.59/1.80         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.59/1.80             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.59/1.80           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.59/1.80               ( r2_relset_1 @
% 1.59/1.80                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.59/1.80                 ( k6_partfun1 @ A ) ) & 
% 1.59/1.80               ( v2_funct_1 @ C ) ) =>
% 1.59/1.80             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.59/1.80               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.59/1.80  thf(zf_stmt_0, negated_conjecture,
% 1.59/1.80    (~( ![A:$i,B:$i,C:$i]:
% 1.59/1.80        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.59/1.80            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.59/1.80          ( ![D:$i]:
% 1.59/1.80            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.59/1.80                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.59/1.80              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.59/1.80                  ( r2_relset_1 @
% 1.59/1.80                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.59/1.80                    ( k6_partfun1 @ A ) ) & 
% 1.59/1.80                  ( v2_funct_1 @ C ) ) =>
% 1.59/1.80                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.59/1.80                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.59/1.80    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.59/1.80  thf('0', plain,
% 1.59/1.80      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.59/1.80        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.59/1.80        (k6_partfun1 @ sk_A))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('1', plain,
% 1.59/1.80      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('2', plain,
% 1.59/1.80      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf(redefinition_k1_partfun1, axiom,
% 1.59/1.80    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.59/1.80     ( ( ( v1_funct_1 @ E ) & 
% 1.59/1.80         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.59/1.80         ( v1_funct_1 @ F ) & 
% 1.59/1.80         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.59/1.80       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.59/1.80  thf('3', plain,
% 1.59/1.80      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.59/1.80         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 1.59/1.80          | ~ (v1_funct_1 @ X28)
% 1.59/1.80          | ~ (v1_funct_1 @ X31)
% 1.59/1.80          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.59/1.80          | ((k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31)
% 1.59/1.80              = (k5_relat_1 @ X28 @ X31)))),
% 1.59/1.80      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.59/1.80  thf('4', plain,
% 1.59/1.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.59/1.80         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.59/1.80            = (k5_relat_1 @ sk_C @ X0))
% 1.59/1.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ sk_C))),
% 1.59/1.80      inference('sup-', [status(thm)], ['2', '3'])).
% 1.59/1.80  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('6', plain,
% 1.59/1.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.59/1.80         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.59/1.80            = (k5_relat_1 @ sk_C @ X0))
% 1.59/1.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.59/1.80          | ~ (v1_funct_1 @ X0))),
% 1.59/1.80      inference('demod', [status(thm)], ['4', '5'])).
% 1.59/1.80  thf('7', plain,
% 1.59/1.80      ((~ (v1_funct_1 @ sk_D)
% 1.59/1.80        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.59/1.80            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.59/1.80      inference('sup-', [status(thm)], ['1', '6'])).
% 1.59/1.80  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('9', plain,
% 1.59/1.80      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.59/1.80         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.59/1.80      inference('demod', [status(thm)], ['7', '8'])).
% 1.59/1.80  thf('10', plain,
% 1.59/1.80      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.59/1.80        (k6_partfun1 @ sk_A))),
% 1.59/1.80      inference('demod', [status(thm)], ['0', '9'])).
% 1.59/1.80  thf('11', plain,
% 1.59/1.80      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('12', plain,
% 1.59/1.80      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf(dt_k1_partfun1, axiom,
% 1.59/1.80    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.59/1.80     ( ( ( v1_funct_1 @ E ) & 
% 1.59/1.80         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.59/1.80         ( v1_funct_1 @ F ) & 
% 1.59/1.80         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.59/1.80       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.59/1.80         ( m1_subset_1 @
% 1.59/1.80           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.59/1.80           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.59/1.80  thf('13', plain,
% 1.59/1.80      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.59/1.80         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 1.59/1.80          | ~ (v1_funct_1 @ X22)
% 1.59/1.80          | ~ (v1_funct_1 @ X25)
% 1.59/1.80          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 1.59/1.80          | (m1_subset_1 @ (k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25) @ 
% 1.59/1.80             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X27))))),
% 1.59/1.80      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.59/1.80  thf('14', plain,
% 1.59/1.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.59/1.80         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.59/1.80           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.59/1.80          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.59/1.80          | ~ (v1_funct_1 @ X1)
% 1.59/1.80          | ~ (v1_funct_1 @ sk_C))),
% 1.59/1.80      inference('sup-', [status(thm)], ['12', '13'])).
% 1.59/1.80  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('16', plain,
% 1.59/1.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.59/1.80         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.59/1.80           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.59/1.80          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.59/1.80          | ~ (v1_funct_1 @ X1))),
% 1.59/1.80      inference('demod', [status(thm)], ['14', '15'])).
% 1.59/1.80  thf('17', plain,
% 1.59/1.80      ((~ (v1_funct_1 @ sk_D)
% 1.59/1.80        | (m1_subset_1 @ 
% 1.59/1.80           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.59/1.80           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.59/1.80      inference('sup-', [status(thm)], ['11', '16'])).
% 1.59/1.80  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('19', plain,
% 1.59/1.80      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.59/1.80         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.59/1.80      inference('demod', [status(thm)], ['7', '8'])).
% 1.59/1.80  thf('20', plain,
% 1.59/1.80      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.59/1.80        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.59/1.80      inference('demod', [status(thm)], ['17', '18', '19'])).
% 1.59/1.80  thf(redefinition_r2_relset_1, axiom,
% 1.59/1.80    (![A:$i,B:$i,C:$i,D:$i]:
% 1.59/1.80     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.59/1.80         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.59/1.80       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.59/1.80  thf('21', plain,
% 1.59/1.80      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.59/1.80         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 1.59/1.80          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 1.59/1.80          | ((X17) = (X20))
% 1.59/1.80          | ~ (r2_relset_1 @ X18 @ X19 @ X17 @ X20))),
% 1.59/1.80      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.59/1.80  thf('22', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 1.59/1.80          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 1.59/1.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.59/1.80      inference('sup-', [status(thm)], ['20', '21'])).
% 1.59/1.80  thf('23', plain,
% 1.59/1.80      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.59/1.80           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.59/1.80        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 1.59/1.80      inference('sup-', [status(thm)], ['10', '22'])).
% 1.59/1.80  thf(t29_relset_1, axiom,
% 1.59/1.80    (![A:$i]:
% 1.59/1.80     ( m1_subset_1 @
% 1.59/1.80       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.59/1.80  thf('24', plain,
% 1.59/1.80      (![X21 : $i]:
% 1.59/1.80         (m1_subset_1 @ (k6_relat_1 @ X21) @ 
% 1.59/1.80          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 1.59/1.80      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.59/1.80  thf(redefinition_k6_partfun1, axiom,
% 1.59/1.80    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.59/1.80  thf('25', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 1.59/1.80      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.59/1.80  thf('26', plain,
% 1.59/1.80      (![X21 : $i]:
% 1.59/1.80         (m1_subset_1 @ (k6_partfun1 @ X21) @ 
% 1.59/1.80          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 1.59/1.80      inference('demod', [status(thm)], ['24', '25'])).
% 1.59/1.80  thf('27', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.59/1.80      inference('demod', [status(thm)], ['23', '26'])).
% 1.59/1.80  thf(t64_funct_1, axiom,
% 1.59/1.80    (![A:$i]:
% 1.59/1.80     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.59/1.80       ( ![B:$i]:
% 1.59/1.80         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.59/1.80           ( ( ( v2_funct_1 @ A ) & 
% 1.59/1.80               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 1.59/1.80               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 1.59/1.80             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.59/1.80  thf('28', plain,
% 1.59/1.80      (![X12 : $i, X13 : $i]:
% 1.59/1.80         (~ (v1_relat_1 @ X12)
% 1.59/1.80          | ~ (v1_funct_1 @ X12)
% 1.59/1.80          | ((X12) = (k2_funct_1 @ X13))
% 1.59/1.80          | ((k5_relat_1 @ X12 @ X13) != (k6_relat_1 @ (k2_relat_1 @ X13)))
% 1.59/1.80          | ((k2_relat_1 @ X12) != (k1_relat_1 @ X13))
% 1.59/1.80          | ~ (v2_funct_1 @ X13)
% 1.59/1.80          | ~ (v1_funct_1 @ X13)
% 1.59/1.80          | ~ (v1_relat_1 @ X13))),
% 1.59/1.80      inference('cnf', [status(esa)], [t64_funct_1])).
% 1.59/1.80  thf('29', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 1.59/1.80      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.59/1.80  thf('30', plain,
% 1.59/1.80      (![X12 : $i, X13 : $i]:
% 1.59/1.80         (~ (v1_relat_1 @ X12)
% 1.59/1.80          | ~ (v1_funct_1 @ X12)
% 1.59/1.80          | ((X12) = (k2_funct_1 @ X13))
% 1.59/1.80          | ((k5_relat_1 @ X12 @ X13) != (k6_partfun1 @ (k2_relat_1 @ X13)))
% 1.59/1.80          | ((k2_relat_1 @ X12) != (k1_relat_1 @ X13))
% 1.59/1.80          | ~ (v2_funct_1 @ X13)
% 1.59/1.80          | ~ (v1_funct_1 @ X13)
% 1.59/1.80          | ~ (v1_relat_1 @ X13))),
% 1.59/1.80      inference('demod', [status(thm)], ['28', '29'])).
% 1.59/1.80  thf('31', plain,
% 1.59/1.80      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 1.59/1.80        | ~ (v1_relat_1 @ sk_D)
% 1.59/1.80        | ~ (v1_funct_1 @ sk_D)
% 1.59/1.80        | ~ (v2_funct_1 @ sk_D)
% 1.59/1.80        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 1.59/1.80        | ((sk_C) = (k2_funct_1 @ sk_D))
% 1.59/1.80        | ~ (v1_funct_1 @ sk_C)
% 1.59/1.80        | ~ (v1_relat_1 @ sk_C))),
% 1.59/1.80      inference('sup-', [status(thm)], ['27', '30'])).
% 1.59/1.80  thf('32', plain,
% 1.59/1.80      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf(cc2_relat_1, axiom,
% 1.59/1.80    (![A:$i]:
% 1.59/1.80     ( ( v1_relat_1 @ A ) =>
% 1.59/1.80       ( ![B:$i]:
% 1.59/1.80         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.59/1.80  thf('33', plain,
% 1.59/1.80      (![X0 : $i, X1 : $i]:
% 1.59/1.80         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.59/1.80          | (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X1))),
% 1.59/1.80      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.59/1.80  thf('34', plain,
% 1.59/1.80      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 1.59/1.80      inference('sup-', [status(thm)], ['32', '33'])).
% 1.59/1.80  thf(fc6_relat_1, axiom,
% 1.59/1.80    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.59/1.80  thf('35', plain,
% 1.59/1.80      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.59/1.80      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.59/1.80  thf('36', plain, ((v1_relat_1 @ sk_D)),
% 1.59/1.80      inference('demod', [status(thm)], ['34', '35'])).
% 1.59/1.80  thf('37', plain, ((v1_funct_1 @ sk_D)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('38', plain,
% 1.59/1.80      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf(redefinition_k2_relset_1, axiom,
% 1.59/1.80    (![A:$i,B:$i,C:$i]:
% 1.59/1.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.59/1.80       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.59/1.80  thf('39', plain,
% 1.59/1.80      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.59/1.80         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 1.59/1.80          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.59/1.80      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.59/1.80  thf('40', plain,
% 1.59/1.80      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.59/1.80      inference('sup-', [status(thm)], ['38', '39'])).
% 1.59/1.80  thf('41', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('42', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.59/1.80      inference('sup+', [status(thm)], ['40', '41'])).
% 1.59/1.80  thf('43', plain, ((v1_funct_1 @ sk_C)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('44', plain,
% 1.59/1.80      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('45', plain,
% 1.59/1.80      (![X0 : $i, X1 : $i]:
% 1.59/1.80         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.59/1.80          | (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X1))),
% 1.59/1.80      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.59/1.80  thf('46', plain,
% 1.59/1.80      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 1.59/1.80      inference('sup-', [status(thm)], ['44', '45'])).
% 1.59/1.80  thf('47', plain,
% 1.59/1.80      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.59/1.80      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.59/1.80  thf('48', plain, ((v1_relat_1 @ sk_C)),
% 1.59/1.80      inference('demod', [status(thm)], ['46', '47'])).
% 1.59/1.80  thf('49', plain,
% 1.59/1.80      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 1.59/1.80        | ~ (v2_funct_1 @ sk_D)
% 1.59/1.80        | ((sk_B) != (k1_relat_1 @ sk_D))
% 1.59/1.80        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 1.59/1.80      inference('demod', [status(thm)], ['31', '36', '37', '42', '43', '48'])).
% 1.59/1.80  thf('50', plain,
% 1.59/1.80      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.59/1.80         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.59/1.80      inference('demod', [status(thm)], ['7', '8'])).
% 1.59/1.80  thf('51', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.59/1.80      inference('demod', [status(thm)], ['23', '26'])).
% 1.59/1.80  thf('52', plain,
% 1.59/1.80      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.59/1.80         = (k6_partfun1 @ sk_A))),
% 1.59/1.80      inference('demod', [status(thm)], ['50', '51'])).
% 1.59/1.80  thf('53', plain,
% 1.59/1.80      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf(t24_funct_2, axiom,
% 1.59/1.80    (![A:$i,B:$i,C:$i]:
% 1.59/1.80     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.59/1.80         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.59/1.80       ( ![D:$i]:
% 1.59/1.80         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.59/1.80             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.59/1.80           ( ( r2_relset_1 @
% 1.59/1.80               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 1.59/1.80               ( k6_partfun1 @ B ) ) =>
% 1.59/1.80             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 1.59/1.80  thf('54', plain,
% 1.59/1.80      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.59/1.80         (~ (v1_funct_1 @ X35)
% 1.59/1.80          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 1.59/1.80          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 1.59/1.80          | ~ (r2_relset_1 @ X36 @ X36 @ 
% 1.59/1.80               (k1_partfun1 @ X36 @ X37 @ X37 @ X36 @ X35 @ X38) @ 
% 1.59/1.80               (k6_partfun1 @ X36))
% 1.59/1.80          | ((k2_relset_1 @ X37 @ X36 @ X38) = (X36))
% 1.59/1.80          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 1.59/1.80          | ~ (v1_funct_2 @ X38 @ X37 @ X36)
% 1.59/1.80          | ~ (v1_funct_1 @ X38))),
% 1.59/1.80      inference('cnf', [status(esa)], [t24_funct_2])).
% 1.59/1.80  thf('55', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.59/1.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.59/1.80          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.59/1.80          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.59/1.80               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.59/1.80               (k6_partfun1 @ sk_A))
% 1.59/1.80          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.59/1.80          | ~ (v1_funct_1 @ sk_C))),
% 1.59/1.80      inference('sup-', [status(thm)], ['53', '54'])).
% 1.59/1.80  thf('56', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('57', plain, ((v1_funct_1 @ sk_C)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('58', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.59/1.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.59/1.80          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.59/1.80          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.59/1.80               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.59/1.80               (k6_partfun1 @ sk_A)))),
% 1.59/1.80      inference('demod', [status(thm)], ['55', '56', '57'])).
% 1.59/1.80  thf('59', plain,
% 1.59/1.80      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 1.59/1.80           (k6_partfun1 @ sk_A))
% 1.59/1.80        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 1.59/1.80        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.59/1.80        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.59/1.80        | ~ (v1_funct_1 @ sk_D))),
% 1.59/1.80      inference('sup-', [status(thm)], ['52', '58'])).
% 1.59/1.80  thf('60', plain,
% 1.59/1.80      (![X21 : $i]:
% 1.59/1.80         (m1_subset_1 @ (k6_partfun1 @ X21) @ 
% 1.59/1.80          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 1.59/1.80      inference('demod', [status(thm)], ['24', '25'])).
% 1.59/1.80  thf('61', plain,
% 1.59/1.80      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.59/1.80         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 1.59/1.80          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 1.59/1.80          | (r2_relset_1 @ X18 @ X19 @ X17 @ X20)
% 1.59/1.80          | ((X17) != (X20)))),
% 1.59/1.80      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.59/1.80  thf('62', plain,
% 1.59/1.80      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.59/1.80         ((r2_relset_1 @ X18 @ X19 @ X20 @ X20)
% 1.59/1.80          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.59/1.80      inference('simplify', [status(thm)], ['61'])).
% 1.59/1.80  thf('63', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 1.59/1.80      inference('sup-', [status(thm)], ['60', '62'])).
% 1.59/1.80  thf('64', plain,
% 1.59/1.80      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('65', plain,
% 1.59/1.80      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.59/1.80         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 1.59/1.80          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.59/1.80      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.59/1.80  thf('66', plain,
% 1.59/1.80      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.59/1.80      inference('sup-', [status(thm)], ['64', '65'])).
% 1.59/1.80  thf('67', plain,
% 1.59/1.80      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('68', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('69', plain, ((v1_funct_1 @ sk_D)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('70', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.59/1.80      inference('demod', [status(thm)], ['59', '63', '66', '67', '68', '69'])).
% 1.59/1.80  thf('71', plain,
% 1.59/1.80      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 1.59/1.80        | ~ (v2_funct_1 @ sk_D)
% 1.59/1.80        | ((sk_B) != (k1_relat_1 @ sk_D))
% 1.59/1.80        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 1.59/1.80      inference('demod', [status(thm)], ['49', '70'])).
% 1.59/1.80  thf('72', plain,
% 1.59/1.80      ((((sk_C) = (k2_funct_1 @ sk_D))
% 1.59/1.80        | ((sk_B) != (k1_relat_1 @ sk_D))
% 1.59/1.80        | ~ (v2_funct_1 @ sk_D))),
% 1.59/1.80      inference('simplify', [status(thm)], ['71'])).
% 1.59/1.80  thf('73', plain,
% 1.59/1.80      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.59/1.80         = (k6_partfun1 @ sk_A))),
% 1.59/1.80      inference('demod', [status(thm)], ['50', '51'])).
% 1.59/1.80  thf('74', plain,
% 1.59/1.80      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf(t30_funct_2, axiom,
% 1.59/1.80    (![A:$i,B:$i,C:$i,D:$i]:
% 1.59/1.80     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.59/1.80         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 1.59/1.80       ( ![E:$i]:
% 1.59/1.80         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 1.59/1.80             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 1.59/1.80           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 1.59/1.80               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 1.59/1.80             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 1.59/1.80               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 1.59/1.80  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 1.59/1.80  thf(zf_stmt_2, axiom,
% 1.59/1.80    (![C:$i,B:$i]:
% 1.59/1.80     ( ( zip_tseitin_1 @ C @ B ) =>
% 1.59/1.80       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 1.59/1.80  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.59/1.80  thf(zf_stmt_4, axiom,
% 1.59/1.80    (![E:$i,D:$i]:
% 1.59/1.80     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 1.59/1.80  thf(zf_stmt_5, axiom,
% 1.59/1.80    (![A:$i,B:$i,C:$i,D:$i]:
% 1.59/1.80     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.59/1.80         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.59/1.80       ( ![E:$i]:
% 1.59/1.80         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.59/1.80             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.59/1.80           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 1.59/1.80               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 1.59/1.80             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 1.59/1.80  thf('75', plain,
% 1.59/1.80      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 1.59/1.80         (~ (v1_funct_1 @ X43)
% 1.59/1.80          | ~ (v1_funct_2 @ X43 @ X44 @ X45)
% 1.59/1.80          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 1.59/1.80          | (zip_tseitin_0 @ X43 @ X46)
% 1.59/1.80          | ~ (v2_funct_1 @ (k1_partfun1 @ X47 @ X44 @ X44 @ X45 @ X46 @ X43))
% 1.59/1.80          | (zip_tseitin_1 @ X45 @ X44)
% 1.59/1.80          | ((k2_relset_1 @ X47 @ X44 @ X46) != (X44))
% 1.59/1.80          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X44)))
% 1.59/1.80          | ~ (v1_funct_2 @ X46 @ X47 @ X44)
% 1.59/1.80          | ~ (v1_funct_1 @ X46))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.59/1.80  thf('76', plain,
% 1.59/1.80      (![X0 : $i, X1 : $i]:
% 1.59/1.80         (~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.59/1.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.59/1.80          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.59/1.80          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.59/1.80          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.59/1.80          | (zip_tseitin_0 @ sk_D @ X0)
% 1.59/1.80          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.59/1.80          | ~ (v1_funct_1 @ sk_D))),
% 1.59/1.80      inference('sup-', [status(thm)], ['74', '75'])).
% 1.59/1.80  thf('77', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('78', plain, ((v1_funct_1 @ sk_D)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('79', plain,
% 1.59/1.80      (![X0 : $i, X1 : $i]:
% 1.59/1.80         (~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.59/1.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.59/1.80          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.59/1.80          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.59/1.80          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.59/1.80          | (zip_tseitin_0 @ sk_D @ X0))),
% 1.59/1.80      inference('demod', [status(thm)], ['76', '77', '78'])).
% 1.59/1.80  thf('80', plain,
% 1.59/1.80      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 1.59/1.80        | (zip_tseitin_0 @ sk_D @ sk_C)
% 1.59/1.80        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.59/1.80        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.59/1.80        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.59/1.80        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.59/1.80        | ~ (v1_funct_1 @ sk_C))),
% 1.59/1.80      inference('sup-', [status(thm)], ['73', '79'])).
% 1.59/1.80  thf(dt_k2_funct_1, axiom,
% 1.59/1.80    (![A:$i]:
% 1.59/1.80     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.59/1.80       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.59/1.80         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.59/1.80  thf('81', plain,
% 1.59/1.80      (![X7 : $i]:
% 1.59/1.80         ((v1_funct_1 @ (k2_funct_1 @ X7))
% 1.59/1.80          | ~ (v1_funct_1 @ X7)
% 1.59/1.80          | ~ (v1_relat_1 @ X7))),
% 1.59/1.80      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.59/1.80  thf(t55_funct_1, axiom,
% 1.59/1.80    (![A:$i]:
% 1.59/1.80     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.59/1.80       ( ( v2_funct_1 @ A ) =>
% 1.59/1.80         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.59/1.80           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.59/1.80  thf('82', plain,
% 1.59/1.80      (![X10 : $i]:
% 1.59/1.80         (~ (v2_funct_1 @ X10)
% 1.59/1.80          | ((k1_relat_1 @ X10) = (k2_relat_1 @ (k2_funct_1 @ X10)))
% 1.59/1.80          | ~ (v1_funct_1 @ X10)
% 1.59/1.80          | ~ (v1_relat_1 @ X10))),
% 1.59/1.80      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.59/1.80  thf('83', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.59/1.80      inference('sup+', [status(thm)], ['40', '41'])).
% 1.59/1.80  thf('84', plain,
% 1.59/1.80      (![X7 : $i]:
% 1.59/1.80         ((v1_funct_1 @ (k2_funct_1 @ X7))
% 1.59/1.80          | ~ (v1_funct_1 @ X7)
% 1.59/1.80          | ~ (v1_relat_1 @ X7))),
% 1.59/1.80      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.59/1.80  thf('85', plain,
% 1.59/1.80      (![X7 : $i]:
% 1.59/1.80         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 1.59/1.80          | ~ (v1_funct_1 @ X7)
% 1.59/1.80          | ~ (v1_relat_1 @ X7))),
% 1.59/1.80      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.59/1.80  thf('86', plain,
% 1.59/1.80      (![X10 : $i]:
% 1.59/1.80         (~ (v2_funct_1 @ X10)
% 1.59/1.80          | ((k2_relat_1 @ X10) = (k1_relat_1 @ (k2_funct_1 @ X10)))
% 1.59/1.80          | ~ (v1_funct_1 @ X10)
% 1.59/1.80          | ~ (v1_relat_1 @ X10))),
% 1.59/1.80      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.59/1.80  thf(t3_funct_2, axiom,
% 1.59/1.80    (![A:$i]:
% 1.59/1.80     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.59/1.80       ( ( v1_funct_1 @ A ) & 
% 1.59/1.80         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.59/1.80         ( m1_subset_1 @
% 1.59/1.80           A @ 
% 1.59/1.80           ( k1_zfmisc_1 @
% 1.59/1.80             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.59/1.80  thf('87', plain,
% 1.59/1.80      (![X51 : $i]:
% 1.59/1.80         ((m1_subset_1 @ X51 @ 
% 1.59/1.80           (k1_zfmisc_1 @ 
% 1.59/1.80            (k2_zfmisc_1 @ (k1_relat_1 @ X51) @ (k2_relat_1 @ X51))))
% 1.59/1.80          | ~ (v1_funct_1 @ X51)
% 1.59/1.80          | ~ (v1_relat_1 @ X51))),
% 1.59/1.80      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.59/1.80  thf('88', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.59/1.80           (k1_zfmisc_1 @ 
% 1.59/1.80            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 1.59/1.80          | ~ (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v2_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.59/1.80          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 1.59/1.80      inference('sup+', [status(thm)], ['86', '87'])).
% 1.59/1.80  thf('89', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (~ (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.59/1.80          | ~ (v2_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X0)
% 1.59/1.80          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.59/1.80             (k1_zfmisc_1 @ 
% 1.59/1.80              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 1.59/1.80               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 1.59/1.80      inference('sup-', [status(thm)], ['85', '88'])).
% 1.59/1.80  thf('90', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.59/1.80           (k1_zfmisc_1 @ 
% 1.59/1.80            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 1.59/1.80          | ~ (v2_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X0))),
% 1.59/1.80      inference('simplify', [status(thm)], ['89'])).
% 1.59/1.80  thf('91', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (~ (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v2_funct_1 @ X0)
% 1.59/1.80          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.59/1.80             (k1_zfmisc_1 @ 
% 1.59/1.80              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 1.59/1.80               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 1.59/1.80      inference('sup-', [status(thm)], ['84', '90'])).
% 1.59/1.80  thf('92', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 1.59/1.80           (k1_zfmisc_1 @ 
% 1.59/1.80            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 1.59/1.80          | ~ (v2_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X0))),
% 1.59/1.80      inference('simplify', [status(thm)], ['91'])).
% 1.59/1.80  thf('93', plain,
% 1.59/1.80      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.59/1.80         (k1_zfmisc_1 @ 
% 1.59/1.80          (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))
% 1.59/1.80        | ~ (v1_relat_1 @ sk_C)
% 1.59/1.80        | ~ (v1_funct_1 @ sk_C)
% 1.59/1.80        | ~ (v2_funct_1 @ sk_C))),
% 1.59/1.80      inference('sup+', [status(thm)], ['83', '92'])).
% 1.59/1.80  thf('94', plain, ((v1_relat_1 @ sk_C)),
% 1.59/1.80      inference('demod', [status(thm)], ['46', '47'])).
% 1.59/1.80  thf('95', plain, ((v1_funct_1 @ sk_C)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('96', plain, ((v2_funct_1 @ sk_C)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('97', plain,
% 1.59/1.80      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.59/1.80        (k1_zfmisc_1 @ 
% 1.59/1.80         (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 1.59/1.80      inference('demod', [status(thm)], ['93', '94', '95', '96'])).
% 1.59/1.80  thf('98', plain,
% 1.59/1.80      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.59/1.80         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C))))
% 1.59/1.80        | ~ (v1_relat_1 @ sk_C)
% 1.59/1.80        | ~ (v1_funct_1 @ sk_C)
% 1.59/1.80        | ~ (v2_funct_1 @ sk_C))),
% 1.59/1.80      inference('sup+', [status(thm)], ['82', '97'])).
% 1.59/1.80  thf('99', plain,
% 1.59/1.80      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf(t35_funct_2, axiom,
% 1.59/1.80    (![A:$i,B:$i,C:$i]:
% 1.59/1.80     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.59/1.80         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.59/1.80       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.59/1.80         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.59/1.80           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 1.59/1.80             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 1.59/1.80  thf('100', plain,
% 1.59/1.80      (![X48 : $i, X49 : $i, X50 : $i]:
% 1.59/1.80         (((X48) = (k1_xboole_0))
% 1.59/1.80          | ~ (v1_funct_1 @ X49)
% 1.59/1.80          | ~ (v1_funct_2 @ X49 @ X50 @ X48)
% 1.59/1.80          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X48)))
% 1.59/1.80          | ((k5_relat_1 @ X49 @ (k2_funct_1 @ X49)) = (k6_partfun1 @ X50))
% 1.59/1.80          | ~ (v2_funct_1 @ X49)
% 1.59/1.80          | ((k2_relset_1 @ X50 @ X48 @ X49) != (X48)))),
% 1.59/1.80      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.59/1.80  thf('101', plain,
% 1.59/1.80      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.59/1.80        | ~ (v2_funct_1 @ sk_C)
% 1.59/1.80        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 1.59/1.80        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.59/1.80        | ~ (v1_funct_1 @ sk_C)
% 1.59/1.80        | ((sk_B) = (k1_xboole_0)))),
% 1.59/1.80      inference('sup-', [status(thm)], ['99', '100'])).
% 1.59/1.80  thf('102', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('103', plain, ((v2_funct_1 @ sk_C)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('104', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('105', plain, ((v1_funct_1 @ sk_C)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('106', plain,
% 1.59/1.80      ((((sk_B) != (sk_B))
% 1.59/1.80        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 1.59/1.80        | ((sk_B) = (k1_xboole_0)))),
% 1.59/1.80      inference('demod', [status(thm)], ['101', '102', '103', '104', '105'])).
% 1.59/1.80  thf('107', plain,
% 1.59/1.80      ((((sk_B) = (k1_xboole_0))
% 1.59/1.80        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 1.59/1.80      inference('simplify', [status(thm)], ['106'])).
% 1.59/1.80  thf('108', plain, (((sk_B) != (k1_xboole_0))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('109', plain,
% 1.59/1.80      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 1.59/1.80      inference('simplify_reflect-', [status(thm)], ['107', '108'])).
% 1.59/1.80  thf(t58_funct_1, axiom,
% 1.59/1.80    (![A:$i]:
% 1.59/1.80     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.59/1.80       ( ( v2_funct_1 @ A ) =>
% 1.59/1.80         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 1.59/1.80             ( k1_relat_1 @ A ) ) & 
% 1.59/1.80           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 1.59/1.80             ( k1_relat_1 @ A ) ) ) ) ))).
% 1.59/1.80  thf('110', plain,
% 1.59/1.80      (![X11 : $i]:
% 1.59/1.80         (~ (v2_funct_1 @ X11)
% 1.59/1.80          | ((k2_relat_1 @ (k5_relat_1 @ X11 @ (k2_funct_1 @ X11)))
% 1.59/1.80              = (k1_relat_1 @ X11))
% 1.59/1.80          | ~ (v1_funct_1 @ X11)
% 1.59/1.80          | ~ (v1_relat_1 @ X11))),
% 1.59/1.80      inference('cnf', [status(esa)], [t58_funct_1])).
% 1.59/1.80  thf('111', plain,
% 1.59/1.80      ((((k2_relat_1 @ (k6_partfun1 @ sk_A)) = (k1_relat_1 @ sk_C))
% 1.59/1.80        | ~ (v1_relat_1 @ sk_C)
% 1.59/1.80        | ~ (v1_funct_1 @ sk_C)
% 1.59/1.80        | ~ (v2_funct_1 @ sk_C))),
% 1.59/1.80      inference('sup+', [status(thm)], ['109', '110'])).
% 1.59/1.80  thf(t71_relat_1, axiom,
% 1.59/1.80    (![A:$i]:
% 1.59/1.80     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.59/1.80       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.59/1.80  thf('112', plain, (![X5 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 1.59/1.80      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.59/1.80  thf('113', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 1.59/1.80      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.59/1.80  thf('114', plain, (![X5 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X5)) = (X5))),
% 1.59/1.80      inference('demod', [status(thm)], ['112', '113'])).
% 1.59/1.80  thf('115', plain, ((v1_relat_1 @ sk_C)),
% 1.59/1.80      inference('demod', [status(thm)], ['46', '47'])).
% 1.59/1.80  thf('116', plain, ((v1_funct_1 @ sk_C)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('117', plain, ((v2_funct_1 @ sk_C)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('118', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 1.59/1.80      inference('demod', [status(thm)], ['111', '114', '115', '116', '117'])).
% 1.59/1.80  thf('119', plain, ((v1_relat_1 @ sk_C)),
% 1.59/1.80      inference('demod', [status(thm)], ['46', '47'])).
% 1.59/1.80  thf('120', plain, ((v1_funct_1 @ sk_C)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('121', plain, ((v2_funct_1 @ sk_C)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('122', plain,
% 1.59/1.80      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.59/1.80        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.59/1.80      inference('demod', [status(thm)], ['98', '118', '119', '120', '121'])).
% 1.59/1.80  thf('123', plain,
% 1.59/1.80      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('124', plain,
% 1.59/1.80      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.59/1.80         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 1.59/1.80          | ~ (v1_funct_1 @ X22)
% 1.59/1.80          | ~ (v1_funct_1 @ X25)
% 1.59/1.80          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 1.59/1.80          | (v1_funct_1 @ (k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25)))),
% 1.59/1.80      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.59/1.80  thf('125', plain,
% 1.59/1.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.59/1.80         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0))
% 1.59/1.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ sk_C))),
% 1.59/1.80      inference('sup-', [status(thm)], ['123', '124'])).
% 1.59/1.80  thf('126', plain, ((v1_funct_1 @ sk_C)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('127', plain,
% 1.59/1.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.59/1.80         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0))
% 1.59/1.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.59/1.80          | ~ (v1_funct_1 @ X0))),
% 1.59/1.80      inference('demod', [status(thm)], ['125', '126'])).
% 1.59/1.80  thf('128', plain,
% 1.59/1.80      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.59/1.80        | (v1_funct_1 @ 
% 1.59/1.80           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ 
% 1.59/1.80            (k2_funct_1 @ sk_C))))),
% 1.59/1.80      inference('sup-', [status(thm)], ['122', '127'])).
% 1.59/1.80  thf('129', plain,
% 1.59/1.80      (![X7 : $i]:
% 1.59/1.80         ((v1_funct_1 @ (k2_funct_1 @ X7))
% 1.59/1.80          | ~ (v1_funct_1 @ X7)
% 1.59/1.80          | ~ (v1_relat_1 @ X7))),
% 1.59/1.80      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.59/1.80  thf('130', plain,
% 1.59/1.80      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.59/1.80        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.59/1.80      inference('demod', [status(thm)], ['98', '118', '119', '120', '121'])).
% 1.59/1.80  thf('131', plain,
% 1.59/1.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.59/1.80         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.59/1.80            = (k5_relat_1 @ sk_C @ X0))
% 1.59/1.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.59/1.80          | ~ (v1_funct_1 @ X0))),
% 1.59/1.80      inference('demod', [status(thm)], ['4', '5'])).
% 1.59/1.80  thf('132', plain,
% 1.59/1.80      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.59/1.80        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ 
% 1.59/1.80            (k2_funct_1 @ sk_C)) = (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))))),
% 1.59/1.80      inference('sup-', [status(thm)], ['130', '131'])).
% 1.59/1.80  thf('133', plain,
% 1.59/1.80      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 1.59/1.80      inference('simplify_reflect-', [status(thm)], ['107', '108'])).
% 1.59/1.80  thf('134', plain,
% 1.59/1.80      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.59/1.80        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ 
% 1.59/1.80            (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 1.59/1.80      inference('demod', [status(thm)], ['132', '133'])).
% 1.59/1.80  thf('135', plain,
% 1.59/1.80      ((~ (v1_relat_1 @ sk_C)
% 1.59/1.80        | ~ (v1_funct_1 @ sk_C)
% 1.59/1.80        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ 
% 1.59/1.80            (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 1.59/1.80      inference('sup-', [status(thm)], ['129', '134'])).
% 1.59/1.80  thf('136', plain, ((v1_relat_1 @ sk_C)),
% 1.59/1.80      inference('demod', [status(thm)], ['46', '47'])).
% 1.59/1.80  thf('137', plain, ((v1_funct_1 @ sk_C)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('138', plain,
% 1.59/1.80      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ (k2_funct_1 @ sk_C))
% 1.59/1.80         = (k6_partfun1 @ sk_A))),
% 1.59/1.80      inference('demod', [status(thm)], ['135', '136', '137'])).
% 1.59/1.80  thf('139', plain,
% 1.59/1.80      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.59/1.80        | (v1_funct_1 @ (k6_partfun1 @ sk_A)))),
% 1.59/1.80      inference('demod', [status(thm)], ['128', '138'])).
% 1.59/1.80  thf('140', plain,
% 1.59/1.80      ((~ (v1_relat_1 @ sk_C)
% 1.59/1.80        | ~ (v1_funct_1 @ sk_C)
% 1.59/1.80        | (v1_funct_1 @ (k6_partfun1 @ sk_A)))),
% 1.59/1.80      inference('sup-', [status(thm)], ['81', '139'])).
% 1.59/1.80  thf('141', plain, ((v1_relat_1 @ sk_C)),
% 1.59/1.80      inference('demod', [status(thm)], ['46', '47'])).
% 1.59/1.80  thf('142', plain, ((v1_funct_1 @ sk_C)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('143', plain, ((v1_funct_1 @ (k6_partfun1 @ sk_A))),
% 1.59/1.80      inference('demod', [status(thm)], ['140', '141', '142'])).
% 1.59/1.80  thf('144', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 1.59/1.80      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.59/1.80  thf('145', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 1.59/1.80      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.59/1.80  thf('146', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 1.59/1.80      inference('demod', [status(thm)], ['144', '145'])).
% 1.59/1.80  thf(t78_relat_1, axiom,
% 1.59/1.80    (![A:$i]:
% 1.59/1.80     ( ( v1_relat_1 @ A ) =>
% 1.59/1.80       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 1.59/1.80  thf('147', plain,
% 1.59/1.80      (![X6 : $i]:
% 1.59/1.80         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X6)) @ X6) = (X6))
% 1.59/1.80          | ~ (v1_relat_1 @ X6))),
% 1.59/1.80      inference('cnf', [status(esa)], [t78_relat_1])).
% 1.59/1.80  thf('148', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 1.59/1.80      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.59/1.80  thf('149', plain,
% 1.59/1.80      (![X6 : $i]:
% 1.59/1.80         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X6)) @ X6) = (X6))
% 1.59/1.80          | ~ (v1_relat_1 @ X6))),
% 1.59/1.80      inference('demod', [status(thm)], ['147', '148'])).
% 1.59/1.80  thf('150', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 1.59/1.80            = (k6_partfun1 @ X0))
% 1.59/1.80          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 1.59/1.80      inference('sup+', [status(thm)], ['146', '149'])).
% 1.59/1.80  thf('151', plain,
% 1.59/1.80      (![X21 : $i]:
% 1.59/1.80         (m1_subset_1 @ (k6_partfun1 @ X21) @ 
% 1.59/1.80          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 1.59/1.80      inference('demod', [status(thm)], ['24', '25'])).
% 1.59/1.80  thf('152', plain,
% 1.59/1.80      (![X0 : $i, X1 : $i]:
% 1.59/1.80         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.59/1.80          | (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X1))),
% 1.59/1.80      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.59/1.80  thf('153', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X0))
% 1.59/1.80          | (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 1.59/1.80      inference('sup-', [status(thm)], ['151', '152'])).
% 1.59/1.80  thf('154', plain,
% 1.59/1.80      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.59/1.80      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.59/1.80  thf('155', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.59/1.80      inference('demod', [status(thm)], ['153', '154'])).
% 1.59/1.80  thf('156', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 1.59/1.80           = (k6_partfun1 @ X0))),
% 1.59/1.80      inference('demod', [status(thm)], ['150', '155'])).
% 1.59/1.80  thf(t53_funct_1, axiom,
% 1.59/1.80    (![A:$i]:
% 1.59/1.80     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.59/1.80       ( ( ?[B:$i]:
% 1.59/1.80           ( ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.59/1.80             ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) ) =>
% 1.59/1.80         ( v2_funct_1 @ A ) ) ))).
% 1.59/1.80  thf('157', plain,
% 1.59/1.80      (![X8 : $i, X9 : $i]:
% 1.59/1.80         (~ (v1_relat_1 @ X8)
% 1.59/1.80          | ~ (v1_funct_1 @ X8)
% 1.59/1.80          | ((k5_relat_1 @ X9 @ X8) != (k6_relat_1 @ (k1_relat_1 @ X9)))
% 1.59/1.80          | (v2_funct_1 @ X9)
% 1.59/1.80          | ~ (v1_funct_1 @ X9)
% 1.59/1.80          | ~ (v1_relat_1 @ X9))),
% 1.59/1.80      inference('cnf', [status(esa)], [t53_funct_1])).
% 1.59/1.80  thf('158', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 1.59/1.80      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.59/1.80  thf('159', plain,
% 1.59/1.80      (![X8 : $i, X9 : $i]:
% 1.59/1.80         (~ (v1_relat_1 @ X8)
% 1.59/1.80          | ~ (v1_funct_1 @ X8)
% 1.59/1.80          | ((k5_relat_1 @ X9 @ X8) != (k6_partfun1 @ (k1_relat_1 @ X9)))
% 1.59/1.80          | (v2_funct_1 @ X9)
% 1.59/1.80          | ~ (v1_funct_1 @ X9)
% 1.59/1.80          | ~ (v1_relat_1 @ X9))),
% 1.59/1.80      inference('demod', [status(thm)], ['157', '158'])).
% 1.59/1.80  thf('160', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (((k6_partfun1 @ X0)
% 1.59/1.80            != (k6_partfun1 @ (k1_relat_1 @ (k6_partfun1 @ X0))))
% 1.59/1.80          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 1.59/1.80          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 1.59/1.80          | (v2_funct_1 @ (k6_partfun1 @ X0))
% 1.59/1.80          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 1.59/1.80          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 1.59/1.80      inference('sup-', [status(thm)], ['156', '159'])).
% 1.59/1.80  thf('161', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 1.59/1.80      inference('demod', [status(thm)], ['144', '145'])).
% 1.59/1.80  thf('162', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.59/1.80      inference('demod', [status(thm)], ['153', '154'])).
% 1.59/1.80  thf('163', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.59/1.80      inference('demod', [status(thm)], ['153', '154'])).
% 1.59/1.80  thf('164', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (((k6_partfun1 @ X0) != (k6_partfun1 @ X0))
% 1.59/1.80          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 1.59/1.80          | (v2_funct_1 @ (k6_partfun1 @ X0))
% 1.59/1.80          | ~ (v1_funct_1 @ (k6_partfun1 @ X0)))),
% 1.59/1.80      inference('demod', [status(thm)], ['160', '161', '162', '163'])).
% 1.59/1.80  thf('165', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         ((v2_funct_1 @ (k6_partfun1 @ X0))
% 1.59/1.80          | ~ (v1_funct_1 @ (k6_partfun1 @ X0)))),
% 1.59/1.80      inference('simplify', [status(thm)], ['164'])).
% 1.59/1.80  thf('166', plain, ((v2_funct_1 @ (k6_partfun1 @ sk_A))),
% 1.59/1.80      inference('sup-', [status(thm)], ['143', '165'])).
% 1.59/1.80  thf('167', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('168', plain,
% 1.59/1.80      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('169', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('170', plain, ((v1_funct_1 @ sk_C)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('171', plain,
% 1.59/1.80      (((zip_tseitin_0 @ sk_D @ sk_C)
% 1.59/1.80        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.59/1.80        | ((sk_B) != (sk_B)))),
% 1.59/1.80      inference('demod', [status(thm)],
% 1.59/1.80                ['80', '166', '167', '168', '169', '170'])).
% 1.59/1.80  thf('172', plain,
% 1.59/1.80      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 1.59/1.80      inference('simplify', [status(thm)], ['171'])).
% 1.59/1.80  thf('173', plain,
% 1.59/1.80      (![X41 : $i, X42 : $i]:
% 1.59/1.80         (((X41) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X41 @ X42))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.59/1.80  thf('174', plain,
% 1.59/1.80      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 1.59/1.80      inference('sup-', [status(thm)], ['172', '173'])).
% 1.59/1.80  thf('175', plain, (((sk_A) != (k1_xboole_0))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('176', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 1.59/1.80      inference('simplify_reflect-', [status(thm)], ['174', '175'])).
% 1.59/1.80  thf('177', plain,
% 1.59/1.80      (![X39 : $i, X40 : $i]:
% 1.59/1.80         ((v2_funct_1 @ X40) | ~ (zip_tseitin_0 @ X40 @ X39))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.59/1.80  thf('178', plain, ((v2_funct_1 @ sk_D)),
% 1.59/1.80      inference('sup-', [status(thm)], ['176', '177'])).
% 1.59/1.80  thf('179', plain,
% 1.59/1.80      ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (k1_relat_1 @ sk_D)))),
% 1.59/1.80      inference('demod', [status(thm)], ['72', '178'])).
% 1.59/1.80  thf('180', plain,
% 1.59/1.80      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('181', plain,
% 1.59/1.80      (![X48 : $i, X49 : $i, X50 : $i]:
% 1.59/1.80         (((X48) = (k1_xboole_0))
% 1.59/1.80          | ~ (v1_funct_1 @ X49)
% 1.59/1.80          | ~ (v1_funct_2 @ X49 @ X50 @ X48)
% 1.59/1.80          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X48)))
% 1.59/1.80          | ((k5_relat_1 @ X49 @ (k2_funct_1 @ X49)) = (k6_partfun1 @ X50))
% 1.59/1.80          | ~ (v2_funct_1 @ X49)
% 1.59/1.80          | ((k2_relset_1 @ X50 @ X48 @ X49) != (X48)))),
% 1.59/1.80      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.59/1.80  thf('182', plain,
% 1.59/1.80      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 1.59/1.80        | ~ (v2_funct_1 @ sk_D)
% 1.59/1.80        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.59/1.80        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.59/1.80        | ~ (v1_funct_1 @ sk_D)
% 1.59/1.80        | ((sk_A) = (k1_xboole_0)))),
% 1.59/1.80      inference('sup-', [status(thm)], ['180', '181'])).
% 1.59/1.80  thf('183', plain,
% 1.59/1.80      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.59/1.80      inference('sup-', [status(thm)], ['64', '65'])).
% 1.59/1.80  thf('184', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('185', plain, ((v1_funct_1 @ sk_D)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('186', plain,
% 1.59/1.80      ((((k2_relat_1 @ sk_D) != (sk_A))
% 1.59/1.80        | ~ (v2_funct_1 @ sk_D)
% 1.59/1.80        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.59/1.80        | ((sk_A) = (k1_xboole_0)))),
% 1.59/1.80      inference('demod', [status(thm)], ['182', '183', '184', '185'])).
% 1.59/1.80  thf('187', plain, (((sk_A) != (k1_xboole_0))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('188', plain,
% 1.59/1.80      ((((k2_relat_1 @ sk_D) != (sk_A))
% 1.59/1.80        | ~ (v2_funct_1 @ sk_D)
% 1.59/1.80        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 1.59/1.80      inference('simplify_reflect-', [status(thm)], ['186', '187'])).
% 1.59/1.80  thf('189', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.59/1.80      inference('demod', [status(thm)], ['59', '63', '66', '67', '68', '69'])).
% 1.59/1.80  thf('190', plain,
% 1.59/1.80      ((((sk_A) != (sk_A))
% 1.59/1.80        | ~ (v2_funct_1 @ sk_D)
% 1.59/1.80        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 1.59/1.80      inference('demod', [status(thm)], ['188', '189'])).
% 1.59/1.80  thf('191', plain,
% 1.59/1.80      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.59/1.80        | ~ (v2_funct_1 @ sk_D))),
% 1.59/1.80      inference('simplify', [status(thm)], ['190'])).
% 1.59/1.80  thf('192', plain, ((v2_funct_1 @ sk_D)),
% 1.59/1.80      inference('sup-', [status(thm)], ['176', '177'])).
% 1.59/1.80  thf('193', plain,
% 1.59/1.80      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 1.59/1.80      inference('demod', [status(thm)], ['191', '192'])).
% 1.59/1.80  thf('194', plain,
% 1.59/1.80      (![X11 : $i]:
% 1.59/1.80         (~ (v2_funct_1 @ X11)
% 1.59/1.80          | ((k2_relat_1 @ (k5_relat_1 @ X11 @ (k2_funct_1 @ X11)))
% 1.59/1.80              = (k1_relat_1 @ X11))
% 1.59/1.80          | ~ (v1_funct_1 @ X11)
% 1.59/1.80          | ~ (v1_relat_1 @ X11))),
% 1.59/1.80      inference('cnf', [status(esa)], [t58_funct_1])).
% 1.59/1.80  thf('195', plain,
% 1.59/1.80      ((((k2_relat_1 @ (k6_partfun1 @ sk_B)) = (k1_relat_1 @ sk_D))
% 1.59/1.80        | ~ (v1_relat_1 @ sk_D)
% 1.59/1.80        | ~ (v1_funct_1 @ sk_D)
% 1.59/1.80        | ~ (v2_funct_1 @ sk_D))),
% 1.59/1.80      inference('sup+', [status(thm)], ['193', '194'])).
% 1.59/1.80  thf('196', plain, (![X5 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X5)) = (X5))),
% 1.59/1.80      inference('demod', [status(thm)], ['112', '113'])).
% 1.59/1.80  thf('197', plain, ((v1_relat_1 @ sk_D)),
% 1.59/1.80      inference('demod', [status(thm)], ['34', '35'])).
% 1.59/1.80  thf('198', plain, ((v1_funct_1 @ sk_D)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('199', plain, ((v2_funct_1 @ sk_D)),
% 1.59/1.80      inference('sup-', [status(thm)], ['176', '177'])).
% 1.59/1.80  thf('200', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.59/1.80      inference('demod', [status(thm)], ['195', '196', '197', '198', '199'])).
% 1.59/1.80  thf('201', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (sk_B)))),
% 1.59/1.80      inference('demod', [status(thm)], ['179', '200'])).
% 1.59/1.80  thf('202', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.59/1.80      inference('simplify', [status(thm)], ['201'])).
% 1.59/1.80  thf('203', plain,
% 1.59/1.80      (![X10 : $i]:
% 1.59/1.80         (~ (v2_funct_1 @ X10)
% 1.59/1.80          | ((k2_relat_1 @ X10) = (k1_relat_1 @ (k2_funct_1 @ X10)))
% 1.59/1.80          | ~ (v1_funct_1 @ X10)
% 1.59/1.80          | ~ (v1_relat_1 @ X10))),
% 1.59/1.80      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.59/1.80  thf('204', plain,
% 1.59/1.80      (![X7 : $i]:
% 1.59/1.80         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 1.59/1.80          | ~ (v1_funct_1 @ X7)
% 1.59/1.80          | ~ (v1_relat_1 @ X7))),
% 1.59/1.80      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.59/1.80  thf('205', plain,
% 1.59/1.80      (![X7 : $i]:
% 1.59/1.80         ((v1_funct_1 @ (k2_funct_1 @ X7))
% 1.59/1.80          | ~ (v1_funct_1 @ X7)
% 1.59/1.80          | ~ (v1_relat_1 @ X7))),
% 1.59/1.80      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.59/1.80  thf('206', plain,
% 1.59/1.80      (![X51 : $i]:
% 1.59/1.80         ((m1_subset_1 @ X51 @ 
% 1.59/1.80           (k1_zfmisc_1 @ 
% 1.59/1.80            (k2_zfmisc_1 @ (k1_relat_1 @ X51) @ (k2_relat_1 @ X51))))
% 1.59/1.80          | ~ (v1_funct_1 @ X51)
% 1.59/1.80          | ~ (v1_relat_1 @ X51))),
% 1.59/1.80      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.59/1.80  thf('207', plain,
% 1.59/1.80      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.59/1.80         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 1.59/1.80          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.59/1.80      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.59/1.80  thf('208', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (~ (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.59/1.80              = (k2_relat_1 @ X0)))),
% 1.59/1.80      inference('sup-', [status(thm)], ['206', '207'])).
% 1.59/1.80  thf('209', plain,
% 1.59/1.80      (![X51 : $i]:
% 1.59/1.80         ((v1_funct_2 @ X51 @ (k1_relat_1 @ X51) @ (k2_relat_1 @ X51))
% 1.59/1.80          | ~ (v1_funct_1 @ X51)
% 1.59/1.80          | ~ (v1_relat_1 @ X51))),
% 1.59/1.80      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.59/1.80  thf('210', plain,
% 1.59/1.80      (![X51 : $i]:
% 1.59/1.80         ((m1_subset_1 @ X51 @ 
% 1.59/1.80           (k1_zfmisc_1 @ 
% 1.59/1.80            (k2_zfmisc_1 @ (k1_relat_1 @ X51) @ (k2_relat_1 @ X51))))
% 1.59/1.80          | ~ (v1_funct_1 @ X51)
% 1.59/1.80          | ~ (v1_relat_1 @ X51))),
% 1.59/1.80      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.59/1.80  thf('211', plain,
% 1.59/1.80      (![X48 : $i, X49 : $i, X50 : $i]:
% 1.59/1.80         (((X48) = (k1_xboole_0))
% 1.59/1.80          | ~ (v1_funct_1 @ X49)
% 1.59/1.80          | ~ (v1_funct_2 @ X49 @ X50 @ X48)
% 1.59/1.80          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X48)))
% 1.59/1.80          | ((k5_relat_1 @ (k2_funct_1 @ X49) @ X49) = (k6_partfun1 @ X48))
% 1.59/1.80          | ~ (v2_funct_1 @ X49)
% 1.59/1.80          | ((k2_relset_1 @ X50 @ X48 @ X49) != (X48)))),
% 1.59/1.80      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.59/1.80  thf('212', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (~ (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.59/1.80              != (k2_relat_1 @ X0))
% 1.59/1.80          | ~ (v2_funct_1 @ X0)
% 1.59/1.80          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 1.59/1.80              = (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.59/1.80          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 1.59/1.80      inference('sup-', [status(thm)], ['210', '211'])).
% 1.59/1.80  thf('213', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.59/1.80          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 1.59/1.80          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 1.59/1.80              = (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.59/1.80          | ~ (v2_funct_1 @ X0)
% 1.59/1.80          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.59/1.80              != (k2_relat_1 @ X0))
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X0))),
% 1.59/1.80      inference('simplify', [status(thm)], ['212'])).
% 1.59/1.80  thf('214', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (~ (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.59/1.80              != (k2_relat_1 @ X0))
% 1.59/1.80          | ~ (v2_funct_1 @ X0)
% 1.59/1.80          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 1.59/1.80              = (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.59/1.80          | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 1.59/1.80      inference('sup-', [status(thm)], ['209', '213'])).
% 1.59/1.80  thf('215', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.59/1.80          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 1.59/1.80              = (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.59/1.80          | ~ (v2_funct_1 @ X0)
% 1.59/1.80          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.59/1.80              != (k2_relat_1 @ X0))
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X0))),
% 1.59/1.80      inference('simplify', [status(thm)], ['214'])).
% 1.59/1.80  thf('216', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (((k2_relat_1 @ X0) != (k2_relat_1 @ X0))
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v2_funct_1 @ X0)
% 1.59/1.80          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 1.59/1.80              = (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.59/1.80          | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 1.59/1.80      inference('sup-', [status(thm)], ['208', '215'])).
% 1.59/1.80  thf('217', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.59/1.80          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 1.59/1.80              = (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.59/1.80          | ~ (v2_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0))),
% 1.59/1.80      inference('simplify', [status(thm)], ['216'])).
% 1.59/1.80  thf('218', plain,
% 1.59/1.80      (![X7 : $i]:
% 1.59/1.80         ((v1_funct_1 @ (k2_funct_1 @ X7))
% 1.59/1.80          | ~ (v1_funct_1 @ X7)
% 1.59/1.80          | ~ (v1_relat_1 @ X7))),
% 1.59/1.80      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.59/1.80  thf('219', plain,
% 1.59/1.80      (![X7 : $i]:
% 1.59/1.80         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 1.59/1.80          | ~ (v1_funct_1 @ X7)
% 1.59/1.80          | ~ (v1_relat_1 @ X7))),
% 1.59/1.80      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.59/1.80  thf('220', plain,
% 1.59/1.80      (![X10 : $i]:
% 1.59/1.80         (~ (v2_funct_1 @ X10)
% 1.59/1.80          | ((k2_relat_1 @ X10) = (k1_relat_1 @ (k2_funct_1 @ X10)))
% 1.59/1.80          | ~ (v1_funct_1 @ X10)
% 1.59/1.80          | ~ (v1_relat_1 @ X10))),
% 1.59/1.80      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.59/1.80  thf('221', plain,
% 1.59/1.80      (![X8 : $i, X9 : $i]:
% 1.59/1.80         (~ (v1_relat_1 @ X8)
% 1.59/1.80          | ~ (v1_funct_1 @ X8)
% 1.59/1.80          | ((k5_relat_1 @ X9 @ X8) != (k6_partfun1 @ (k1_relat_1 @ X9)))
% 1.59/1.80          | (v2_funct_1 @ X9)
% 1.59/1.80          | ~ (v1_funct_1 @ X9)
% 1.59/1.80          | ~ (v1_relat_1 @ X9))),
% 1.59/1.80      inference('demod', [status(thm)], ['157', '158'])).
% 1.59/1.80  thf('222', plain,
% 1.59/1.80      (![X0 : $i, X1 : $i]:
% 1.59/1.80         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X1)
% 1.59/1.80            != (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.59/1.80          | ~ (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v2_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.59/1.80          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.59/1.80          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.59/1.80          | ~ (v1_funct_1 @ X1)
% 1.59/1.80          | ~ (v1_relat_1 @ X1))),
% 1.59/1.80      inference('sup-', [status(thm)], ['220', '221'])).
% 1.59/1.80  thf('223', plain,
% 1.59/1.80      (![X0 : $i, X1 : $i]:
% 1.59/1.80         (~ (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X1)
% 1.59/1.80          | ~ (v1_funct_1 @ X1)
% 1.59/1.80          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.59/1.80          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.59/1.80          | ~ (v2_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X0)
% 1.59/1.80          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X1)
% 1.59/1.80              != (k6_partfun1 @ (k2_relat_1 @ X0))))),
% 1.59/1.80      inference('sup-', [status(thm)], ['219', '222'])).
% 1.59/1.80  thf('224', plain,
% 1.59/1.80      (![X0 : $i, X1 : $i]:
% 1.59/1.80         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X1)
% 1.59/1.80            != (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.59/1.80          | ~ (v2_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.59/1.80          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.59/1.80          | ~ (v1_funct_1 @ X1)
% 1.59/1.80          | ~ (v1_relat_1 @ X1)
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X0))),
% 1.59/1.80      inference('simplify', [status(thm)], ['223'])).
% 1.59/1.80  thf('225', plain,
% 1.59/1.80      (![X0 : $i, X1 : $i]:
% 1.59/1.80         (~ (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X1)
% 1.59/1.80          | ~ (v1_funct_1 @ X1)
% 1.59/1.80          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.59/1.80          | ~ (v2_funct_1 @ X0)
% 1.59/1.80          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X1)
% 1.59/1.80              != (k6_partfun1 @ (k2_relat_1 @ X0))))),
% 1.59/1.80      inference('sup-', [status(thm)], ['218', '224'])).
% 1.59/1.80  thf('226', plain,
% 1.59/1.80      (![X0 : $i, X1 : $i]:
% 1.59/1.80         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X1)
% 1.59/1.80            != (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.59/1.80          | ~ (v2_funct_1 @ X0)
% 1.59/1.80          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.59/1.80          | ~ (v1_funct_1 @ X1)
% 1.59/1.80          | ~ (v1_relat_1 @ X1)
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X0))),
% 1.59/1.80      inference('simplify', [status(thm)], ['225'])).
% 1.59/1.80  thf('227', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (((k6_partfun1 @ (k2_relat_1 @ X0))
% 1.59/1.80            != (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v2_funct_1 @ X0)
% 1.59/1.80          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.59/1.80          | ~ (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.59/1.80          | ~ (v2_funct_1 @ X0))),
% 1.59/1.80      inference('sup-', [status(thm)], ['217', '226'])).
% 1.59/1.80  thf('228', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 1.59/1.80          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.59/1.80          | ~ (v2_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0))),
% 1.59/1.80      inference('simplify', [status(thm)], ['227'])).
% 1.59/1.80  thf('229', plain,
% 1.59/1.80      (![X10 : $i]:
% 1.59/1.80         (~ (v2_funct_1 @ X10)
% 1.59/1.80          | ((k1_relat_1 @ X10) = (k2_relat_1 @ (k2_funct_1 @ X10)))
% 1.59/1.80          | ~ (v1_funct_1 @ X10)
% 1.59/1.80          | ~ (v1_relat_1 @ X10))),
% 1.59/1.80      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.59/1.80  thf('230', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (~ (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.59/1.80              = (k2_relat_1 @ X0)))),
% 1.59/1.80      inference('sup-', [status(thm)], ['206', '207'])).
% 1.59/1.80  thf('231', plain,
% 1.59/1.80      (![X51 : $i]:
% 1.59/1.80         ((v1_funct_2 @ X51 @ (k1_relat_1 @ X51) @ (k2_relat_1 @ X51))
% 1.59/1.80          | ~ (v1_funct_1 @ X51)
% 1.59/1.80          | ~ (v1_relat_1 @ X51))),
% 1.59/1.80      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.59/1.80  thf('232', plain,
% 1.59/1.80      (![X51 : $i]:
% 1.59/1.80         ((m1_subset_1 @ X51 @ 
% 1.59/1.80           (k1_zfmisc_1 @ 
% 1.59/1.80            (k2_zfmisc_1 @ (k1_relat_1 @ X51) @ (k2_relat_1 @ X51))))
% 1.59/1.80          | ~ (v1_funct_1 @ X51)
% 1.59/1.80          | ~ (v1_relat_1 @ X51))),
% 1.59/1.80      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.59/1.80  thf('233', plain,
% 1.59/1.80      (![X48 : $i, X49 : $i, X50 : $i]:
% 1.59/1.80         (((X48) = (k1_xboole_0))
% 1.59/1.80          | ~ (v1_funct_1 @ X49)
% 1.59/1.80          | ~ (v1_funct_2 @ X49 @ X50 @ X48)
% 1.59/1.80          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X48)))
% 1.59/1.80          | ((k5_relat_1 @ X49 @ (k2_funct_1 @ X49)) = (k6_partfun1 @ X50))
% 1.59/1.80          | ~ (v2_funct_1 @ X49)
% 1.59/1.80          | ((k2_relset_1 @ X50 @ X48 @ X49) != (X48)))),
% 1.59/1.80      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.59/1.80  thf('234', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (~ (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.59/1.80              != (k2_relat_1 @ X0))
% 1.59/1.80          | ~ (v2_funct_1 @ X0)
% 1.59/1.80          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.59/1.80              = (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.59/1.80          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 1.59/1.80      inference('sup-', [status(thm)], ['232', '233'])).
% 1.59/1.80  thf('235', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.59/1.80          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 1.59/1.80          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.59/1.80              = (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.59/1.80          | ~ (v2_funct_1 @ X0)
% 1.59/1.80          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.59/1.80              != (k2_relat_1 @ X0))
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X0))),
% 1.59/1.80      inference('simplify', [status(thm)], ['234'])).
% 1.59/1.80  thf('236', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (~ (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.59/1.80              != (k2_relat_1 @ X0))
% 1.59/1.80          | ~ (v2_funct_1 @ X0)
% 1.59/1.80          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.59/1.80              = (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.59/1.80          | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 1.59/1.80      inference('sup-', [status(thm)], ['231', '235'])).
% 1.59/1.80  thf('237', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.59/1.80          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.59/1.80              = (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.59/1.80          | ~ (v2_funct_1 @ X0)
% 1.59/1.80          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.59/1.80              != (k2_relat_1 @ X0))
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X0))),
% 1.59/1.80      inference('simplify', [status(thm)], ['236'])).
% 1.59/1.80  thf('238', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (((k2_relat_1 @ X0) != (k2_relat_1 @ X0))
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v2_funct_1 @ X0)
% 1.59/1.80          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.59/1.80              = (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.59/1.80          | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 1.59/1.80      inference('sup-', [status(thm)], ['230', '237'])).
% 1.59/1.80  thf('239', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.59/1.80          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 1.59/1.80              = (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.59/1.80          | ~ (v2_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0))),
% 1.59/1.80      inference('simplify', [status(thm)], ['238'])).
% 1.59/1.80  thf('240', plain,
% 1.59/1.80      (![X12 : $i, X13 : $i]:
% 1.59/1.80         (~ (v1_relat_1 @ X12)
% 1.59/1.80          | ~ (v1_funct_1 @ X12)
% 1.59/1.80          | ((X12) = (k2_funct_1 @ X13))
% 1.59/1.80          | ((k5_relat_1 @ X12 @ X13) != (k6_partfun1 @ (k2_relat_1 @ X13)))
% 1.59/1.80          | ((k2_relat_1 @ X12) != (k1_relat_1 @ X13))
% 1.59/1.80          | ~ (v2_funct_1 @ X13)
% 1.59/1.80          | ~ (v1_funct_1 @ X13)
% 1.59/1.80          | ~ (v1_relat_1 @ X13))),
% 1.59/1.80      inference('demod', [status(thm)], ['28', '29'])).
% 1.59/1.80  thf('241', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (((k6_partfun1 @ (k1_relat_1 @ X0))
% 1.59/1.80            != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v2_funct_1 @ X0)
% 1.59/1.80          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.59/1.80          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.59/1.80          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.59/1.80          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.59/1.80          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.59/1.80          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X0))),
% 1.59/1.80      inference('sup-', [status(thm)], ['239', '240'])).
% 1.59/1.80  thf('242', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.59/1.80          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.59/1.80          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.59/1.80          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.59/1.80          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.59/1.80          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.59/1.80          | ~ (v2_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ((k6_partfun1 @ (k1_relat_1 @ X0))
% 1.59/1.80              != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 1.59/1.80      inference('simplify', [status(thm)], ['241'])).
% 1.59/1.80  thf('243', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (((k6_partfun1 @ (k1_relat_1 @ X0))
% 1.59/1.80            != (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.59/1.80          | ~ (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v2_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v2_funct_1 @ X0)
% 1.59/1.80          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.59/1.80          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.59/1.80          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.59/1.80          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.59/1.80          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.59/1.80          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 1.59/1.80      inference('sup-', [status(thm)], ['229', '242'])).
% 1.59/1.80  thf('244', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.59/1.80          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.59/1.80          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.59/1.80          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.59/1.80          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.59/1.80          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.59/1.80          | ~ (v2_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X0))),
% 1.59/1.80      inference('simplify', [status(thm)], ['243'])).
% 1.59/1.80  thf('245', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v2_funct_1 @ X0)
% 1.59/1.80          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.59/1.80          | ~ (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v2_funct_1 @ X0)
% 1.59/1.80          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.59/1.80          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.59/1.80          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.59/1.80          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.59/1.80          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 1.59/1.80      inference('sup-', [status(thm)], ['228', '244'])).
% 1.59/1.80  thf('246', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.59/1.80          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.59/1.80          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.59/1.80          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.59/1.80          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.59/1.80          | ~ (v2_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0))),
% 1.59/1.80      inference('simplify', [status(thm)], ['245'])).
% 1.59/1.80  thf('247', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (~ (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v2_funct_1 @ X0)
% 1.59/1.80          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.59/1.80          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.59/1.80          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.59/1.80          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 1.59/1.80      inference('sup-', [status(thm)], ['205', '246'])).
% 1.59/1.80  thf('248', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.59/1.80          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.59/1.80          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.59/1.80          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.59/1.80          | ~ (v2_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X0))),
% 1.59/1.80      inference('simplify', [status(thm)], ['247'])).
% 1.59/1.80  thf('249', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (~ (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v2_funct_1 @ X0)
% 1.59/1.80          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.59/1.80          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.59/1.80          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 1.59/1.80      inference('sup-', [status(thm)], ['204', '248'])).
% 1.59/1.80  thf('250', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.59/1.80          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.59/1.80          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.59/1.80          | ~ (v2_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X0))),
% 1.59/1.80      inference('simplify', [status(thm)], ['249'])).
% 1.59/1.80  thf('251', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (((k2_relat_1 @ X0) != (k2_relat_1 @ X0))
% 1.59/1.80          | ~ (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v2_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v2_funct_1 @ X0)
% 1.59/1.80          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.59/1.80          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 1.59/1.80      inference('sup-', [status(thm)], ['203', '250'])).
% 1.59/1.80  thf('252', plain,
% 1.59/1.80      (![X0 : $i]:
% 1.59/1.80         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.59/1.80          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.59/1.80          | ~ (v2_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_funct_1 @ X0)
% 1.59/1.80          | ~ (v1_relat_1 @ X0))),
% 1.59/1.80      inference('simplify', [status(thm)], ['251'])).
% 1.59/1.80  thf('253', plain,
% 1.59/1.80      ((((sk_D) = (k2_funct_1 @ sk_C))
% 1.59/1.80        | ~ (v1_relat_1 @ sk_D)
% 1.59/1.80        | ~ (v1_funct_1 @ sk_D)
% 1.59/1.80        | ~ (v2_funct_1 @ sk_D)
% 1.59/1.80        | ((k2_relat_1 @ sk_D) = (k1_xboole_0)))),
% 1.59/1.80      inference('sup+', [status(thm)], ['202', '252'])).
% 1.59/1.80  thf('254', plain, ((v1_relat_1 @ sk_D)),
% 1.59/1.80      inference('demod', [status(thm)], ['34', '35'])).
% 1.59/1.80  thf('255', plain, ((v1_funct_1 @ sk_D)),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('256', plain, ((v2_funct_1 @ sk_D)),
% 1.59/1.80      inference('sup-', [status(thm)], ['176', '177'])).
% 1.59/1.80  thf('257', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.59/1.80      inference('demod', [status(thm)], ['59', '63', '66', '67', '68', '69'])).
% 1.59/1.80  thf('258', plain,
% 1.59/1.80      ((((sk_D) = (k2_funct_1 @ sk_C)) | ((sk_A) = (k1_xboole_0)))),
% 1.59/1.80      inference('demod', [status(thm)], ['253', '254', '255', '256', '257'])).
% 1.59/1.80  thf('259', plain, (((sk_A) != (k1_xboole_0))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('260', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf('261', plain, ($false),
% 1.59/1.80      inference('simplify_reflect-', [status(thm)], ['258', '259', '260'])).
% 1.59/1.80  
% 1.59/1.80  % SZS output end Refutation
% 1.59/1.80  
% 1.59/1.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

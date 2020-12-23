%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0Qywnjm714

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:23 EST 2020

% Result     : Theorem 1.18s
% Output     : Refutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 655 expanded)
%              Number of leaves         :   50 ( 216 expanded)
%              Depth                    :   17
%              Number of atoms          : 1467 (16217 expanded)
%              Number of equality atoms :   97 (1102 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ( ( k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44 )
        = ( k5_relat_1 @ X41 @ X44 ) ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X40 ) ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( X19 = X22 )
      | ~ ( r2_relset_1 @ X20 @ X21 @ X19 @ X22 ) ) ),
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
    ! [X23: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('25',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('26',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( X9
        = ( k2_funct_1 @ X10 ) )
      | ( ( k5_relat_1 @ X9 @ X10 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X10 ) ) )
      | ( ( k2_relat_1 @ X9 )
       != ( k1_relat_1 @ X10 ) )
      | ~ ( v2_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('29',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('30',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( X9
        = ( k2_funct_1 @ X10 ) )
      | ( ( k5_relat_1 @ X9 @ X10 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X10 ) ) )
      | ( ( k2_relat_1 @ X9 )
       != ( k1_relat_1 @ X10 ) )
      | ~ ( v2_funct_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
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

thf('34',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_funct_2 @ X48 @ X49 @ X50 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ~ ( r2_relset_1 @ X49 @ X49 @ ( k1_partfun1 @ X49 @ X50 @ X50 @ X49 @ X48 @ X51 ) @ ( k6_partfun1 @ X49 ) )
      | ( ( k2_relset_1 @ X50 @ X49 @ X51 )
        = X49 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X49 ) ) )
      | ~ ( v1_funct_2 @ X51 @ X50 @ X49 )
      | ~ ( v1_funct_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['32','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('41',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('42',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['39','42','43','44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('50',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('51',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('55',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['39','42','43','44','45'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('59',plain,(
    ! [X4: $i] :
      ( ( ( k10_relat_1 @ X4 @ ( k2_relat_1 @ X4 ) )
        = ( k1_relat_1 @ X4 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('60',plain,
    ( ( ( k10_relat_1 @ sk_D @ sk_A )
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('62',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k8_relset_1 @ X24 @ X25 @ X26 @ X25 )
        = ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('63',plain,
    ( ( k8_relset_1 @ sk_B @ sk_A @ sk_D @ sk_A )
    = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('65',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( ( k8_relset_1 @ X16 @ X17 @ X15 @ X18 )
        = ( k10_relat_1 @ X15 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_B @ sk_A @ sk_D @ X0 )
      = ( k10_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
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

thf('68',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('69',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('70',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('71',plain,(
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

thf('72',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('73',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['74','75'])).

thf('77',plain,
    ( sk_B
    = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['69','76'])).

thf('78',plain,
    ( ( k10_relat_1 @ sk_D @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['63','66','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['49','50'])).

thf('80',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['60','78','79'])).

thf('81',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('84',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('86',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B != sk_B )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['31','46','51','52','57','80','81','86'])).

thf('88',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

thf(t48_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) ) )
           => ( ( v2_funct_1 @ B )
              & ( v2_funct_1 @ A ) ) ) ) ) )).

thf('90',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( v2_funct_1 @ X8 )
      | ( ( k2_relat_1 @ X7 )
       != ( k1_relat_1 @ X8 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('91',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('92',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('93',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('94',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X6 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['49','50'])).

thf('96',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['55','56'])).

thf('98',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['60','78','79'])).

thf('99',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['84','85'])).

thf('101',plain,
    ( ( sk_B != sk_B )
    | ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['91','94','95','96','97','98','99','100'])).

thf('102',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['88','102'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('104',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X11 ) )
        = X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('105',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['49','50'])).

thf('107',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['101'])).

thf('109',plain,
    ( ( k2_funct_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['105','106','107','108'])).

thf('110',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['109','110'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0Qywnjm714
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:22:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.18/1.41  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.18/1.41  % Solved by: fo/fo7.sh
% 1.18/1.41  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.18/1.41  % done 343 iterations in 0.946s
% 1.18/1.41  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.18/1.41  % SZS output start Refutation
% 1.18/1.41  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.18/1.41  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.18/1.41  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.18/1.41  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.18/1.41  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.18/1.41  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.18/1.41  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.18/1.41  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.18/1.41  thf(sk_C_type, type, sk_C: $i).
% 1.18/1.41  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.18/1.41  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.18/1.41  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.18/1.41  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.18/1.41  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.18/1.41  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.18/1.41  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.18/1.41  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 1.18/1.41  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 1.18/1.41  thf(sk_A_type, type, sk_A: $i).
% 1.18/1.41  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.18/1.41  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.18/1.41  thf(sk_B_type, type, sk_B: $i).
% 1.18/1.41  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.18/1.41  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.18/1.41  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.18/1.41  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.18/1.41  thf(sk_D_type, type, sk_D: $i).
% 1.18/1.41  thf(t36_funct_2, conjecture,
% 1.18/1.41    (![A:$i,B:$i,C:$i]:
% 1.18/1.41     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.18/1.41         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.18/1.41       ( ![D:$i]:
% 1.18/1.41         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.18/1.41             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.18/1.41           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.18/1.41               ( r2_relset_1 @
% 1.18/1.41                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.18/1.41                 ( k6_partfun1 @ A ) ) & 
% 1.18/1.41               ( v2_funct_1 @ C ) ) =>
% 1.18/1.41             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.18/1.41               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.18/1.41  thf(zf_stmt_0, negated_conjecture,
% 1.18/1.41    (~( ![A:$i,B:$i,C:$i]:
% 1.18/1.41        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.18/1.41            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.18/1.41          ( ![D:$i]:
% 1.18/1.41            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.18/1.41                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.18/1.41              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.18/1.41                  ( r2_relset_1 @
% 1.18/1.41                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.18/1.41                    ( k6_partfun1 @ A ) ) & 
% 1.18/1.41                  ( v2_funct_1 @ C ) ) =>
% 1.18/1.41                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.18/1.41                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.18/1.41    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.18/1.41  thf('0', plain,
% 1.18/1.41      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.18/1.41        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.18/1.41        (k6_partfun1 @ sk_A))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('1', plain,
% 1.18/1.41      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('2', plain,
% 1.18/1.41      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf(redefinition_k1_partfun1, axiom,
% 1.18/1.41    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.18/1.41     ( ( ( v1_funct_1 @ E ) & 
% 1.18/1.41         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.18/1.41         ( v1_funct_1 @ F ) & 
% 1.18/1.41         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.18/1.41       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.18/1.41  thf('3', plain,
% 1.18/1.41      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 1.18/1.41         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 1.18/1.41          | ~ (v1_funct_1 @ X41)
% 1.18/1.41          | ~ (v1_funct_1 @ X44)
% 1.18/1.41          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 1.18/1.41          | ((k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44)
% 1.18/1.41              = (k5_relat_1 @ X41 @ X44)))),
% 1.18/1.41      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.18/1.41  thf('4', plain,
% 1.18/1.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.18/1.41         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.18/1.41            = (k5_relat_1 @ sk_C @ X0))
% 1.18/1.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.18/1.41          | ~ (v1_funct_1 @ X0)
% 1.18/1.41          | ~ (v1_funct_1 @ sk_C))),
% 1.18/1.41      inference('sup-', [status(thm)], ['2', '3'])).
% 1.18/1.41  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('6', plain,
% 1.18/1.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.18/1.41         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.18/1.41            = (k5_relat_1 @ sk_C @ X0))
% 1.18/1.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.18/1.41          | ~ (v1_funct_1 @ X0))),
% 1.18/1.41      inference('demod', [status(thm)], ['4', '5'])).
% 1.18/1.41  thf('7', plain,
% 1.18/1.41      ((~ (v1_funct_1 @ sk_D)
% 1.18/1.41        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.18/1.41            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.18/1.41      inference('sup-', [status(thm)], ['1', '6'])).
% 1.18/1.41  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('9', plain,
% 1.18/1.41      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.18/1.41         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.18/1.41      inference('demod', [status(thm)], ['7', '8'])).
% 1.18/1.41  thf('10', plain,
% 1.18/1.41      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.18/1.41        (k6_partfun1 @ sk_A))),
% 1.18/1.41      inference('demod', [status(thm)], ['0', '9'])).
% 1.18/1.41  thf('11', plain,
% 1.18/1.41      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('12', plain,
% 1.18/1.41      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf(dt_k1_partfun1, axiom,
% 1.18/1.41    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.18/1.41     ( ( ( v1_funct_1 @ E ) & 
% 1.18/1.41         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.18/1.41         ( v1_funct_1 @ F ) & 
% 1.18/1.41         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.18/1.41       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.18/1.41         ( m1_subset_1 @
% 1.18/1.41           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.18/1.41           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.18/1.41  thf('13', plain,
% 1.18/1.41      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.18/1.41         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 1.18/1.41          | ~ (v1_funct_1 @ X35)
% 1.18/1.41          | ~ (v1_funct_1 @ X38)
% 1.18/1.41          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 1.18/1.41          | (m1_subset_1 @ (k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38) @ 
% 1.18/1.41             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X40))))),
% 1.18/1.41      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.18/1.41  thf('14', plain,
% 1.18/1.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.18/1.41         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.18/1.41           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.18/1.41          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.18/1.41          | ~ (v1_funct_1 @ X1)
% 1.18/1.41          | ~ (v1_funct_1 @ sk_C))),
% 1.18/1.41      inference('sup-', [status(thm)], ['12', '13'])).
% 1.18/1.41  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('16', plain,
% 1.18/1.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.18/1.41         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.18/1.41           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.18/1.41          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.18/1.41          | ~ (v1_funct_1 @ X1))),
% 1.18/1.41      inference('demod', [status(thm)], ['14', '15'])).
% 1.18/1.41  thf('17', plain,
% 1.18/1.41      ((~ (v1_funct_1 @ sk_D)
% 1.18/1.41        | (m1_subset_1 @ 
% 1.18/1.41           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.18/1.41           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.18/1.41      inference('sup-', [status(thm)], ['11', '16'])).
% 1.18/1.41  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('19', plain,
% 1.18/1.41      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.18/1.41         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.18/1.41      inference('demod', [status(thm)], ['7', '8'])).
% 1.18/1.41  thf('20', plain,
% 1.18/1.41      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.18/1.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.18/1.41      inference('demod', [status(thm)], ['17', '18', '19'])).
% 1.18/1.41  thf(redefinition_r2_relset_1, axiom,
% 1.18/1.41    (![A:$i,B:$i,C:$i,D:$i]:
% 1.18/1.41     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.18/1.41         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.18/1.41       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.18/1.41  thf('21', plain,
% 1.18/1.41      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.18/1.41         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.18/1.41          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.18/1.41          | ((X19) = (X22))
% 1.18/1.41          | ~ (r2_relset_1 @ X20 @ X21 @ X19 @ X22))),
% 1.18/1.41      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.18/1.41  thf('22', plain,
% 1.18/1.41      (![X0 : $i]:
% 1.18/1.41         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 1.18/1.41          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 1.18/1.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.18/1.41      inference('sup-', [status(thm)], ['20', '21'])).
% 1.18/1.41  thf('23', plain,
% 1.18/1.41      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.18/1.41           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.18/1.41        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 1.18/1.41      inference('sup-', [status(thm)], ['10', '22'])).
% 1.18/1.41  thf(t29_relset_1, axiom,
% 1.18/1.41    (![A:$i]:
% 1.18/1.41     ( m1_subset_1 @
% 1.18/1.41       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.18/1.41  thf('24', plain,
% 1.18/1.41      (![X23 : $i]:
% 1.18/1.41         (m1_subset_1 @ (k6_relat_1 @ X23) @ 
% 1.18/1.41          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 1.18/1.41      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.18/1.41  thf(redefinition_k6_partfun1, axiom,
% 1.18/1.41    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.18/1.41  thf('25', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 1.18/1.41      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.18/1.41  thf('26', plain,
% 1.18/1.41      (![X23 : $i]:
% 1.18/1.41         (m1_subset_1 @ (k6_partfun1 @ X23) @ 
% 1.18/1.41          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 1.18/1.41      inference('demod', [status(thm)], ['24', '25'])).
% 1.18/1.41  thf('27', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.18/1.41      inference('demod', [status(thm)], ['23', '26'])).
% 1.18/1.41  thf(t64_funct_1, axiom,
% 1.18/1.41    (![A:$i]:
% 1.18/1.41     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.18/1.41       ( ![B:$i]:
% 1.18/1.41         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.18/1.41           ( ( ( v2_funct_1 @ A ) & 
% 1.18/1.41               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 1.18/1.41               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 1.18/1.41             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.18/1.41  thf('28', plain,
% 1.18/1.41      (![X9 : $i, X10 : $i]:
% 1.18/1.41         (~ (v1_relat_1 @ X9)
% 1.18/1.41          | ~ (v1_funct_1 @ X9)
% 1.18/1.41          | ((X9) = (k2_funct_1 @ X10))
% 1.18/1.41          | ((k5_relat_1 @ X9 @ X10) != (k6_relat_1 @ (k2_relat_1 @ X10)))
% 1.18/1.41          | ((k2_relat_1 @ X9) != (k1_relat_1 @ X10))
% 1.18/1.41          | ~ (v2_funct_1 @ X10)
% 1.18/1.41          | ~ (v1_funct_1 @ X10)
% 1.18/1.41          | ~ (v1_relat_1 @ X10))),
% 1.18/1.41      inference('cnf', [status(esa)], [t64_funct_1])).
% 1.18/1.41  thf('29', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 1.18/1.41      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.18/1.41  thf('30', plain,
% 1.18/1.41      (![X9 : $i, X10 : $i]:
% 1.18/1.41         (~ (v1_relat_1 @ X9)
% 1.18/1.41          | ~ (v1_funct_1 @ X9)
% 1.18/1.41          | ((X9) = (k2_funct_1 @ X10))
% 1.18/1.41          | ((k5_relat_1 @ X9 @ X10) != (k6_partfun1 @ (k2_relat_1 @ X10)))
% 1.18/1.41          | ((k2_relat_1 @ X9) != (k1_relat_1 @ X10))
% 1.18/1.41          | ~ (v2_funct_1 @ X10)
% 1.18/1.41          | ~ (v1_funct_1 @ X10)
% 1.18/1.41          | ~ (v1_relat_1 @ X10))),
% 1.18/1.41      inference('demod', [status(thm)], ['28', '29'])).
% 1.18/1.41  thf('31', plain,
% 1.18/1.41      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 1.18/1.41        | ~ (v1_relat_1 @ sk_D)
% 1.18/1.41        | ~ (v1_funct_1 @ sk_D)
% 1.18/1.41        | ~ (v2_funct_1 @ sk_D)
% 1.18/1.41        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 1.18/1.41        | ((sk_C) = (k2_funct_1 @ sk_D))
% 1.18/1.41        | ~ (v1_funct_1 @ sk_C)
% 1.18/1.41        | ~ (v1_relat_1 @ sk_C))),
% 1.18/1.41      inference('sup-', [status(thm)], ['27', '30'])).
% 1.18/1.41  thf('32', plain,
% 1.18/1.41      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.18/1.41        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.18/1.41        (k6_partfun1 @ sk_A))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('33', plain,
% 1.18/1.41      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf(t24_funct_2, axiom,
% 1.18/1.41    (![A:$i,B:$i,C:$i]:
% 1.18/1.41     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.18/1.41         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.18/1.41       ( ![D:$i]:
% 1.18/1.41         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.18/1.41             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.18/1.41           ( ( r2_relset_1 @
% 1.18/1.41               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 1.18/1.41               ( k6_partfun1 @ B ) ) =>
% 1.18/1.41             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 1.18/1.41  thf('34', plain,
% 1.18/1.41      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 1.18/1.41         (~ (v1_funct_1 @ X48)
% 1.18/1.41          | ~ (v1_funct_2 @ X48 @ X49 @ X50)
% 1.18/1.41          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 1.18/1.41          | ~ (r2_relset_1 @ X49 @ X49 @ 
% 1.18/1.41               (k1_partfun1 @ X49 @ X50 @ X50 @ X49 @ X48 @ X51) @ 
% 1.18/1.41               (k6_partfun1 @ X49))
% 1.18/1.41          | ((k2_relset_1 @ X50 @ X49 @ X51) = (X49))
% 1.18/1.41          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X49)))
% 1.18/1.41          | ~ (v1_funct_2 @ X51 @ X50 @ X49)
% 1.18/1.41          | ~ (v1_funct_1 @ X51))),
% 1.18/1.41      inference('cnf', [status(esa)], [t24_funct_2])).
% 1.18/1.41  thf('35', plain,
% 1.18/1.41      (![X0 : $i]:
% 1.18/1.41         (~ (v1_funct_1 @ X0)
% 1.18/1.41          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.18/1.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.18/1.41          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.18/1.41          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.18/1.41               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.18/1.41               (k6_partfun1 @ sk_A))
% 1.18/1.41          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.18/1.41          | ~ (v1_funct_1 @ sk_C))),
% 1.18/1.41      inference('sup-', [status(thm)], ['33', '34'])).
% 1.18/1.41  thf('36', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('37', plain, ((v1_funct_1 @ sk_C)),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('38', plain,
% 1.18/1.41      (![X0 : $i]:
% 1.18/1.41         (~ (v1_funct_1 @ X0)
% 1.18/1.41          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.18/1.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.18/1.41          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.18/1.41          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.18/1.41               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.18/1.41               (k6_partfun1 @ sk_A)))),
% 1.18/1.41      inference('demod', [status(thm)], ['35', '36', '37'])).
% 1.18/1.41  thf('39', plain,
% 1.18/1.41      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 1.18/1.41        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.18/1.41        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.18/1.41        | ~ (v1_funct_1 @ sk_D))),
% 1.18/1.41      inference('sup-', [status(thm)], ['32', '38'])).
% 1.18/1.41  thf('40', plain,
% 1.18/1.41      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf(redefinition_k2_relset_1, axiom,
% 1.18/1.41    (![A:$i,B:$i,C:$i]:
% 1.18/1.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.18/1.41       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.18/1.41  thf('41', plain,
% 1.18/1.41      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.18/1.41         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 1.18/1.41          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.18/1.41      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.18/1.41  thf('42', plain,
% 1.18/1.41      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.18/1.41      inference('sup-', [status(thm)], ['40', '41'])).
% 1.18/1.41  thf('43', plain,
% 1.18/1.41      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('44', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('45', plain, ((v1_funct_1 @ sk_D)),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('46', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.18/1.41      inference('demod', [status(thm)], ['39', '42', '43', '44', '45'])).
% 1.18/1.41  thf('47', plain,
% 1.18/1.41      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf(cc2_relat_1, axiom,
% 1.18/1.41    (![A:$i]:
% 1.18/1.41     ( ( v1_relat_1 @ A ) =>
% 1.18/1.41       ( ![B:$i]:
% 1.18/1.41         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.18/1.41  thf('48', plain,
% 1.18/1.41      (![X0 : $i, X1 : $i]:
% 1.18/1.41         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.18/1.41          | (v1_relat_1 @ X0)
% 1.18/1.41          | ~ (v1_relat_1 @ X1))),
% 1.18/1.41      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.18/1.41  thf('49', plain,
% 1.18/1.41      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 1.18/1.41      inference('sup-', [status(thm)], ['47', '48'])).
% 1.18/1.41  thf(fc6_relat_1, axiom,
% 1.18/1.41    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.18/1.41  thf('50', plain,
% 1.18/1.41      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.18/1.41      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.18/1.41  thf('51', plain, ((v1_relat_1 @ sk_D)),
% 1.18/1.41      inference('demod', [status(thm)], ['49', '50'])).
% 1.18/1.41  thf('52', plain, ((v1_funct_1 @ sk_D)),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('53', plain,
% 1.18/1.41      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('54', plain,
% 1.18/1.41      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.18/1.41         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 1.18/1.41          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.18/1.41      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.18/1.41  thf('55', plain,
% 1.18/1.41      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.18/1.41      inference('sup-', [status(thm)], ['53', '54'])).
% 1.18/1.41  thf('56', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('57', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.18/1.41      inference('sup+', [status(thm)], ['55', '56'])).
% 1.18/1.41  thf('58', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.18/1.41      inference('demod', [status(thm)], ['39', '42', '43', '44', '45'])).
% 1.18/1.41  thf(t169_relat_1, axiom,
% 1.18/1.41    (![A:$i]:
% 1.18/1.41     ( ( v1_relat_1 @ A ) =>
% 1.18/1.41       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 1.18/1.41  thf('59', plain,
% 1.18/1.41      (![X4 : $i]:
% 1.18/1.41         (((k10_relat_1 @ X4 @ (k2_relat_1 @ X4)) = (k1_relat_1 @ X4))
% 1.18/1.41          | ~ (v1_relat_1 @ X4))),
% 1.18/1.41      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.18/1.41  thf('60', plain,
% 1.18/1.41      ((((k10_relat_1 @ sk_D @ sk_A) = (k1_relat_1 @ sk_D))
% 1.18/1.41        | ~ (v1_relat_1 @ sk_D))),
% 1.18/1.41      inference('sup+', [status(thm)], ['58', '59'])).
% 1.18/1.41  thf('61', plain,
% 1.18/1.41      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf(t38_relset_1, axiom,
% 1.18/1.41    (![A:$i,B:$i,C:$i]:
% 1.18/1.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.18/1.41       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 1.18/1.41         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.18/1.41  thf('62', plain,
% 1.18/1.41      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.18/1.41         (((k8_relset_1 @ X24 @ X25 @ X26 @ X25)
% 1.18/1.41            = (k1_relset_1 @ X24 @ X25 @ X26))
% 1.18/1.41          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.18/1.41      inference('cnf', [status(esa)], [t38_relset_1])).
% 1.18/1.41  thf('63', plain,
% 1.18/1.41      (((k8_relset_1 @ sk_B @ sk_A @ sk_D @ sk_A)
% 1.18/1.41         = (k1_relset_1 @ sk_B @ sk_A @ sk_D))),
% 1.18/1.41      inference('sup-', [status(thm)], ['61', '62'])).
% 1.18/1.41  thf('64', plain,
% 1.18/1.41      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf(redefinition_k8_relset_1, axiom,
% 1.18/1.41    (![A:$i,B:$i,C:$i,D:$i]:
% 1.18/1.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.18/1.41       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 1.18/1.41  thf('65', plain,
% 1.18/1.41      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 1.18/1.41         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 1.18/1.41          | ((k8_relset_1 @ X16 @ X17 @ X15 @ X18) = (k10_relat_1 @ X15 @ X18)))),
% 1.18/1.41      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 1.18/1.41  thf('66', plain,
% 1.18/1.41      (![X0 : $i]:
% 1.18/1.41         ((k8_relset_1 @ sk_B @ sk_A @ sk_D @ X0) = (k10_relat_1 @ sk_D @ X0))),
% 1.18/1.41      inference('sup-', [status(thm)], ['64', '65'])).
% 1.18/1.41  thf('67', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf(d1_funct_2, axiom,
% 1.18/1.41    (![A:$i,B:$i,C:$i]:
% 1.18/1.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.18/1.41       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.18/1.41           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.18/1.41             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.18/1.41         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.18/1.41           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.18/1.41             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.18/1.41  thf(zf_stmt_1, axiom,
% 1.18/1.41    (![C:$i,B:$i,A:$i]:
% 1.18/1.41     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.18/1.41       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.18/1.41  thf('68', plain,
% 1.18/1.41      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.18/1.41         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 1.18/1.41          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 1.18/1.41          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.18/1.41  thf('69', plain,
% 1.18/1.41      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 1.18/1.41        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 1.18/1.41      inference('sup-', [status(thm)], ['67', '68'])).
% 1.18/1.41  thf(zf_stmt_2, axiom,
% 1.18/1.41    (![B:$i,A:$i]:
% 1.18/1.41     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.18/1.41       ( zip_tseitin_0 @ B @ A ) ))).
% 1.18/1.41  thf('70', plain,
% 1.18/1.41      (![X27 : $i, X28 : $i]:
% 1.18/1.41         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.18/1.41  thf('71', plain,
% 1.18/1.41      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.18/1.41  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.18/1.41  thf(zf_stmt_5, axiom,
% 1.18/1.41    (![A:$i,B:$i,C:$i]:
% 1.18/1.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.18/1.41       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.18/1.41         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.18/1.41           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.18/1.41             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.18/1.41  thf('72', plain,
% 1.18/1.41      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.18/1.41         (~ (zip_tseitin_0 @ X32 @ X33)
% 1.18/1.41          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 1.18/1.41          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.18/1.41  thf('73', plain,
% 1.18/1.41      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 1.18/1.41      inference('sup-', [status(thm)], ['71', '72'])).
% 1.18/1.41  thf('74', plain,
% 1.18/1.41      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 1.18/1.41      inference('sup-', [status(thm)], ['70', '73'])).
% 1.18/1.41  thf('75', plain, (((sk_A) != (k1_xboole_0))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('76', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 1.18/1.41      inference('simplify_reflect-', [status(thm)], ['74', '75'])).
% 1.18/1.41  thf('77', plain, (((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D))),
% 1.18/1.41      inference('demod', [status(thm)], ['69', '76'])).
% 1.18/1.41  thf('78', plain, (((k10_relat_1 @ sk_D @ sk_A) = (sk_B))),
% 1.18/1.41      inference('demod', [status(thm)], ['63', '66', '77'])).
% 1.18/1.41  thf('79', plain, ((v1_relat_1 @ sk_D)),
% 1.18/1.41      inference('demod', [status(thm)], ['49', '50'])).
% 1.18/1.41  thf('80', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.18/1.41      inference('demod', [status(thm)], ['60', '78', '79'])).
% 1.18/1.41  thf('81', plain, ((v1_funct_1 @ sk_C)),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('82', plain,
% 1.18/1.41      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('83', plain,
% 1.18/1.41      (![X0 : $i, X1 : $i]:
% 1.18/1.41         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.18/1.41          | (v1_relat_1 @ X0)
% 1.18/1.41          | ~ (v1_relat_1 @ X1))),
% 1.18/1.41      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.18/1.41  thf('84', plain,
% 1.18/1.41      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 1.18/1.41      inference('sup-', [status(thm)], ['82', '83'])).
% 1.18/1.41  thf('85', plain,
% 1.18/1.41      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.18/1.41      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.18/1.41  thf('86', plain, ((v1_relat_1 @ sk_C)),
% 1.18/1.41      inference('demod', [status(thm)], ['84', '85'])).
% 1.18/1.41  thf('87', plain,
% 1.18/1.41      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 1.18/1.41        | ~ (v2_funct_1 @ sk_D)
% 1.18/1.41        | ((sk_B) != (sk_B))
% 1.18/1.41        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 1.18/1.41      inference('demod', [status(thm)],
% 1.18/1.41                ['31', '46', '51', '52', '57', '80', '81', '86'])).
% 1.18/1.41  thf('88', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 1.18/1.41      inference('simplify', [status(thm)], ['87'])).
% 1.18/1.41  thf('89', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.18/1.41      inference('demod', [status(thm)], ['23', '26'])).
% 1.18/1.41  thf(t48_funct_1, axiom,
% 1.18/1.41    (![A:$i]:
% 1.18/1.41     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.18/1.41       ( ![B:$i]:
% 1.18/1.41         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.18/1.41           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 1.18/1.41               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 1.18/1.41             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 1.18/1.41  thf('90', plain,
% 1.18/1.41      (![X7 : $i, X8 : $i]:
% 1.18/1.41         (~ (v1_relat_1 @ X7)
% 1.18/1.41          | ~ (v1_funct_1 @ X7)
% 1.18/1.41          | (v2_funct_1 @ X8)
% 1.18/1.41          | ((k2_relat_1 @ X7) != (k1_relat_1 @ X8))
% 1.18/1.41          | ~ (v2_funct_1 @ (k5_relat_1 @ X7 @ X8))
% 1.18/1.41          | ~ (v1_funct_1 @ X8)
% 1.18/1.41          | ~ (v1_relat_1 @ X8))),
% 1.18/1.41      inference('cnf', [status(esa)], [t48_funct_1])).
% 1.18/1.41  thf('91', plain,
% 1.18/1.41      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 1.18/1.41        | ~ (v1_relat_1 @ sk_D)
% 1.18/1.41        | ~ (v1_funct_1 @ sk_D)
% 1.18/1.41        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 1.18/1.41        | (v2_funct_1 @ sk_D)
% 1.18/1.41        | ~ (v1_funct_1 @ sk_C)
% 1.18/1.41        | ~ (v1_relat_1 @ sk_C))),
% 1.18/1.41      inference('sup-', [status(thm)], ['89', '90'])).
% 1.18/1.41  thf(fc4_funct_1, axiom,
% 1.18/1.41    (![A:$i]:
% 1.18/1.41     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.18/1.41       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.18/1.41  thf('92', plain, (![X6 : $i]: (v2_funct_1 @ (k6_relat_1 @ X6))),
% 1.18/1.41      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.18/1.41  thf('93', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 1.18/1.41      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.18/1.41  thf('94', plain, (![X6 : $i]: (v2_funct_1 @ (k6_partfun1 @ X6))),
% 1.18/1.41      inference('demod', [status(thm)], ['92', '93'])).
% 1.18/1.41  thf('95', plain, ((v1_relat_1 @ sk_D)),
% 1.18/1.41      inference('demod', [status(thm)], ['49', '50'])).
% 1.18/1.41  thf('96', plain, ((v1_funct_1 @ sk_D)),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('97', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.18/1.41      inference('sup+', [status(thm)], ['55', '56'])).
% 1.18/1.41  thf('98', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.18/1.41      inference('demod', [status(thm)], ['60', '78', '79'])).
% 1.18/1.41  thf('99', plain, ((v1_funct_1 @ sk_C)),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('100', plain, ((v1_relat_1 @ sk_C)),
% 1.18/1.41      inference('demod', [status(thm)], ['84', '85'])).
% 1.18/1.41  thf('101', plain, ((((sk_B) != (sk_B)) | (v2_funct_1 @ sk_D))),
% 1.18/1.41      inference('demod', [status(thm)],
% 1.18/1.41                ['91', '94', '95', '96', '97', '98', '99', '100'])).
% 1.18/1.41  thf('102', plain, ((v2_funct_1 @ sk_D)),
% 1.18/1.41      inference('simplify', [status(thm)], ['101'])).
% 1.18/1.41  thf('103', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.18/1.41      inference('demod', [status(thm)], ['88', '102'])).
% 1.18/1.41  thf(t65_funct_1, axiom,
% 1.18/1.41    (![A:$i]:
% 1.18/1.41     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.18/1.41       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 1.18/1.41  thf('104', plain,
% 1.18/1.41      (![X11 : $i]:
% 1.18/1.41         (~ (v2_funct_1 @ X11)
% 1.18/1.41          | ((k2_funct_1 @ (k2_funct_1 @ X11)) = (X11))
% 1.18/1.41          | ~ (v1_funct_1 @ X11)
% 1.18/1.41          | ~ (v1_relat_1 @ X11))),
% 1.18/1.41      inference('cnf', [status(esa)], [t65_funct_1])).
% 1.18/1.41  thf('105', plain,
% 1.18/1.41      ((((k2_funct_1 @ sk_C) = (sk_D))
% 1.18/1.41        | ~ (v1_relat_1 @ sk_D)
% 1.18/1.41        | ~ (v1_funct_1 @ sk_D)
% 1.18/1.41        | ~ (v2_funct_1 @ sk_D))),
% 1.18/1.41      inference('sup+', [status(thm)], ['103', '104'])).
% 1.18/1.41  thf('106', plain, ((v1_relat_1 @ sk_D)),
% 1.18/1.41      inference('demod', [status(thm)], ['49', '50'])).
% 1.18/1.41  thf('107', plain, ((v1_funct_1 @ sk_D)),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('108', plain, ((v2_funct_1 @ sk_D)),
% 1.18/1.41      inference('simplify', [status(thm)], ['101'])).
% 1.18/1.41  thf('109', plain, (((k2_funct_1 @ sk_C) = (sk_D))),
% 1.18/1.41      inference('demod', [status(thm)], ['105', '106', '107', '108'])).
% 1.18/1.41  thf('110', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.18/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.41  thf('111', plain, ($false),
% 1.18/1.41      inference('simplify_reflect-', [status(thm)], ['109', '110'])).
% 1.18/1.41  
% 1.18/1.41  % SZS output end Refutation
% 1.18/1.41  
% 1.18/1.42  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

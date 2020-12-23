%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5KW0ZVUPz7

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:22 EST 2020

% Result     : Theorem 21.81s
% Output     : Refutation 21.81s
% Verified   : 
% Statistics : Number of formulae       :  198 (2103 expanded)
%              Number of leaves         :   52 ( 634 expanded)
%              Depth                    :   22
%              Number of atoms          : 1927 (56800 expanded)
%              Number of equality atoms :  131 (3846 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

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
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( ( k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37 )
        = ( k5_relat_1 @ X34 @ X37 ) ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X33 ) ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( X15 = X18 )
      | ~ ( r2_relset_1 @ X16 @ X17 @ X15 @ X18 ) ) ),
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
    ! [X19: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('25',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('26',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( X7
        = ( k2_funct_1 @ X8 ) )
      | ( ( k5_relat_1 @ X7 @ X8 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X8 ) ) )
      | ( ( k2_relat_1 @ X7 )
       != ( k1_relat_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('29',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('30',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( X7
        = ( k2_funct_1 @ X8 ) )
      | ( ( k5_relat_1 @ X7 @ X8 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X8 ) ) )
      | ( ( k2_relat_1 @ X7 )
       != ( k1_relat_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
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
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( r2_relset_1 @ X42 @ X42 @ ( k1_partfun1 @ X42 @ X43 @ X43 @ X42 @ X41 @ X44 ) @ ( k6_partfun1 @ X42 ) )
      | ( ( k2_relset_1 @ X43 @ X42 @ X44 )
        = X42 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X43 @ X42 )
      | ~ ( v1_funct_1 @ X44 ) ) ),
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

thf('58',plain,(
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

thf('59',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ( X22
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('60',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('61',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('62',plain,(
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

thf('63',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('64',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('69',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('70',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['60','67','70'])).

thf('72',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('75',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('77',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B != sk_B )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['31','46','51','52','57','71','72','77'])).

thf('79',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('81',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('82',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
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

thf(zf_stmt_6,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [C: $i,B: $i] :
      ( ( zip_tseitin_3 @ C @ B )
     => ( ( C = k1_xboole_0 )
        & ( B != k1_xboole_0 ) ) ) )).

thf(zf_stmt_8,type,(
    zip_tseitin_2: $i > $i > $o )).

thf(zf_stmt_9,axiom,(
    ! [E: $i,D: $i] :
      ( ( zip_tseitin_2 @ E @ D )
     => ( ( v2_funct_1 @ D )
        & ( v2_funct_1 @ E ) ) ) )).

thf(zf_stmt_10,axiom,(
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
           => ( ( zip_tseitin_3 @ C @ B )
              | ( zip_tseitin_2 @ E @ D ) ) ) ) ) )).

thf('84',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X51 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ( zip_tseitin_2 @ X49 @ X52 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X53 @ X50 @ X50 @ X51 @ X52 @ X49 ) )
      | ( zip_tseitin_3 @ X51 @ X50 )
      | ( ( k2_relset_1 @ X53 @ X50 @ X52 )
       != X50 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X50 ) ) )
      | ~ ( v1_funct_2 @ X52 @ X53 @ X50 )
      | ~ ( v1_funct_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_3 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_2 @ sk_D @ X0 )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_3 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_2 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( zip_tseitin_2 @ sk_D @ sk_C )
    | ( zip_tseitin_3 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['82','88'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('90',plain,(
    ! [X5: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('91',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('92',plain,(
    ! [X5: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X5 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( zip_tseitin_2 @ sk_D @ sk_C )
    | ( zip_tseitin_3 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['89','92','93','94','95','96'])).

thf('98',plain,
    ( ( zip_tseitin_3 @ sk_A @ sk_B )
    | ( zip_tseitin_2 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X47: $i,X48: $i] :
      ( ( X47 = k1_xboole_0 )
      | ~ ( zip_tseitin_3 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('100',plain,
    ( ( zip_tseitin_2 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    zip_tseitin_2 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X45: $i,X46: $i] :
      ( ( v2_funct_1 @ X46 )
      | ~ ( zip_tseitin_2 @ X46 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('104',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['79','104'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('106',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k5_relat_1 @ X6 @ ( k2_funct_1 @ X6 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('107',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('108',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k5_relat_1 @ X6 @ ( k2_funct_1 @ X6 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( X7
        = ( k2_funct_1 @ X8 ) )
      | ( ( k5_relat_1 @ X7 @ X8 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X8 ) ) )
      | ( ( k2_relat_1 @ X7 )
       != ( k1_relat_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ( ( k2_relat_1 @ sk_D )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_D ) ) )
    | ( sk_D
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['105','111'])).

thf('113',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['60','67','70'])).

thf('114',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['55','56'])).

thf('115',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['49','50'])).

thf('116',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['102','103'])).

thf('118',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['79','104'])).

thf('119',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['75','76'])).

thf('120',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['79','104'])).

thf('121',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['79','104'])).

thf('123',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['39','42','43','44','45'])).

thf('125',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['79','104'])).

thf('126',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ( X22
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('128',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('130',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('132',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['129','132'])).

thf('134',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['133','134'])).

thf('136',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('138',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['128','135','138'])).

thf('140',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['79','104'])).

thf('141',plain,
    ( ( ( k6_partfun1 @ sk_B )
     != ( k6_partfun1 @ sk_B ) )
    | ( sk_A != sk_A )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['112','113','114','115','116','117','118','119','120','121','122','123','124','125','139','140'])).

thf('142',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['142','143'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5KW0ZVUPz7
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:36:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 21.81/22.00  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 21.81/22.00  % Solved by: fo/fo7.sh
% 21.81/22.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 21.81/22.00  % done 3765 iterations in 21.543s
% 21.81/22.00  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 21.81/22.00  % SZS output start Refutation
% 21.81/22.00  thf(sk_A_type, type, sk_A: $i).
% 21.81/22.00  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $o).
% 21.81/22.00  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 21.81/22.00  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 21.81/22.00  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 21.81/22.00  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 21.81/22.00  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 21.81/22.00  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 21.81/22.00  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 21.81/22.00  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 21.81/22.00  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 21.81/22.00  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 21.81/22.00  thf(sk_C_type, type, sk_C: $i).
% 21.81/22.00  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 21.81/22.00  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 21.81/22.00  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 21.81/22.00  thf(sk_B_type, type, sk_B: $i).
% 21.81/22.00  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 21.81/22.00  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 21.81/22.00  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 21.81/22.00  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 21.81/22.00  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 21.81/22.00  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 21.81/22.00  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 21.81/22.00  thf(sk_D_type, type, sk_D: $i).
% 21.81/22.00  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 21.81/22.00  thf(t36_funct_2, conjecture,
% 21.81/22.00    (![A:$i,B:$i,C:$i]:
% 21.81/22.00     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 21.81/22.00         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 21.81/22.00       ( ![D:$i]:
% 21.81/22.00         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 21.81/22.00             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 21.81/22.00           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 21.81/22.00               ( r2_relset_1 @
% 21.81/22.00                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 21.81/22.00                 ( k6_partfun1 @ A ) ) & 
% 21.81/22.00               ( v2_funct_1 @ C ) ) =>
% 21.81/22.00             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 21.81/22.00               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 21.81/22.00  thf(zf_stmt_0, negated_conjecture,
% 21.81/22.00    (~( ![A:$i,B:$i,C:$i]:
% 21.81/22.00        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 21.81/22.00            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 21.81/22.00          ( ![D:$i]:
% 21.81/22.00            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 21.81/22.00                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 21.81/22.00              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 21.81/22.00                  ( r2_relset_1 @
% 21.81/22.00                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 21.81/22.00                    ( k6_partfun1 @ A ) ) & 
% 21.81/22.00                  ( v2_funct_1 @ C ) ) =>
% 21.81/22.00                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 21.81/22.00                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 21.81/22.00    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 21.81/22.00  thf('0', plain,
% 21.81/22.00      ((r2_relset_1 @ sk_A @ sk_A @ 
% 21.81/22.00        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 21.81/22.00        (k6_partfun1 @ sk_A))),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf('1', plain,
% 21.81/22.00      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf('2', plain,
% 21.81/22.00      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf(redefinition_k1_partfun1, axiom,
% 21.81/22.00    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 21.81/22.00     ( ( ( v1_funct_1 @ E ) & 
% 21.81/22.00         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 21.81/22.00         ( v1_funct_1 @ F ) & 
% 21.81/22.00         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 21.81/22.00       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 21.81/22.00  thf('3', plain,
% 21.81/22.00      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 21.81/22.00         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 21.81/22.00          | ~ (v1_funct_1 @ X34)
% 21.81/22.00          | ~ (v1_funct_1 @ X37)
% 21.81/22.00          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 21.81/22.00          | ((k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37)
% 21.81/22.00              = (k5_relat_1 @ X34 @ X37)))),
% 21.81/22.00      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 21.81/22.00  thf('4', plain,
% 21.81/22.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.81/22.00         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 21.81/22.00            = (k5_relat_1 @ sk_C @ X0))
% 21.81/22.00          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 21.81/22.00          | ~ (v1_funct_1 @ X0)
% 21.81/22.00          | ~ (v1_funct_1 @ sk_C))),
% 21.81/22.00      inference('sup-', [status(thm)], ['2', '3'])).
% 21.81/22.00  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf('6', plain,
% 21.81/22.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.81/22.00         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 21.81/22.00            = (k5_relat_1 @ sk_C @ X0))
% 21.81/22.00          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 21.81/22.00          | ~ (v1_funct_1 @ X0))),
% 21.81/22.00      inference('demod', [status(thm)], ['4', '5'])).
% 21.81/22.00  thf('7', plain,
% 21.81/22.00      ((~ (v1_funct_1 @ sk_D)
% 21.81/22.00        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 21.81/22.00            = (k5_relat_1 @ sk_C @ sk_D)))),
% 21.81/22.00      inference('sup-', [status(thm)], ['1', '6'])).
% 21.81/22.00  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf('9', plain,
% 21.81/22.00      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 21.81/22.00         = (k5_relat_1 @ sk_C @ sk_D))),
% 21.81/22.00      inference('demod', [status(thm)], ['7', '8'])).
% 21.81/22.00  thf('10', plain,
% 21.81/22.00      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 21.81/22.00        (k6_partfun1 @ sk_A))),
% 21.81/22.00      inference('demod', [status(thm)], ['0', '9'])).
% 21.81/22.00  thf('11', plain,
% 21.81/22.00      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf('12', plain,
% 21.81/22.00      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf(dt_k1_partfun1, axiom,
% 21.81/22.00    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 21.81/22.00     ( ( ( v1_funct_1 @ E ) & 
% 21.81/22.00         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 21.81/22.00         ( v1_funct_1 @ F ) & 
% 21.81/22.00         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 21.81/22.00       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 21.81/22.00         ( m1_subset_1 @
% 21.81/22.00           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 21.81/22.00           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 21.81/22.00  thf('13', plain,
% 21.81/22.00      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 21.81/22.00         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 21.81/22.00          | ~ (v1_funct_1 @ X28)
% 21.81/22.00          | ~ (v1_funct_1 @ X31)
% 21.81/22.00          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 21.81/22.00          | (m1_subset_1 @ (k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31) @ 
% 21.81/22.00             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X33))))),
% 21.81/22.00      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 21.81/22.00  thf('14', plain,
% 21.81/22.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.81/22.00         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 21.81/22.00           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 21.81/22.00          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 21.81/22.00          | ~ (v1_funct_1 @ X1)
% 21.81/22.00          | ~ (v1_funct_1 @ sk_C))),
% 21.81/22.00      inference('sup-', [status(thm)], ['12', '13'])).
% 21.81/22.00  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf('16', plain,
% 21.81/22.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.81/22.00         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 21.81/22.00           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 21.81/22.00          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 21.81/22.00          | ~ (v1_funct_1 @ X1))),
% 21.81/22.00      inference('demod', [status(thm)], ['14', '15'])).
% 21.81/22.00  thf('17', plain,
% 21.81/22.00      ((~ (v1_funct_1 @ sk_D)
% 21.81/22.00        | (m1_subset_1 @ 
% 21.81/22.00           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 21.81/22.00           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 21.81/22.00      inference('sup-', [status(thm)], ['11', '16'])).
% 21.81/22.00  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf('19', plain,
% 21.81/22.00      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 21.81/22.00         = (k5_relat_1 @ sk_C @ sk_D))),
% 21.81/22.00      inference('demod', [status(thm)], ['7', '8'])).
% 21.81/22.00  thf('20', plain,
% 21.81/22.00      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 21.81/22.00        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 21.81/22.00      inference('demod', [status(thm)], ['17', '18', '19'])).
% 21.81/22.00  thf(redefinition_r2_relset_1, axiom,
% 21.81/22.00    (![A:$i,B:$i,C:$i,D:$i]:
% 21.81/22.00     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 21.81/22.00         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 21.81/22.00       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 21.81/22.00  thf('21', plain,
% 21.81/22.00      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 21.81/22.00         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 21.81/22.00          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 21.81/22.00          | ((X15) = (X18))
% 21.81/22.00          | ~ (r2_relset_1 @ X16 @ X17 @ X15 @ X18))),
% 21.81/22.00      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 21.81/22.00  thf('22', plain,
% 21.81/22.00      (![X0 : $i]:
% 21.81/22.00         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 21.81/22.00          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 21.81/22.00          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 21.81/22.00      inference('sup-', [status(thm)], ['20', '21'])).
% 21.81/22.00  thf('23', plain,
% 21.81/22.00      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 21.81/22.00           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 21.81/22.00        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 21.81/22.00      inference('sup-', [status(thm)], ['10', '22'])).
% 21.81/22.00  thf(t29_relset_1, axiom,
% 21.81/22.00    (![A:$i]:
% 21.81/22.00     ( m1_subset_1 @
% 21.81/22.00       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 21.81/22.00  thf('24', plain,
% 21.81/22.00      (![X19 : $i]:
% 21.81/22.00         (m1_subset_1 @ (k6_relat_1 @ X19) @ 
% 21.81/22.00          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))),
% 21.81/22.00      inference('cnf', [status(esa)], [t29_relset_1])).
% 21.81/22.00  thf(redefinition_k6_partfun1, axiom,
% 21.81/22.00    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 21.81/22.00  thf('25', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 21.81/22.00      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 21.81/22.00  thf('26', plain,
% 21.81/22.00      (![X19 : $i]:
% 21.81/22.00         (m1_subset_1 @ (k6_partfun1 @ X19) @ 
% 21.81/22.00          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))),
% 21.81/22.00      inference('demod', [status(thm)], ['24', '25'])).
% 21.81/22.00  thf('27', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 21.81/22.00      inference('demod', [status(thm)], ['23', '26'])).
% 21.81/22.00  thf(t64_funct_1, axiom,
% 21.81/22.00    (![A:$i]:
% 21.81/22.00     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 21.81/22.00       ( ![B:$i]:
% 21.81/22.00         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 21.81/22.00           ( ( ( v2_funct_1 @ A ) & 
% 21.81/22.00               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 21.81/22.00               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 21.81/22.00             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 21.81/22.00  thf('28', plain,
% 21.81/22.00      (![X7 : $i, X8 : $i]:
% 21.81/22.00         (~ (v1_relat_1 @ X7)
% 21.81/22.00          | ~ (v1_funct_1 @ X7)
% 21.81/22.00          | ((X7) = (k2_funct_1 @ X8))
% 21.81/22.00          | ((k5_relat_1 @ X7 @ X8) != (k6_relat_1 @ (k2_relat_1 @ X8)))
% 21.81/22.00          | ((k2_relat_1 @ X7) != (k1_relat_1 @ X8))
% 21.81/22.00          | ~ (v2_funct_1 @ X8)
% 21.81/22.00          | ~ (v1_funct_1 @ X8)
% 21.81/22.00          | ~ (v1_relat_1 @ X8))),
% 21.81/22.00      inference('cnf', [status(esa)], [t64_funct_1])).
% 21.81/22.00  thf('29', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 21.81/22.00      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 21.81/22.00  thf('30', plain,
% 21.81/22.00      (![X7 : $i, X8 : $i]:
% 21.81/22.00         (~ (v1_relat_1 @ X7)
% 21.81/22.00          | ~ (v1_funct_1 @ X7)
% 21.81/22.00          | ((X7) = (k2_funct_1 @ X8))
% 21.81/22.00          | ((k5_relat_1 @ X7 @ X8) != (k6_partfun1 @ (k2_relat_1 @ X8)))
% 21.81/22.00          | ((k2_relat_1 @ X7) != (k1_relat_1 @ X8))
% 21.81/22.00          | ~ (v2_funct_1 @ X8)
% 21.81/22.00          | ~ (v1_funct_1 @ X8)
% 21.81/22.00          | ~ (v1_relat_1 @ X8))),
% 21.81/22.00      inference('demod', [status(thm)], ['28', '29'])).
% 21.81/22.00  thf('31', plain,
% 21.81/22.00      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 21.81/22.00        | ~ (v1_relat_1 @ sk_D)
% 21.81/22.00        | ~ (v1_funct_1 @ sk_D)
% 21.81/22.00        | ~ (v2_funct_1 @ sk_D)
% 21.81/22.00        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 21.81/22.00        | ((sk_C) = (k2_funct_1 @ sk_D))
% 21.81/22.00        | ~ (v1_funct_1 @ sk_C)
% 21.81/22.00        | ~ (v1_relat_1 @ sk_C))),
% 21.81/22.00      inference('sup-', [status(thm)], ['27', '30'])).
% 21.81/22.00  thf('32', plain,
% 21.81/22.00      ((r2_relset_1 @ sk_A @ sk_A @ 
% 21.81/22.00        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 21.81/22.00        (k6_partfun1 @ sk_A))),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf('33', plain,
% 21.81/22.00      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf(t24_funct_2, axiom,
% 21.81/22.00    (![A:$i,B:$i,C:$i]:
% 21.81/22.00     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 21.81/22.00         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 21.81/22.00       ( ![D:$i]:
% 21.81/22.00         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 21.81/22.00             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 21.81/22.00           ( ( r2_relset_1 @
% 21.81/22.00               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 21.81/22.00               ( k6_partfun1 @ B ) ) =>
% 21.81/22.00             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 21.81/22.00  thf('34', plain,
% 21.81/22.00      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 21.81/22.00         (~ (v1_funct_1 @ X41)
% 21.81/22.00          | ~ (v1_funct_2 @ X41 @ X42 @ X43)
% 21.81/22.00          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 21.81/22.00          | ~ (r2_relset_1 @ X42 @ X42 @ 
% 21.81/22.00               (k1_partfun1 @ X42 @ X43 @ X43 @ X42 @ X41 @ X44) @ 
% 21.81/22.00               (k6_partfun1 @ X42))
% 21.81/22.00          | ((k2_relset_1 @ X43 @ X42 @ X44) = (X42))
% 21.81/22.00          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42)))
% 21.81/22.00          | ~ (v1_funct_2 @ X44 @ X43 @ X42)
% 21.81/22.00          | ~ (v1_funct_1 @ X44))),
% 21.81/22.00      inference('cnf', [status(esa)], [t24_funct_2])).
% 21.81/22.00  thf('35', plain,
% 21.81/22.00      (![X0 : $i]:
% 21.81/22.00         (~ (v1_funct_1 @ X0)
% 21.81/22.00          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 21.81/22.00          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 21.81/22.00          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 21.81/22.00          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 21.81/22.00               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 21.81/22.00               (k6_partfun1 @ sk_A))
% 21.81/22.00          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 21.81/22.00          | ~ (v1_funct_1 @ sk_C))),
% 21.81/22.00      inference('sup-', [status(thm)], ['33', '34'])).
% 21.81/22.00  thf('36', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf('37', plain, ((v1_funct_1 @ sk_C)),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf('38', plain,
% 21.81/22.00      (![X0 : $i]:
% 21.81/22.00         (~ (v1_funct_1 @ X0)
% 21.81/22.00          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 21.81/22.00          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 21.81/22.00          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 21.81/22.00          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 21.81/22.00               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 21.81/22.00               (k6_partfun1 @ sk_A)))),
% 21.81/22.00      inference('demod', [status(thm)], ['35', '36', '37'])).
% 21.81/22.00  thf('39', plain,
% 21.81/22.00      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 21.81/22.00        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 21.81/22.00        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 21.81/22.00        | ~ (v1_funct_1 @ sk_D))),
% 21.81/22.00      inference('sup-', [status(thm)], ['32', '38'])).
% 21.81/22.00  thf('40', plain,
% 21.81/22.00      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf(redefinition_k2_relset_1, axiom,
% 21.81/22.00    (![A:$i,B:$i,C:$i]:
% 21.81/22.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 21.81/22.00       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 21.81/22.00  thf('41', plain,
% 21.81/22.00      (![X12 : $i, X13 : $i, X14 : $i]:
% 21.81/22.00         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 21.81/22.00          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 21.81/22.00      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 21.81/22.00  thf('42', plain,
% 21.81/22.00      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 21.81/22.00      inference('sup-', [status(thm)], ['40', '41'])).
% 21.81/22.00  thf('43', plain,
% 21.81/22.00      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf('44', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf('45', plain, ((v1_funct_1 @ sk_D)),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf('46', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 21.81/22.00      inference('demod', [status(thm)], ['39', '42', '43', '44', '45'])).
% 21.81/22.00  thf('47', plain,
% 21.81/22.00      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf(cc2_relat_1, axiom,
% 21.81/22.00    (![A:$i]:
% 21.81/22.00     ( ( v1_relat_1 @ A ) =>
% 21.81/22.00       ( ![B:$i]:
% 21.81/22.00         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 21.81/22.00  thf('48', plain,
% 21.81/22.00      (![X0 : $i, X1 : $i]:
% 21.81/22.00         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 21.81/22.00          | (v1_relat_1 @ X0)
% 21.81/22.00          | ~ (v1_relat_1 @ X1))),
% 21.81/22.00      inference('cnf', [status(esa)], [cc2_relat_1])).
% 21.81/22.00  thf('49', plain,
% 21.81/22.00      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 21.81/22.00      inference('sup-', [status(thm)], ['47', '48'])).
% 21.81/22.00  thf(fc6_relat_1, axiom,
% 21.81/22.00    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 21.81/22.00  thf('50', plain,
% 21.81/22.00      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 21.81/22.00      inference('cnf', [status(esa)], [fc6_relat_1])).
% 21.81/22.00  thf('51', plain, ((v1_relat_1 @ sk_D)),
% 21.81/22.00      inference('demod', [status(thm)], ['49', '50'])).
% 21.81/22.00  thf('52', plain, ((v1_funct_1 @ sk_D)),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf('53', plain,
% 21.81/22.00      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf('54', plain,
% 21.81/22.00      (![X12 : $i, X13 : $i, X14 : $i]:
% 21.81/22.00         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 21.81/22.00          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 21.81/22.00      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 21.81/22.00  thf('55', plain,
% 21.81/22.00      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 21.81/22.00      inference('sup-', [status(thm)], ['53', '54'])).
% 21.81/22.00  thf('56', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf('57', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 21.81/22.00      inference('sup+', [status(thm)], ['55', '56'])).
% 21.81/22.00  thf('58', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf(d1_funct_2, axiom,
% 21.81/22.00    (![A:$i,B:$i,C:$i]:
% 21.81/22.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 21.81/22.00       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 21.81/22.00           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 21.81/22.00             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 21.81/22.00         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 21.81/22.00           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 21.81/22.00             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 21.81/22.00  thf(zf_stmt_1, axiom,
% 21.81/22.00    (![C:$i,B:$i,A:$i]:
% 21.81/22.00     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 21.81/22.00       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 21.81/22.00  thf('59', plain,
% 21.81/22.00      (![X22 : $i, X23 : $i, X24 : $i]:
% 21.81/22.00         (~ (v1_funct_2 @ X24 @ X22 @ X23)
% 21.81/22.00          | ((X22) = (k1_relset_1 @ X22 @ X23 @ X24))
% 21.81/22.00          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_1])).
% 21.81/22.00  thf('60', plain,
% 21.81/22.00      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 21.81/22.00        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 21.81/22.00      inference('sup-', [status(thm)], ['58', '59'])).
% 21.81/22.00  thf(zf_stmt_2, axiom,
% 21.81/22.00    (![B:$i,A:$i]:
% 21.81/22.00     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 21.81/22.00       ( zip_tseitin_0 @ B @ A ) ))).
% 21.81/22.00  thf('61', plain,
% 21.81/22.00      (![X20 : $i, X21 : $i]:
% 21.81/22.00         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_2])).
% 21.81/22.00  thf('62', plain,
% 21.81/22.00      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 21.81/22.00  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 21.81/22.00  thf(zf_stmt_5, axiom,
% 21.81/22.00    (![A:$i,B:$i,C:$i]:
% 21.81/22.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 21.81/22.00       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 21.81/22.00         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 21.81/22.00           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 21.81/22.00             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 21.81/22.00  thf('63', plain,
% 21.81/22.00      (![X25 : $i, X26 : $i, X27 : $i]:
% 21.81/22.00         (~ (zip_tseitin_0 @ X25 @ X26)
% 21.81/22.00          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 21.81/22.00          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_5])).
% 21.81/22.00  thf('64', plain,
% 21.81/22.00      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 21.81/22.00      inference('sup-', [status(thm)], ['62', '63'])).
% 21.81/22.00  thf('65', plain,
% 21.81/22.00      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 21.81/22.00      inference('sup-', [status(thm)], ['61', '64'])).
% 21.81/22.00  thf('66', plain, (((sk_A) != (k1_xboole_0))),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf('67', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 21.81/22.00      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 21.81/22.00  thf('68', plain,
% 21.81/22.00      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf(redefinition_k1_relset_1, axiom,
% 21.81/22.00    (![A:$i,B:$i,C:$i]:
% 21.81/22.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 21.81/22.00       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 21.81/22.00  thf('69', plain,
% 21.81/22.00      (![X9 : $i, X10 : $i, X11 : $i]:
% 21.81/22.00         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 21.81/22.00          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 21.81/22.00      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 21.81/22.00  thf('70', plain,
% 21.81/22.00      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 21.81/22.00      inference('sup-', [status(thm)], ['68', '69'])).
% 21.81/22.00  thf('71', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 21.81/22.00      inference('demod', [status(thm)], ['60', '67', '70'])).
% 21.81/22.00  thf('72', plain, ((v1_funct_1 @ sk_C)),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf('73', plain,
% 21.81/22.00      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf('74', plain,
% 21.81/22.00      (![X0 : $i, X1 : $i]:
% 21.81/22.00         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 21.81/22.00          | (v1_relat_1 @ X0)
% 21.81/22.00          | ~ (v1_relat_1 @ X1))),
% 21.81/22.00      inference('cnf', [status(esa)], [cc2_relat_1])).
% 21.81/22.00  thf('75', plain,
% 21.81/22.00      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 21.81/22.00      inference('sup-', [status(thm)], ['73', '74'])).
% 21.81/22.00  thf('76', plain,
% 21.81/22.00      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 21.81/22.00      inference('cnf', [status(esa)], [fc6_relat_1])).
% 21.81/22.00  thf('77', plain, ((v1_relat_1 @ sk_C)),
% 21.81/22.00      inference('demod', [status(thm)], ['75', '76'])).
% 21.81/22.00  thf('78', plain,
% 21.81/22.00      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 21.81/22.00        | ~ (v2_funct_1 @ sk_D)
% 21.81/22.00        | ((sk_B) != (sk_B))
% 21.81/22.00        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 21.81/22.00      inference('demod', [status(thm)],
% 21.81/22.00                ['31', '46', '51', '52', '57', '71', '72', '77'])).
% 21.81/22.00  thf('79', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 21.81/22.00      inference('simplify', [status(thm)], ['78'])).
% 21.81/22.00  thf('80', plain,
% 21.81/22.00      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 21.81/22.00         = (k5_relat_1 @ sk_C @ sk_D))),
% 21.81/22.00      inference('demod', [status(thm)], ['7', '8'])).
% 21.81/22.00  thf('81', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 21.81/22.00      inference('demod', [status(thm)], ['23', '26'])).
% 21.81/22.00  thf('82', plain,
% 21.81/22.00      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 21.81/22.00         = (k6_partfun1 @ sk_A))),
% 21.81/22.00      inference('demod', [status(thm)], ['80', '81'])).
% 21.81/22.00  thf('83', plain,
% 21.81/22.00      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf(t30_funct_2, axiom,
% 21.81/22.00    (![A:$i,B:$i,C:$i,D:$i]:
% 21.81/22.00     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 21.81/22.00         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 21.81/22.00       ( ![E:$i]:
% 21.81/22.00         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 21.81/22.00             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 21.81/22.00           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 21.81/22.00               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 21.81/22.00             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 21.81/22.00               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 21.81/22.00  thf(zf_stmt_6, type, zip_tseitin_3 : $i > $i > $o).
% 21.81/22.00  thf(zf_stmt_7, axiom,
% 21.81/22.00    (![C:$i,B:$i]:
% 21.81/22.00     ( ( zip_tseitin_3 @ C @ B ) =>
% 21.81/22.00       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 21.81/22.00  thf(zf_stmt_8, type, zip_tseitin_2 : $i > $i > $o).
% 21.81/22.00  thf(zf_stmt_9, axiom,
% 21.81/22.00    (![E:$i,D:$i]:
% 21.81/22.00     ( ( zip_tseitin_2 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 21.81/22.00  thf(zf_stmt_10, axiom,
% 21.81/22.00    (![A:$i,B:$i,C:$i,D:$i]:
% 21.81/22.00     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 21.81/22.00         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 21.81/22.00       ( ![E:$i]:
% 21.81/22.00         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 21.81/22.00             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 21.81/22.00           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 21.81/22.00               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 21.81/22.00             ( ( zip_tseitin_3 @ C @ B ) | ( zip_tseitin_2 @ E @ D ) ) ) ) ) ))).
% 21.81/22.00  thf('84', plain,
% 21.81/22.00      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 21.81/22.00         (~ (v1_funct_1 @ X49)
% 21.81/22.00          | ~ (v1_funct_2 @ X49 @ X50 @ X51)
% 21.81/22.00          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 21.81/22.00          | (zip_tseitin_2 @ X49 @ X52)
% 21.81/22.00          | ~ (v2_funct_1 @ (k1_partfun1 @ X53 @ X50 @ X50 @ X51 @ X52 @ X49))
% 21.81/22.00          | (zip_tseitin_3 @ X51 @ X50)
% 21.81/22.00          | ((k2_relset_1 @ X53 @ X50 @ X52) != (X50))
% 21.81/22.00          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X50)))
% 21.81/22.00          | ~ (v1_funct_2 @ X52 @ X53 @ X50)
% 21.81/22.00          | ~ (v1_funct_1 @ X52))),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_10])).
% 21.81/22.00  thf('85', plain,
% 21.81/22.00      (![X0 : $i, X1 : $i]:
% 21.81/22.00         (~ (v1_funct_1 @ X0)
% 21.81/22.00          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 21.81/22.00          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 21.81/22.00          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 21.81/22.00          | (zip_tseitin_3 @ sk_A @ sk_B)
% 21.81/22.00          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 21.81/22.00          | (zip_tseitin_2 @ sk_D @ X0)
% 21.81/22.00          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 21.81/22.00          | ~ (v1_funct_1 @ sk_D))),
% 21.81/22.00      inference('sup-', [status(thm)], ['83', '84'])).
% 21.81/22.00  thf('86', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf('87', plain, ((v1_funct_1 @ sk_D)),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf('88', plain,
% 21.81/22.00      (![X0 : $i, X1 : $i]:
% 21.81/22.00         (~ (v1_funct_1 @ X0)
% 21.81/22.00          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 21.81/22.00          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 21.81/22.00          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 21.81/22.00          | (zip_tseitin_3 @ sk_A @ sk_B)
% 21.81/22.00          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 21.81/22.00          | (zip_tseitin_2 @ sk_D @ X0))),
% 21.81/22.00      inference('demod', [status(thm)], ['85', '86', '87'])).
% 21.81/22.00  thf('89', plain,
% 21.81/22.00      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 21.81/22.00        | (zip_tseitin_2 @ sk_D @ sk_C)
% 21.81/22.00        | (zip_tseitin_3 @ sk_A @ sk_B)
% 21.81/22.00        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 21.81/22.00        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 21.81/22.00        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 21.81/22.00        | ~ (v1_funct_1 @ sk_C))),
% 21.81/22.00      inference('sup-', [status(thm)], ['82', '88'])).
% 21.81/22.00  thf(fc4_funct_1, axiom,
% 21.81/22.00    (![A:$i]:
% 21.81/22.00     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 21.81/22.00       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 21.81/22.00  thf('90', plain, (![X5 : $i]: (v2_funct_1 @ (k6_relat_1 @ X5))),
% 21.81/22.00      inference('cnf', [status(esa)], [fc4_funct_1])).
% 21.81/22.00  thf('91', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 21.81/22.00      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 21.81/22.00  thf('92', plain, (![X5 : $i]: (v2_funct_1 @ (k6_partfun1 @ X5))),
% 21.81/22.00      inference('demod', [status(thm)], ['90', '91'])).
% 21.81/22.00  thf('93', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf('94', plain,
% 21.81/22.00      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf('95', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf('96', plain, ((v1_funct_1 @ sk_C)),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf('97', plain,
% 21.81/22.00      (((zip_tseitin_2 @ sk_D @ sk_C)
% 21.81/22.00        | (zip_tseitin_3 @ sk_A @ sk_B)
% 21.81/22.00        | ((sk_B) != (sk_B)))),
% 21.81/22.00      inference('demod', [status(thm)], ['89', '92', '93', '94', '95', '96'])).
% 21.81/22.00  thf('98', plain,
% 21.81/22.00      (((zip_tseitin_3 @ sk_A @ sk_B) | (zip_tseitin_2 @ sk_D @ sk_C))),
% 21.81/22.00      inference('simplify', [status(thm)], ['97'])).
% 21.81/22.00  thf('99', plain,
% 21.81/22.00      (![X47 : $i, X48 : $i]:
% 21.81/22.00         (((X47) = (k1_xboole_0)) | ~ (zip_tseitin_3 @ X47 @ X48))),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_7])).
% 21.81/22.00  thf('100', plain,
% 21.81/22.00      (((zip_tseitin_2 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 21.81/22.00      inference('sup-', [status(thm)], ['98', '99'])).
% 21.81/22.00  thf('101', plain, (((sk_A) != (k1_xboole_0))),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf('102', plain, ((zip_tseitin_2 @ sk_D @ sk_C)),
% 21.81/22.00      inference('simplify_reflect-', [status(thm)], ['100', '101'])).
% 21.81/22.00  thf('103', plain,
% 21.81/22.00      (![X45 : $i, X46 : $i]:
% 21.81/22.00         ((v2_funct_1 @ X46) | ~ (zip_tseitin_2 @ X46 @ X45))),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_9])).
% 21.81/22.00  thf('104', plain, ((v2_funct_1 @ sk_D)),
% 21.81/22.00      inference('sup-', [status(thm)], ['102', '103'])).
% 21.81/22.00  thf('105', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 21.81/22.00      inference('demod', [status(thm)], ['79', '104'])).
% 21.81/22.00  thf(t61_funct_1, axiom,
% 21.81/22.00    (![A:$i]:
% 21.81/22.00     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 21.81/22.00       ( ( v2_funct_1 @ A ) =>
% 21.81/22.00         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 21.81/22.00             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 21.81/22.00           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 21.81/22.00             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 21.81/22.00  thf('106', plain,
% 21.81/22.00      (![X6 : $i]:
% 21.81/22.00         (~ (v2_funct_1 @ X6)
% 21.81/22.00          | ((k5_relat_1 @ X6 @ (k2_funct_1 @ X6))
% 21.81/22.00              = (k6_relat_1 @ (k1_relat_1 @ X6)))
% 21.81/22.00          | ~ (v1_funct_1 @ X6)
% 21.81/22.00          | ~ (v1_relat_1 @ X6))),
% 21.81/22.00      inference('cnf', [status(esa)], [t61_funct_1])).
% 21.81/22.00  thf('107', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 21.81/22.00      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 21.81/22.00  thf('108', plain,
% 21.81/22.00      (![X6 : $i]:
% 21.81/22.00         (~ (v2_funct_1 @ X6)
% 21.81/22.00          | ((k5_relat_1 @ X6 @ (k2_funct_1 @ X6))
% 21.81/22.00              = (k6_partfun1 @ (k1_relat_1 @ X6)))
% 21.81/22.00          | ~ (v1_funct_1 @ X6)
% 21.81/22.00          | ~ (v1_relat_1 @ X6))),
% 21.81/22.00      inference('demod', [status(thm)], ['106', '107'])).
% 21.81/22.00  thf('109', plain,
% 21.81/22.00      (![X7 : $i, X8 : $i]:
% 21.81/22.00         (~ (v1_relat_1 @ X7)
% 21.81/22.00          | ~ (v1_funct_1 @ X7)
% 21.81/22.00          | ((X7) = (k2_funct_1 @ X8))
% 21.81/22.00          | ((k5_relat_1 @ X7 @ X8) != (k6_partfun1 @ (k2_relat_1 @ X8)))
% 21.81/22.00          | ((k2_relat_1 @ X7) != (k1_relat_1 @ X8))
% 21.81/22.00          | ~ (v2_funct_1 @ X8)
% 21.81/22.00          | ~ (v1_funct_1 @ X8)
% 21.81/22.00          | ~ (v1_relat_1 @ X8))),
% 21.81/22.00      inference('demod', [status(thm)], ['28', '29'])).
% 21.81/22.00  thf('110', plain,
% 21.81/22.00      (![X0 : $i]:
% 21.81/22.00         (((k6_partfun1 @ (k1_relat_1 @ X0))
% 21.81/22.00            != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 21.81/22.00          | ~ (v1_relat_1 @ X0)
% 21.81/22.00          | ~ (v1_funct_1 @ X0)
% 21.81/22.00          | ~ (v2_funct_1 @ X0)
% 21.81/22.00          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 21.81/22.00          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 21.81/22.00          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 21.81/22.00          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 21.81/22.00          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 21.81/22.00          | ~ (v1_funct_1 @ X0)
% 21.81/22.00          | ~ (v1_relat_1 @ X0))),
% 21.81/22.00      inference('sup-', [status(thm)], ['108', '109'])).
% 21.81/22.00  thf('111', plain,
% 21.81/22.00      (![X0 : $i]:
% 21.81/22.00         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 21.81/22.00          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 21.81/22.00          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 21.81/22.00          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 21.81/22.00          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 21.81/22.00          | ~ (v2_funct_1 @ X0)
% 21.81/22.00          | ~ (v1_funct_1 @ X0)
% 21.81/22.00          | ~ (v1_relat_1 @ X0)
% 21.81/22.00          | ((k6_partfun1 @ (k1_relat_1 @ X0))
% 21.81/22.00              != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 21.81/22.00      inference('simplify', [status(thm)], ['110'])).
% 21.81/22.00  thf('112', plain,
% 21.81/22.00      ((((k6_partfun1 @ (k1_relat_1 @ sk_D))
% 21.81/22.00          != (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 21.81/22.00        | ~ (v1_relat_1 @ sk_D)
% 21.81/22.00        | ~ (v1_funct_1 @ sk_D)
% 21.81/22.00        | ~ (v2_funct_1 @ sk_D)
% 21.81/22.00        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D))
% 21.81/22.00        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 21.81/22.00        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_D))
% 21.81/22.00        | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ (k2_funct_1 @ sk_D)))
% 21.81/22.00        | ((sk_D) = (k2_funct_1 @ (k2_funct_1 @ sk_D))))),
% 21.81/22.00      inference('sup-', [status(thm)], ['105', '111'])).
% 21.81/22.00  thf('113', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 21.81/22.00      inference('demod', [status(thm)], ['60', '67', '70'])).
% 21.81/22.00  thf('114', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 21.81/22.00      inference('sup+', [status(thm)], ['55', '56'])).
% 21.81/22.00  thf('115', plain, ((v1_relat_1 @ sk_D)),
% 21.81/22.00      inference('demod', [status(thm)], ['49', '50'])).
% 21.81/22.00  thf('116', plain, ((v1_funct_1 @ sk_D)),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf('117', plain, ((v2_funct_1 @ sk_D)),
% 21.81/22.00      inference('sup-', [status(thm)], ['102', '103'])).
% 21.81/22.00  thf('118', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 21.81/22.00      inference('demod', [status(thm)], ['79', '104'])).
% 21.81/22.00  thf('119', plain, ((v1_relat_1 @ sk_C)),
% 21.81/22.00      inference('demod', [status(thm)], ['75', '76'])).
% 21.81/22.00  thf('120', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 21.81/22.00      inference('demod', [status(thm)], ['79', '104'])).
% 21.81/22.00  thf('121', plain, ((v1_funct_1 @ sk_C)),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf('122', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 21.81/22.00      inference('demod', [status(thm)], ['79', '104'])).
% 21.81/22.00  thf('123', plain, ((v2_funct_1 @ sk_C)),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf('124', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 21.81/22.00      inference('demod', [status(thm)], ['39', '42', '43', '44', '45'])).
% 21.81/22.00  thf('125', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 21.81/22.00      inference('demod', [status(thm)], ['79', '104'])).
% 21.81/22.00  thf('126', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf('127', plain,
% 21.81/22.00      (![X22 : $i, X23 : $i, X24 : $i]:
% 21.81/22.00         (~ (v1_funct_2 @ X24 @ X22 @ X23)
% 21.81/22.00          | ((X22) = (k1_relset_1 @ X22 @ X23 @ X24))
% 21.81/22.00          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_1])).
% 21.81/22.00  thf('128', plain,
% 21.81/22.00      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 21.81/22.00        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 21.81/22.00      inference('sup-', [status(thm)], ['126', '127'])).
% 21.81/22.00  thf('129', plain,
% 21.81/22.00      (![X20 : $i, X21 : $i]:
% 21.81/22.00         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_2])).
% 21.81/22.00  thf('130', plain,
% 21.81/22.00      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf('131', plain,
% 21.81/22.00      (![X25 : $i, X26 : $i, X27 : $i]:
% 21.81/22.00         (~ (zip_tseitin_0 @ X25 @ X26)
% 21.81/22.00          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 21.81/22.00          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_5])).
% 21.81/22.00  thf('132', plain,
% 21.81/22.00      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 21.81/22.00      inference('sup-', [status(thm)], ['130', '131'])).
% 21.81/22.00  thf('133', plain,
% 21.81/22.00      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 21.81/22.00      inference('sup-', [status(thm)], ['129', '132'])).
% 21.81/22.00  thf('134', plain, (((sk_B) != (k1_xboole_0))),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf('135', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 21.81/22.00      inference('simplify_reflect-', [status(thm)], ['133', '134'])).
% 21.81/22.00  thf('136', plain,
% 21.81/22.00      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf('137', plain,
% 21.81/22.00      (![X9 : $i, X10 : $i, X11 : $i]:
% 21.81/22.00         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 21.81/22.00          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 21.81/22.00      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 21.81/22.00  thf('138', plain,
% 21.81/22.00      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 21.81/22.00      inference('sup-', [status(thm)], ['136', '137'])).
% 21.81/22.00  thf('139', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 21.81/22.00      inference('demod', [status(thm)], ['128', '135', '138'])).
% 21.81/22.00  thf('140', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 21.81/22.00      inference('demod', [status(thm)], ['79', '104'])).
% 21.81/22.00  thf('141', plain,
% 21.81/22.00      ((((k6_partfun1 @ sk_B) != (k6_partfun1 @ sk_B))
% 21.81/22.00        | ((sk_A) != (sk_A))
% 21.81/22.00        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 21.81/22.00      inference('demod', [status(thm)],
% 21.81/22.00                ['112', '113', '114', '115', '116', '117', '118', '119', 
% 21.81/22.00                 '120', '121', '122', '123', '124', '125', '139', '140'])).
% 21.81/22.00  thf('142', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 21.81/22.00      inference('simplify', [status(thm)], ['141'])).
% 21.81/22.00  thf('143', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 21.81/22.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.81/22.00  thf('144', plain, ($false),
% 21.81/22.00      inference('simplify_reflect-', [status(thm)], ['142', '143'])).
% 21.81/22.00  
% 21.81/22.00  % SZS output end Refutation
% 21.81/22.00  
% 21.81/22.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cZZm0fJfMp

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:04 EST 2020

% Result     : Theorem 13.22s
% Output     : Refutation 13.22s
% Verified   : 
% Statistics : Number of formulae       :  192 (1382 expanded)
%              Number of leaves         :   48 ( 431 expanded)
%              Depth                    :   17
%              Number of atoms          : 1635 (32242 expanded)
%              Number of equality atoms :   92 ( 422 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t87_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( v3_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ ( k6_partfun1 @ A ) )
           => ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( v3_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ A )
              & ( v3_funct_2 @ C @ A @ A )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ ( k6_partfun1 @ A ) )
             => ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k2_funct_2 @ A @ B )
        = ( k2_funct_1 @ B ) ) ) )).

thf('2',plain,(
    ! [X48: $i,X49: $i] :
      ( ( ( k2_funct_2 @ X49 @ X48 )
        = ( k2_funct_1 @ X48 ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X49 ) ) )
      | ~ ( v3_funct_2 @ X48 @ X49 @ X49 )
      | ~ ( v1_funct_2 @ X48 @ X49 @ X49 )
      | ~ ( v1_funct_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B )
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('8',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('9',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('10',plain,(
    ! [X50: $i] :
      ( ( k6_partfun1 @ X50 )
      = ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('11',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('14',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ( ( k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45 )
        = ( k5_relat_1 @ X42 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
      = ( k5_relat_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
    = ( k5_relat_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ sk_C ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['11','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('24',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
    = ( k5_relat_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('32',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('33',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( X17 = X20 )
      | ~ ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ sk_C ) @ X0 )
      | ( ( k5_relat_1 @ sk_B @ sk_C )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_B @ sk_C )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','34'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('36',plain,(
    ! [X41: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('37',plain,(
    ! [X50: $i] :
      ( ( k6_partfun1 @ X50 )
      = ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('38',plain,(
    ! [X41: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k5_relat_1 @ sk_B @ sk_C )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['35','38'])).

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

thf('40',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( X6
        = ( k2_funct_1 @ X7 ) )
      | ( ( k5_relat_1 @ X6 @ X7 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X7 ) ) )
      | ( ( k2_relat_1 @ X6 )
       != ( k1_relat_1 @ X7 ) )
      | ~ ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('41',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_B )
     != ( k1_relat_1 @ sk_C ) )
    | ( sk_B
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) ) ) ) )).

thf('43',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_1 @ X21 )
      | ~ ( v3_funct_2 @ X21 @ X22 @ X23 )
      | ( v2_funct_2 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('44',plain,
    ( ( v2_funct_2 @ sk_C @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_funct_2 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['44','45','46'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('48',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v2_funct_2 @ X33 @ X32 )
      | ( ( k2_relat_1 @ X33 )
        = X32 )
      | ~ ( v5_relat_1 @ X33 @ X32 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v5_relat_1 @ sk_C @ sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('51',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('52',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('54',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('55',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['49','52','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('58',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_1 @ X21 )
      | ~ ( v3_funct_2 @ X21 @ X22 @ X23 )
      | ( v2_funct_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('61',plain,
    ( ( v2_funct_1 @ sk_C )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_1 @ X21 )
      | ~ ( v3_funct_2 @ X21 @ X22 @ X23 )
      | ( v2_funct_2 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('67',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v2_funct_2 @ X33 @ X32 )
      | ( ( k2_relat_1 @ X33 )
        = X32 )
      | ~ ( v5_relat_1 @ X33 @ X32 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('72',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('75',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('78',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['72','75','78'])).

thf('80',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
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

thf('81',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ( X26
        = ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('82',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('84',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('85',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_A @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('87',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X25 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('88',plain,(
    ! [X24: $i] :
      ( zip_tseitin_0 @ X24 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['86','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['89'])).

thf('91',plain,(
    zip_tseitin_1 @ sk_C @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['85','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('93',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('94',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['82','91','94'])).

thf('96',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['73','74'])).

thf('98',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ sk_A ) )
    | ( sk_A != sk_A )
    | ( sk_B
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['41','56','57','58','64','79','95','96','97'])).

thf('99',plain,
    ( sk_B
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['98'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('100',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k5_relat_1 @ X5 @ ( k2_funct_1 @ X5 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('101',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( X6
        = ( k2_funct_1 @ X7 ) )
      | ( ( k5_relat_1 @ X6 @ X7 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X7 ) ) )
      | ( ( k2_relat_1 @ X6 )
       != ( k1_relat_1 @ X7 ) )
      | ~ ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
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
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
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
      | ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,
    ( ( ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['99','103'])).

thf('105',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['82','91','94'])).

thf('106',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['72','75','78'])).

thf('107',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('108',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('110',plain,
    ( sk_B
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['98'])).

thf('111',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['73','74'])).

thf('112',plain,
    ( sk_B
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['98'])).

thf('113',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( sk_B
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['98'])).

thf('115',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_1 @ X21 )
      | ~ ( v3_funct_2 @ X21 @ X22 @ X23 )
      | ( v2_funct_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('117',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['49','52','55'])).

thf('122',plain,
    ( sk_B
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['98'])).

thf('123',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ( X26
        = ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('125',plain,
    ( ~ ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('128',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['89'])).

thf('130',plain,(
    zip_tseitin_1 @ sk_B @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('133',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['125','130','133'])).

thf('135',plain,
    ( sk_B
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['98'])).

thf('136',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ sk_A ) )
    | ( sk_A != sk_A )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['104','105','106','107','108','109','110','111','112','113','114','120','121','122','134','135'])).

thf('137',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 )
      | ( X17 != X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('140',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_relset_1 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['138','140'])).

thf('142',plain,(
    $false ),
    inference(demod,[status(thm)],['8','137','141'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cZZm0fJfMp
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:06:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 13.22/13.40  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 13.22/13.40  % Solved by: fo/fo7.sh
% 13.22/13.40  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 13.22/13.40  % done 4980 iterations in 12.938s
% 13.22/13.40  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 13.22/13.40  % SZS output start Refutation
% 13.22/13.40  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 13.22/13.40  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 13.22/13.40  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 13.22/13.40  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 13.22/13.40  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 13.22/13.40  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 13.22/13.40  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 13.22/13.40  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 13.22/13.40  thf(sk_C_type, type, sk_C: $i).
% 13.22/13.40  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 13.22/13.40  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 13.22/13.40  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 13.22/13.40  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 13.22/13.40  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 13.22/13.40  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 13.22/13.40  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 13.22/13.40  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 13.22/13.40  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 13.22/13.40  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 13.22/13.40  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 13.22/13.40  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 13.22/13.40  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 13.22/13.40  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 13.22/13.40  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 13.22/13.40  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 13.22/13.40  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 13.22/13.40  thf(sk_B_type, type, sk_B: $i).
% 13.22/13.40  thf(sk_A_type, type, sk_A: $i).
% 13.22/13.40  thf(t87_funct_2, conjecture,
% 13.22/13.40    (![A:$i,B:$i]:
% 13.22/13.40     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 13.22/13.40         ( v3_funct_2 @ B @ A @ A ) & 
% 13.22/13.40         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 13.22/13.40       ( ![C:$i]:
% 13.22/13.40         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 13.22/13.40             ( v3_funct_2 @ C @ A @ A ) & 
% 13.22/13.40             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 13.22/13.40           ( ( r2_relset_1 @
% 13.22/13.40               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 13.22/13.40               ( k6_partfun1 @ A ) ) =>
% 13.22/13.40             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 13.22/13.40  thf(zf_stmt_0, negated_conjecture,
% 13.22/13.40    (~( ![A:$i,B:$i]:
% 13.22/13.40        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 13.22/13.40            ( v3_funct_2 @ B @ A @ A ) & 
% 13.22/13.40            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 13.22/13.40          ( ![C:$i]:
% 13.22/13.40            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 13.22/13.40                ( v3_funct_2 @ C @ A @ A ) & 
% 13.22/13.40                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 13.22/13.40              ( ( r2_relset_1 @
% 13.22/13.40                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 13.22/13.40                  ( k6_partfun1 @ A ) ) =>
% 13.22/13.40                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 13.22/13.40    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 13.22/13.40  thf('0', plain,
% 13.22/13.40      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B))),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf('1', plain,
% 13.22/13.40      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf(redefinition_k2_funct_2, axiom,
% 13.22/13.40    (![A:$i,B:$i]:
% 13.22/13.40     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 13.22/13.40         ( v3_funct_2 @ B @ A @ A ) & 
% 13.22/13.40         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 13.22/13.40       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 13.22/13.40  thf('2', plain,
% 13.22/13.40      (![X48 : $i, X49 : $i]:
% 13.22/13.40         (((k2_funct_2 @ X49 @ X48) = (k2_funct_1 @ X48))
% 13.22/13.40          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X49)))
% 13.22/13.40          | ~ (v3_funct_2 @ X48 @ X49 @ X49)
% 13.22/13.40          | ~ (v1_funct_2 @ X48 @ X49 @ X49)
% 13.22/13.40          | ~ (v1_funct_1 @ X48))),
% 13.22/13.40      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 13.22/13.40  thf('3', plain,
% 13.22/13.40      ((~ (v1_funct_1 @ sk_B)
% 13.22/13.40        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 13.22/13.40        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 13.22/13.40        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 13.22/13.40      inference('sup-', [status(thm)], ['1', '2'])).
% 13.22/13.40  thf('4', plain, ((v1_funct_1 @ sk_B)),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf('5', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf('6', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf('7', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 13.22/13.40      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 13.22/13.40  thf('8', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 13.22/13.40      inference('demod', [status(thm)], ['0', '7'])).
% 13.22/13.40  thf('9', plain,
% 13.22/13.40      ((r2_relset_1 @ sk_A @ sk_A @ 
% 13.22/13.40        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 13.22/13.40        (k6_partfun1 @ sk_A))),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf(redefinition_k6_partfun1, axiom,
% 13.22/13.40    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 13.22/13.40  thf('10', plain, (![X50 : $i]: ((k6_partfun1 @ X50) = (k6_relat_1 @ X50))),
% 13.22/13.40      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 13.22/13.40  thf('11', plain,
% 13.22/13.40      ((r2_relset_1 @ sk_A @ sk_A @ 
% 13.22/13.40        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 13.22/13.40        (k6_relat_1 @ sk_A))),
% 13.22/13.40      inference('demod', [status(thm)], ['9', '10'])).
% 13.22/13.40  thf('12', plain,
% 13.22/13.40      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf('13', plain,
% 13.22/13.40      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf(redefinition_k1_partfun1, axiom,
% 13.22/13.40    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 13.22/13.40     ( ( ( v1_funct_1 @ E ) & 
% 13.22/13.40         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 13.22/13.40         ( v1_funct_1 @ F ) & 
% 13.22/13.40         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 13.22/13.40       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 13.22/13.40  thf('14', plain,
% 13.22/13.40      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 13.22/13.40         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 13.22/13.40          | ~ (v1_funct_1 @ X42)
% 13.22/13.40          | ~ (v1_funct_1 @ X45)
% 13.22/13.40          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 13.22/13.40          | ((k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45)
% 13.22/13.40              = (k5_relat_1 @ X42 @ X45)))),
% 13.22/13.40      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 13.22/13.40  thf('15', plain,
% 13.22/13.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.22/13.40         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 13.22/13.40            = (k5_relat_1 @ sk_B @ X0))
% 13.22/13.40          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 13.22/13.40          | ~ (v1_funct_1 @ X0)
% 13.22/13.40          | ~ (v1_funct_1 @ sk_B))),
% 13.22/13.40      inference('sup-', [status(thm)], ['13', '14'])).
% 13.22/13.40  thf('16', plain, ((v1_funct_1 @ sk_B)),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf('17', plain,
% 13.22/13.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.22/13.40         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 13.22/13.40            = (k5_relat_1 @ sk_B @ X0))
% 13.22/13.40          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 13.22/13.40          | ~ (v1_funct_1 @ X0))),
% 13.22/13.40      inference('demod', [status(thm)], ['15', '16'])).
% 13.22/13.40  thf('18', plain,
% 13.22/13.40      ((~ (v1_funct_1 @ sk_C)
% 13.22/13.40        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 13.22/13.40            = (k5_relat_1 @ sk_B @ sk_C)))),
% 13.22/13.40      inference('sup-', [status(thm)], ['12', '17'])).
% 13.22/13.40  thf('19', plain, ((v1_funct_1 @ sk_C)),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf('20', plain,
% 13.22/13.40      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 13.22/13.40         = (k5_relat_1 @ sk_B @ sk_C))),
% 13.22/13.40      inference('demod', [status(thm)], ['18', '19'])).
% 13.22/13.40  thf('21', plain,
% 13.22/13.40      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_B @ sk_C) @ 
% 13.22/13.40        (k6_relat_1 @ sk_A))),
% 13.22/13.40      inference('demod', [status(thm)], ['11', '20'])).
% 13.22/13.40  thf('22', plain,
% 13.22/13.40      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf('23', plain,
% 13.22/13.40      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf(dt_k1_partfun1, axiom,
% 13.22/13.40    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 13.22/13.40     ( ( ( v1_funct_1 @ E ) & 
% 13.22/13.40         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 13.22/13.40         ( v1_funct_1 @ F ) & 
% 13.22/13.40         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 13.22/13.40       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 13.22/13.40         ( m1_subset_1 @
% 13.22/13.40           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 13.22/13.40           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 13.22/13.40  thf('24', plain,
% 13.22/13.40      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 13.22/13.40         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 13.22/13.40          | ~ (v1_funct_1 @ X34)
% 13.22/13.40          | ~ (v1_funct_1 @ X37)
% 13.22/13.40          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 13.22/13.40          | (m1_subset_1 @ (k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37) @ 
% 13.22/13.40             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X39))))),
% 13.22/13.40      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 13.22/13.40  thf('25', plain,
% 13.22/13.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.22/13.40         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 13.22/13.40           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 13.22/13.40          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 13.22/13.40          | ~ (v1_funct_1 @ X1)
% 13.22/13.40          | ~ (v1_funct_1 @ sk_B))),
% 13.22/13.40      inference('sup-', [status(thm)], ['23', '24'])).
% 13.22/13.40  thf('26', plain, ((v1_funct_1 @ sk_B)),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf('27', plain,
% 13.22/13.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.22/13.40         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 13.22/13.40           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 13.22/13.40          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 13.22/13.40          | ~ (v1_funct_1 @ X1))),
% 13.22/13.40      inference('demod', [status(thm)], ['25', '26'])).
% 13.22/13.40  thf('28', plain,
% 13.22/13.40      ((~ (v1_funct_1 @ sk_C)
% 13.22/13.40        | (m1_subset_1 @ 
% 13.22/13.40           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 13.22/13.40           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 13.22/13.40      inference('sup-', [status(thm)], ['22', '27'])).
% 13.22/13.40  thf('29', plain, ((v1_funct_1 @ sk_C)),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf('30', plain,
% 13.22/13.40      ((m1_subset_1 @ 
% 13.22/13.40        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 13.22/13.40        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 13.22/13.40      inference('demod', [status(thm)], ['28', '29'])).
% 13.22/13.40  thf('31', plain,
% 13.22/13.40      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 13.22/13.40         = (k5_relat_1 @ sk_B @ sk_C))),
% 13.22/13.40      inference('demod', [status(thm)], ['18', '19'])).
% 13.22/13.40  thf('32', plain,
% 13.22/13.40      ((m1_subset_1 @ (k5_relat_1 @ sk_B @ sk_C) @ 
% 13.22/13.40        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 13.22/13.40      inference('demod', [status(thm)], ['30', '31'])).
% 13.22/13.40  thf(redefinition_r2_relset_1, axiom,
% 13.22/13.40    (![A:$i,B:$i,C:$i,D:$i]:
% 13.22/13.40     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 13.22/13.40         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 13.22/13.40       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 13.22/13.40  thf('33', plain,
% 13.22/13.40      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 13.22/13.40         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 13.22/13.40          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 13.22/13.40          | ((X17) = (X20))
% 13.22/13.40          | ~ (r2_relset_1 @ X18 @ X19 @ X17 @ X20))),
% 13.22/13.40      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 13.22/13.40  thf('34', plain,
% 13.22/13.40      (![X0 : $i]:
% 13.22/13.40         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_B @ sk_C) @ X0)
% 13.22/13.40          | ((k5_relat_1 @ sk_B @ sk_C) = (X0))
% 13.22/13.40          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 13.22/13.40      inference('sup-', [status(thm)], ['32', '33'])).
% 13.22/13.40  thf('35', plain,
% 13.22/13.40      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 13.22/13.40           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 13.22/13.40        | ((k5_relat_1 @ sk_B @ sk_C) = (k6_relat_1 @ sk_A)))),
% 13.22/13.40      inference('sup-', [status(thm)], ['21', '34'])).
% 13.22/13.40  thf(dt_k6_partfun1, axiom,
% 13.22/13.40    (![A:$i]:
% 13.22/13.40     ( ( m1_subset_1 @
% 13.22/13.40         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 13.22/13.40       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 13.22/13.40  thf('36', plain,
% 13.22/13.40      (![X41 : $i]:
% 13.22/13.40         (m1_subset_1 @ (k6_partfun1 @ X41) @ 
% 13.22/13.40          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))),
% 13.22/13.40      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 13.22/13.40  thf('37', plain, (![X50 : $i]: ((k6_partfun1 @ X50) = (k6_relat_1 @ X50))),
% 13.22/13.40      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 13.22/13.40  thf('38', plain,
% 13.22/13.40      (![X41 : $i]:
% 13.22/13.40         (m1_subset_1 @ (k6_relat_1 @ X41) @ 
% 13.22/13.40          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))),
% 13.22/13.40      inference('demod', [status(thm)], ['36', '37'])).
% 13.22/13.40  thf('39', plain, (((k5_relat_1 @ sk_B @ sk_C) = (k6_relat_1 @ sk_A))),
% 13.22/13.40      inference('demod', [status(thm)], ['35', '38'])).
% 13.22/13.40  thf(t64_funct_1, axiom,
% 13.22/13.40    (![A:$i]:
% 13.22/13.40     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 13.22/13.40       ( ![B:$i]:
% 13.22/13.40         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 13.22/13.40           ( ( ( v2_funct_1 @ A ) & 
% 13.22/13.40               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 13.22/13.40               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 13.22/13.40             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 13.22/13.40  thf('40', plain,
% 13.22/13.40      (![X6 : $i, X7 : $i]:
% 13.22/13.40         (~ (v1_relat_1 @ X6)
% 13.22/13.40          | ~ (v1_funct_1 @ X6)
% 13.22/13.40          | ((X6) = (k2_funct_1 @ X7))
% 13.22/13.40          | ((k5_relat_1 @ X6 @ X7) != (k6_relat_1 @ (k2_relat_1 @ X7)))
% 13.22/13.40          | ((k2_relat_1 @ X6) != (k1_relat_1 @ X7))
% 13.22/13.40          | ~ (v2_funct_1 @ X7)
% 13.22/13.40          | ~ (v1_funct_1 @ X7)
% 13.22/13.40          | ~ (v1_relat_1 @ X7))),
% 13.22/13.40      inference('cnf', [status(esa)], [t64_funct_1])).
% 13.22/13.40  thf('41', plain,
% 13.22/13.40      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 13.22/13.40        | ~ (v1_relat_1 @ sk_C)
% 13.22/13.40        | ~ (v1_funct_1 @ sk_C)
% 13.22/13.40        | ~ (v2_funct_1 @ sk_C)
% 13.22/13.40        | ((k2_relat_1 @ sk_B) != (k1_relat_1 @ sk_C))
% 13.22/13.40        | ((sk_B) = (k2_funct_1 @ sk_C))
% 13.22/13.40        | ~ (v1_funct_1 @ sk_B)
% 13.22/13.40        | ~ (v1_relat_1 @ sk_B))),
% 13.22/13.40      inference('sup-', [status(thm)], ['39', '40'])).
% 13.22/13.40  thf('42', plain,
% 13.22/13.40      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf(cc2_funct_2, axiom,
% 13.22/13.40    (![A:$i,B:$i,C:$i]:
% 13.22/13.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 13.22/13.40       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 13.22/13.40         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 13.22/13.40  thf('43', plain,
% 13.22/13.40      (![X21 : $i, X22 : $i, X23 : $i]:
% 13.22/13.40         (~ (v1_funct_1 @ X21)
% 13.22/13.40          | ~ (v3_funct_2 @ X21 @ X22 @ X23)
% 13.22/13.40          | (v2_funct_2 @ X21 @ X23)
% 13.22/13.40          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 13.22/13.40      inference('cnf', [status(esa)], [cc2_funct_2])).
% 13.22/13.40  thf('44', plain,
% 13.22/13.40      (((v2_funct_2 @ sk_C @ sk_A)
% 13.22/13.40        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 13.22/13.40        | ~ (v1_funct_1 @ sk_C))),
% 13.22/13.40      inference('sup-', [status(thm)], ['42', '43'])).
% 13.22/13.40  thf('45', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf('46', plain, ((v1_funct_1 @ sk_C)),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf('47', plain, ((v2_funct_2 @ sk_C @ sk_A)),
% 13.22/13.40      inference('demod', [status(thm)], ['44', '45', '46'])).
% 13.22/13.40  thf(d3_funct_2, axiom,
% 13.22/13.40    (![A:$i,B:$i]:
% 13.22/13.40     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 13.22/13.40       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 13.22/13.40  thf('48', plain,
% 13.22/13.40      (![X32 : $i, X33 : $i]:
% 13.22/13.40         (~ (v2_funct_2 @ X33 @ X32)
% 13.22/13.40          | ((k2_relat_1 @ X33) = (X32))
% 13.22/13.40          | ~ (v5_relat_1 @ X33 @ X32)
% 13.22/13.40          | ~ (v1_relat_1 @ X33))),
% 13.22/13.40      inference('cnf', [status(esa)], [d3_funct_2])).
% 13.22/13.40  thf('49', plain,
% 13.22/13.40      ((~ (v1_relat_1 @ sk_C)
% 13.22/13.40        | ~ (v5_relat_1 @ sk_C @ sk_A)
% 13.22/13.40        | ((k2_relat_1 @ sk_C) = (sk_A)))),
% 13.22/13.40      inference('sup-', [status(thm)], ['47', '48'])).
% 13.22/13.40  thf('50', plain,
% 13.22/13.40      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf(cc1_relset_1, axiom,
% 13.22/13.40    (![A:$i,B:$i,C:$i]:
% 13.22/13.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 13.22/13.40       ( v1_relat_1 @ C ) ))).
% 13.22/13.40  thf('51', plain,
% 13.22/13.40      (![X8 : $i, X9 : $i, X10 : $i]:
% 13.22/13.40         ((v1_relat_1 @ X8)
% 13.22/13.40          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 13.22/13.40      inference('cnf', [status(esa)], [cc1_relset_1])).
% 13.22/13.40  thf('52', plain, ((v1_relat_1 @ sk_C)),
% 13.22/13.40      inference('sup-', [status(thm)], ['50', '51'])).
% 13.22/13.40  thf('53', plain,
% 13.22/13.40      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf(cc2_relset_1, axiom,
% 13.22/13.40    (![A:$i,B:$i,C:$i]:
% 13.22/13.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 13.22/13.40       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 13.22/13.40  thf('54', plain,
% 13.22/13.40      (![X11 : $i, X12 : $i, X13 : $i]:
% 13.22/13.40         ((v5_relat_1 @ X11 @ X13)
% 13.22/13.40          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 13.22/13.40      inference('cnf', [status(esa)], [cc2_relset_1])).
% 13.22/13.40  thf('55', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 13.22/13.40      inference('sup-', [status(thm)], ['53', '54'])).
% 13.22/13.40  thf('56', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 13.22/13.40      inference('demod', [status(thm)], ['49', '52', '55'])).
% 13.22/13.40  thf('57', plain, ((v1_relat_1 @ sk_C)),
% 13.22/13.40      inference('sup-', [status(thm)], ['50', '51'])).
% 13.22/13.40  thf('58', plain, ((v1_funct_1 @ sk_C)),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf('59', plain,
% 13.22/13.40      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf('60', plain,
% 13.22/13.40      (![X21 : $i, X22 : $i, X23 : $i]:
% 13.22/13.40         (~ (v1_funct_1 @ X21)
% 13.22/13.40          | ~ (v3_funct_2 @ X21 @ X22 @ X23)
% 13.22/13.40          | (v2_funct_1 @ X21)
% 13.22/13.40          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 13.22/13.40      inference('cnf', [status(esa)], [cc2_funct_2])).
% 13.22/13.40  thf('61', plain,
% 13.22/13.40      (((v2_funct_1 @ sk_C)
% 13.22/13.40        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 13.22/13.40        | ~ (v1_funct_1 @ sk_C))),
% 13.22/13.40      inference('sup-', [status(thm)], ['59', '60'])).
% 13.22/13.40  thf('62', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf('63', plain, ((v1_funct_1 @ sk_C)),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf('64', plain, ((v2_funct_1 @ sk_C)),
% 13.22/13.40      inference('demod', [status(thm)], ['61', '62', '63'])).
% 13.22/13.40  thf('65', plain,
% 13.22/13.40      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf('66', plain,
% 13.22/13.40      (![X21 : $i, X22 : $i, X23 : $i]:
% 13.22/13.40         (~ (v1_funct_1 @ X21)
% 13.22/13.40          | ~ (v3_funct_2 @ X21 @ X22 @ X23)
% 13.22/13.40          | (v2_funct_2 @ X21 @ X23)
% 13.22/13.40          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 13.22/13.40      inference('cnf', [status(esa)], [cc2_funct_2])).
% 13.22/13.40  thf('67', plain,
% 13.22/13.40      (((v2_funct_2 @ sk_B @ sk_A)
% 13.22/13.40        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 13.22/13.40        | ~ (v1_funct_1 @ sk_B))),
% 13.22/13.40      inference('sup-', [status(thm)], ['65', '66'])).
% 13.22/13.40  thf('68', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf('69', plain, ((v1_funct_1 @ sk_B)),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf('70', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 13.22/13.40      inference('demod', [status(thm)], ['67', '68', '69'])).
% 13.22/13.40  thf('71', plain,
% 13.22/13.40      (![X32 : $i, X33 : $i]:
% 13.22/13.40         (~ (v2_funct_2 @ X33 @ X32)
% 13.22/13.40          | ((k2_relat_1 @ X33) = (X32))
% 13.22/13.40          | ~ (v5_relat_1 @ X33 @ X32)
% 13.22/13.40          | ~ (v1_relat_1 @ X33))),
% 13.22/13.40      inference('cnf', [status(esa)], [d3_funct_2])).
% 13.22/13.40  thf('72', plain,
% 13.22/13.40      ((~ (v1_relat_1 @ sk_B)
% 13.22/13.40        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 13.22/13.40        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 13.22/13.40      inference('sup-', [status(thm)], ['70', '71'])).
% 13.22/13.40  thf('73', plain,
% 13.22/13.40      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf('74', plain,
% 13.22/13.40      (![X8 : $i, X9 : $i, X10 : $i]:
% 13.22/13.40         ((v1_relat_1 @ X8)
% 13.22/13.40          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 13.22/13.40      inference('cnf', [status(esa)], [cc1_relset_1])).
% 13.22/13.40  thf('75', plain, ((v1_relat_1 @ sk_B)),
% 13.22/13.40      inference('sup-', [status(thm)], ['73', '74'])).
% 13.22/13.40  thf('76', plain,
% 13.22/13.40      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf('77', plain,
% 13.22/13.40      (![X11 : $i, X12 : $i, X13 : $i]:
% 13.22/13.40         ((v5_relat_1 @ X11 @ X13)
% 13.22/13.40          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 13.22/13.40      inference('cnf', [status(esa)], [cc2_relset_1])).
% 13.22/13.40  thf('78', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 13.22/13.40      inference('sup-', [status(thm)], ['76', '77'])).
% 13.22/13.40  thf('79', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 13.22/13.40      inference('demod', [status(thm)], ['72', '75', '78'])).
% 13.22/13.40  thf('80', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf(d1_funct_2, axiom,
% 13.22/13.40    (![A:$i,B:$i,C:$i]:
% 13.22/13.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 13.22/13.40       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 13.22/13.40           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 13.22/13.40             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 13.22/13.40         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 13.22/13.40           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 13.22/13.40             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 13.22/13.40  thf(zf_stmt_1, axiom,
% 13.22/13.40    (![C:$i,B:$i,A:$i]:
% 13.22/13.40     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 13.22/13.40       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 13.22/13.40  thf('81', plain,
% 13.22/13.40      (![X26 : $i, X27 : $i, X28 : $i]:
% 13.22/13.40         (~ (v1_funct_2 @ X28 @ X26 @ X27)
% 13.22/13.40          | ((X26) = (k1_relset_1 @ X26 @ X27 @ X28))
% 13.22/13.40          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_1])).
% 13.22/13.40  thf('82', plain,
% 13.22/13.40      ((~ (zip_tseitin_1 @ sk_C @ sk_A @ sk_A)
% 13.22/13.40        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_A @ sk_C)))),
% 13.22/13.40      inference('sup-', [status(thm)], ['80', '81'])).
% 13.22/13.40  thf('83', plain,
% 13.22/13.40      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 13.22/13.40  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 13.22/13.40  thf(zf_stmt_4, axiom,
% 13.22/13.40    (![B:$i,A:$i]:
% 13.22/13.40     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 13.22/13.40       ( zip_tseitin_0 @ B @ A ) ))).
% 13.22/13.40  thf(zf_stmt_5, axiom,
% 13.22/13.40    (![A:$i,B:$i,C:$i]:
% 13.22/13.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 13.22/13.40       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 13.22/13.40         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 13.22/13.40           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 13.22/13.40             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 13.22/13.40  thf('84', plain,
% 13.22/13.40      (![X29 : $i, X30 : $i, X31 : $i]:
% 13.22/13.40         (~ (zip_tseitin_0 @ X29 @ X30)
% 13.22/13.40          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 13.22/13.40          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_5])).
% 13.22/13.40  thf('85', plain,
% 13.22/13.40      (((zip_tseitin_1 @ sk_C @ sk_A @ sk_A) | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 13.22/13.40      inference('sup-', [status(thm)], ['83', '84'])).
% 13.22/13.40  thf('86', plain,
% 13.22/13.40      (![X24 : $i, X25 : $i]:
% 13.22/13.40         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_4])).
% 13.22/13.40  thf('87', plain,
% 13.22/13.40      (![X24 : $i, X25 : $i]:
% 13.22/13.40         ((zip_tseitin_0 @ X24 @ X25) | ((X25) != (k1_xboole_0)))),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_4])).
% 13.22/13.40  thf('88', plain, (![X24 : $i]: (zip_tseitin_0 @ X24 @ k1_xboole_0)),
% 13.22/13.40      inference('simplify', [status(thm)], ['87'])).
% 13.22/13.40  thf('89', plain,
% 13.22/13.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.22/13.40         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 13.22/13.40      inference('sup+', [status(thm)], ['86', '88'])).
% 13.22/13.40  thf('90', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 13.22/13.40      inference('eq_fact', [status(thm)], ['89'])).
% 13.22/13.40  thf('91', plain, ((zip_tseitin_1 @ sk_C @ sk_A @ sk_A)),
% 13.22/13.40      inference('demod', [status(thm)], ['85', '90'])).
% 13.22/13.40  thf('92', plain,
% 13.22/13.40      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf(redefinition_k1_relset_1, axiom,
% 13.22/13.40    (![A:$i,B:$i,C:$i]:
% 13.22/13.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 13.22/13.40       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 13.22/13.40  thf('93', plain,
% 13.22/13.40      (![X14 : $i, X15 : $i, X16 : $i]:
% 13.22/13.40         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 13.22/13.40          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 13.22/13.40      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 13.22/13.40  thf('94', plain,
% 13.22/13.40      (((k1_relset_1 @ sk_A @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 13.22/13.40      inference('sup-', [status(thm)], ['92', '93'])).
% 13.22/13.40  thf('95', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 13.22/13.40      inference('demod', [status(thm)], ['82', '91', '94'])).
% 13.22/13.40  thf('96', plain, ((v1_funct_1 @ sk_B)),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf('97', plain, ((v1_relat_1 @ sk_B)),
% 13.22/13.40      inference('sup-', [status(thm)], ['73', '74'])).
% 13.22/13.40  thf('98', plain,
% 13.22/13.40      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ sk_A))
% 13.22/13.40        | ((sk_A) != (sk_A))
% 13.22/13.40        | ((sk_B) = (k2_funct_1 @ sk_C)))),
% 13.22/13.40      inference('demod', [status(thm)],
% 13.22/13.40                ['41', '56', '57', '58', '64', '79', '95', '96', '97'])).
% 13.22/13.40  thf('99', plain, (((sk_B) = (k2_funct_1 @ sk_C))),
% 13.22/13.40      inference('simplify', [status(thm)], ['98'])).
% 13.22/13.40  thf(t61_funct_1, axiom,
% 13.22/13.40    (![A:$i]:
% 13.22/13.40     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 13.22/13.40       ( ( v2_funct_1 @ A ) =>
% 13.22/13.40         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 13.22/13.40             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 13.22/13.40           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 13.22/13.40             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 13.22/13.40  thf('100', plain,
% 13.22/13.40      (![X5 : $i]:
% 13.22/13.40         (~ (v2_funct_1 @ X5)
% 13.22/13.40          | ((k5_relat_1 @ X5 @ (k2_funct_1 @ X5))
% 13.22/13.40              = (k6_relat_1 @ (k1_relat_1 @ X5)))
% 13.22/13.40          | ~ (v1_funct_1 @ X5)
% 13.22/13.40          | ~ (v1_relat_1 @ X5))),
% 13.22/13.40      inference('cnf', [status(esa)], [t61_funct_1])).
% 13.22/13.40  thf('101', plain,
% 13.22/13.40      (![X6 : $i, X7 : $i]:
% 13.22/13.40         (~ (v1_relat_1 @ X6)
% 13.22/13.40          | ~ (v1_funct_1 @ X6)
% 13.22/13.40          | ((X6) = (k2_funct_1 @ X7))
% 13.22/13.40          | ((k5_relat_1 @ X6 @ X7) != (k6_relat_1 @ (k2_relat_1 @ X7)))
% 13.22/13.40          | ((k2_relat_1 @ X6) != (k1_relat_1 @ X7))
% 13.22/13.40          | ~ (v2_funct_1 @ X7)
% 13.22/13.40          | ~ (v1_funct_1 @ X7)
% 13.22/13.40          | ~ (v1_relat_1 @ X7))),
% 13.22/13.40      inference('cnf', [status(esa)], [t64_funct_1])).
% 13.22/13.40  thf('102', plain,
% 13.22/13.40      (![X0 : $i]:
% 13.22/13.40         (((k6_relat_1 @ (k1_relat_1 @ X0))
% 13.22/13.40            != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 13.22/13.40          | ~ (v1_relat_1 @ X0)
% 13.22/13.40          | ~ (v1_funct_1 @ X0)
% 13.22/13.40          | ~ (v2_funct_1 @ X0)
% 13.22/13.40          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 13.22/13.40          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 13.22/13.40          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 13.22/13.40          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 13.22/13.40          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 13.22/13.40          | ~ (v1_funct_1 @ X0)
% 13.22/13.40          | ~ (v1_relat_1 @ X0))),
% 13.22/13.40      inference('sup-', [status(thm)], ['100', '101'])).
% 13.22/13.40  thf('103', plain,
% 13.22/13.40      (![X0 : $i]:
% 13.22/13.40         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 13.22/13.40          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 13.22/13.40          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 13.22/13.40          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 13.22/13.40          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 13.22/13.40          | ~ (v2_funct_1 @ X0)
% 13.22/13.40          | ~ (v1_funct_1 @ X0)
% 13.22/13.40          | ~ (v1_relat_1 @ X0)
% 13.22/13.40          | ((k6_relat_1 @ (k1_relat_1 @ X0))
% 13.22/13.40              != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 13.22/13.40      inference('simplify', [status(thm)], ['102'])).
% 13.22/13.40  thf('104', plain,
% 13.22/13.40      ((((k6_relat_1 @ (k1_relat_1 @ sk_C))
% 13.22/13.40          != (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 13.22/13.40        | ~ (v1_relat_1 @ sk_C)
% 13.22/13.40        | ~ (v1_funct_1 @ sk_C)
% 13.22/13.40        | ~ (v2_funct_1 @ sk_C)
% 13.22/13.40        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 13.22/13.40        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 13.22/13.40        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 13.22/13.40        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 13.22/13.40        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 13.22/13.40      inference('sup-', [status(thm)], ['99', '103'])).
% 13.22/13.40  thf('105', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 13.22/13.40      inference('demod', [status(thm)], ['82', '91', '94'])).
% 13.22/13.40  thf('106', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 13.22/13.40      inference('demod', [status(thm)], ['72', '75', '78'])).
% 13.22/13.40  thf('107', plain, ((v1_relat_1 @ sk_C)),
% 13.22/13.40      inference('sup-', [status(thm)], ['50', '51'])).
% 13.22/13.40  thf('108', plain, ((v1_funct_1 @ sk_C)),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf('109', plain, ((v2_funct_1 @ sk_C)),
% 13.22/13.40      inference('demod', [status(thm)], ['61', '62', '63'])).
% 13.22/13.40  thf('110', plain, (((sk_B) = (k2_funct_1 @ sk_C))),
% 13.22/13.40      inference('simplify', [status(thm)], ['98'])).
% 13.22/13.40  thf('111', plain, ((v1_relat_1 @ sk_B)),
% 13.22/13.40      inference('sup-', [status(thm)], ['73', '74'])).
% 13.22/13.40  thf('112', plain, (((sk_B) = (k2_funct_1 @ sk_C))),
% 13.22/13.40      inference('simplify', [status(thm)], ['98'])).
% 13.22/13.40  thf('113', plain, ((v1_funct_1 @ sk_B)),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf('114', plain, (((sk_B) = (k2_funct_1 @ sk_C))),
% 13.22/13.40      inference('simplify', [status(thm)], ['98'])).
% 13.22/13.40  thf('115', plain,
% 13.22/13.40      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf('116', plain,
% 13.22/13.40      (![X21 : $i, X22 : $i, X23 : $i]:
% 13.22/13.40         (~ (v1_funct_1 @ X21)
% 13.22/13.40          | ~ (v3_funct_2 @ X21 @ X22 @ X23)
% 13.22/13.40          | (v2_funct_1 @ X21)
% 13.22/13.40          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 13.22/13.40      inference('cnf', [status(esa)], [cc2_funct_2])).
% 13.22/13.40  thf('117', plain,
% 13.22/13.40      (((v2_funct_1 @ sk_B)
% 13.22/13.40        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 13.22/13.40        | ~ (v1_funct_1 @ sk_B))),
% 13.22/13.40      inference('sup-', [status(thm)], ['115', '116'])).
% 13.22/13.40  thf('118', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf('119', plain, ((v1_funct_1 @ sk_B)),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf('120', plain, ((v2_funct_1 @ sk_B)),
% 13.22/13.40      inference('demod', [status(thm)], ['117', '118', '119'])).
% 13.22/13.40  thf('121', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 13.22/13.40      inference('demod', [status(thm)], ['49', '52', '55'])).
% 13.22/13.40  thf('122', plain, (((sk_B) = (k2_funct_1 @ sk_C))),
% 13.22/13.40      inference('simplify', [status(thm)], ['98'])).
% 13.22/13.40  thf('123', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf('124', plain,
% 13.22/13.40      (![X26 : $i, X27 : $i, X28 : $i]:
% 13.22/13.40         (~ (v1_funct_2 @ X28 @ X26 @ X27)
% 13.22/13.40          | ((X26) = (k1_relset_1 @ X26 @ X27 @ X28))
% 13.22/13.40          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_1])).
% 13.22/13.40  thf('125', plain,
% 13.22/13.40      ((~ (zip_tseitin_1 @ sk_B @ sk_A @ sk_A)
% 13.22/13.40        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_A @ sk_B)))),
% 13.22/13.40      inference('sup-', [status(thm)], ['123', '124'])).
% 13.22/13.40  thf('126', plain,
% 13.22/13.40      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf('127', plain,
% 13.22/13.40      (![X29 : $i, X30 : $i, X31 : $i]:
% 13.22/13.40         (~ (zip_tseitin_0 @ X29 @ X30)
% 13.22/13.40          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 13.22/13.40          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_5])).
% 13.22/13.40  thf('128', plain,
% 13.22/13.40      (((zip_tseitin_1 @ sk_B @ sk_A @ sk_A) | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 13.22/13.40      inference('sup-', [status(thm)], ['126', '127'])).
% 13.22/13.40  thf('129', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 13.22/13.40      inference('eq_fact', [status(thm)], ['89'])).
% 13.22/13.40  thf('130', plain, ((zip_tseitin_1 @ sk_B @ sk_A @ sk_A)),
% 13.22/13.40      inference('demod', [status(thm)], ['128', '129'])).
% 13.22/13.40  thf('131', plain,
% 13.22/13.40      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf('132', plain,
% 13.22/13.40      (![X14 : $i, X15 : $i, X16 : $i]:
% 13.22/13.40         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 13.22/13.40          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 13.22/13.40      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 13.22/13.40  thf('133', plain,
% 13.22/13.40      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 13.22/13.40      inference('sup-', [status(thm)], ['131', '132'])).
% 13.22/13.40  thf('134', plain, (((sk_A) = (k1_relat_1 @ sk_B))),
% 13.22/13.40      inference('demod', [status(thm)], ['125', '130', '133'])).
% 13.22/13.40  thf('135', plain, (((sk_B) = (k2_funct_1 @ sk_C))),
% 13.22/13.40      inference('simplify', [status(thm)], ['98'])).
% 13.22/13.40  thf('136', plain,
% 13.22/13.40      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ sk_A))
% 13.22/13.40        | ((sk_A) != (sk_A))
% 13.22/13.40        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 13.22/13.40      inference('demod', [status(thm)],
% 13.22/13.40                ['104', '105', '106', '107', '108', '109', '110', '111', 
% 13.22/13.40                 '112', '113', '114', '120', '121', '122', '134', '135'])).
% 13.22/13.40  thf('137', plain, (((sk_C) = (k2_funct_1 @ sk_B))),
% 13.22/13.40      inference('simplify', [status(thm)], ['136'])).
% 13.22/13.40  thf('138', plain,
% 13.22/13.40      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 13.22/13.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.22/13.40  thf('139', plain,
% 13.22/13.40      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 13.22/13.40         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 13.22/13.40          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 13.22/13.40          | (r2_relset_1 @ X18 @ X19 @ X17 @ X20)
% 13.22/13.40          | ((X17) != (X20)))),
% 13.22/13.40      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 13.22/13.40  thf('140', plain,
% 13.22/13.40      (![X18 : $i, X19 : $i, X20 : $i]:
% 13.22/13.40         ((r2_relset_1 @ X18 @ X19 @ X20 @ X20)
% 13.22/13.40          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 13.22/13.40      inference('simplify', [status(thm)], ['139'])).
% 13.22/13.40  thf('141', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 13.22/13.40      inference('sup-', [status(thm)], ['138', '140'])).
% 13.22/13.40  thf('142', plain, ($false),
% 13.22/13.40      inference('demod', [status(thm)], ['8', '137', '141'])).
% 13.22/13.40  
% 13.22/13.40  % SZS output end Refutation
% 13.22/13.40  
% 13.22/13.41  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

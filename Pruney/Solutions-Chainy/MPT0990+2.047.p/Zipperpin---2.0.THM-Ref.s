%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5lv5biznTo

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:01 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :  175 (2070 expanded)
%              Number of leaves         :   44 ( 629 expanded)
%              Depth                    :   18
%              Number of atoms          : 1644 (54463 expanded)
%              Number of equality atoms :  120 (3766 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( ( k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38 )
        = ( k5_relat_1 @ X35 @ X38 ) ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X34 ) ) ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( X16 = X19 )
      | ~ ( r2_relset_1 @ X17 @ X18 @ X16 @ X19 ) ) ),
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
    ! [X20: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('25',plain,(
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('26',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ( X5
        = ( k2_funct_1 @ X6 ) )
      | ( ( k5_relat_1 @ X5 @ X6 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X6 ) ) )
      | ( ( k2_relat_1 @ X5 )
       != ( k1_relat_1 @ X6 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('29',plain,(
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('30',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ( X5
        = ( k2_funct_1 @ X6 ) )
      | ( ( k5_relat_1 @ X5 @ X6 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X6 ) ) )
      | ( ( k2_relat_1 @ X5 )
       != ( k1_relat_1 @ X6 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
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
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( r2_relset_1 @ X43 @ X43 @ ( k1_partfun1 @ X43 @ X44 @ X44 @ X43 @ X42 @ X45 ) @ ( k6_partfun1 @ X43 ) )
      | ( ( k2_relset_1 @ X44 @ X43 @ X45 )
        = X43 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X45 @ X44 @ X43 )
      | ~ ( v1_funct_1 @ X45 ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
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

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('48',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('49',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('53',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
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

thf('57',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ( X23
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('58',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('59',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('60',plain,(
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

thf('61',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('62',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['63','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('67',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('68',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['58','65','68'])).

thf('70',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('73',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B != sk_B )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['31','46','49','50','55','69','70','73'])).

thf('75',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
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

thf('77',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v2_funct_1 @ X3 )
      | ( ( k2_relat_1 @ X2 )
       != ( k1_relat_1 @ X3 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X2 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('78',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('79',plain,(
    ! [X1: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('80',plain,(
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('81',plain,(
    ! [X1: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X1 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['47','48'])).

thf('83',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['53','54'])).

thf('85',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['58','65','68'])).

thf('86',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['71','72'])).

thf('88',plain,
    ( ( sk_B != sk_B )
    | ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['78','81','82','83','84','85','86','87'])).

thf('89',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['75','89'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('91',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ X4 @ ( k2_funct_1 @ X4 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('92',plain,(
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('93',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ X4 @ ( k2_funct_1 @ X4 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ( X5
        = ( k2_funct_1 @ X6 ) )
      | ( ( k5_relat_1 @ X5 @ X6 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X6 ) ) )
      | ( ( k2_relat_1 @ X5 )
       != ( k1_relat_1 @ X6 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('95',plain,(
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
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
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
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,
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
    inference('sup-',[status(thm)],['90','96'])).

thf('98',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['58','65','68'])).

thf('99',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['53','54'])).

thf('100',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['47','48'])).

thf('101',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['88'])).

thf('103',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['75','89'])).

thf('104',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['71','72'])).

thf('105',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['75','89'])).

thf('106',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['75','89'])).

thf('108',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['39','42','43','44','45'])).

thf('110',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['75','89'])).

thf('111',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ( X23
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('113',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('115',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('117',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['114','117'])).

thf('119',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['118','119'])).

thf('121',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('123',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['113','120','123'])).

thf('125',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['75','89'])).

thf('126',plain,
    ( ( ( k6_partfun1 @ sk_B )
     != ( k6_partfun1 @ sk_B ) )
    | ( sk_A != sk_A )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['97','98','99','100','101','102','103','104','105','106','107','108','109','110','124','125'])).

thf('127',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['127','128'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5lv5biznTo
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:53:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.61/0.83  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.61/0.83  % Solved by: fo/fo7.sh
% 0.61/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.83  % done 267 iterations in 0.385s
% 0.61/0.83  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.61/0.83  % SZS output start Refutation
% 0.61/0.83  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.61/0.83  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.61/0.83  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.61/0.83  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.61/0.83  thf(sk_D_type, type, sk_D: $i).
% 0.61/0.83  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.61/0.83  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.61/0.83  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.61/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.83  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.61/0.83  thf(sk_C_type, type, sk_C: $i).
% 0.61/0.83  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.61/0.83  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.61/0.83  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.61/0.83  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.61/0.83  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.61/0.83  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.61/0.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.61/0.83  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.61/0.83  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.61/0.83  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.61/0.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.61/0.83  thf(sk_B_type, type, sk_B: $i).
% 0.61/0.83  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.61/0.83  thf(t36_funct_2, conjecture,
% 0.61/0.83    (![A:$i,B:$i,C:$i]:
% 0.61/0.83     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.61/0.83         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.61/0.83       ( ![D:$i]:
% 0.61/0.83         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.61/0.83             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.61/0.83           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.61/0.83               ( r2_relset_1 @
% 0.61/0.83                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.61/0.83                 ( k6_partfun1 @ A ) ) & 
% 0.61/0.83               ( v2_funct_1 @ C ) ) =>
% 0.61/0.83             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.61/0.83               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.61/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.83    (~( ![A:$i,B:$i,C:$i]:
% 0.61/0.83        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.61/0.83            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.61/0.83          ( ![D:$i]:
% 0.61/0.83            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.61/0.83                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.61/0.83              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.61/0.83                  ( r2_relset_1 @
% 0.61/0.83                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.61/0.83                    ( k6_partfun1 @ A ) ) & 
% 0.61/0.83                  ( v2_funct_1 @ C ) ) =>
% 0.61/0.83                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.61/0.83                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.61/0.83    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.61/0.83  thf('0', plain,
% 0.61/0.83      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.61/0.83        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.61/0.83        (k6_partfun1 @ sk_A))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('1', plain,
% 0.61/0.83      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('2', plain,
% 0.61/0.83      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf(redefinition_k1_partfun1, axiom,
% 0.61/0.83    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.61/0.83     ( ( ( v1_funct_1 @ E ) & 
% 0.61/0.83         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.61/0.83         ( v1_funct_1 @ F ) & 
% 0.61/0.83         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.61/0.83       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.61/0.83  thf('3', plain,
% 0.61/0.83      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.61/0.83         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.61/0.83          | ~ (v1_funct_1 @ X35)
% 0.61/0.83          | ~ (v1_funct_1 @ X38)
% 0.61/0.83          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.61/0.83          | ((k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38)
% 0.61/0.83              = (k5_relat_1 @ X35 @ X38)))),
% 0.61/0.83      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.61/0.83  thf('4', plain,
% 0.61/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.83         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.61/0.83            = (k5_relat_1 @ sk_C @ X0))
% 0.61/0.83          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.61/0.83          | ~ (v1_funct_1 @ X0)
% 0.61/0.83          | ~ (v1_funct_1 @ sk_C))),
% 0.61/0.83      inference('sup-', [status(thm)], ['2', '3'])).
% 0.61/0.83  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('6', plain,
% 0.61/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.83         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.61/0.83            = (k5_relat_1 @ sk_C @ X0))
% 0.61/0.83          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.61/0.83          | ~ (v1_funct_1 @ X0))),
% 0.61/0.83      inference('demod', [status(thm)], ['4', '5'])).
% 0.61/0.83  thf('7', plain,
% 0.61/0.83      ((~ (v1_funct_1 @ sk_D)
% 0.61/0.83        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.61/0.83            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['1', '6'])).
% 0.61/0.83  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('9', plain,
% 0.61/0.83      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.61/0.83         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.61/0.83      inference('demod', [status(thm)], ['7', '8'])).
% 0.61/0.83  thf('10', plain,
% 0.61/0.83      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.61/0.83        (k6_partfun1 @ sk_A))),
% 0.61/0.83      inference('demod', [status(thm)], ['0', '9'])).
% 0.61/0.83  thf('11', plain,
% 0.61/0.83      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('12', plain,
% 0.61/0.83      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf(dt_k1_partfun1, axiom,
% 0.61/0.83    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.61/0.83     ( ( ( v1_funct_1 @ E ) & 
% 0.61/0.83         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.61/0.84         ( v1_funct_1 @ F ) & 
% 0.61/0.84         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.61/0.84       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.61/0.84         ( m1_subset_1 @
% 0.61/0.84           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.61/0.84           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.61/0.84  thf('13', plain,
% 0.61/0.84      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.61/0.84         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.61/0.84          | ~ (v1_funct_1 @ X29)
% 0.61/0.84          | ~ (v1_funct_1 @ X32)
% 0.61/0.84          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.61/0.84          | (m1_subset_1 @ (k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32) @ 
% 0.61/0.84             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X34))))),
% 0.61/0.84      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.61/0.84  thf('14', plain,
% 0.61/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.84         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.61/0.84           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.61/0.84          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.61/0.84          | ~ (v1_funct_1 @ X1)
% 0.61/0.84          | ~ (v1_funct_1 @ sk_C))),
% 0.61/0.84      inference('sup-', [status(thm)], ['12', '13'])).
% 0.61/0.84  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('16', plain,
% 0.61/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.84         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.61/0.84           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.61/0.84          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.61/0.84          | ~ (v1_funct_1 @ X1))),
% 0.61/0.84      inference('demod', [status(thm)], ['14', '15'])).
% 0.61/0.84  thf('17', plain,
% 0.61/0.84      ((~ (v1_funct_1 @ sk_D)
% 0.61/0.84        | (m1_subset_1 @ 
% 0.61/0.84           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.61/0.84           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.61/0.84      inference('sup-', [status(thm)], ['11', '16'])).
% 0.61/0.84  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('19', plain,
% 0.61/0.84      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.61/0.84         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.61/0.84      inference('demod', [status(thm)], ['7', '8'])).
% 0.61/0.84  thf('20', plain,
% 0.61/0.84      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.61/0.84        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.61/0.84      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.61/0.84  thf(redefinition_r2_relset_1, axiom,
% 0.61/0.84    (![A:$i,B:$i,C:$i,D:$i]:
% 0.61/0.84     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.61/0.84         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.61/0.84       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.61/0.84  thf('21', plain,
% 0.61/0.84      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.61/0.84         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.61/0.84          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.61/0.84          | ((X16) = (X19))
% 0.61/0.84          | ~ (r2_relset_1 @ X17 @ X18 @ X16 @ X19))),
% 0.61/0.84      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.61/0.84  thf('22', plain,
% 0.61/0.84      (![X0 : $i]:
% 0.61/0.84         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 0.61/0.84          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 0.61/0.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.61/0.84      inference('sup-', [status(thm)], ['20', '21'])).
% 0.61/0.84  thf('23', plain,
% 0.61/0.84      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.61/0.84           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.61/0.84        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['10', '22'])).
% 0.61/0.84  thf(t29_relset_1, axiom,
% 0.61/0.84    (![A:$i]:
% 0.61/0.84     ( m1_subset_1 @
% 0.61/0.84       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.61/0.84  thf('24', plain,
% 0.61/0.84      (![X20 : $i]:
% 0.61/0.84         (m1_subset_1 @ (k6_relat_1 @ X20) @ 
% 0.61/0.84          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))),
% 0.61/0.84      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.61/0.84  thf(redefinition_k6_partfun1, axiom,
% 0.61/0.84    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.61/0.84  thf('25', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 0.61/0.84      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.61/0.84  thf('26', plain,
% 0.61/0.84      (![X20 : $i]:
% 0.61/0.84         (m1_subset_1 @ (k6_partfun1 @ X20) @ 
% 0.61/0.84          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))),
% 0.61/0.84      inference('demod', [status(thm)], ['24', '25'])).
% 0.61/0.84  thf('27', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.61/0.84      inference('demod', [status(thm)], ['23', '26'])).
% 0.61/0.84  thf(t64_funct_1, axiom,
% 0.61/0.84    (![A:$i]:
% 0.61/0.84     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.61/0.84       ( ![B:$i]:
% 0.61/0.84         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.61/0.84           ( ( ( v2_funct_1 @ A ) & 
% 0.61/0.84               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.61/0.84               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.61/0.84             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.61/0.84  thf('28', plain,
% 0.61/0.84      (![X5 : $i, X6 : $i]:
% 0.61/0.84         (~ (v1_relat_1 @ X5)
% 0.61/0.84          | ~ (v1_funct_1 @ X5)
% 0.61/0.84          | ((X5) = (k2_funct_1 @ X6))
% 0.61/0.84          | ((k5_relat_1 @ X5 @ X6) != (k6_relat_1 @ (k2_relat_1 @ X6)))
% 0.61/0.84          | ((k2_relat_1 @ X5) != (k1_relat_1 @ X6))
% 0.61/0.84          | ~ (v2_funct_1 @ X6)
% 0.61/0.84          | ~ (v1_funct_1 @ X6)
% 0.61/0.84          | ~ (v1_relat_1 @ X6))),
% 0.61/0.84      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.61/0.84  thf('29', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 0.61/0.84      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.61/0.84  thf('30', plain,
% 0.61/0.84      (![X5 : $i, X6 : $i]:
% 0.61/0.84         (~ (v1_relat_1 @ X5)
% 0.61/0.84          | ~ (v1_funct_1 @ X5)
% 0.61/0.84          | ((X5) = (k2_funct_1 @ X6))
% 0.61/0.84          | ((k5_relat_1 @ X5 @ X6) != (k6_partfun1 @ (k2_relat_1 @ X6)))
% 0.61/0.84          | ((k2_relat_1 @ X5) != (k1_relat_1 @ X6))
% 0.61/0.84          | ~ (v2_funct_1 @ X6)
% 0.61/0.84          | ~ (v1_funct_1 @ X6)
% 0.61/0.84          | ~ (v1_relat_1 @ X6))),
% 0.61/0.84      inference('demod', [status(thm)], ['28', '29'])).
% 0.61/0.84  thf('31', plain,
% 0.61/0.84      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 0.61/0.84        | ~ (v1_relat_1 @ sk_D)
% 0.61/0.84        | ~ (v1_funct_1 @ sk_D)
% 0.61/0.84        | ~ (v2_funct_1 @ sk_D)
% 0.61/0.84        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.61/0.84        | ((sk_C) = (k2_funct_1 @ sk_D))
% 0.61/0.84        | ~ (v1_funct_1 @ sk_C)
% 0.61/0.84        | ~ (v1_relat_1 @ sk_C))),
% 0.61/0.84      inference('sup-', [status(thm)], ['27', '30'])).
% 0.61/0.84  thf('32', plain,
% 0.61/0.84      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.61/0.84        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.61/0.84        (k6_partfun1 @ sk_A))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('33', plain,
% 0.61/0.84      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf(t24_funct_2, axiom,
% 0.61/0.84    (![A:$i,B:$i,C:$i]:
% 0.61/0.84     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.61/0.84         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.61/0.84       ( ![D:$i]:
% 0.61/0.84         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.61/0.84             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.61/0.84           ( ( r2_relset_1 @
% 0.61/0.84               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.61/0.84               ( k6_partfun1 @ B ) ) =>
% 0.61/0.84             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.61/0.84  thf('34', plain,
% 0.61/0.84      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.61/0.84         (~ (v1_funct_1 @ X42)
% 0.61/0.84          | ~ (v1_funct_2 @ X42 @ X43 @ X44)
% 0.61/0.84          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 0.61/0.84          | ~ (r2_relset_1 @ X43 @ X43 @ 
% 0.61/0.84               (k1_partfun1 @ X43 @ X44 @ X44 @ X43 @ X42 @ X45) @ 
% 0.61/0.84               (k6_partfun1 @ X43))
% 0.61/0.84          | ((k2_relset_1 @ X44 @ X43 @ X45) = (X43))
% 0.61/0.84          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43)))
% 0.61/0.84          | ~ (v1_funct_2 @ X45 @ X44 @ X43)
% 0.61/0.84          | ~ (v1_funct_1 @ X45))),
% 0.61/0.84      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.61/0.84  thf('35', plain,
% 0.61/0.84      (![X0 : $i]:
% 0.61/0.84         (~ (v1_funct_1 @ X0)
% 0.61/0.84          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.61/0.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.61/0.84          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.61/0.84          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.61/0.84               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.61/0.84               (k6_partfun1 @ sk_A))
% 0.61/0.84          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.61/0.84          | ~ (v1_funct_1 @ sk_C))),
% 0.61/0.84      inference('sup-', [status(thm)], ['33', '34'])).
% 0.61/0.84  thf('36', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('37', plain, ((v1_funct_1 @ sk_C)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('38', plain,
% 0.61/0.84      (![X0 : $i]:
% 0.61/0.84         (~ (v1_funct_1 @ X0)
% 0.61/0.84          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.61/0.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.61/0.84          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.61/0.84          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.61/0.84               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.61/0.84               (k6_partfun1 @ sk_A)))),
% 0.61/0.84      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.61/0.84  thf('39', plain,
% 0.61/0.84      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.61/0.84        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.61/0.84        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.61/0.84        | ~ (v1_funct_1 @ sk_D))),
% 0.61/0.84      inference('sup-', [status(thm)], ['32', '38'])).
% 0.61/0.84  thf('40', plain,
% 0.61/0.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf(redefinition_k2_relset_1, axiom,
% 0.61/0.84    (![A:$i,B:$i,C:$i]:
% 0.61/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.84       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.61/0.84  thf('41', plain,
% 0.61/0.84      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.61/0.84         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 0.61/0.84          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.61/0.84      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.61/0.84  thf('42', plain,
% 0.61/0.84      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.61/0.84      inference('sup-', [status(thm)], ['40', '41'])).
% 0.61/0.84  thf('43', plain,
% 0.61/0.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('44', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('45', plain, ((v1_funct_1 @ sk_D)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('46', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.61/0.84      inference('demod', [status(thm)], ['39', '42', '43', '44', '45'])).
% 0.61/0.84  thf('47', plain,
% 0.61/0.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf(cc1_relset_1, axiom,
% 0.61/0.84    (![A:$i,B:$i,C:$i]:
% 0.61/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.84       ( v1_relat_1 @ C ) ))).
% 0.61/0.84  thf('48', plain,
% 0.61/0.84      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.61/0.84         ((v1_relat_1 @ X7)
% 0.61/0.84          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.61/0.84      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.61/0.84  thf('49', plain, ((v1_relat_1 @ sk_D)),
% 0.61/0.84      inference('sup-', [status(thm)], ['47', '48'])).
% 0.61/0.84  thf('50', plain, ((v1_funct_1 @ sk_D)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('51', plain,
% 0.61/0.84      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('52', plain,
% 0.61/0.84      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.61/0.84         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 0.61/0.84          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.61/0.84      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.61/0.84  thf('53', plain,
% 0.61/0.84      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.61/0.84      inference('sup-', [status(thm)], ['51', '52'])).
% 0.61/0.84  thf('54', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('55', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.61/0.84      inference('sup+', [status(thm)], ['53', '54'])).
% 0.61/0.84  thf('56', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf(d1_funct_2, axiom,
% 0.61/0.84    (![A:$i,B:$i,C:$i]:
% 0.61/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.84       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.61/0.84           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.61/0.84             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.61/0.84         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.61/0.84           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.61/0.84             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.61/0.84  thf(zf_stmt_1, axiom,
% 0.61/0.84    (![C:$i,B:$i,A:$i]:
% 0.61/0.84     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.61/0.84       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.61/0.84  thf('57', plain,
% 0.61/0.84      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.61/0.84         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 0.61/0.84          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 0.61/0.84          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.61/0.84  thf('58', plain,
% 0.61/0.84      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 0.61/0.84        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['56', '57'])).
% 0.61/0.84  thf(zf_stmt_2, axiom,
% 0.61/0.84    (![B:$i,A:$i]:
% 0.61/0.84     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.61/0.84       ( zip_tseitin_0 @ B @ A ) ))).
% 0.61/0.84  thf('59', plain,
% 0.61/0.84      (![X21 : $i, X22 : $i]:
% 0.61/0.84         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.61/0.84  thf('60', plain,
% 0.61/0.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.61/0.84  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.61/0.84  thf(zf_stmt_5, axiom,
% 0.61/0.84    (![A:$i,B:$i,C:$i]:
% 0.61/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.84       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.61/0.84         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.61/0.84           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.61/0.84             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.61/0.84  thf('61', plain,
% 0.61/0.84      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.61/0.84         (~ (zip_tseitin_0 @ X26 @ X27)
% 0.61/0.84          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 0.61/0.84          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.61/0.84  thf('62', plain,
% 0.61/0.84      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 0.61/0.84      inference('sup-', [status(thm)], ['60', '61'])).
% 0.61/0.84  thf('63', plain,
% 0.61/0.84      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 0.61/0.84      inference('sup-', [status(thm)], ['59', '62'])).
% 0.61/0.84  thf('64', plain, (((sk_A) != (k1_xboole_0))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('65', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 0.61/0.84      inference('simplify_reflect-', [status(thm)], ['63', '64'])).
% 0.61/0.84  thf('66', plain,
% 0.61/0.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf(redefinition_k1_relset_1, axiom,
% 0.61/0.84    (![A:$i,B:$i,C:$i]:
% 0.61/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.84       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.61/0.84  thf('67', plain,
% 0.61/0.84      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.61/0.84         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 0.61/0.84          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.61/0.84      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.61/0.84  thf('68', plain,
% 0.61/0.84      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.61/0.84      inference('sup-', [status(thm)], ['66', '67'])).
% 0.61/0.84  thf('69', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.61/0.84      inference('demod', [status(thm)], ['58', '65', '68'])).
% 0.61/0.84  thf('70', plain, ((v1_funct_1 @ sk_C)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('71', plain,
% 0.61/0.84      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('72', plain,
% 0.61/0.84      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.61/0.84         ((v1_relat_1 @ X7)
% 0.61/0.84          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.61/0.84      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.61/0.84  thf('73', plain, ((v1_relat_1 @ sk_C)),
% 0.61/0.84      inference('sup-', [status(thm)], ['71', '72'])).
% 0.61/0.84  thf('74', plain,
% 0.61/0.84      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 0.61/0.84        | ~ (v2_funct_1 @ sk_D)
% 0.61/0.84        | ((sk_B) != (sk_B))
% 0.61/0.84        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 0.61/0.84      inference('demod', [status(thm)],
% 0.61/0.84                ['31', '46', '49', '50', '55', '69', '70', '73'])).
% 0.61/0.84  thf('75', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 0.61/0.84      inference('simplify', [status(thm)], ['74'])).
% 0.61/0.84  thf('76', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.61/0.84      inference('demod', [status(thm)], ['23', '26'])).
% 0.61/0.84  thf(t48_funct_1, axiom,
% 0.61/0.84    (![A:$i]:
% 0.61/0.84     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.61/0.84       ( ![B:$i]:
% 0.61/0.84         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.61/0.84           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.61/0.84               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.61/0.84             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.61/0.84  thf('77', plain,
% 0.61/0.84      (![X2 : $i, X3 : $i]:
% 0.61/0.84         (~ (v1_relat_1 @ X2)
% 0.61/0.84          | ~ (v1_funct_1 @ X2)
% 0.61/0.84          | (v2_funct_1 @ X3)
% 0.61/0.84          | ((k2_relat_1 @ X2) != (k1_relat_1 @ X3))
% 0.61/0.84          | ~ (v2_funct_1 @ (k5_relat_1 @ X2 @ X3))
% 0.61/0.84          | ~ (v1_funct_1 @ X3)
% 0.61/0.84          | ~ (v1_relat_1 @ X3))),
% 0.61/0.84      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.61/0.84  thf('78', plain,
% 0.61/0.84      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.61/0.84        | ~ (v1_relat_1 @ sk_D)
% 0.61/0.84        | ~ (v1_funct_1 @ sk_D)
% 0.61/0.84        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.61/0.84        | (v2_funct_1 @ sk_D)
% 0.61/0.84        | ~ (v1_funct_1 @ sk_C)
% 0.61/0.84        | ~ (v1_relat_1 @ sk_C))),
% 0.61/0.84      inference('sup-', [status(thm)], ['76', '77'])).
% 0.61/0.84  thf(fc4_funct_1, axiom,
% 0.61/0.84    (![A:$i]:
% 0.61/0.84     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.61/0.84       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.61/0.84  thf('79', plain, (![X1 : $i]: (v2_funct_1 @ (k6_relat_1 @ X1))),
% 0.61/0.84      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.61/0.84  thf('80', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 0.61/0.84      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.61/0.84  thf('81', plain, (![X1 : $i]: (v2_funct_1 @ (k6_partfun1 @ X1))),
% 0.61/0.84      inference('demod', [status(thm)], ['79', '80'])).
% 0.61/0.84  thf('82', plain, ((v1_relat_1 @ sk_D)),
% 0.61/0.84      inference('sup-', [status(thm)], ['47', '48'])).
% 0.61/0.84  thf('83', plain, ((v1_funct_1 @ sk_D)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('84', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.61/0.84      inference('sup+', [status(thm)], ['53', '54'])).
% 0.61/0.84  thf('85', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.61/0.84      inference('demod', [status(thm)], ['58', '65', '68'])).
% 0.61/0.84  thf('86', plain, ((v1_funct_1 @ sk_C)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('87', plain, ((v1_relat_1 @ sk_C)),
% 0.61/0.84      inference('sup-', [status(thm)], ['71', '72'])).
% 0.61/0.84  thf('88', plain, ((((sk_B) != (sk_B)) | (v2_funct_1 @ sk_D))),
% 0.61/0.84      inference('demod', [status(thm)],
% 0.61/0.84                ['78', '81', '82', '83', '84', '85', '86', '87'])).
% 0.61/0.84  thf('89', plain, ((v2_funct_1 @ sk_D)),
% 0.61/0.84      inference('simplify', [status(thm)], ['88'])).
% 0.61/0.84  thf('90', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.61/0.84      inference('demod', [status(thm)], ['75', '89'])).
% 0.61/0.84  thf(t61_funct_1, axiom,
% 0.61/0.84    (![A:$i]:
% 0.61/0.84     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.61/0.84       ( ( v2_funct_1 @ A ) =>
% 0.61/0.84         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.61/0.84             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.61/0.84           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.61/0.84             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.61/0.84  thf('91', plain,
% 0.61/0.84      (![X4 : $i]:
% 0.61/0.84         (~ (v2_funct_1 @ X4)
% 0.61/0.84          | ((k5_relat_1 @ X4 @ (k2_funct_1 @ X4))
% 0.61/0.84              = (k6_relat_1 @ (k1_relat_1 @ X4)))
% 0.61/0.84          | ~ (v1_funct_1 @ X4)
% 0.61/0.84          | ~ (v1_relat_1 @ X4))),
% 0.61/0.84      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.61/0.84  thf('92', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 0.61/0.84      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.61/0.84  thf('93', plain,
% 0.61/0.84      (![X4 : $i]:
% 0.61/0.84         (~ (v2_funct_1 @ X4)
% 0.61/0.84          | ((k5_relat_1 @ X4 @ (k2_funct_1 @ X4))
% 0.61/0.84              = (k6_partfun1 @ (k1_relat_1 @ X4)))
% 0.61/0.84          | ~ (v1_funct_1 @ X4)
% 0.61/0.84          | ~ (v1_relat_1 @ X4))),
% 0.61/0.84      inference('demod', [status(thm)], ['91', '92'])).
% 0.61/0.84  thf('94', plain,
% 0.61/0.84      (![X5 : $i, X6 : $i]:
% 0.61/0.84         (~ (v1_relat_1 @ X5)
% 0.61/0.84          | ~ (v1_funct_1 @ X5)
% 0.61/0.84          | ((X5) = (k2_funct_1 @ X6))
% 0.61/0.84          | ((k5_relat_1 @ X5 @ X6) != (k6_partfun1 @ (k2_relat_1 @ X6)))
% 0.61/0.84          | ((k2_relat_1 @ X5) != (k1_relat_1 @ X6))
% 0.61/0.84          | ~ (v2_funct_1 @ X6)
% 0.61/0.84          | ~ (v1_funct_1 @ X6)
% 0.61/0.84          | ~ (v1_relat_1 @ X6))),
% 0.61/0.84      inference('demod', [status(thm)], ['28', '29'])).
% 0.61/0.84  thf('95', plain,
% 0.61/0.84      (![X0 : $i]:
% 0.61/0.84         (((k6_partfun1 @ (k1_relat_1 @ X0))
% 0.61/0.84            != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.61/0.84          | ~ (v1_relat_1 @ X0)
% 0.61/0.84          | ~ (v1_funct_1 @ X0)
% 0.61/0.84          | ~ (v2_funct_1 @ X0)
% 0.61/0.84          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.61/0.84          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.61/0.84          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.61/0.84          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.61/0.84          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.61/0.84          | ~ (v1_funct_1 @ X0)
% 0.61/0.84          | ~ (v1_relat_1 @ X0))),
% 0.61/0.84      inference('sup-', [status(thm)], ['93', '94'])).
% 0.61/0.84  thf('96', plain,
% 0.61/0.84      (![X0 : $i]:
% 0.61/0.84         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.61/0.84          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.61/0.84          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.61/0.84          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.61/0.84          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.61/0.84          | ~ (v2_funct_1 @ X0)
% 0.61/0.84          | ~ (v1_funct_1 @ X0)
% 0.61/0.84          | ~ (v1_relat_1 @ X0)
% 0.61/0.84          | ((k6_partfun1 @ (k1_relat_1 @ X0))
% 0.61/0.84              != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.61/0.84      inference('simplify', [status(thm)], ['95'])).
% 0.61/0.84  thf('97', plain,
% 0.61/0.84      ((((k6_partfun1 @ (k1_relat_1 @ sk_D))
% 0.61/0.84          != (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 0.61/0.84        | ~ (v1_relat_1 @ sk_D)
% 0.61/0.84        | ~ (v1_funct_1 @ sk_D)
% 0.61/0.84        | ~ (v2_funct_1 @ sk_D)
% 0.61/0.84        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D))
% 0.61/0.84        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 0.61/0.84        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_D))
% 0.61/0.84        | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ (k2_funct_1 @ sk_D)))
% 0.61/0.84        | ((sk_D) = (k2_funct_1 @ (k2_funct_1 @ sk_D))))),
% 0.61/0.84      inference('sup-', [status(thm)], ['90', '96'])).
% 0.61/0.84  thf('98', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.61/0.84      inference('demod', [status(thm)], ['58', '65', '68'])).
% 0.61/0.84  thf('99', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.61/0.84      inference('sup+', [status(thm)], ['53', '54'])).
% 0.61/0.84  thf('100', plain, ((v1_relat_1 @ sk_D)),
% 0.61/0.84      inference('sup-', [status(thm)], ['47', '48'])).
% 0.61/0.84  thf('101', plain, ((v1_funct_1 @ sk_D)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('102', plain, ((v2_funct_1 @ sk_D)),
% 0.61/0.84      inference('simplify', [status(thm)], ['88'])).
% 0.61/0.84  thf('103', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.61/0.84      inference('demod', [status(thm)], ['75', '89'])).
% 0.61/0.84  thf('104', plain, ((v1_relat_1 @ sk_C)),
% 0.61/0.84      inference('sup-', [status(thm)], ['71', '72'])).
% 0.61/0.84  thf('105', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.61/0.84      inference('demod', [status(thm)], ['75', '89'])).
% 0.61/0.84  thf('106', plain, ((v1_funct_1 @ sk_C)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('107', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.61/0.84      inference('demod', [status(thm)], ['75', '89'])).
% 0.61/0.84  thf('108', plain, ((v2_funct_1 @ sk_C)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('109', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.61/0.84      inference('demod', [status(thm)], ['39', '42', '43', '44', '45'])).
% 0.61/0.84  thf('110', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.61/0.84      inference('demod', [status(thm)], ['75', '89'])).
% 0.61/0.84  thf('111', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('112', plain,
% 0.61/0.84      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.61/0.84         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 0.61/0.84          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 0.61/0.84          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.61/0.84  thf('113', plain,
% 0.61/0.84      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.61/0.84        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.61/0.84      inference('sup-', [status(thm)], ['111', '112'])).
% 0.61/0.84  thf('114', plain,
% 0.61/0.84      (![X21 : $i, X22 : $i]:
% 0.61/0.84         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.61/0.84  thf('115', plain,
% 0.61/0.84      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('116', plain,
% 0.61/0.84      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.61/0.84         (~ (zip_tseitin_0 @ X26 @ X27)
% 0.61/0.84          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 0.61/0.84          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.61/0.84  thf('117', plain,
% 0.61/0.84      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.61/0.84      inference('sup-', [status(thm)], ['115', '116'])).
% 0.61/0.84  thf('118', plain,
% 0.61/0.84      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.61/0.84      inference('sup-', [status(thm)], ['114', '117'])).
% 0.61/0.84  thf('119', plain, (((sk_B) != (k1_xboole_0))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('120', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.61/0.84      inference('simplify_reflect-', [status(thm)], ['118', '119'])).
% 0.61/0.84  thf('121', plain,
% 0.61/0.84      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('122', plain,
% 0.61/0.84      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.61/0.84         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 0.61/0.84          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.61/0.84      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.61/0.84  thf('123', plain,
% 0.61/0.84      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.61/0.84      inference('sup-', [status(thm)], ['121', '122'])).
% 0.61/0.84  thf('124', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.61/0.84      inference('demod', [status(thm)], ['113', '120', '123'])).
% 0.61/0.84  thf('125', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.61/0.84      inference('demod', [status(thm)], ['75', '89'])).
% 0.61/0.84  thf('126', plain,
% 0.61/0.84      ((((k6_partfun1 @ sk_B) != (k6_partfun1 @ sk_B))
% 0.61/0.84        | ((sk_A) != (sk_A))
% 0.61/0.84        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 0.61/0.84      inference('demod', [status(thm)],
% 0.61/0.84                ['97', '98', '99', '100', '101', '102', '103', '104', '105', 
% 0.61/0.84                 '106', '107', '108', '109', '110', '124', '125'])).
% 0.61/0.84  thf('127', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 0.61/0.84      inference('simplify', [status(thm)], ['126'])).
% 0.61/0.84  thf('128', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf('129', plain, ($false),
% 0.61/0.84      inference('simplify_reflect-', [status(thm)], ['127', '128'])).
% 0.61/0.84  
% 0.61/0.84  % SZS output end Refutation
% 0.61/0.84  
% 0.61/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

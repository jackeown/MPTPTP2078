%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gunC54cLGu

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:04 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  204 (1636 expanded)
%              Number of leaves         :   43 ( 498 expanded)
%              Depth                    :   19
%              Number of atoms          : 1842 (39446 expanded)
%              Number of equality atoms :  134 ( 662 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X39: $i,X40: $i] :
      ( ( ( k2_funct_2 @ X40 @ X39 )
        = ( k2_funct_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X40 ) ) )
      | ~ ( v3_funct_2 @ X39 @ X40 @ X40 )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X40 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
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
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
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

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('14',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19'])).

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
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','22'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('24',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('25',plain,(
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('26',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_funct_2,axiom,(
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

thf('29',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( X46
        = ( k2_funct_1 @ X49 ) )
      | ~ ( r2_relset_1 @ X48 @ X48 @ ( k1_partfun1 @ X48 @ X47 @ X47 @ X48 @ X49 @ X46 ) @ ( k6_partfun1 @ X48 ) )
      | ( X47 = k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X49 )
      | ( ( k2_relset_1 @ X48 @ X47 @ X49 )
       != X47 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X47 ) ) )
      | ~ ( v1_funct_2 @ X49 @ X48 @ X47 )
      | ~ ( v1_funct_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t36_funct_2])).

thf('30',plain,(
    ! [X41: $i] :
      ( ( k6_partfun1 @ X41 )
      = ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('31',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( X46
        = ( k2_funct_1 @ X49 ) )
      | ~ ( r2_relset_1 @ X48 @ X48 @ ( k1_partfun1 @ X48 @ X47 @ X47 @ X48 @ X49 @ X46 ) @ ( k6_relat_1 @ X48 ) )
      | ( X47 = k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X49 )
      | ( ( k2_relset_1 @ X48 @ X47 @ X49 )
       != X47 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X47 ) ) )
      | ~ ( v1_funct_2 @ X49 @ X48 @ X47 )
      | ~ ( v1_funct_1 @ X49 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','36'])).

thf('38',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('39',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( r2_relset_1 @ X17 @ X18 @ X16 @ X19 )
      | ( X16 != X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('40',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_relset_1 @ X17 @ X18 @ X19 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('46',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('47',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) ) ) ) )).

thf('49',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_1 @ X20 )
      | ~ ( v3_funct_2 @ X20 @ X21 @ X22 )
      | ( v2_funct_2 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('50',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['50','51','52'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('54',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v2_funct_2 @ X24 @ X23 )
      | ( ( k2_relat_1 @ X24 )
        = X23 )
      | ~ ( v5_relat_1 @ X24 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('55',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('57',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('58',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('60',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v5_relat_1 @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('61',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['55','58','61'])).

thf('63',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['47','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_1 @ X20 )
      | ~ ( v3_funct_2 @ X20 @ X21 @ X22 )
      | ( v2_funct_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('66',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,
    ( ( sk_A != sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','41','42','43','44','63','69'])).

thf('71',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('73',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_relset_1 @ X17 @ X18 @ X19 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('76',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['73','76'])).

thf('78',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['73','76'])).

thf('79',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','77','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_1 @ X20 )
      | ~ ( v3_funct_2 @ X20 @ X21 @ X22 )
      | ( v2_funct_2 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('82',plain,
    ( ( v2_funct_2 @ sk_C @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v2_funct_2 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v2_funct_2 @ X24 @ X23 )
      | ( ( k2_relat_1 @ X24 )
        = X23 )
      | ~ ( v5_relat_1 @ X24 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('87',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v5_relat_1 @ sk_C @ sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('90',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v5_relat_1 @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('93',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['87','90','93'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('95',plain,(
    ! [X1: $i] :
      ( ( ( k2_relat_1 @ X1 )
       != k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('96',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['88','89'])).

thf('98',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['73','76'])).

thf('100',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['55','58','61'])).

thf('103',plain,(
    ! [X1: $i] :
      ( ( ( k2_relat_1 @ X1 )
       != k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('104',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['56','57'])).

thf('106',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['73','76'])).

thf('108',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['79','101','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
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

thf('113',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( ( k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36 )
        = ( k5_relat_1 @ X33 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
      = ( k5_relat_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['111','116'])).

thf('118',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('120',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['87','90','93'])).

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

thf('122',plain,(
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

thf('123',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ sk_C )
       != ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C ) )
      | ( X0
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['88','89'])).

thf('125',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_1 @ X20 )
      | ~ ( v3_funct_2 @ X20 @ X21 @ X22 )
      | ( v2_funct_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('128',plain,
    ( ( v2_funct_1 @ sk_C )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ sk_C )
       != ( k6_relat_1 @ sk_A ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C ) )
      | ( X0
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['123','124','125','131'])).

thf('133',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( sk_B
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_B )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['120','132'])).

thf('134',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['56','57'])).

thf('135',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['55','58','61'])).

thf('137',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ sk_A ) )
    | ( sk_B
      = ( k2_funct_1 @ sk_C ) )
    | ( sk_A
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['133','134','135','136'])).

thf('138',plain,
    ( ( sk_A
     != ( k1_relat_1 @ sk_C ) )
    | ( sk_B
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['73','76'])).

thf('140',plain,
    ( ( k1_xboole_0
     != ( k1_relat_1 @ sk_C ) )
    | ( sk_B
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['100'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('142',plain,(
    ! [X3: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X3 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('143',plain,(
    ! [X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
       != k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('145',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,(
    ! [X3: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X3 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('149',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['147','148'])).

thf('150',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['108'])).

thf('151',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['100'])).

thf('152',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( k1_xboole_0
      = ( k2_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['140','141','149','150','151'])).

thf('153',plain,
    ( k1_xboole_0
    = ( k2_funct_1 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['146'])).

thf('155',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('156',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_relset_1 @ X17 @ X18 @ X19 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('158',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    $false ),
    inference(demod,[status(thm)],['110','153','158'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gunC54cLGu
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:21:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.54/0.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.78  % Solved by: fo/fo7.sh
% 0.54/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.78  % done 512 iterations in 0.326s
% 0.54/0.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.78  % SZS output start Refutation
% 0.54/0.78  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.54/0.78  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.54/0.78  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.54/0.78  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.54/0.78  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.54/0.78  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.54/0.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.78  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.54/0.78  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.54/0.78  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.54/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.78  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.54/0.78  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.54/0.78  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.54/0.78  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.54/0.78  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.54/0.78  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.54/0.78  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.54/0.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.78  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.54/0.78  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.54/0.78  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.54/0.78  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.54/0.78  thf(sk_C_type, type, sk_C: $i).
% 0.54/0.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.78  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.78  thf(t87_funct_2, conjecture,
% 0.54/0.78    (![A:$i,B:$i]:
% 0.54/0.78     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.54/0.78         ( v3_funct_2 @ B @ A @ A ) & 
% 0.54/0.78         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.54/0.78       ( ![C:$i]:
% 0.54/0.78         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.54/0.78             ( v3_funct_2 @ C @ A @ A ) & 
% 0.54/0.78             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.54/0.78           ( ( r2_relset_1 @
% 0.54/0.78               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.54/0.78               ( k6_partfun1 @ A ) ) =>
% 0.54/0.78             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 0.54/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.78    (~( ![A:$i,B:$i]:
% 0.54/0.78        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.54/0.78            ( v3_funct_2 @ B @ A @ A ) & 
% 0.54/0.78            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.54/0.78          ( ![C:$i]:
% 0.54/0.78            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.54/0.78                ( v3_funct_2 @ C @ A @ A ) & 
% 0.54/0.78                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.54/0.78              ( ( r2_relset_1 @
% 0.54/0.78                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.54/0.78                  ( k6_partfun1 @ A ) ) =>
% 0.54/0.78                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 0.54/0.78    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 0.54/0.78  thf('0', plain,
% 0.54/0.78      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.78  thf('1', plain,
% 0.54/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.78  thf(redefinition_k2_funct_2, axiom,
% 0.54/0.78    (![A:$i,B:$i]:
% 0.54/0.78     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.54/0.78         ( v3_funct_2 @ B @ A @ A ) & 
% 0.54/0.78         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.54/0.78       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.54/0.78  thf('2', plain,
% 0.54/0.78      (![X39 : $i, X40 : $i]:
% 0.54/0.78         (((k2_funct_2 @ X40 @ X39) = (k2_funct_1 @ X39))
% 0.54/0.78          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X40)))
% 0.54/0.78          | ~ (v3_funct_2 @ X39 @ X40 @ X40)
% 0.54/0.78          | ~ (v1_funct_2 @ X39 @ X40 @ X40)
% 0.54/0.78          | ~ (v1_funct_1 @ X39))),
% 0.54/0.78      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.54/0.78  thf('3', plain,
% 0.54/0.78      ((~ (v1_funct_1 @ sk_B)
% 0.54/0.78        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.54/0.78        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.54/0.78        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 0.54/0.78      inference('sup-', [status(thm)], ['1', '2'])).
% 0.54/0.78  thf('4', plain, ((v1_funct_1 @ sk_B)),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.78  thf('5', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.78  thf('6', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.78  thf('7', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.54/0.78      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.54/0.78  thf('8', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.54/0.78      inference('demod', [status(thm)], ['0', '7'])).
% 0.54/0.78  thf('9', plain,
% 0.54/0.78      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.54/0.78        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.54/0.78        (k6_partfun1 @ sk_A))),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.78  thf(redefinition_k6_partfun1, axiom,
% 0.54/0.78    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.54/0.78  thf('10', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 0.54/0.78      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.54/0.78  thf('11', plain,
% 0.54/0.78      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.54/0.78        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.54/0.78        (k6_relat_1 @ sk_A))),
% 0.54/0.78      inference('demod', [status(thm)], ['9', '10'])).
% 0.54/0.78  thf('12', plain,
% 0.54/0.78      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.78  thf('13', plain,
% 0.54/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.78  thf(dt_k1_partfun1, axiom,
% 0.54/0.78    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.54/0.78     ( ( ( v1_funct_1 @ E ) & 
% 0.54/0.78         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.54/0.78         ( v1_funct_1 @ F ) & 
% 0.54/0.78         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.54/0.78       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.54/0.78         ( m1_subset_1 @
% 0.54/0.78           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.54/0.78           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.54/0.78  thf('14', plain,
% 0.54/0.78      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.54/0.78         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.54/0.78          | ~ (v1_funct_1 @ X25)
% 0.54/0.78          | ~ (v1_funct_1 @ X28)
% 0.54/0.78          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.54/0.78          | (m1_subset_1 @ (k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28) @ 
% 0.54/0.78             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X30))))),
% 0.54/0.78      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.54/0.78  thf('15', plain,
% 0.54/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.78         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 0.54/0.78           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.54/0.78          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.54/0.78          | ~ (v1_funct_1 @ X1)
% 0.54/0.78          | ~ (v1_funct_1 @ sk_B))),
% 0.54/0.78      inference('sup-', [status(thm)], ['13', '14'])).
% 0.54/0.78  thf('16', plain, ((v1_funct_1 @ sk_B)),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.78  thf('17', plain,
% 0.54/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.78         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 0.54/0.78           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.54/0.78          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.54/0.78          | ~ (v1_funct_1 @ X1))),
% 0.54/0.78      inference('demod', [status(thm)], ['15', '16'])).
% 0.54/0.78  thf('18', plain,
% 0.54/0.78      ((~ (v1_funct_1 @ sk_C)
% 0.54/0.78        | (m1_subset_1 @ 
% 0.54/0.78           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.54/0.78           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.54/0.78      inference('sup-', [status(thm)], ['12', '17'])).
% 0.54/0.78  thf('19', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.78  thf('20', plain,
% 0.54/0.78      ((m1_subset_1 @ 
% 0.54/0.78        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.54/0.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.54/0.78      inference('demod', [status(thm)], ['18', '19'])).
% 0.54/0.78  thf(redefinition_r2_relset_1, axiom,
% 0.54/0.78    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.78     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.54/0.78         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.54/0.78       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.54/0.78  thf('21', plain,
% 0.54/0.78      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.54/0.78         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.54/0.78          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.54/0.78          | ((X16) = (X19))
% 0.54/0.78          | ~ (r2_relset_1 @ X17 @ X18 @ X16 @ X19))),
% 0.54/0.78      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.54/0.78  thf('22', plain,
% 0.54/0.78      (![X0 : $i]:
% 0.54/0.78         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.54/0.78             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ X0)
% 0.54/0.78          | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) = (X0))
% 0.54/0.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.54/0.78      inference('sup-', [status(thm)], ['20', '21'])).
% 0.54/0.78  thf('23', plain,
% 0.54/0.78      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 0.54/0.78           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.54/0.78        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.54/0.78            = (k6_relat_1 @ sk_A)))),
% 0.54/0.78      inference('sup-', [status(thm)], ['11', '22'])).
% 0.54/0.78  thf(dt_k6_partfun1, axiom,
% 0.54/0.78    (![A:$i]:
% 0.54/0.78     ( ( m1_subset_1 @
% 0.54/0.78         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.54/0.78       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.54/0.78  thf('24', plain,
% 0.54/0.78      (![X32 : $i]:
% 0.54/0.78         (m1_subset_1 @ (k6_partfun1 @ X32) @ 
% 0.54/0.78          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 0.54/0.78      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.54/0.78  thf('25', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 0.54/0.78      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.54/0.78  thf('26', plain,
% 0.54/0.78      (![X32 : $i]:
% 0.54/0.78         (m1_subset_1 @ (k6_relat_1 @ X32) @ 
% 0.54/0.78          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 0.54/0.78      inference('demod', [status(thm)], ['24', '25'])).
% 0.54/0.78  thf('27', plain,
% 0.54/0.78      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.54/0.78         = (k6_relat_1 @ sk_A))),
% 0.54/0.78      inference('demod', [status(thm)], ['23', '26'])).
% 0.54/0.78  thf('28', plain,
% 0.54/0.78      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.78  thf(t36_funct_2, axiom,
% 0.54/0.78    (![A:$i,B:$i,C:$i]:
% 0.54/0.78     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.54/0.78         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.54/0.78       ( ![D:$i]:
% 0.54/0.78         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.54/0.78             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.54/0.78           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.54/0.78               ( r2_relset_1 @
% 0.54/0.78                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.54/0.78                 ( k6_partfun1 @ A ) ) & 
% 0.54/0.78               ( v2_funct_1 @ C ) ) =>
% 0.54/0.78             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.54/0.78               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.54/0.78  thf('29', plain,
% 0.54/0.78      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.54/0.78         (~ (v1_funct_1 @ X46)
% 0.54/0.78          | ~ (v1_funct_2 @ X46 @ X47 @ X48)
% 0.54/0.78          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 0.54/0.78          | ((X46) = (k2_funct_1 @ X49))
% 0.54/0.78          | ~ (r2_relset_1 @ X48 @ X48 @ 
% 0.54/0.78               (k1_partfun1 @ X48 @ X47 @ X47 @ X48 @ X49 @ X46) @ 
% 0.54/0.78               (k6_partfun1 @ X48))
% 0.54/0.78          | ((X47) = (k1_xboole_0))
% 0.54/0.78          | ((X48) = (k1_xboole_0))
% 0.54/0.78          | ~ (v2_funct_1 @ X49)
% 0.54/0.78          | ((k2_relset_1 @ X48 @ X47 @ X49) != (X47))
% 0.54/0.78          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X47)))
% 0.54/0.78          | ~ (v1_funct_2 @ X49 @ X48 @ X47)
% 0.54/0.78          | ~ (v1_funct_1 @ X49))),
% 0.54/0.78      inference('cnf', [status(esa)], [t36_funct_2])).
% 0.54/0.78  thf('30', plain, (![X41 : $i]: ((k6_partfun1 @ X41) = (k6_relat_1 @ X41))),
% 0.54/0.78      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.54/0.78  thf('31', plain,
% 0.54/0.78      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.54/0.78         (~ (v1_funct_1 @ X46)
% 0.54/0.78          | ~ (v1_funct_2 @ X46 @ X47 @ X48)
% 0.54/0.78          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 0.54/0.78          | ((X46) = (k2_funct_1 @ X49))
% 0.54/0.78          | ~ (r2_relset_1 @ X48 @ X48 @ 
% 0.54/0.78               (k1_partfun1 @ X48 @ X47 @ X47 @ X48 @ X49 @ X46) @ 
% 0.54/0.78               (k6_relat_1 @ X48))
% 0.54/0.78          | ((X47) = (k1_xboole_0))
% 0.54/0.78          | ((X48) = (k1_xboole_0))
% 0.54/0.78          | ~ (v2_funct_1 @ X49)
% 0.54/0.78          | ((k2_relset_1 @ X48 @ X47 @ X49) != (X47))
% 0.54/0.78          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X47)))
% 0.54/0.78          | ~ (v1_funct_2 @ X49 @ X48 @ X47)
% 0.54/0.78          | ~ (v1_funct_1 @ X49))),
% 0.54/0.78      inference('demod', [status(thm)], ['29', '30'])).
% 0.54/0.78  thf('32', plain,
% 0.54/0.78      (![X0 : $i]:
% 0.54/0.78         (~ (v1_funct_1 @ X0)
% 0.54/0.78          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.54/0.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.54/0.78          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.54/0.78          | ~ (v2_funct_1 @ X0)
% 0.54/0.78          | ((sk_A) = (k1_xboole_0))
% 0.54/0.78          | ((sk_A) = (k1_xboole_0))
% 0.54/0.78          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.54/0.78               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.54/0.78               (k6_relat_1 @ sk_A))
% 0.54/0.78          | ((sk_C) = (k2_funct_1 @ X0))
% 0.54/0.78          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.54/0.78          | ~ (v1_funct_1 @ sk_C))),
% 0.54/0.78      inference('sup-', [status(thm)], ['28', '31'])).
% 0.54/0.78  thf('33', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.78  thf('34', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.78  thf('35', plain,
% 0.54/0.78      (![X0 : $i]:
% 0.54/0.78         (~ (v1_funct_1 @ X0)
% 0.54/0.78          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.54/0.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.54/0.78          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.54/0.78          | ~ (v2_funct_1 @ X0)
% 0.54/0.78          | ((sk_A) = (k1_xboole_0))
% 0.54/0.78          | ((sk_A) = (k1_xboole_0))
% 0.54/0.78          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.54/0.78               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.54/0.78               (k6_relat_1 @ sk_A))
% 0.54/0.78          | ((sk_C) = (k2_funct_1 @ X0)))),
% 0.54/0.78      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.54/0.78  thf('36', plain,
% 0.54/0.78      (![X0 : $i]:
% 0.54/0.78         (((sk_C) = (k2_funct_1 @ X0))
% 0.54/0.78          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.54/0.78               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.54/0.78               (k6_relat_1 @ sk_A))
% 0.54/0.78          | ((sk_A) = (k1_xboole_0))
% 0.54/0.78          | ~ (v2_funct_1 @ X0)
% 0.54/0.78          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.54/0.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.54/0.78          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.54/0.78          | ~ (v1_funct_1 @ X0))),
% 0.54/0.78      inference('simplify', [status(thm)], ['35'])).
% 0.54/0.78  thf('37', plain,
% 0.54/0.78      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 0.54/0.78           (k6_relat_1 @ sk_A))
% 0.54/0.78        | ~ (v1_funct_1 @ sk_B)
% 0.54/0.78        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.54/0.78        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.54/0.78        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 0.54/0.78        | ~ (v2_funct_1 @ sk_B)
% 0.54/0.78        | ((sk_A) = (k1_xboole_0))
% 0.54/0.78        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 0.54/0.78      inference('sup-', [status(thm)], ['27', '36'])).
% 0.54/0.78  thf('38', plain,
% 0.54/0.78      (![X32 : $i]:
% 0.54/0.78         (m1_subset_1 @ (k6_relat_1 @ X32) @ 
% 0.54/0.78          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 0.54/0.78      inference('demod', [status(thm)], ['24', '25'])).
% 0.54/0.78  thf('39', plain,
% 0.54/0.78      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.54/0.78         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.54/0.78          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.54/0.78          | (r2_relset_1 @ X17 @ X18 @ X16 @ X19)
% 0.54/0.78          | ((X16) != (X19)))),
% 0.54/0.78      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.54/0.78  thf('40', plain,
% 0.54/0.78      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.54/0.78         ((r2_relset_1 @ X17 @ X18 @ X19 @ X19)
% 0.54/0.78          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.54/0.78      inference('simplify', [status(thm)], ['39'])).
% 0.54/0.78  thf('41', plain,
% 0.54/0.78      (![X0 : $i]:
% 0.54/0.78         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.54/0.78      inference('sup-', [status(thm)], ['38', '40'])).
% 0.54/0.78  thf('42', plain, ((v1_funct_1 @ sk_B)),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.78  thf('43', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.78  thf('44', plain,
% 0.54/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.78  thf('45', plain,
% 0.54/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.78  thf(redefinition_k2_relset_1, axiom,
% 0.54/0.78    (![A:$i,B:$i,C:$i]:
% 0.54/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.78       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.54/0.78  thf('46', plain,
% 0.54/0.78      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.54/0.78         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 0.54/0.78          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.54/0.78      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.54/0.78  thf('47', plain,
% 0.54/0.78      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 0.54/0.78      inference('sup-', [status(thm)], ['45', '46'])).
% 0.54/0.78  thf('48', plain,
% 0.54/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.78  thf(cc2_funct_2, axiom,
% 0.54/0.78    (![A:$i,B:$i,C:$i]:
% 0.54/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.78       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.54/0.78         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.54/0.78  thf('49', plain,
% 0.54/0.78      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.54/0.78         (~ (v1_funct_1 @ X20)
% 0.54/0.78          | ~ (v3_funct_2 @ X20 @ X21 @ X22)
% 0.54/0.78          | (v2_funct_2 @ X20 @ X22)
% 0.54/0.78          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.54/0.78      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.54/0.78  thf('50', plain,
% 0.54/0.78      (((v2_funct_2 @ sk_B @ sk_A)
% 0.54/0.78        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.54/0.78        | ~ (v1_funct_1 @ sk_B))),
% 0.54/0.78      inference('sup-', [status(thm)], ['48', '49'])).
% 0.54/0.78  thf('51', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.78  thf('52', plain, ((v1_funct_1 @ sk_B)),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.78  thf('53', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 0.54/0.78      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.54/0.78  thf(d3_funct_2, axiom,
% 0.54/0.78    (![A:$i,B:$i]:
% 0.54/0.78     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.54/0.78       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.54/0.78  thf('54', plain,
% 0.54/0.78      (![X23 : $i, X24 : $i]:
% 0.54/0.78         (~ (v2_funct_2 @ X24 @ X23)
% 0.54/0.78          | ((k2_relat_1 @ X24) = (X23))
% 0.54/0.78          | ~ (v5_relat_1 @ X24 @ X23)
% 0.54/0.78          | ~ (v1_relat_1 @ X24))),
% 0.54/0.78      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.54/0.78  thf('55', plain,
% 0.54/0.78      ((~ (v1_relat_1 @ sk_B)
% 0.54/0.78        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 0.54/0.78        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 0.54/0.78      inference('sup-', [status(thm)], ['53', '54'])).
% 0.54/0.78  thf('56', plain,
% 0.54/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.78  thf(cc1_relset_1, axiom,
% 0.54/0.78    (![A:$i,B:$i,C:$i]:
% 0.54/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.78       ( v1_relat_1 @ C ) ))).
% 0.54/0.78  thf('57', plain,
% 0.54/0.78      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.54/0.78         ((v1_relat_1 @ X7)
% 0.54/0.78          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.54/0.78      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.54/0.78  thf('58', plain, ((v1_relat_1 @ sk_B)),
% 0.54/0.78      inference('sup-', [status(thm)], ['56', '57'])).
% 0.54/0.78  thf('59', plain,
% 0.54/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.78  thf(cc2_relset_1, axiom,
% 0.54/0.78    (![A:$i,B:$i,C:$i]:
% 0.54/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.78       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.54/0.78  thf('60', plain,
% 0.54/0.78      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.54/0.78         ((v5_relat_1 @ X10 @ X12)
% 0.54/0.78          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.54/0.78      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.54/0.78  thf('61', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 0.54/0.78      inference('sup-', [status(thm)], ['59', '60'])).
% 0.54/0.78  thf('62', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.54/0.78      inference('demod', [status(thm)], ['55', '58', '61'])).
% 0.54/0.78  thf('63', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 0.54/0.78      inference('demod', [status(thm)], ['47', '62'])).
% 0.54/0.78  thf('64', plain,
% 0.54/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.78  thf('65', plain,
% 0.54/0.78      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.54/0.78         (~ (v1_funct_1 @ X20)
% 0.54/0.78          | ~ (v3_funct_2 @ X20 @ X21 @ X22)
% 0.54/0.78          | (v2_funct_1 @ X20)
% 0.54/0.78          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.54/0.78      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.54/0.78  thf('66', plain,
% 0.54/0.78      (((v2_funct_1 @ sk_B)
% 0.54/0.78        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.54/0.78        | ~ (v1_funct_1 @ sk_B))),
% 0.54/0.78      inference('sup-', [status(thm)], ['64', '65'])).
% 0.54/0.78  thf('67', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.78  thf('68', plain, ((v1_funct_1 @ sk_B)),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.78  thf('69', plain, ((v2_funct_1 @ sk_B)),
% 0.54/0.78      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.54/0.78  thf('70', plain,
% 0.54/0.78      ((((sk_A) != (sk_A))
% 0.54/0.78        | ((sk_A) = (k1_xboole_0))
% 0.54/0.78        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 0.54/0.78      inference('demod', [status(thm)],
% 0.54/0.78                ['37', '41', '42', '43', '44', '63', '69'])).
% 0.54/0.78  thf('71', plain,
% 0.54/0.78      ((((sk_C) = (k2_funct_1 @ sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 0.54/0.78      inference('simplify', [status(thm)], ['70'])).
% 0.54/0.78  thf('72', plain,
% 0.54/0.78      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.54/0.78      inference('demod', [status(thm)], ['0', '7'])).
% 0.54/0.78  thf('73', plain,
% 0.54/0.78      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.54/0.78      inference('sup-', [status(thm)], ['71', '72'])).
% 0.54/0.78  thf('74', plain,
% 0.54/0.78      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.78  thf('75', plain,
% 0.54/0.78      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.54/0.78         ((r2_relset_1 @ X17 @ X18 @ X19 @ X19)
% 0.54/0.78          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.54/0.78      inference('simplify', [status(thm)], ['39'])).
% 0.54/0.78  thf('76', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 0.54/0.78      inference('sup-', [status(thm)], ['74', '75'])).
% 0.54/0.78  thf('77', plain, (((sk_A) = (k1_xboole_0))),
% 0.54/0.78      inference('demod', [status(thm)], ['73', '76'])).
% 0.54/0.78  thf('78', plain, (((sk_A) = (k1_xboole_0))),
% 0.54/0.78      inference('demod', [status(thm)], ['73', '76'])).
% 0.54/0.78  thf('79', plain,
% 0.54/0.78      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.54/0.78      inference('demod', [status(thm)], ['8', '77', '78'])).
% 0.54/0.78  thf('80', plain,
% 0.54/0.78      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.78  thf('81', plain,
% 0.54/0.78      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.54/0.78         (~ (v1_funct_1 @ X20)
% 0.54/0.78          | ~ (v3_funct_2 @ X20 @ X21 @ X22)
% 0.54/0.78          | (v2_funct_2 @ X20 @ X22)
% 0.54/0.78          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.54/0.78      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.54/0.78  thf('82', plain,
% 0.54/0.78      (((v2_funct_2 @ sk_C @ sk_A)
% 0.54/0.78        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.54/0.78        | ~ (v1_funct_1 @ sk_C))),
% 0.54/0.78      inference('sup-', [status(thm)], ['80', '81'])).
% 0.54/0.78  thf('83', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.78  thf('84', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.78  thf('85', plain, ((v2_funct_2 @ sk_C @ sk_A)),
% 0.54/0.78      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.54/0.79  thf('86', plain,
% 0.54/0.79      (![X23 : $i, X24 : $i]:
% 0.54/0.79         (~ (v2_funct_2 @ X24 @ X23)
% 0.54/0.79          | ((k2_relat_1 @ X24) = (X23))
% 0.54/0.79          | ~ (v5_relat_1 @ X24 @ X23)
% 0.54/0.79          | ~ (v1_relat_1 @ X24))),
% 0.54/0.79      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.54/0.79  thf('87', plain,
% 0.54/0.79      ((~ (v1_relat_1 @ sk_C)
% 0.54/0.79        | ~ (v5_relat_1 @ sk_C @ sk_A)
% 0.54/0.79        | ((k2_relat_1 @ sk_C) = (sk_A)))),
% 0.54/0.79      inference('sup-', [status(thm)], ['85', '86'])).
% 0.54/0.79  thf('88', plain,
% 0.54/0.79      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.54/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.79  thf('89', plain,
% 0.54/0.79      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.54/0.79         ((v1_relat_1 @ X7)
% 0.54/0.79          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.54/0.79      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.54/0.79  thf('90', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.79      inference('sup-', [status(thm)], ['88', '89'])).
% 0.54/0.79  thf('91', plain,
% 0.54/0.79      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.54/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.79  thf('92', plain,
% 0.54/0.79      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.54/0.79         ((v5_relat_1 @ X10 @ X12)
% 0.54/0.79          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.54/0.79      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.54/0.79  thf('93', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.54/0.79      inference('sup-', [status(thm)], ['91', '92'])).
% 0.54/0.79  thf('94', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.54/0.79      inference('demod', [status(thm)], ['87', '90', '93'])).
% 0.54/0.79  thf(t64_relat_1, axiom,
% 0.54/0.79    (![A:$i]:
% 0.54/0.79     ( ( v1_relat_1 @ A ) =>
% 0.54/0.79       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.54/0.79           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.54/0.79         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.54/0.79  thf('95', plain,
% 0.54/0.79      (![X1 : $i]:
% 0.54/0.79         (((k2_relat_1 @ X1) != (k1_xboole_0))
% 0.54/0.79          | ((X1) = (k1_xboole_0))
% 0.54/0.79          | ~ (v1_relat_1 @ X1))),
% 0.54/0.79      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.54/0.79  thf('96', plain,
% 0.54/0.79      ((((sk_A) != (k1_xboole_0))
% 0.54/0.79        | ~ (v1_relat_1 @ sk_C)
% 0.54/0.79        | ((sk_C) = (k1_xboole_0)))),
% 0.54/0.79      inference('sup-', [status(thm)], ['94', '95'])).
% 0.54/0.79  thf('97', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.79      inference('sup-', [status(thm)], ['88', '89'])).
% 0.54/0.79  thf('98', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.54/0.79      inference('demod', [status(thm)], ['96', '97'])).
% 0.54/0.79  thf('99', plain, (((sk_A) = (k1_xboole_0))),
% 0.54/0.79      inference('demod', [status(thm)], ['73', '76'])).
% 0.54/0.79  thf('100', plain,
% 0.54/0.79      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.54/0.79      inference('demod', [status(thm)], ['98', '99'])).
% 0.54/0.79  thf('101', plain, (((sk_C) = (k1_xboole_0))),
% 0.54/0.79      inference('simplify', [status(thm)], ['100'])).
% 0.54/0.79  thf('102', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.54/0.79      inference('demod', [status(thm)], ['55', '58', '61'])).
% 0.54/0.79  thf('103', plain,
% 0.54/0.79      (![X1 : $i]:
% 0.54/0.79         (((k2_relat_1 @ X1) != (k1_xboole_0))
% 0.54/0.79          | ((X1) = (k1_xboole_0))
% 0.54/0.79          | ~ (v1_relat_1 @ X1))),
% 0.54/0.79      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.54/0.79  thf('104', plain,
% 0.54/0.79      ((((sk_A) != (k1_xboole_0))
% 0.54/0.79        | ~ (v1_relat_1 @ sk_B)
% 0.54/0.79        | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.79      inference('sup-', [status(thm)], ['102', '103'])).
% 0.54/0.79  thf('105', plain, ((v1_relat_1 @ sk_B)),
% 0.54/0.79      inference('sup-', [status(thm)], ['56', '57'])).
% 0.54/0.79  thf('106', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.79      inference('demod', [status(thm)], ['104', '105'])).
% 0.54/0.79  thf('107', plain, (((sk_A) = (k1_xboole_0))),
% 0.54/0.79      inference('demod', [status(thm)], ['73', '76'])).
% 0.54/0.79  thf('108', plain,
% 0.54/0.79      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.79      inference('demod', [status(thm)], ['106', '107'])).
% 0.54/0.79  thf('109', plain, (((sk_B) = (k1_xboole_0))),
% 0.54/0.79      inference('simplify', [status(thm)], ['108'])).
% 0.54/0.79  thf('110', plain,
% 0.54/0.79      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ 
% 0.54/0.79          (k2_funct_1 @ k1_xboole_0))),
% 0.54/0.79      inference('demod', [status(thm)], ['79', '101', '109'])).
% 0.54/0.79  thf('111', plain,
% 0.54/0.79      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.54/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.79  thf('112', plain,
% 0.54/0.79      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.54/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.79  thf(redefinition_k1_partfun1, axiom,
% 0.54/0.79    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.54/0.79     ( ( ( v1_funct_1 @ E ) & 
% 0.54/0.79         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.54/0.79         ( v1_funct_1 @ F ) & 
% 0.54/0.79         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.54/0.79       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.54/0.79  thf('113', plain,
% 0.54/0.79      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.54/0.79         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.54/0.79          | ~ (v1_funct_1 @ X33)
% 0.54/0.79          | ~ (v1_funct_1 @ X36)
% 0.54/0.79          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.54/0.79          | ((k1_partfun1 @ X34 @ X35 @ X37 @ X38 @ X33 @ X36)
% 0.54/0.79              = (k5_relat_1 @ X33 @ X36)))),
% 0.54/0.79      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.54/0.79  thf('114', plain,
% 0.54/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.79         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.54/0.79            = (k5_relat_1 @ sk_B @ X0))
% 0.54/0.79          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.54/0.79          | ~ (v1_funct_1 @ X0)
% 0.54/0.79          | ~ (v1_funct_1 @ sk_B))),
% 0.54/0.79      inference('sup-', [status(thm)], ['112', '113'])).
% 0.54/0.79  thf('115', plain, ((v1_funct_1 @ sk_B)),
% 0.54/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.79  thf('116', plain,
% 0.54/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.79         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.54/0.79            = (k5_relat_1 @ sk_B @ X0))
% 0.54/0.79          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.54/0.79          | ~ (v1_funct_1 @ X0))),
% 0.54/0.79      inference('demod', [status(thm)], ['114', '115'])).
% 0.54/0.79  thf('117', plain,
% 0.54/0.79      ((~ (v1_funct_1 @ sk_C)
% 0.54/0.79        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.54/0.79            = (k5_relat_1 @ sk_B @ sk_C)))),
% 0.54/0.79      inference('sup-', [status(thm)], ['111', '116'])).
% 0.54/0.79  thf('118', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.79  thf('119', plain,
% 0.54/0.79      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.54/0.79         = (k6_relat_1 @ sk_A))),
% 0.54/0.79      inference('demod', [status(thm)], ['23', '26'])).
% 0.54/0.79  thf('120', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_B @ sk_C))),
% 0.54/0.79      inference('demod', [status(thm)], ['117', '118', '119'])).
% 0.54/0.79  thf('121', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.54/0.79      inference('demod', [status(thm)], ['87', '90', '93'])).
% 0.54/0.79  thf(t64_funct_1, axiom,
% 0.54/0.79    (![A:$i]:
% 0.54/0.79     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.54/0.79       ( ![B:$i]:
% 0.54/0.79         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.54/0.79           ( ( ( v2_funct_1 @ A ) & 
% 0.54/0.79               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.54/0.79               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.54/0.79             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.54/0.79  thf('122', plain,
% 0.54/0.79      (![X5 : $i, X6 : $i]:
% 0.54/0.79         (~ (v1_relat_1 @ X5)
% 0.54/0.79          | ~ (v1_funct_1 @ X5)
% 0.54/0.79          | ((X5) = (k2_funct_1 @ X6))
% 0.54/0.79          | ((k5_relat_1 @ X5 @ X6) != (k6_relat_1 @ (k2_relat_1 @ X6)))
% 0.54/0.79          | ((k2_relat_1 @ X5) != (k1_relat_1 @ X6))
% 0.54/0.79          | ~ (v2_funct_1 @ X6)
% 0.54/0.79          | ~ (v1_funct_1 @ X6)
% 0.54/0.79          | ~ (v1_relat_1 @ X6))),
% 0.54/0.79      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.54/0.79  thf('123', plain,
% 0.54/0.79      (![X0 : $i]:
% 0.54/0.79         (((k5_relat_1 @ X0 @ sk_C) != (k6_relat_1 @ sk_A))
% 0.54/0.79          | ~ (v1_relat_1 @ sk_C)
% 0.54/0.79          | ~ (v1_funct_1 @ sk_C)
% 0.54/0.79          | ~ (v2_funct_1 @ sk_C)
% 0.54/0.79          | ((k2_relat_1 @ X0) != (k1_relat_1 @ sk_C))
% 0.54/0.79          | ((X0) = (k2_funct_1 @ sk_C))
% 0.54/0.79          | ~ (v1_funct_1 @ X0)
% 0.54/0.79          | ~ (v1_relat_1 @ X0))),
% 0.54/0.79      inference('sup-', [status(thm)], ['121', '122'])).
% 0.54/0.79  thf('124', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.79      inference('sup-', [status(thm)], ['88', '89'])).
% 0.54/0.79  thf('125', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.79  thf('126', plain,
% 0.54/0.79      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.54/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.79  thf('127', plain,
% 0.54/0.79      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.54/0.79         (~ (v1_funct_1 @ X20)
% 0.54/0.79          | ~ (v3_funct_2 @ X20 @ X21 @ X22)
% 0.54/0.79          | (v2_funct_1 @ X20)
% 0.54/0.79          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.54/0.79      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.54/0.79  thf('128', plain,
% 0.54/0.79      (((v2_funct_1 @ sk_C)
% 0.54/0.79        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.54/0.79        | ~ (v1_funct_1 @ sk_C))),
% 0.54/0.79      inference('sup-', [status(thm)], ['126', '127'])).
% 0.54/0.79  thf('129', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.54/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.79  thf('130', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.79  thf('131', plain, ((v2_funct_1 @ sk_C)),
% 0.54/0.79      inference('demod', [status(thm)], ['128', '129', '130'])).
% 0.54/0.79  thf('132', plain,
% 0.54/0.79      (![X0 : $i]:
% 0.54/0.79         (((k5_relat_1 @ X0 @ sk_C) != (k6_relat_1 @ sk_A))
% 0.54/0.79          | ((k2_relat_1 @ X0) != (k1_relat_1 @ sk_C))
% 0.54/0.79          | ((X0) = (k2_funct_1 @ sk_C))
% 0.54/0.79          | ~ (v1_funct_1 @ X0)
% 0.54/0.79          | ~ (v1_relat_1 @ X0))),
% 0.54/0.79      inference('demod', [status(thm)], ['123', '124', '125', '131'])).
% 0.54/0.79  thf('133', plain,
% 0.54/0.79      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ sk_A))
% 0.54/0.79        | ~ (v1_relat_1 @ sk_B)
% 0.54/0.79        | ~ (v1_funct_1 @ sk_B)
% 0.54/0.79        | ((sk_B) = (k2_funct_1 @ sk_C))
% 0.54/0.79        | ((k2_relat_1 @ sk_B) != (k1_relat_1 @ sk_C)))),
% 0.54/0.79      inference('sup-', [status(thm)], ['120', '132'])).
% 0.54/0.79  thf('134', plain, ((v1_relat_1 @ sk_B)),
% 0.54/0.79      inference('sup-', [status(thm)], ['56', '57'])).
% 0.54/0.79  thf('135', plain, ((v1_funct_1 @ sk_B)),
% 0.54/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.79  thf('136', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.54/0.79      inference('demod', [status(thm)], ['55', '58', '61'])).
% 0.54/0.79  thf('137', plain,
% 0.54/0.79      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ sk_A))
% 0.54/0.79        | ((sk_B) = (k2_funct_1 @ sk_C))
% 0.54/0.79        | ((sk_A) != (k1_relat_1 @ sk_C)))),
% 0.54/0.79      inference('demod', [status(thm)], ['133', '134', '135', '136'])).
% 0.54/0.79  thf('138', plain,
% 0.54/0.79      ((((sk_A) != (k1_relat_1 @ sk_C)) | ((sk_B) = (k2_funct_1 @ sk_C)))),
% 0.54/0.79      inference('simplify', [status(thm)], ['137'])).
% 0.54/0.79  thf('139', plain, (((sk_A) = (k1_xboole_0))),
% 0.54/0.79      inference('demod', [status(thm)], ['73', '76'])).
% 0.54/0.79  thf('140', plain,
% 0.54/0.79      ((((k1_xboole_0) != (k1_relat_1 @ sk_C)) | ((sk_B) = (k2_funct_1 @ sk_C)))),
% 0.54/0.79      inference('demod', [status(thm)], ['138', '139'])).
% 0.54/0.79  thf('141', plain, (((sk_C) = (k1_xboole_0))),
% 0.54/0.79      inference('simplify', [status(thm)], ['100'])).
% 0.54/0.79  thf(t71_relat_1, axiom,
% 0.54/0.79    (![A:$i]:
% 0.54/0.79     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.54/0.79       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.54/0.79  thf('142', plain, (![X3 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X3)) = (X3))),
% 0.54/0.79      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.54/0.79  thf('143', plain,
% 0.54/0.79      (![X1 : $i]:
% 0.54/0.79         (((k1_relat_1 @ X1) != (k1_xboole_0))
% 0.54/0.79          | ((X1) = (k1_xboole_0))
% 0.54/0.79          | ~ (v1_relat_1 @ X1))),
% 0.54/0.79      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.54/0.79  thf('144', plain,
% 0.54/0.79      (![X0 : $i]:
% 0.54/0.79         (((X0) != (k1_xboole_0))
% 0.54/0.79          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.54/0.79          | ((k6_relat_1 @ X0) = (k1_xboole_0)))),
% 0.54/0.79      inference('sup-', [status(thm)], ['142', '143'])).
% 0.54/0.79  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.54/0.79  thf('145', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.54/0.79      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.54/0.79  thf('146', plain,
% 0.54/0.79      (![X0 : $i]:
% 0.54/0.79         (((X0) != (k1_xboole_0)) | ((k6_relat_1 @ X0) = (k1_xboole_0)))),
% 0.54/0.79      inference('demod', [status(thm)], ['144', '145'])).
% 0.54/0.79  thf('147', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.79      inference('simplify', [status(thm)], ['146'])).
% 0.54/0.79  thf('148', plain, (![X3 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X3)) = (X3))),
% 0.54/0.79      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.54/0.79  thf('149', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.79      inference('sup+', [status(thm)], ['147', '148'])).
% 0.54/0.79  thf('150', plain, (((sk_B) = (k1_xboole_0))),
% 0.54/0.79      inference('simplify', [status(thm)], ['108'])).
% 0.54/0.79  thf('151', plain, (((sk_C) = (k1_xboole_0))),
% 0.54/0.79      inference('simplify', [status(thm)], ['100'])).
% 0.54/0.79  thf('152', plain,
% 0.54/0.79      ((((k1_xboole_0) != (k1_xboole_0))
% 0.54/0.79        | ((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0)))),
% 0.54/0.79      inference('demod', [status(thm)], ['140', '141', '149', '150', '151'])).
% 0.54/0.79  thf('153', plain, (((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))),
% 0.54/0.79      inference('simplify', [status(thm)], ['152'])).
% 0.54/0.79  thf('154', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.79      inference('simplify', [status(thm)], ['146'])).
% 0.54/0.79  thf('155', plain,
% 0.54/0.79      (![X32 : $i]:
% 0.54/0.79         (m1_subset_1 @ (k6_relat_1 @ X32) @ 
% 0.54/0.79          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 0.54/0.79      inference('demod', [status(thm)], ['24', '25'])).
% 0.54/0.79  thf('156', plain,
% 0.54/0.79      ((m1_subset_1 @ k1_xboole_0 @ 
% 0.54/0.79        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.54/0.79      inference('sup+', [status(thm)], ['154', '155'])).
% 0.54/0.79  thf('157', plain,
% 0.54/0.79      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.54/0.79         ((r2_relset_1 @ X17 @ X18 @ X19 @ X19)
% 0.54/0.79          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.54/0.79      inference('simplify', [status(thm)], ['39'])).
% 0.54/0.79  thf('158', plain,
% 0.54/0.79      ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.54/0.79      inference('sup-', [status(thm)], ['156', '157'])).
% 0.54/0.79  thf('159', plain, ($false),
% 0.54/0.79      inference('demod', [status(thm)], ['110', '153', '158'])).
% 0.54/0.79  
% 0.54/0.79  % SZS output end Refutation
% 0.54/0.79  
% 0.62/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

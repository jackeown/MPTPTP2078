%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5L71l75j39

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:08 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  173 (2695 expanded)
%              Number of leaves         :   41 ( 804 expanded)
%              Depth                    :   17
%              Number of atoms          : 1497 (69799 expanded)
%              Number of equality atoms :   84 ( 975 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

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

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
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

thf('12',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('19',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( X20 = X23 )
      | ~ ( r2_relset_1 @ X21 @ X22 @ X20 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','20'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('22',plain,(
    ! [X38: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('23',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
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

thf('25',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ( X45
        = ( k2_funct_1 @ X48 ) )
      | ~ ( r2_relset_1 @ X47 @ X47 @ ( k1_partfun1 @ X47 @ X46 @ X46 @ X47 @ X48 @ X45 ) @ ( k6_partfun1 @ X47 ) )
      | ( X46 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X48 )
      | ( ( k2_relset_1 @ X47 @ X46 @ X48 )
       != X46 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) )
      | ~ ( v1_funct_2 @ X48 @ X47 @ X46 )
      | ~ ( v1_funct_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t36_funct_2])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','30'])).

thf('32',plain,(
    ! [X38: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('33',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( r2_relset_1 @ X21 @ X22 @ X20 @ X23 )
      | ( X20 != X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('34',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_relset_1 @ X21 @ X22 @ X23 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('40',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('41',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
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

thf('43',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_1 @ X24 )
      | ~ ( v3_funct_2 @ X24 @ X25 @ X26 )
      | ( v2_funct_2 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('44',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['44','45','46'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('48',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v2_funct_2 @ X28 @ X27 )
      | ( ( k2_relat_1 @ X28 )
        = X27 )
      | ~ ( v5_relat_1 @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('51',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('52',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('53',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('54',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('56',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('57',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['49','54','57'])).

thf('59',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['41','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_1 @ X24 )
      | ~ ( v3_funct_2 @ X24 @ X25 @ X26 )
      | ( v2_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('62',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,
    ( ( sk_A != sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','35','36','37','38','59','65'])).

thf('67',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('69',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_relset_1 @ X21 @ X22 @ X23 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('72',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','72'])).

thf('74',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','72'])).

thf('75',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','73','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('77',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('78',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('79',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('80',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','72'])).

thf('82',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','72'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('83',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('84',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['83'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('85',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('86',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','72'])).

thf('87',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','72'])).

thf('88',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('89',plain,(
    k1_xboole_0 = sk_C ),
    inference(demod,[status(thm)],['80','81','82','84','85','86','87','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('92',plain,(
    r1_tarski @ sk_B @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('94',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_B )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','72'])).

thf('96',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','72'])).

thf('97',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('98',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('99',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','72'])).

thf('100',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','72'])).

thf('101',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('102',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['94','95','96','97','98','99','100','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) )
        & ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A )
        & ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A )
        & ( m1_subset_1 @ ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ) )).

thf('104',plain,(
    ! [X35: $i,X36: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X35 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) )
      | ~ ( v3_funct_2 @ X36 @ X35 @ X35 )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X35 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('105',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('110',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['105','106','107','108','109'])).

thf('111',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('112',plain,(
    r1_tarski @ ( k2_funct_1 @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('114',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ ( k2_funct_1 @ sk_B ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','72'])).

thf('116',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','72'])).

thf('117',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('118',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('119',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','72'])).

thf('120',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','72'])).

thf('121',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('122',plain,
    ( k1_xboole_0
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['114','115','116','117','118','119','120','121'])).

thf('123',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['94','95','96','97','98','99','100','101'])).

thf('124',plain,
    ( k1_xboole_0
    = ( k2_funct_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('126',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('127',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_relset_1 @ X21 @ X22 @ X23 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    $false ),
    inference(demod,[status(thm)],['75','89','102','124','129'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5L71l75j39
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:46:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.59/0.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.78  % Solved by: fo/fo7.sh
% 0.59/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.78  % done 870 iterations in 0.326s
% 0.59/0.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.78  % SZS output start Refutation
% 0.59/0.78  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.59/0.78  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.59/0.78  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.59/0.78  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.59/0.78  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.59/0.78  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.59/0.78  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.59/0.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.78  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.59/0.78  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.59/0.78  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.59/0.78  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.59/0.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.78  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.78  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.59/0.78  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.59/0.78  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.59/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.78  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.78  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.59/0.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.78  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.59/0.78  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.59/0.78  thf(t87_funct_2, conjecture,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.59/0.78         ( v3_funct_2 @ B @ A @ A ) & 
% 0.59/0.78         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.59/0.78       ( ![C:$i]:
% 0.59/0.78         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.59/0.78             ( v3_funct_2 @ C @ A @ A ) & 
% 0.59/0.78             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.59/0.78           ( ( r2_relset_1 @
% 0.59/0.78               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.59/0.78               ( k6_partfun1 @ A ) ) =>
% 0.59/0.78             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 0.59/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.78    (~( ![A:$i,B:$i]:
% 0.59/0.78        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.59/0.78            ( v3_funct_2 @ B @ A @ A ) & 
% 0.59/0.78            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.59/0.78          ( ![C:$i]:
% 0.59/0.78            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.59/0.78                ( v3_funct_2 @ C @ A @ A ) & 
% 0.59/0.78                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.59/0.78              ( ( r2_relset_1 @
% 0.59/0.78                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.59/0.78                  ( k6_partfun1 @ A ) ) =>
% 0.59/0.78                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 0.59/0.78    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 0.59/0.78  thf('0', plain,
% 0.59/0.78      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('1', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(redefinition_k2_funct_2, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.59/0.78         ( v3_funct_2 @ B @ A @ A ) & 
% 0.59/0.78         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.59/0.78       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.59/0.78  thf('2', plain,
% 0.59/0.78      (![X39 : $i, X40 : $i]:
% 0.59/0.78         (((k2_funct_2 @ X40 @ X39) = (k2_funct_1 @ X39))
% 0.59/0.78          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X40)))
% 0.59/0.78          | ~ (v3_funct_2 @ X39 @ X40 @ X40)
% 0.59/0.78          | ~ (v1_funct_2 @ X39 @ X40 @ X40)
% 0.59/0.78          | ~ (v1_funct_1 @ X39))),
% 0.59/0.78      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.59/0.78  thf('3', plain,
% 0.59/0.78      ((~ (v1_funct_1 @ sk_B)
% 0.59/0.78        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.59/0.78        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.59/0.78        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['1', '2'])).
% 0.59/0.78  thf('4', plain, ((v1_funct_1 @ sk_B)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('5', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('6', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('7', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.59/0.78      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.59/0.78  thf('8', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.59/0.78      inference('demod', [status(thm)], ['0', '7'])).
% 0.59/0.78  thf('9', plain,
% 0.59/0.78      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.78        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.59/0.78        (k6_partfun1 @ sk_A))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('10', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('11', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(dt_k1_partfun1, axiom,
% 0.59/0.78    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.59/0.78     ( ( ( v1_funct_1 @ E ) & 
% 0.59/0.78         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.59/0.78         ( v1_funct_1 @ F ) & 
% 0.59/0.78         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.59/0.78       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.59/0.78         ( m1_subset_1 @
% 0.59/0.78           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.59/0.78           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.59/0.78  thf('12', plain,
% 0.59/0.78      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.59/0.78         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.59/0.78          | ~ (v1_funct_1 @ X29)
% 0.59/0.78          | ~ (v1_funct_1 @ X32)
% 0.59/0.78          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.59/0.78          | (m1_subset_1 @ (k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32) @ 
% 0.59/0.78             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X34))))),
% 0.59/0.78      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.59/0.78  thf('13', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.78         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 0.59/0.78           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.59/0.78          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.59/0.78          | ~ (v1_funct_1 @ X1)
% 0.59/0.78          | ~ (v1_funct_1 @ sk_B))),
% 0.59/0.78      inference('sup-', [status(thm)], ['11', '12'])).
% 0.59/0.78  thf('14', plain, ((v1_funct_1 @ sk_B)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('15', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.78         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 0.59/0.78           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.59/0.78          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.59/0.78          | ~ (v1_funct_1 @ X1))),
% 0.59/0.78      inference('demod', [status(thm)], ['13', '14'])).
% 0.59/0.78  thf('16', plain,
% 0.59/0.78      ((~ (v1_funct_1 @ sk_C)
% 0.59/0.78        | (m1_subset_1 @ 
% 0.59/0.78           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.59/0.78           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['10', '15'])).
% 0.59/0.78  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('18', plain,
% 0.59/0.78      ((m1_subset_1 @ 
% 0.59/0.78        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.59/0.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.78      inference('demod', [status(thm)], ['16', '17'])).
% 0.59/0.78  thf(redefinition_r2_relset_1, axiom,
% 0.59/0.78    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.78     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.59/0.78         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.78       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.59/0.78  thf('19', plain,
% 0.59/0.78      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.59/0.78         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.59/0.78          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.59/0.78          | ((X20) = (X23))
% 0.59/0.78          | ~ (r2_relset_1 @ X21 @ X22 @ X20 @ X23))),
% 0.59/0.78      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.59/0.78  thf('20', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.78             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ X0)
% 0.59/0.78          | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) = (X0))
% 0.59/0.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['18', '19'])).
% 0.59/0.78  thf('21', plain,
% 0.59/0.78      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.59/0.78           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.59/0.78        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.59/0.78            = (k6_partfun1 @ sk_A)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['9', '20'])).
% 0.59/0.78  thf(dt_k6_partfun1, axiom,
% 0.59/0.78    (![A:$i]:
% 0.59/0.78     ( ( m1_subset_1 @
% 0.59/0.78         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.59/0.78       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.59/0.78  thf('22', plain,
% 0.59/0.78      (![X38 : $i]:
% 0.59/0.78         (m1_subset_1 @ (k6_partfun1 @ X38) @ 
% 0.59/0.78          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X38)))),
% 0.59/0.78      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.59/0.78  thf('23', plain,
% 0.59/0.78      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.59/0.78         = (k6_partfun1 @ sk_A))),
% 0.59/0.78      inference('demod', [status(thm)], ['21', '22'])).
% 0.59/0.78  thf('24', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(t36_funct_2, axiom,
% 0.59/0.78    (![A:$i,B:$i,C:$i]:
% 0.59/0.78     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.59/0.78         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.78       ( ![D:$i]:
% 0.59/0.78         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.59/0.78             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.59/0.78           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.59/0.78               ( r2_relset_1 @
% 0.59/0.78                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.59/0.78                 ( k6_partfun1 @ A ) ) & 
% 0.59/0.78               ( v2_funct_1 @ C ) ) =>
% 0.59/0.78             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.59/0.78               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.59/0.78  thf('25', plain,
% 0.59/0.78      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.59/0.78         (~ (v1_funct_1 @ X45)
% 0.59/0.78          | ~ (v1_funct_2 @ X45 @ X46 @ X47)
% 0.59/0.78          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 0.59/0.78          | ((X45) = (k2_funct_1 @ X48))
% 0.59/0.78          | ~ (r2_relset_1 @ X47 @ X47 @ 
% 0.59/0.78               (k1_partfun1 @ X47 @ X46 @ X46 @ X47 @ X48 @ X45) @ 
% 0.59/0.78               (k6_partfun1 @ X47))
% 0.59/0.78          | ((X46) = (k1_xboole_0))
% 0.59/0.78          | ((X47) = (k1_xboole_0))
% 0.59/0.78          | ~ (v2_funct_1 @ X48)
% 0.59/0.78          | ((k2_relset_1 @ X47 @ X46 @ X48) != (X46))
% 0.59/0.78          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46)))
% 0.59/0.78          | ~ (v1_funct_2 @ X48 @ X47 @ X46)
% 0.59/0.78          | ~ (v1_funct_1 @ X48))),
% 0.59/0.78      inference('cnf', [status(esa)], [t36_funct_2])).
% 0.59/0.78  thf('26', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (v1_funct_1 @ X0)
% 0.59/0.78          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.59/0.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.59/0.78          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.59/0.78          | ~ (v2_funct_1 @ X0)
% 0.59/0.78          | ((sk_A) = (k1_xboole_0))
% 0.59/0.78          | ((sk_A) = (k1_xboole_0))
% 0.59/0.78          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.78               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.59/0.78               (k6_partfun1 @ sk_A))
% 0.59/0.78          | ((sk_C) = (k2_funct_1 @ X0))
% 0.59/0.78          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.59/0.78          | ~ (v1_funct_1 @ sk_C))),
% 0.59/0.78      inference('sup-', [status(thm)], ['24', '25'])).
% 0.59/0.78  thf('27', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('28', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('29', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (v1_funct_1 @ X0)
% 0.59/0.78          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.59/0.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.59/0.78          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.59/0.78          | ~ (v2_funct_1 @ X0)
% 0.59/0.78          | ((sk_A) = (k1_xboole_0))
% 0.59/0.78          | ((sk_A) = (k1_xboole_0))
% 0.59/0.78          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.78               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.59/0.78               (k6_partfun1 @ sk_A))
% 0.59/0.78          | ((sk_C) = (k2_funct_1 @ X0)))),
% 0.59/0.78      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.59/0.78  thf('30', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (((sk_C) = (k2_funct_1 @ X0))
% 0.59/0.78          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.78               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.59/0.78               (k6_partfun1 @ sk_A))
% 0.59/0.78          | ((sk_A) = (k1_xboole_0))
% 0.59/0.78          | ~ (v2_funct_1 @ X0)
% 0.59/0.78          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.59/0.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.59/0.78          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.59/0.78          | ~ (v1_funct_1 @ X0))),
% 0.59/0.78      inference('simplify', [status(thm)], ['29'])).
% 0.59/0.78  thf('31', plain,
% 0.59/0.78      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 0.59/0.78           (k6_partfun1 @ sk_A))
% 0.59/0.78        | ~ (v1_funct_1 @ sk_B)
% 0.59/0.78        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.59/0.78        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.59/0.78        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 0.59/0.78        | ~ (v2_funct_1 @ sk_B)
% 0.59/0.78        | ((sk_A) = (k1_xboole_0))
% 0.59/0.78        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['23', '30'])).
% 0.59/0.78  thf('32', plain,
% 0.59/0.78      (![X38 : $i]:
% 0.59/0.78         (m1_subset_1 @ (k6_partfun1 @ X38) @ 
% 0.59/0.78          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X38)))),
% 0.59/0.78      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.59/0.78  thf('33', plain,
% 0.59/0.78      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.59/0.78         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.59/0.78          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.59/0.78          | (r2_relset_1 @ X21 @ X22 @ X20 @ X23)
% 0.59/0.78          | ((X20) != (X23)))),
% 0.59/0.78      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.59/0.78  thf('34', plain,
% 0.59/0.78      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.59/0.78         ((r2_relset_1 @ X21 @ X22 @ X23 @ X23)
% 0.59/0.78          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.59/0.78      inference('simplify', [status(thm)], ['33'])).
% 0.59/0.78  thf('35', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['32', '34'])).
% 0.59/0.78  thf('36', plain, ((v1_funct_1 @ sk_B)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('37', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('38', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('39', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(redefinition_k2_relset_1, axiom,
% 0.59/0.78    (![A:$i,B:$i,C:$i]:
% 0.59/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.78       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.59/0.78  thf('40', plain,
% 0.59/0.78      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.59/0.78         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.59/0.78          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.59/0.78      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.59/0.78  thf('41', plain,
% 0.59/0.78      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 0.59/0.78      inference('sup-', [status(thm)], ['39', '40'])).
% 0.59/0.78  thf('42', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(cc2_funct_2, axiom,
% 0.59/0.78    (![A:$i,B:$i,C:$i]:
% 0.59/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.78       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.59/0.78         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.59/0.78  thf('43', plain,
% 0.59/0.78      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.59/0.78         (~ (v1_funct_1 @ X24)
% 0.59/0.78          | ~ (v3_funct_2 @ X24 @ X25 @ X26)
% 0.59/0.78          | (v2_funct_2 @ X24 @ X26)
% 0.59/0.78          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.59/0.78      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.59/0.78  thf('44', plain,
% 0.59/0.78      (((v2_funct_2 @ sk_B @ sk_A)
% 0.59/0.78        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.59/0.78        | ~ (v1_funct_1 @ sk_B))),
% 0.59/0.78      inference('sup-', [status(thm)], ['42', '43'])).
% 0.59/0.78  thf('45', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('46', plain, ((v1_funct_1 @ sk_B)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('47', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 0.59/0.78      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.59/0.78  thf(d3_funct_2, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.59/0.78       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.59/0.78  thf('48', plain,
% 0.59/0.78      (![X27 : $i, X28 : $i]:
% 0.59/0.78         (~ (v2_funct_2 @ X28 @ X27)
% 0.59/0.78          | ((k2_relat_1 @ X28) = (X27))
% 0.59/0.78          | ~ (v5_relat_1 @ X28 @ X27)
% 0.59/0.78          | ~ (v1_relat_1 @ X28))),
% 0.59/0.78      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.59/0.78  thf('49', plain,
% 0.59/0.78      ((~ (v1_relat_1 @ sk_B)
% 0.59/0.78        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 0.59/0.78        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['47', '48'])).
% 0.59/0.78  thf('50', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(cc2_relat_1, axiom,
% 0.59/0.78    (![A:$i]:
% 0.59/0.78     ( ( v1_relat_1 @ A ) =>
% 0.59/0.78       ( ![B:$i]:
% 0.59/0.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.59/0.78  thf('51', plain,
% 0.59/0.78      (![X10 : $i, X11 : $i]:
% 0.59/0.78         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.59/0.78          | (v1_relat_1 @ X10)
% 0.59/0.78          | ~ (v1_relat_1 @ X11))),
% 0.59/0.78      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.59/0.78  thf('52', plain,
% 0.59/0.78      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 0.59/0.78      inference('sup-', [status(thm)], ['50', '51'])).
% 0.59/0.78  thf(fc6_relat_1, axiom,
% 0.59/0.78    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.59/0.78  thf('53', plain,
% 0.59/0.78      (![X12 : $i, X13 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X12 @ X13))),
% 0.59/0.78      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.59/0.78  thf('54', plain, ((v1_relat_1 @ sk_B)),
% 0.59/0.78      inference('demod', [status(thm)], ['52', '53'])).
% 0.59/0.78  thf('55', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(cc2_relset_1, axiom,
% 0.59/0.78    (![A:$i,B:$i,C:$i]:
% 0.59/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.78       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.59/0.78  thf('56', plain,
% 0.59/0.78      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.59/0.78         ((v5_relat_1 @ X14 @ X16)
% 0.59/0.78          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.59/0.78      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.59/0.78  thf('57', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 0.59/0.78      inference('sup-', [status(thm)], ['55', '56'])).
% 0.59/0.78  thf('58', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.59/0.78      inference('demod', [status(thm)], ['49', '54', '57'])).
% 0.59/0.78  thf('59', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 0.59/0.78      inference('demod', [status(thm)], ['41', '58'])).
% 0.59/0.78  thf('60', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('61', plain,
% 0.59/0.78      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.59/0.78         (~ (v1_funct_1 @ X24)
% 0.59/0.78          | ~ (v3_funct_2 @ X24 @ X25 @ X26)
% 0.59/0.78          | (v2_funct_1 @ X24)
% 0.59/0.78          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.59/0.78      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.59/0.78  thf('62', plain,
% 0.59/0.78      (((v2_funct_1 @ sk_B)
% 0.59/0.78        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.59/0.78        | ~ (v1_funct_1 @ sk_B))),
% 0.59/0.78      inference('sup-', [status(thm)], ['60', '61'])).
% 0.59/0.78  thf('63', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('64', plain, ((v1_funct_1 @ sk_B)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('65', plain, ((v2_funct_1 @ sk_B)),
% 0.59/0.78      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.59/0.78  thf('66', plain,
% 0.59/0.78      ((((sk_A) != (sk_A))
% 0.59/0.78        | ((sk_A) = (k1_xboole_0))
% 0.59/0.78        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 0.59/0.78      inference('demod', [status(thm)],
% 0.59/0.78                ['31', '35', '36', '37', '38', '59', '65'])).
% 0.59/0.78  thf('67', plain,
% 0.59/0.78      ((((sk_C) = (k2_funct_1 @ sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 0.59/0.78      inference('simplify', [status(thm)], ['66'])).
% 0.59/0.78  thf('68', plain,
% 0.59/0.78      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.59/0.78      inference('demod', [status(thm)], ['0', '7'])).
% 0.59/0.78  thf('69', plain,
% 0.59/0.78      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['67', '68'])).
% 0.59/0.78  thf('70', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('71', plain,
% 0.59/0.78      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.59/0.78         ((r2_relset_1 @ X21 @ X22 @ X23 @ X23)
% 0.59/0.78          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.59/0.78      inference('simplify', [status(thm)], ['33'])).
% 0.59/0.78  thf('72', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 0.59/0.78      inference('sup-', [status(thm)], ['70', '71'])).
% 0.59/0.78  thf('73', plain, (((sk_A) = (k1_xboole_0))),
% 0.59/0.78      inference('demod', [status(thm)], ['69', '72'])).
% 0.59/0.78  thf('74', plain, (((sk_A) = (k1_xboole_0))),
% 0.59/0.78      inference('demod', [status(thm)], ['69', '72'])).
% 0.59/0.78  thf('75', plain,
% 0.59/0.78      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.59/0.78      inference('demod', [status(thm)], ['8', '73', '74'])).
% 0.59/0.78  thf('76', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(t3_subset, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.59/0.78  thf('77', plain,
% 0.59/0.78      (![X7 : $i, X8 : $i]:
% 0.59/0.78         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.59/0.78      inference('cnf', [status(esa)], [t3_subset])).
% 0.59/0.78  thf('78', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 0.59/0.78      inference('sup-', [status(thm)], ['76', '77'])).
% 0.59/0.78  thf(d10_xboole_0, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.59/0.78  thf('79', plain,
% 0.59/0.78      (![X0 : $i, X2 : $i]:
% 0.59/0.78         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.59/0.78      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.78  thf('80', plain,
% 0.59/0.78      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_C)
% 0.59/0.78        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (sk_C)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['78', '79'])).
% 0.59/0.78  thf('81', plain, (((sk_A) = (k1_xboole_0))),
% 0.59/0.78      inference('demod', [status(thm)], ['69', '72'])).
% 0.59/0.78  thf('82', plain, (((sk_A) = (k1_xboole_0))),
% 0.59/0.78      inference('demod', [status(thm)], ['69', '72'])).
% 0.59/0.78  thf(t113_zfmisc_1, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.59/0.78       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.59/0.78  thf('83', plain,
% 0.59/0.78      (![X5 : $i, X6 : $i]:
% 0.59/0.78         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.59/0.78      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.59/0.78  thf('84', plain,
% 0.59/0.78      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.59/0.78      inference('simplify', [status(thm)], ['83'])).
% 0.59/0.78  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.59/0.78  thf('85', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.59/0.78      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.59/0.78  thf('86', plain, (((sk_A) = (k1_xboole_0))),
% 0.59/0.78      inference('demod', [status(thm)], ['69', '72'])).
% 0.59/0.78  thf('87', plain, (((sk_A) = (k1_xboole_0))),
% 0.59/0.78      inference('demod', [status(thm)], ['69', '72'])).
% 0.59/0.78  thf('88', plain,
% 0.59/0.78      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.59/0.78      inference('simplify', [status(thm)], ['83'])).
% 0.59/0.78  thf('89', plain, (((k1_xboole_0) = (sk_C))),
% 0.59/0.78      inference('demod', [status(thm)],
% 0.59/0.78                ['80', '81', '82', '84', '85', '86', '87', '88'])).
% 0.59/0.78  thf('90', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('91', plain,
% 0.59/0.78      (![X7 : $i, X8 : $i]:
% 0.59/0.78         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.59/0.78      inference('cnf', [status(esa)], [t3_subset])).
% 0.59/0.78  thf('92', plain, ((r1_tarski @ sk_B @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 0.59/0.78      inference('sup-', [status(thm)], ['90', '91'])).
% 0.59/0.78  thf('93', plain,
% 0.59/0.78      (![X0 : $i, X2 : $i]:
% 0.59/0.78         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.59/0.78      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.78  thf('94', plain,
% 0.59/0.78      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_B)
% 0.59/0.78        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (sk_B)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['92', '93'])).
% 0.59/0.78  thf('95', plain, (((sk_A) = (k1_xboole_0))),
% 0.59/0.78      inference('demod', [status(thm)], ['69', '72'])).
% 0.59/0.78  thf('96', plain, (((sk_A) = (k1_xboole_0))),
% 0.59/0.78      inference('demod', [status(thm)], ['69', '72'])).
% 0.59/0.78  thf('97', plain,
% 0.59/0.78      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.59/0.78      inference('simplify', [status(thm)], ['83'])).
% 0.59/0.78  thf('98', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.59/0.78      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.59/0.78  thf('99', plain, (((sk_A) = (k1_xboole_0))),
% 0.59/0.78      inference('demod', [status(thm)], ['69', '72'])).
% 0.59/0.78  thf('100', plain, (((sk_A) = (k1_xboole_0))),
% 0.59/0.78      inference('demod', [status(thm)], ['69', '72'])).
% 0.59/0.78  thf('101', plain,
% 0.59/0.78      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.59/0.78      inference('simplify', [status(thm)], ['83'])).
% 0.59/0.78  thf('102', plain, (((k1_xboole_0) = (sk_B))),
% 0.59/0.78      inference('demod', [status(thm)],
% 0.59/0.78                ['94', '95', '96', '97', '98', '99', '100', '101'])).
% 0.59/0.78  thf('103', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(dt_k2_funct_2, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.59/0.78         ( v3_funct_2 @ B @ A @ A ) & 
% 0.59/0.78         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.59/0.78       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 0.59/0.78         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.59/0.78         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.59/0.78         ( m1_subset_1 @
% 0.59/0.78           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 0.59/0.78  thf('104', plain,
% 0.59/0.78      (![X35 : $i, X36 : $i]:
% 0.59/0.78         ((m1_subset_1 @ (k2_funct_2 @ X35 @ X36) @ 
% 0.59/0.78           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))
% 0.59/0.78          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))
% 0.59/0.78          | ~ (v3_funct_2 @ X36 @ X35 @ X35)
% 0.59/0.78          | ~ (v1_funct_2 @ X36 @ X35 @ X35)
% 0.59/0.78          | ~ (v1_funct_1 @ X36))),
% 0.59/0.78      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.59/0.78  thf('105', plain,
% 0.59/0.78      ((~ (v1_funct_1 @ sk_B)
% 0.59/0.78        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.59/0.78        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.59/0.78        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.59/0.78           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['103', '104'])).
% 0.59/0.78  thf('106', plain, ((v1_funct_1 @ sk_B)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('107', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('108', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('109', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.59/0.78      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.59/0.78  thf('110', plain,
% 0.59/0.78      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.59/0.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.78      inference('demod', [status(thm)], ['105', '106', '107', '108', '109'])).
% 0.59/0.78  thf('111', plain,
% 0.59/0.78      (![X7 : $i, X8 : $i]:
% 0.59/0.78         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.59/0.78      inference('cnf', [status(esa)], [t3_subset])).
% 0.59/0.78  thf('112', plain,
% 0.59/0.78      ((r1_tarski @ (k2_funct_1 @ sk_B) @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 0.59/0.78      inference('sup-', [status(thm)], ['110', '111'])).
% 0.59/0.78  thf('113', plain,
% 0.59/0.78      (![X0 : $i, X2 : $i]:
% 0.59/0.78         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.59/0.78      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.78  thf('114', plain,
% 0.59/0.78      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_A) @ (k2_funct_1 @ sk_B))
% 0.59/0.78        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (k2_funct_1 @ sk_B)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['112', '113'])).
% 0.59/0.78  thf('115', plain, (((sk_A) = (k1_xboole_0))),
% 0.59/0.78      inference('demod', [status(thm)], ['69', '72'])).
% 0.59/0.78  thf('116', plain, (((sk_A) = (k1_xboole_0))),
% 0.59/0.78      inference('demod', [status(thm)], ['69', '72'])).
% 0.59/0.78  thf('117', plain,
% 0.59/0.78      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.59/0.78      inference('simplify', [status(thm)], ['83'])).
% 0.59/0.78  thf('118', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.59/0.78      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.59/0.78  thf('119', plain, (((sk_A) = (k1_xboole_0))),
% 0.59/0.78      inference('demod', [status(thm)], ['69', '72'])).
% 0.59/0.78  thf('120', plain, (((sk_A) = (k1_xboole_0))),
% 0.59/0.78      inference('demod', [status(thm)], ['69', '72'])).
% 0.59/0.78  thf('121', plain,
% 0.59/0.78      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.59/0.78      inference('simplify', [status(thm)], ['83'])).
% 0.59/0.78  thf('122', plain, (((k1_xboole_0) = (k2_funct_1 @ sk_B))),
% 0.59/0.78      inference('demod', [status(thm)],
% 0.59/0.78                ['114', '115', '116', '117', '118', '119', '120', '121'])).
% 0.59/0.78  thf('123', plain, (((k1_xboole_0) = (sk_B))),
% 0.59/0.78      inference('demod', [status(thm)],
% 0.59/0.78                ['94', '95', '96', '97', '98', '99', '100', '101'])).
% 0.59/0.78  thf('124', plain, (((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))),
% 0.59/0.78      inference('demod', [status(thm)], ['122', '123'])).
% 0.59/0.78  thf('125', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.59/0.78      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.59/0.78  thf('126', plain,
% 0.59/0.78      (![X7 : $i, X9 : $i]:
% 0.59/0.78         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.59/0.78      inference('cnf', [status(esa)], [t3_subset])).
% 0.59/0.78  thf('127', plain,
% 0.59/0.78      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['125', '126'])).
% 0.59/0.78  thf('128', plain,
% 0.59/0.78      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.59/0.78         ((r2_relset_1 @ X21 @ X22 @ X23 @ X23)
% 0.59/0.78          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.59/0.78      inference('simplify', [status(thm)], ['33'])).
% 0.59/0.78  thf('129', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.59/0.78      inference('sup-', [status(thm)], ['127', '128'])).
% 0.59/0.78  thf('130', plain, ($false),
% 0.59/0.78      inference('demod', [status(thm)], ['75', '89', '102', '124', '129'])).
% 0.59/0.78  
% 0.59/0.78  % SZS output end Refutation
% 0.59/0.78  
% 0.59/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

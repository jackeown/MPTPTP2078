%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DGffRIpXkm

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:05 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :  215 (1154 expanded)
%              Number of leaves         :   45 ( 360 expanded)
%              Depth                    :   17
%              Number of atoms          : 1919 (26964 expanded)
%              Number of equality atoms :  140 ( 479 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

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
    ! [X37: $i,X38: $i] :
      ( ( ( k2_funct_2 @ X38 @ X37 )
        = ( k2_funct_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X38 ) ) )
      | ~ ( v3_funct_2 @ X37 @ X38 @ X38 )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X38 )
      | ~ ( v1_funct_1 @ X37 ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X32 @ X33 @ X35 @ X36 @ X31 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X36 ) ) ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( X21 = X24 )
      | ~ ( r2_relset_1 @ X22 @ X23 @ X21 @ X24 ) ) ),
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

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('22',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('23',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('24',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,(
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

thf('27',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ( X44
        = ( k2_funct_1 @ X47 ) )
      | ~ ( r2_relset_1 @ X46 @ X46 @ ( k1_partfun1 @ X46 @ X45 @ X45 @ X46 @ X47 @ X44 ) @ ( k6_partfun1 @ X46 ) )
      | ( X45 = k1_xboole_0 )
      | ( X46 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X47 )
      | ( ( k2_relset_1 @ X46 @ X45 @ X47 )
       != X45 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) )
      | ~ ( v1_funct_2 @ X47 @ X46 @ X45 )
      | ~ ( v1_funct_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t36_funct_2])).

thf('28',plain,(
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
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
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
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
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
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
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
    inference('sup-',[status(thm)],['25','32'])).

thf('34',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('35',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( r2_relset_1 @ X22 @ X23 @ X21 @ X24 )
      | ( X21 != X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('36',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_relset_1 @ X22 @ X23 @ X24 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('42',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('43',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
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

thf('45',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_1 @ X26 )
      | ~ ( v3_funct_2 @ X26 @ X27 @ X28 )
      | ( v2_funct_2 @ X26 @ X28 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('46',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['46','47','48'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('50',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v2_funct_2 @ X30 @ X29 )
      | ( ( k2_relat_1 @ X30 )
        = X29 )
      | ~ ( v5_relat_1 @ X30 @ X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('53',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('54',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('56',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v5_relat_1 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('57',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['51','54','57'])).

thf('59',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['43','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_1 @ X26 )
      | ~ ( v3_funct_2 @ X26 @ X27 @ X28 )
      | ( v2_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
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
    inference(demod,[status(thm)],['33','37','38','39','40','59','65'])).

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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_relset_1 @ X22 @ X23 @ X24 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

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

thf('77',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_1 @ X26 )
      | ~ ( v3_funct_2 @ X26 @ X27 @ X28 )
      | ( v2_funct_2 @ X26 @ X28 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('78',plain,
    ( ( v2_funct_2 @ sk_C @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v2_funct_2 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v2_funct_2 @ X30 @ X29 )
      | ( ( k2_relat_1 @ X30 )
        = X29 )
      | ~ ( v5_relat_1 @ X30 @ X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('83',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v5_relat_1 @ sk_C @ sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('86',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v5_relat_1 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('89',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['83','86','89'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('91',plain,(
    ! [X3: $i] :
      ( ( ( k2_relat_1 @ X3 )
       != k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('92',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['84','85'])).

thf('94',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','72'])).

thf('96',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['51','54','57'])).

thf('99',plain,(
    ! [X3: $i] :
      ( ( ( k2_relat_1 @ X3 )
       != k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('100',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['52','53'])).

thf('102',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','72'])).

thf('104',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( v1_funct_1 @ ( k1_partfun1 @ X32 @ X33 @ X35 @ X36 @ X31 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['106','111'])).

thf('113',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('116',plain,(
    v1_funct_1 @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['114','115'])).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ X0 )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('118',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ X0 )
        = ( k5_relat_1 @ X0 @ ( k6_partfun1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('120',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('121',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('122',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['120','121'])).

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

thf('124',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( X10
        = ( k2_funct_1 @ X11 ) )
      | ( ( k5_relat_1 @ X11 @ X10 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X11 ) ) )
      | ( ( k2_relat_1 @ X11 )
       != ( k1_relat_1 @ X10 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t63_funct_1])).

thf('125',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('126',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( X10
        = ( k2_funct_1 @ X11 ) )
      | ( ( k5_relat_1 @ X11 @ X10 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X11 ) ) )
      | ( ( k2_relat_1 @ X11 )
       != ( k1_relat_1 @ X10 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
       != ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k6_partfun1 @ X0 ) )
       != ( k1_relat_1 @ X1 ) )
      | ( X1
        = ( k2_funct_1 @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['123','126'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('128',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('129',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('130',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X6 ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('132',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('133',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X7 ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X5: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('135',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('136',plain,(
    ! [X5: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X5 ) )
      = X5 ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
       != ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ( X0
       != ( k1_relat_1 @ X1 ) )
      | ( X1
        = ( k2_funct_1 @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['127','130','133','136'])).

thf('138',plain,(
    ! [X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X1
        = ( k2_funct_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X1 ) ) ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X1 ) ) )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X1 ) ) @ X1 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) @ ( k6_partfun1 @ X0 ) )
       != ( k6_partfun1 @ ( k1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) )
      | ( ( k6_partfun1 @ X0 )
        = ( k2_funct_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['122','138'])).

thf('140',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('141',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('142',plain,(
    ! [X4: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('143',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X6 ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
       != ( k6_partfun1 @ X0 ) )
      | ( ( k6_partfun1 @ X0 )
        = ( k2_funct_1 @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['139','140','141','142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ X0 )
        = ( k2_funct_1 @ ( k6_partfun1 @ X0 ) ) )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
       != ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k6_partfun1 @ X0 ) )
       != ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k6_partfun1 @ X0 )
        = ( k2_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['119','145'])).

thf('147',plain,(
    ! [X5: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X5 ) )
      = X5 ) ),
    inference(demod,[status(thm)],['134','135'])).

thf(t126_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k8_relat_1 @ ( k2_relat_1 @ A ) @ A )
        = A ) ) )).

thf('148',plain,(
    ! [X2: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X2 ) @ X2 )
        = X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t126_relat_1])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X6 ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X6 ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ X0 )
       != ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k6_partfun1 @ X0 )
        = ( k2_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['146','151','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ X0 )
        = ( k2_funct_1 @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k2_funct_1 @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['116','154'])).

thf('156',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','72'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('157',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('158',plain,(
    ! [X39: $i] :
      ( ( k6_partfun1 @ X39 )
      = ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('159',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','72'])).

thf('161',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['157','158'])).

thf('162',plain,
    ( k1_xboole_0
    = ( k2_funct_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['155','156','159','160','161'])).

thf('163',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['157','158'])).

thf('164',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('165',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_relset_1 @ X22 @ X23 @ X24 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('167',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    $false ),
    inference(demod,[status(thm)],['75','97','105','162','167'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DGffRIpXkm
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:13:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.67/0.91  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.67/0.91  % Solved by: fo/fo7.sh
% 0.67/0.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.91  % done 585 iterations in 0.455s
% 0.67/0.91  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.67/0.91  % SZS output start Refutation
% 0.67/0.91  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.67/0.91  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.67/0.91  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.67/0.91  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.67/0.91  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.67/0.91  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.67/0.91  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.67/0.91  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.67/0.91  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.91  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.67/0.91  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.67/0.91  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.67/0.91  thf(sk_B_type, type, sk_B: $i).
% 0.67/0.91  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.67/0.91  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.67/0.91  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.67/0.91  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.67/0.91  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.67/0.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.67/0.91  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.67/0.91  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.67/0.91  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.67/0.91  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.67/0.91  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.67/0.91  thf(sk_C_type, type, sk_C: $i).
% 0.67/0.91  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.67/0.91  thf(t87_funct_2, conjecture,
% 0.67/0.91    (![A:$i,B:$i]:
% 0.67/0.91     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.67/0.91         ( v3_funct_2 @ B @ A @ A ) & 
% 0.67/0.91         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.67/0.91       ( ![C:$i]:
% 0.67/0.91         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.67/0.91             ( v3_funct_2 @ C @ A @ A ) & 
% 0.67/0.91             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.67/0.91           ( ( r2_relset_1 @
% 0.67/0.91               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.67/0.91               ( k6_partfun1 @ A ) ) =>
% 0.67/0.91             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 0.67/0.91  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.91    (~( ![A:$i,B:$i]:
% 0.67/0.91        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.67/0.91            ( v3_funct_2 @ B @ A @ A ) & 
% 0.67/0.91            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.67/0.91          ( ![C:$i]:
% 0.67/0.91            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.67/0.91                ( v3_funct_2 @ C @ A @ A ) & 
% 0.67/0.91                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.67/0.91              ( ( r2_relset_1 @
% 0.67/0.91                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.67/0.91                  ( k6_partfun1 @ A ) ) =>
% 0.67/0.91                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 0.67/0.91    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 0.67/0.91  thf('0', plain,
% 0.67/0.91      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('1', plain,
% 0.67/0.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf(redefinition_k2_funct_2, axiom,
% 0.67/0.91    (![A:$i,B:$i]:
% 0.67/0.91     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.67/0.91         ( v3_funct_2 @ B @ A @ A ) & 
% 0.67/0.91         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.67/0.91       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.67/0.91  thf('2', plain,
% 0.67/0.91      (![X37 : $i, X38 : $i]:
% 0.67/0.91         (((k2_funct_2 @ X38 @ X37) = (k2_funct_1 @ X37))
% 0.67/0.91          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X38)))
% 0.67/0.91          | ~ (v3_funct_2 @ X37 @ X38 @ X38)
% 0.67/0.91          | ~ (v1_funct_2 @ X37 @ X38 @ X38)
% 0.67/0.91          | ~ (v1_funct_1 @ X37))),
% 0.67/0.91      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.67/0.91  thf('3', plain,
% 0.67/0.91      ((~ (v1_funct_1 @ sk_B)
% 0.67/0.91        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.67/0.91        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.67/0.91        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 0.67/0.91      inference('sup-', [status(thm)], ['1', '2'])).
% 0.67/0.91  thf('4', plain, ((v1_funct_1 @ sk_B)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('5', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('6', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('7', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.67/0.91      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.67/0.91  thf('8', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.67/0.91      inference('demod', [status(thm)], ['0', '7'])).
% 0.67/0.91  thf('9', plain,
% 0.67/0.91      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.67/0.91        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.67/0.91        (k6_partfun1 @ sk_A))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('10', plain,
% 0.67/0.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('11', plain,
% 0.67/0.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf(dt_k1_partfun1, axiom,
% 0.67/0.91    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.67/0.91     ( ( ( v1_funct_1 @ E ) & 
% 0.67/0.91         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.67/0.91         ( v1_funct_1 @ F ) & 
% 0.67/0.91         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.67/0.91       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.67/0.91         ( m1_subset_1 @
% 0.67/0.91           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.67/0.91           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.67/0.91  thf('12', plain,
% 0.67/0.91      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.67/0.91         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.67/0.91          | ~ (v1_funct_1 @ X31)
% 0.67/0.91          | ~ (v1_funct_1 @ X34)
% 0.67/0.91          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.67/0.91          | (m1_subset_1 @ (k1_partfun1 @ X32 @ X33 @ X35 @ X36 @ X31 @ X34) @ 
% 0.67/0.91             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X36))))),
% 0.67/0.91      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.67/0.91  thf('13', plain,
% 0.67/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.91         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 0.67/0.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.67/0.91          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.67/0.91          | ~ (v1_funct_1 @ X1)
% 0.67/0.91          | ~ (v1_funct_1 @ sk_B))),
% 0.67/0.91      inference('sup-', [status(thm)], ['11', '12'])).
% 0.67/0.91  thf('14', plain, ((v1_funct_1 @ sk_B)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('15', plain,
% 0.67/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.91         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 0.67/0.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.67/0.91          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.67/0.91          | ~ (v1_funct_1 @ X1))),
% 0.67/0.91      inference('demod', [status(thm)], ['13', '14'])).
% 0.67/0.91  thf('16', plain,
% 0.67/0.91      ((~ (v1_funct_1 @ sk_C)
% 0.67/0.91        | (m1_subset_1 @ 
% 0.67/0.91           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.67/0.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.67/0.91      inference('sup-', [status(thm)], ['10', '15'])).
% 0.67/0.91  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('18', plain,
% 0.67/0.91      ((m1_subset_1 @ 
% 0.67/0.91        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.67/0.91        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.67/0.91      inference('demod', [status(thm)], ['16', '17'])).
% 0.67/0.91  thf(redefinition_r2_relset_1, axiom,
% 0.67/0.91    (![A:$i,B:$i,C:$i,D:$i]:
% 0.67/0.91     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.67/0.91         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.67/0.91       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.67/0.91  thf('19', plain,
% 0.67/0.91      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.67/0.91         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.67/0.91          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.67/0.91          | ((X21) = (X24))
% 0.67/0.91          | ~ (r2_relset_1 @ X22 @ X23 @ X21 @ X24))),
% 0.67/0.91      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.67/0.91  thf('20', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.67/0.91             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ X0)
% 0.67/0.91          | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) = (X0))
% 0.67/0.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.67/0.91      inference('sup-', [status(thm)], ['18', '19'])).
% 0.67/0.91  thf('21', plain,
% 0.67/0.91      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.67/0.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.67/0.91        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.67/0.91            = (k6_partfun1 @ sk_A)))),
% 0.67/0.91      inference('sup-', [status(thm)], ['9', '20'])).
% 0.67/0.91  thf(t29_relset_1, axiom,
% 0.67/0.91    (![A:$i]:
% 0.67/0.91     ( m1_subset_1 @
% 0.67/0.91       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.67/0.91  thf('22', plain,
% 0.67/0.91      (![X25 : $i]:
% 0.67/0.91         (m1_subset_1 @ (k6_relat_1 @ X25) @ 
% 0.67/0.91          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))),
% 0.67/0.91      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.67/0.91  thf(redefinition_k6_partfun1, axiom,
% 0.67/0.91    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.67/0.91  thf('23', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 0.67/0.91      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.67/0.91  thf('24', plain,
% 0.67/0.91      (![X25 : $i]:
% 0.67/0.91         (m1_subset_1 @ (k6_partfun1 @ X25) @ 
% 0.67/0.91          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))),
% 0.67/0.91      inference('demod', [status(thm)], ['22', '23'])).
% 0.67/0.91  thf('25', plain,
% 0.67/0.91      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.67/0.91         = (k6_partfun1 @ sk_A))),
% 0.67/0.91      inference('demod', [status(thm)], ['21', '24'])).
% 0.67/0.91  thf('26', plain,
% 0.67/0.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf(t36_funct_2, axiom,
% 0.67/0.91    (![A:$i,B:$i,C:$i]:
% 0.67/0.91     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.67/0.91         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.67/0.91       ( ![D:$i]:
% 0.67/0.91         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.67/0.91             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.67/0.91           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.67/0.91               ( r2_relset_1 @
% 0.67/0.91                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.67/0.91                 ( k6_partfun1 @ A ) ) & 
% 0.67/0.91               ( v2_funct_1 @ C ) ) =>
% 0.67/0.91             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.67/0.91               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.67/0.91  thf('27', plain,
% 0.67/0.91      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.67/0.91         (~ (v1_funct_1 @ X44)
% 0.67/0.91          | ~ (v1_funct_2 @ X44 @ X45 @ X46)
% 0.67/0.91          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 0.67/0.91          | ((X44) = (k2_funct_1 @ X47))
% 0.67/0.91          | ~ (r2_relset_1 @ X46 @ X46 @ 
% 0.67/0.91               (k1_partfun1 @ X46 @ X45 @ X45 @ X46 @ X47 @ X44) @ 
% 0.67/0.91               (k6_partfun1 @ X46))
% 0.67/0.91          | ((X45) = (k1_xboole_0))
% 0.67/0.91          | ((X46) = (k1_xboole_0))
% 0.67/0.91          | ~ (v2_funct_1 @ X47)
% 0.67/0.91          | ((k2_relset_1 @ X46 @ X45 @ X47) != (X45))
% 0.67/0.91          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45)))
% 0.67/0.91          | ~ (v1_funct_2 @ X47 @ X46 @ X45)
% 0.67/0.91          | ~ (v1_funct_1 @ X47))),
% 0.67/0.91      inference('cnf', [status(esa)], [t36_funct_2])).
% 0.67/0.91  thf('28', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (~ (v1_funct_1 @ X0)
% 0.67/0.91          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.67/0.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.67/0.91          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.67/0.91          | ~ (v2_funct_1 @ X0)
% 0.67/0.91          | ((sk_A) = (k1_xboole_0))
% 0.67/0.91          | ((sk_A) = (k1_xboole_0))
% 0.67/0.91          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.67/0.91               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.67/0.91               (k6_partfun1 @ sk_A))
% 0.67/0.91          | ((sk_C) = (k2_funct_1 @ X0))
% 0.67/0.91          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.67/0.91          | ~ (v1_funct_1 @ sk_C))),
% 0.67/0.91      inference('sup-', [status(thm)], ['26', '27'])).
% 0.67/0.91  thf('29', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('30', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('31', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (~ (v1_funct_1 @ X0)
% 0.67/0.91          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.67/0.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.67/0.91          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.67/0.91          | ~ (v2_funct_1 @ X0)
% 0.67/0.91          | ((sk_A) = (k1_xboole_0))
% 0.67/0.91          | ((sk_A) = (k1_xboole_0))
% 0.67/0.91          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.67/0.91               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.67/0.91               (k6_partfun1 @ sk_A))
% 0.67/0.91          | ((sk_C) = (k2_funct_1 @ X0)))),
% 0.67/0.91      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.67/0.91  thf('32', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (((sk_C) = (k2_funct_1 @ X0))
% 0.67/0.91          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.67/0.91               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.67/0.91               (k6_partfun1 @ sk_A))
% 0.67/0.91          | ((sk_A) = (k1_xboole_0))
% 0.67/0.91          | ~ (v2_funct_1 @ X0)
% 0.67/0.91          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.67/0.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.67/0.91          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.67/0.91          | ~ (v1_funct_1 @ X0))),
% 0.67/0.91      inference('simplify', [status(thm)], ['31'])).
% 0.67/0.91  thf('33', plain,
% 0.67/0.91      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 0.67/0.91           (k6_partfun1 @ sk_A))
% 0.67/0.91        | ~ (v1_funct_1 @ sk_B)
% 0.67/0.91        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.67/0.91        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.67/0.91        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 0.67/0.91        | ~ (v2_funct_1 @ sk_B)
% 0.67/0.91        | ((sk_A) = (k1_xboole_0))
% 0.67/0.91        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 0.67/0.91      inference('sup-', [status(thm)], ['25', '32'])).
% 0.67/0.91  thf('34', plain,
% 0.67/0.91      (![X25 : $i]:
% 0.67/0.91         (m1_subset_1 @ (k6_partfun1 @ X25) @ 
% 0.67/0.91          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))),
% 0.67/0.91      inference('demod', [status(thm)], ['22', '23'])).
% 0.67/0.91  thf('35', plain,
% 0.67/0.91      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.67/0.91         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.67/0.91          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.67/0.91          | (r2_relset_1 @ X22 @ X23 @ X21 @ X24)
% 0.67/0.91          | ((X21) != (X24)))),
% 0.67/0.91      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.67/0.91  thf('36', plain,
% 0.67/0.91      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.67/0.91         ((r2_relset_1 @ X22 @ X23 @ X24 @ X24)
% 0.67/0.91          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.67/0.91      inference('simplify', [status(thm)], ['35'])).
% 0.67/0.91  thf('37', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 0.67/0.91      inference('sup-', [status(thm)], ['34', '36'])).
% 0.67/0.91  thf('38', plain, ((v1_funct_1 @ sk_B)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('39', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('40', plain,
% 0.67/0.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('41', plain,
% 0.67/0.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf(redefinition_k2_relset_1, axiom,
% 0.67/0.91    (![A:$i,B:$i,C:$i]:
% 0.67/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.67/0.91       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.67/0.91  thf('42', plain,
% 0.67/0.91      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.67/0.91         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 0.67/0.91          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.67/0.91      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.67/0.91  thf('43', plain,
% 0.67/0.91      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 0.67/0.91      inference('sup-', [status(thm)], ['41', '42'])).
% 0.67/0.91  thf('44', plain,
% 0.67/0.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf(cc2_funct_2, axiom,
% 0.67/0.91    (![A:$i,B:$i,C:$i]:
% 0.67/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.67/0.91       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.67/0.91         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.67/0.91  thf('45', plain,
% 0.67/0.91      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.67/0.91         (~ (v1_funct_1 @ X26)
% 0.67/0.91          | ~ (v3_funct_2 @ X26 @ X27 @ X28)
% 0.67/0.91          | (v2_funct_2 @ X26 @ X28)
% 0.67/0.91          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.67/0.91      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.67/0.91  thf('46', plain,
% 0.67/0.91      (((v2_funct_2 @ sk_B @ sk_A)
% 0.67/0.91        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.67/0.91        | ~ (v1_funct_1 @ sk_B))),
% 0.67/0.91      inference('sup-', [status(thm)], ['44', '45'])).
% 0.67/0.91  thf('47', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('48', plain, ((v1_funct_1 @ sk_B)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('49', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 0.67/0.91      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.67/0.91  thf(d3_funct_2, axiom,
% 0.67/0.91    (![A:$i,B:$i]:
% 0.67/0.91     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.67/0.91       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.67/0.91  thf('50', plain,
% 0.67/0.91      (![X29 : $i, X30 : $i]:
% 0.67/0.91         (~ (v2_funct_2 @ X30 @ X29)
% 0.67/0.91          | ((k2_relat_1 @ X30) = (X29))
% 0.67/0.91          | ~ (v5_relat_1 @ X30 @ X29)
% 0.67/0.91          | ~ (v1_relat_1 @ X30))),
% 0.67/0.91      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.67/0.91  thf('51', plain,
% 0.67/0.91      ((~ (v1_relat_1 @ sk_B)
% 0.67/0.91        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 0.67/0.91        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 0.67/0.91      inference('sup-', [status(thm)], ['49', '50'])).
% 0.67/0.91  thf('52', plain,
% 0.67/0.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf(cc1_relset_1, axiom,
% 0.67/0.91    (![A:$i,B:$i,C:$i]:
% 0.67/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.67/0.91       ( v1_relat_1 @ C ) ))).
% 0.67/0.91  thf('53', plain,
% 0.67/0.91      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.67/0.91         ((v1_relat_1 @ X12)
% 0.67/0.91          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.67/0.91      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.67/0.91  thf('54', plain, ((v1_relat_1 @ sk_B)),
% 0.67/0.91      inference('sup-', [status(thm)], ['52', '53'])).
% 0.67/0.91  thf('55', plain,
% 0.67/0.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf(cc2_relset_1, axiom,
% 0.67/0.91    (![A:$i,B:$i,C:$i]:
% 0.67/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.67/0.91       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.67/0.91  thf('56', plain,
% 0.67/0.91      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.67/0.91         ((v5_relat_1 @ X15 @ X17)
% 0.67/0.91          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.67/0.91      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.67/0.91  thf('57', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 0.67/0.91      inference('sup-', [status(thm)], ['55', '56'])).
% 0.67/0.91  thf('58', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.67/0.91      inference('demod', [status(thm)], ['51', '54', '57'])).
% 0.67/0.91  thf('59', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 0.67/0.91      inference('demod', [status(thm)], ['43', '58'])).
% 0.67/0.91  thf('60', plain,
% 0.67/0.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('61', plain,
% 0.67/0.91      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.67/0.91         (~ (v1_funct_1 @ X26)
% 0.67/0.91          | ~ (v3_funct_2 @ X26 @ X27 @ X28)
% 0.67/0.91          | (v2_funct_1 @ X26)
% 0.67/0.91          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.67/0.91      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.67/0.91  thf('62', plain,
% 0.67/0.91      (((v2_funct_1 @ sk_B)
% 0.67/0.91        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.67/0.91        | ~ (v1_funct_1 @ sk_B))),
% 0.67/0.91      inference('sup-', [status(thm)], ['60', '61'])).
% 0.67/0.91  thf('63', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('64', plain, ((v1_funct_1 @ sk_B)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('65', plain, ((v2_funct_1 @ sk_B)),
% 0.67/0.91      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.67/0.91  thf('66', plain,
% 0.67/0.91      ((((sk_A) != (sk_A))
% 0.67/0.91        | ((sk_A) = (k1_xboole_0))
% 0.67/0.91        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 0.67/0.91      inference('demod', [status(thm)],
% 0.67/0.91                ['33', '37', '38', '39', '40', '59', '65'])).
% 0.67/0.91  thf('67', plain,
% 0.67/0.91      ((((sk_C) = (k2_funct_1 @ sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 0.67/0.91      inference('simplify', [status(thm)], ['66'])).
% 0.67/0.91  thf('68', plain,
% 0.67/0.91      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.67/0.91      inference('demod', [status(thm)], ['0', '7'])).
% 0.67/0.91  thf('69', plain,
% 0.67/0.91      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.67/0.91      inference('sup-', [status(thm)], ['67', '68'])).
% 0.67/0.91  thf('70', plain,
% 0.67/0.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('71', plain,
% 0.67/0.91      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.67/0.91         ((r2_relset_1 @ X22 @ X23 @ X24 @ X24)
% 0.67/0.91          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.67/0.91      inference('simplify', [status(thm)], ['35'])).
% 0.67/0.91  thf('72', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 0.67/0.91      inference('sup-', [status(thm)], ['70', '71'])).
% 0.67/0.91  thf('73', plain, (((sk_A) = (k1_xboole_0))),
% 0.67/0.91      inference('demod', [status(thm)], ['69', '72'])).
% 0.67/0.91  thf('74', plain, (((sk_A) = (k1_xboole_0))),
% 0.67/0.91      inference('demod', [status(thm)], ['69', '72'])).
% 0.67/0.91  thf('75', plain,
% 0.67/0.91      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.67/0.91      inference('demod', [status(thm)], ['8', '73', '74'])).
% 0.67/0.91  thf('76', plain,
% 0.67/0.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('77', plain,
% 0.67/0.91      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.67/0.91         (~ (v1_funct_1 @ X26)
% 0.67/0.91          | ~ (v3_funct_2 @ X26 @ X27 @ X28)
% 0.67/0.91          | (v2_funct_2 @ X26 @ X28)
% 0.67/0.91          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.67/0.91      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.67/0.91  thf('78', plain,
% 0.67/0.91      (((v2_funct_2 @ sk_C @ sk_A)
% 0.67/0.91        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.67/0.91        | ~ (v1_funct_1 @ sk_C))),
% 0.67/0.91      inference('sup-', [status(thm)], ['76', '77'])).
% 0.67/0.91  thf('79', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('80', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('81', plain, ((v2_funct_2 @ sk_C @ sk_A)),
% 0.67/0.91      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.67/0.91  thf('82', plain,
% 0.67/0.91      (![X29 : $i, X30 : $i]:
% 0.67/0.91         (~ (v2_funct_2 @ X30 @ X29)
% 0.67/0.91          | ((k2_relat_1 @ X30) = (X29))
% 0.67/0.91          | ~ (v5_relat_1 @ X30 @ X29)
% 0.67/0.91          | ~ (v1_relat_1 @ X30))),
% 0.67/0.91      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.67/0.91  thf('83', plain,
% 0.67/0.91      ((~ (v1_relat_1 @ sk_C)
% 0.67/0.91        | ~ (v5_relat_1 @ sk_C @ sk_A)
% 0.67/0.91        | ((k2_relat_1 @ sk_C) = (sk_A)))),
% 0.67/0.91      inference('sup-', [status(thm)], ['81', '82'])).
% 0.67/0.91  thf('84', plain,
% 0.67/0.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('85', plain,
% 0.67/0.91      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.67/0.91         ((v1_relat_1 @ X12)
% 0.67/0.91          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.67/0.91      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.67/0.91  thf('86', plain, ((v1_relat_1 @ sk_C)),
% 0.67/0.91      inference('sup-', [status(thm)], ['84', '85'])).
% 0.67/0.91  thf('87', plain,
% 0.67/0.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('88', plain,
% 0.67/0.91      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.67/0.91         ((v5_relat_1 @ X15 @ X17)
% 0.67/0.91          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.67/0.91      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.67/0.91  thf('89', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.67/0.91      inference('sup-', [status(thm)], ['87', '88'])).
% 0.67/0.91  thf('90', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.67/0.91      inference('demod', [status(thm)], ['83', '86', '89'])).
% 0.67/0.91  thf(t64_relat_1, axiom,
% 0.67/0.91    (![A:$i]:
% 0.67/0.91     ( ( v1_relat_1 @ A ) =>
% 0.67/0.91       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.67/0.91           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.67/0.91         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.67/0.91  thf('91', plain,
% 0.67/0.91      (![X3 : $i]:
% 0.67/0.91         (((k2_relat_1 @ X3) != (k1_xboole_0))
% 0.67/0.91          | ((X3) = (k1_xboole_0))
% 0.67/0.91          | ~ (v1_relat_1 @ X3))),
% 0.67/0.91      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.67/0.91  thf('92', plain,
% 0.67/0.91      ((((sk_A) != (k1_xboole_0))
% 0.67/0.91        | ~ (v1_relat_1 @ sk_C)
% 0.67/0.91        | ((sk_C) = (k1_xboole_0)))),
% 0.67/0.91      inference('sup-', [status(thm)], ['90', '91'])).
% 0.67/0.91  thf('93', plain, ((v1_relat_1 @ sk_C)),
% 0.67/0.91      inference('sup-', [status(thm)], ['84', '85'])).
% 0.67/0.91  thf('94', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.67/0.91      inference('demod', [status(thm)], ['92', '93'])).
% 0.67/0.91  thf('95', plain, (((sk_A) = (k1_xboole_0))),
% 0.67/0.91      inference('demod', [status(thm)], ['69', '72'])).
% 0.67/0.91  thf('96', plain,
% 0.67/0.91      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.67/0.91      inference('demod', [status(thm)], ['94', '95'])).
% 0.67/0.91  thf('97', plain, (((sk_C) = (k1_xboole_0))),
% 0.67/0.91      inference('simplify', [status(thm)], ['96'])).
% 0.67/0.91  thf('98', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.67/0.91      inference('demod', [status(thm)], ['51', '54', '57'])).
% 0.67/0.91  thf('99', plain,
% 0.67/0.91      (![X3 : $i]:
% 0.67/0.91         (((k2_relat_1 @ X3) != (k1_xboole_0))
% 0.67/0.91          | ((X3) = (k1_xboole_0))
% 0.67/0.91          | ~ (v1_relat_1 @ X3))),
% 0.67/0.91      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.67/0.91  thf('100', plain,
% 0.67/0.91      ((((sk_A) != (k1_xboole_0))
% 0.67/0.91        | ~ (v1_relat_1 @ sk_B)
% 0.67/0.91        | ((sk_B) = (k1_xboole_0)))),
% 0.67/0.91      inference('sup-', [status(thm)], ['98', '99'])).
% 0.67/0.91  thf('101', plain, ((v1_relat_1 @ sk_B)),
% 0.67/0.91      inference('sup-', [status(thm)], ['52', '53'])).
% 0.67/0.91  thf('102', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.67/0.91      inference('demod', [status(thm)], ['100', '101'])).
% 0.67/0.91  thf('103', plain, (((sk_A) = (k1_xboole_0))),
% 0.67/0.91      inference('demod', [status(thm)], ['69', '72'])).
% 0.67/0.91  thf('104', plain,
% 0.67/0.91      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.67/0.91      inference('demod', [status(thm)], ['102', '103'])).
% 0.67/0.91  thf('105', plain, (((sk_B) = (k1_xboole_0))),
% 0.67/0.91      inference('simplify', [status(thm)], ['104'])).
% 0.67/0.91  thf('106', plain,
% 0.67/0.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('107', plain,
% 0.67/0.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('108', plain,
% 0.67/0.91      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.67/0.91         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.67/0.91          | ~ (v1_funct_1 @ X31)
% 0.67/0.91          | ~ (v1_funct_1 @ X34)
% 0.67/0.91          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.67/0.91          | (v1_funct_1 @ (k1_partfun1 @ X32 @ X33 @ X35 @ X36 @ X31 @ X34)))),
% 0.67/0.91      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.67/0.91  thf('109', plain,
% 0.67/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.91         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0))
% 0.67/0.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.67/0.91          | ~ (v1_funct_1 @ X0)
% 0.67/0.91          | ~ (v1_funct_1 @ sk_B))),
% 0.67/0.91      inference('sup-', [status(thm)], ['107', '108'])).
% 0.67/0.91  thf('110', plain, ((v1_funct_1 @ sk_B)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('111', plain,
% 0.67/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.91         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0))
% 0.67/0.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.67/0.91          | ~ (v1_funct_1 @ X0))),
% 0.67/0.91      inference('demod', [status(thm)], ['109', '110'])).
% 0.67/0.91  thf('112', plain,
% 0.67/0.91      ((~ (v1_funct_1 @ sk_C)
% 0.67/0.91        | (v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)))),
% 0.67/0.91      inference('sup-', [status(thm)], ['106', '111'])).
% 0.67/0.91  thf('113', plain, ((v1_funct_1 @ sk_C)),
% 0.67/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.91  thf('114', plain,
% 0.67/0.91      ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C))),
% 0.67/0.91      inference('demod', [status(thm)], ['112', '113'])).
% 0.67/0.91  thf('115', plain,
% 0.67/0.91      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.67/0.91         = (k6_partfun1 @ sk_A))),
% 0.67/0.91      inference('demod', [status(thm)], ['21', '24'])).
% 0.67/0.91  thf('116', plain, ((v1_funct_1 @ (k6_partfun1 @ sk_A))),
% 0.67/0.91      inference('demod', [status(thm)], ['114', '115'])).
% 0.67/0.91  thf(t123_relat_1, axiom,
% 0.67/0.91    (![A:$i,B:$i]:
% 0.67/0.91     ( ( v1_relat_1 @ B ) =>
% 0.67/0.91       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.67/0.91  thf('117', plain,
% 0.67/0.91      (![X0 : $i, X1 : $i]:
% 0.67/0.91         (((k8_relat_1 @ X1 @ X0) = (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.67/0.91          | ~ (v1_relat_1 @ X0))),
% 0.67/0.91      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.67/0.91  thf('118', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 0.67/0.91      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.67/0.91  thf('119', plain,
% 0.67/0.91      (![X0 : $i, X1 : $i]:
% 0.67/0.91         (((k8_relat_1 @ X1 @ X0) = (k5_relat_1 @ X0 @ (k6_partfun1 @ X1)))
% 0.67/0.91          | ~ (v1_relat_1 @ X0))),
% 0.67/0.91      inference('demod', [status(thm)], ['117', '118'])).
% 0.67/0.91  thf(t71_relat_1, axiom,
% 0.67/0.91    (![A:$i]:
% 0.67/0.91     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.67/0.91       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.67/0.91  thf('120', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 0.67/0.91      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.67/0.91  thf('121', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 0.67/0.91      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.67/0.91  thf('122', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 0.67/0.91      inference('demod', [status(thm)], ['120', '121'])).
% 0.67/0.91  thf('123', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 0.67/0.91      inference('demod', [status(thm)], ['120', '121'])).
% 0.67/0.91  thf(t63_funct_1, axiom,
% 0.67/0.91    (![A:$i]:
% 0.67/0.91     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.67/0.91       ( ![B:$i]:
% 0.67/0.91         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.67/0.91           ( ( ( v2_funct_1 @ A ) & 
% 0.67/0.91               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.67/0.91               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.67/0.91             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.67/0.91  thf('124', plain,
% 0.67/0.91      (![X10 : $i, X11 : $i]:
% 0.67/0.91         (~ (v1_relat_1 @ X10)
% 0.67/0.91          | ~ (v1_funct_1 @ X10)
% 0.67/0.91          | ((X10) = (k2_funct_1 @ X11))
% 0.67/0.91          | ((k5_relat_1 @ X11 @ X10) != (k6_relat_1 @ (k1_relat_1 @ X11)))
% 0.67/0.91          | ((k2_relat_1 @ X11) != (k1_relat_1 @ X10))
% 0.67/0.91          | ~ (v2_funct_1 @ X11)
% 0.67/0.91          | ~ (v1_funct_1 @ X11)
% 0.67/0.91          | ~ (v1_relat_1 @ X11))),
% 0.67/0.91      inference('cnf', [status(esa)], [t63_funct_1])).
% 0.67/0.91  thf('125', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 0.67/0.91      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.67/0.91  thf('126', plain,
% 0.67/0.91      (![X10 : $i, X11 : $i]:
% 0.67/0.91         (~ (v1_relat_1 @ X10)
% 0.67/0.91          | ~ (v1_funct_1 @ X10)
% 0.67/0.91          | ((X10) = (k2_funct_1 @ X11))
% 0.67/0.91          | ((k5_relat_1 @ X11 @ X10) != (k6_partfun1 @ (k1_relat_1 @ X11)))
% 0.67/0.91          | ((k2_relat_1 @ X11) != (k1_relat_1 @ X10))
% 0.67/0.91          | ~ (v2_funct_1 @ X11)
% 0.67/0.91          | ~ (v1_funct_1 @ X11)
% 0.67/0.91          | ~ (v1_relat_1 @ X11))),
% 0.67/0.91      inference('demod', [status(thm)], ['124', '125'])).
% 0.67/0.91  thf('127', plain,
% 0.67/0.91      (![X0 : $i, X1 : $i]:
% 0.67/0.91         (((k5_relat_1 @ (k6_partfun1 @ X0) @ X1) != (k6_partfun1 @ X0))
% 0.67/0.91          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 0.67/0.91          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 0.67/0.91          | ~ (v2_funct_1 @ (k6_partfun1 @ X0))
% 0.67/0.91          | ((k2_relat_1 @ (k6_partfun1 @ X0)) != (k1_relat_1 @ X1))
% 0.67/0.91          | ((X1) = (k2_funct_1 @ (k6_partfun1 @ X0)))
% 0.67/0.91          | ~ (v1_funct_1 @ X1)
% 0.67/0.91          | ~ (v1_relat_1 @ X1))),
% 0.67/0.91      inference('sup-', [status(thm)], ['123', '126'])).
% 0.67/0.91  thf(fc4_funct_1, axiom,
% 0.67/0.91    (![A:$i]:
% 0.67/0.91     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.67/0.91       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.67/0.91  thf('128', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.67/0.91      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.67/0.91  thf('129', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 0.67/0.91      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.67/0.91  thf('130', plain, (![X6 : $i]: (v1_relat_1 @ (k6_partfun1 @ X6))),
% 0.67/0.91      inference('demod', [status(thm)], ['128', '129'])).
% 0.67/0.91  thf('131', plain, (![X7 : $i]: (v2_funct_1 @ (k6_relat_1 @ X7))),
% 0.67/0.91      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.67/0.91  thf('132', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 0.67/0.91      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.67/0.91  thf('133', plain, (![X7 : $i]: (v2_funct_1 @ (k6_partfun1 @ X7))),
% 0.67/0.91      inference('demod', [status(thm)], ['131', '132'])).
% 0.67/0.91  thf('134', plain, (![X5 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 0.67/0.91      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.67/0.91  thf('135', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 0.67/0.91      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.67/0.91  thf('136', plain, (![X5 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X5)) = (X5))),
% 0.67/0.91      inference('demod', [status(thm)], ['134', '135'])).
% 0.67/0.91  thf('137', plain,
% 0.67/0.91      (![X0 : $i, X1 : $i]:
% 0.67/0.91         (((k5_relat_1 @ (k6_partfun1 @ X0) @ X1) != (k6_partfun1 @ X0))
% 0.67/0.91          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 0.67/0.91          | ((X0) != (k1_relat_1 @ X1))
% 0.67/0.91          | ((X1) = (k2_funct_1 @ (k6_partfun1 @ X0)))
% 0.67/0.91          | ~ (v1_funct_1 @ X1)
% 0.67/0.91          | ~ (v1_relat_1 @ X1))),
% 0.67/0.91      inference('demod', [status(thm)], ['127', '130', '133', '136'])).
% 0.67/0.91  thf('138', plain,
% 0.67/0.91      (![X1 : $i]:
% 0.67/0.91         (~ (v1_relat_1 @ X1)
% 0.67/0.91          | ~ (v1_funct_1 @ X1)
% 0.67/0.91          | ((X1) = (k2_funct_1 @ (k6_partfun1 @ (k1_relat_1 @ X1))))
% 0.67/0.91          | ~ (v1_funct_1 @ (k6_partfun1 @ (k1_relat_1 @ X1)))
% 0.67/0.91          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X1)) @ X1)
% 0.67/0.91              != (k6_partfun1 @ (k1_relat_1 @ X1))))),
% 0.67/0.91      inference('simplify', [status(thm)], ['137'])).
% 0.67/0.91  thf('139', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 0.67/0.91          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ (k6_partfun1 @ X0))) @ 
% 0.67/0.91              (k6_partfun1 @ X0))
% 0.67/0.91              != (k6_partfun1 @ (k1_relat_1 @ (k6_partfun1 @ X0))))
% 0.67/0.91          | ((k6_partfun1 @ X0)
% 0.67/0.91              = (k2_funct_1 @ (k6_partfun1 @ (k1_relat_1 @ (k6_partfun1 @ X0)))))
% 0.67/0.91          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 0.67/0.91          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.67/0.91      inference('sup-', [status(thm)], ['122', '138'])).
% 0.67/0.91  thf('140', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 0.67/0.91      inference('demod', [status(thm)], ['120', '121'])).
% 0.67/0.91  thf('141', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 0.67/0.91      inference('demod', [status(thm)], ['120', '121'])).
% 0.67/0.91  thf('142', plain, (![X4 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 0.67/0.91      inference('demod', [status(thm)], ['120', '121'])).
% 0.67/0.91  thf('143', plain, (![X6 : $i]: (v1_relat_1 @ (k6_partfun1 @ X6))),
% 0.67/0.91      inference('demod', [status(thm)], ['128', '129'])).
% 0.67/0.91  thf('144', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 0.67/0.91          | ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 0.67/0.91              != (k6_partfun1 @ X0))
% 0.67/0.91          | ((k6_partfun1 @ X0) = (k2_funct_1 @ (k6_partfun1 @ X0)))
% 0.67/0.91          | ~ (v1_funct_1 @ (k6_partfun1 @ X0)))),
% 0.67/0.91      inference('demod', [status(thm)], ['139', '140', '141', '142', '143'])).
% 0.67/0.91  thf('145', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (((k6_partfun1 @ X0) = (k2_funct_1 @ (k6_partfun1 @ X0)))
% 0.67/0.91          | ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 0.67/0.91              != (k6_partfun1 @ X0))
% 0.67/0.91          | ~ (v1_funct_1 @ (k6_partfun1 @ X0)))),
% 0.67/0.91      inference('simplify', [status(thm)], ['144'])).
% 0.67/0.91  thf('146', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (((k8_relat_1 @ X0 @ (k6_partfun1 @ X0)) != (k6_partfun1 @ X0))
% 0.67/0.91          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 0.67/0.91          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 0.67/0.91          | ((k6_partfun1 @ X0) = (k2_funct_1 @ (k6_partfun1 @ X0))))),
% 0.67/0.91      inference('sup-', [status(thm)], ['119', '145'])).
% 0.67/0.91  thf('147', plain, (![X5 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X5)) = (X5))),
% 0.67/0.91      inference('demod', [status(thm)], ['134', '135'])).
% 0.67/0.91  thf(t126_relat_1, axiom,
% 0.67/0.91    (![A:$i]:
% 0.67/0.91     ( ( v1_relat_1 @ A ) =>
% 0.67/0.91       ( ( k8_relat_1 @ ( k2_relat_1 @ A ) @ A ) = ( A ) ) ))).
% 0.67/0.91  thf('148', plain,
% 0.67/0.91      (![X2 : $i]:
% 0.67/0.91         (((k8_relat_1 @ (k2_relat_1 @ X2) @ X2) = (X2)) | ~ (v1_relat_1 @ X2))),
% 0.67/0.91      inference('cnf', [status(esa)], [t126_relat_1])).
% 0.67/0.91  thf('149', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (((k8_relat_1 @ X0 @ (k6_partfun1 @ X0)) = (k6_partfun1 @ X0))
% 0.67/0.91          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.67/0.91      inference('sup+', [status(thm)], ['147', '148'])).
% 0.67/0.91  thf('150', plain, (![X6 : $i]: (v1_relat_1 @ (k6_partfun1 @ X6))),
% 0.67/0.91      inference('demod', [status(thm)], ['128', '129'])).
% 0.67/0.91  thf('151', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         ((k8_relat_1 @ X0 @ (k6_partfun1 @ X0)) = (k6_partfun1 @ X0))),
% 0.67/0.91      inference('demod', [status(thm)], ['149', '150'])).
% 0.67/0.91  thf('152', plain, (![X6 : $i]: (v1_relat_1 @ (k6_partfun1 @ X6))),
% 0.67/0.91      inference('demod', [status(thm)], ['128', '129'])).
% 0.67/0.91  thf('153', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (((k6_partfun1 @ X0) != (k6_partfun1 @ X0))
% 0.67/0.91          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 0.67/0.91          | ((k6_partfun1 @ X0) = (k2_funct_1 @ (k6_partfun1 @ X0))))),
% 0.67/0.91      inference('demod', [status(thm)], ['146', '151', '152'])).
% 0.67/0.91  thf('154', plain,
% 0.67/0.91      (![X0 : $i]:
% 0.67/0.91         (((k6_partfun1 @ X0) = (k2_funct_1 @ (k6_partfun1 @ X0)))
% 0.67/0.91          | ~ (v1_funct_1 @ (k6_partfun1 @ X0)))),
% 0.67/0.91      inference('simplify', [status(thm)], ['153'])).
% 0.67/0.91  thf('155', plain,
% 0.67/0.91      (((k6_partfun1 @ sk_A) = (k2_funct_1 @ (k6_partfun1 @ sk_A)))),
% 0.67/0.91      inference('sup-', [status(thm)], ['116', '154'])).
% 0.67/0.91  thf('156', plain, (((sk_A) = (k1_xboole_0))),
% 0.67/0.91      inference('demod', [status(thm)], ['69', '72'])).
% 0.67/0.91  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.67/0.91  thf('157', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.67/0.91      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.67/0.91  thf('158', plain, (![X39 : $i]: ((k6_partfun1 @ X39) = (k6_relat_1 @ X39))),
% 0.67/0.91      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.67/0.91  thf('159', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.67/0.91      inference('demod', [status(thm)], ['157', '158'])).
% 0.67/0.91  thf('160', plain, (((sk_A) = (k1_xboole_0))),
% 0.67/0.91      inference('demod', [status(thm)], ['69', '72'])).
% 0.67/0.91  thf('161', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.67/0.91      inference('demod', [status(thm)], ['157', '158'])).
% 0.67/0.91  thf('162', plain, (((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))),
% 0.67/0.91      inference('demod', [status(thm)], ['155', '156', '159', '160', '161'])).
% 0.67/0.91  thf('163', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.67/0.91      inference('demod', [status(thm)], ['157', '158'])).
% 0.67/0.91  thf('164', plain,
% 0.67/0.91      (![X25 : $i]:
% 0.67/0.91         (m1_subset_1 @ (k6_partfun1 @ X25) @ 
% 0.67/0.91          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))),
% 0.67/0.91      inference('demod', [status(thm)], ['22', '23'])).
% 0.67/0.91  thf('165', plain,
% 0.67/0.91      ((m1_subset_1 @ k1_xboole_0 @ 
% 0.67/0.91        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.67/0.91      inference('sup+', [status(thm)], ['163', '164'])).
% 0.67/0.91  thf('166', plain,
% 0.67/0.91      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.67/0.91         ((r2_relset_1 @ X22 @ X23 @ X24 @ X24)
% 0.67/0.91          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.67/0.91      inference('simplify', [status(thm)], ['35'])).
% 0.67/0.91  thf('167', plain,
% 0.67/0.91      ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.67/0.91      inference('sup-', [status(thm)], ['165', '166'])).
% 0.67/0.91  thf('168', plain, ($false),
% 0.67/0.91      inference('demod', [status(thm)], ['75', '97', '105', '162', '167'])).
% 0.67/0.91  
% 0.67/0.91  % SZS output end Refutation
% 0.67/0.91  
% 0.67/0.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

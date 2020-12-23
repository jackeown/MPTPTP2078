%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kG6t31KshT

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:56 EST 2020

% Result     : Theorem 0.99s
% Output     : Refutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 655 expanded)
%              Number of leaves         :   48 ( 212 expanded)
%              Depth                    :   20
%              Number of atoms          : 1524 (15631 expanded)
%              Number of equality atoms :  101 (1032 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
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

thf('2',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ( ( k1_partfun1 @ X41 @ X42 @ X44 @ X45 @ X40 @ X43 )
        = ( k5_relat_1 @ X40 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('18',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( X28 = X31 )
      | ~ ( r2_relset_1 @ X29 @ X30 @ X28 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','19'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('21',plain,(
    ! [X39: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('22',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['6','7','22'])).

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

thf('24',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( X16
        = ( k2_funct_1 @ X17 ) )
      | ( ( k5_relat_1 @ X16 @ X17 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X17 ) ) )
      | ( ( k2_relat_1 @ X16 )
       != ( k1_relat_1 @ X17 ) )
      | ~ ( v2_funct_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('25',plain,(
    ! [X46: $i] :
      ( ( k6_partfun1 @ X46 )
      = ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('26',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( X16
        = ( k2_funct_1 @ X17 ) )
      | ( ( k5_relat_1 @ X16 @ X17 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X17 ) ) )
      | ( ( k2_relat_1 @ X16 )
       != ( k1_relat_1 @ X17 ) )
      | ~ ( v2_funct_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
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
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('29',plain,(
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

thf('30',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ~ ( r2_relset_1 @ X48 @ X48 @ ( k1_partfun1 @ X48 @ X49 @ X49 @ X48 @ X47 @ X50 ) @ ( k6_partfun1 @ X48 ) )
      | ( ( k2_relset_1 @ X49 @ X48 @ X50 )
        = X48 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) )
      | ~ ( v1_funct_2 @ X50 @ X49 @ X48 )
      | ~ ( v1_funct_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,(
    ! [X39: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('37',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( r2_relset_1 @ X29 @ X30 @ X28 @ X31 )
      | ( X28 != X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('38',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( r2_relset_1 @ X29 @ X30 @ X31 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('41',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X27 @ X25 )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
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
    inference(demod,[status(thm)],['35','39','42','43','44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('48',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X27 @ X25 )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
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
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('59',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['27','46','49','50','55','56','59'])).

thf('61',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['6','7','22'])).

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

thf('63',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( v2_funct_1 @ X15 )
      | ( ( k2_relat_1 @ X14 )
       != ( k1_relat_1 @ X15 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X14 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('64',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('65',plain,(
    ! [X11: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('66',plain,(
    ! [X46: $i] :
      ( ( k6_partfun1 @ X46 )
      = ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('67',plain,(
    ! [X11: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X11 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['47','48'])).

thf('69',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['53','54'])).

thf('71',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['57','58'])).

thf('73',plain,
    ( ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['64','67','68','69','70','71','72'])).

thf('74',plain,
    ( ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(clc,[status(thm)],['61','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('76',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('77',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['75','76'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('79',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['47','48'])).

thf('81',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['53','54'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('83',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X12 @ ( k2_relat_1 @ X13 ) )
      | ( ( k9_relat_1 @ X13 @ ( k10_relat_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['57','58'])).

thf('86',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['81','87'])).

thf('89',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['6','7','22'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('90',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) )
        = ( k10_relat_1 @ X5 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('91',plain,
    ( ( ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) )
      = ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('92',plain,(
    ! [X8: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('93',plain,(
    ! [X46: $i] :
      ( ( k6_partfun1 @ X46 )
      = ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('94',plain,(
    ! [X8: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X8 ) )
      = X8 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['57','58'])).

thf('96',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['47','48'])).

thf('97',plain,
    ( sk_A
    = ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['91','94','95','96'])).

thf('98',plain,
    ( ( k9_relat_1 @ sk_C @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['88','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('101',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['99','100'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('102',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X6
        = ( k7_relat_1 @ X6 @ X7 ) )
      | ~ ( v4_relat_1 @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('103',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['57','58'])).

thf('105',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['103','104'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('106',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X2 @ X3 ) )
        = ( k9_relat_1 @ X2 @ X3 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('107',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['57','58'])).

thf('109',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['53','54'])).

thf('111',plain,
    ( sk_B
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['98','111'])).

thf('113',plain,
    ( ( sk_B != sk_B )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['74','112'])).

thf('114',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['113'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('115',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X18 ) )
        = X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('116',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['47','48'])).

thf('118',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ~ ( v2_funct_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['64','67','68','69','70','71','72'])).

thf('123',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['98','111'])).

thf('124',plain,
    ( ( sk_B != sk_B )
    | ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    $false ),
    inference(demod,[status(thm)],['121','125'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kG6t31KshT
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:30:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.99/1.22  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.99/1.22  % Solved by: fo/fo7.sh
% 0.99/1.22  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.99/1.22  % done 969 iterations in 0.760s
% 0.99/1.22  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.99/1.22  % SZS output start Refutation
% 0.99/1.22  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.99/1.22  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.99/1.22  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.99/1.22  thf(sk_D_type, type, sk_D: $i).
% 0.99/1.22  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.99/1.22  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.99/1.22  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.99/1.22  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.99/1.22  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.99/1.22  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.99/1.22  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.99/1.22  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.99/1.22  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.99/1.22  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.99/1.22  thf(sk_B_type, type, sk_B: $i).
% 0.99/1.22  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.99/1.22  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.99/1.22  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.99/1.22  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.99/1.22  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.99/1.22  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.99/1.22  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.99/1.22  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.99/1.22  thf(sk_C_type, type, sk_C: $i).
% 0.99/1.22  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.99/1.22  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.99/1.22  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.99/1.22  thf(sk_A_type, type, sk_A: $i).
% 0.99/1.22  thf(t36_funct_2, conjecture,
% 0.99/1.22    (![A:$i,B:$i,C:$i]:
% 0.99/1.22     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.99/1.22         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.99/1.22       ( ![D:$i]:
% 0.99/1.22         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.99/1.22             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.99/1.22           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.99/1.22               ( r2_relset_1 @
% 0.99/1.22                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.99/1.22                 ( k6_partfun1 @ A ) ) & 
% 0.99/1.22               ( v2_funct_1 @ C ) ) =>
% 0.99/1.22             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.99/1.22               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.99/1.22  thf(zf_stmt_0, negated_conjecture,
% 0.99/1.22    (~( ![A:$i,B:$i,C:$i]:
% 0.99/1.22        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.99/1.22            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.99/1.22          ( ![D:$i]:
% 0.99/1.22            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.99/1.22                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.99/1.22              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.99/1.22                  ( r2_relset_1 @
% 0.99/1.22                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.99/1.22                    ( k6_partfun1 @ A ) ) & 
% 0.99/1.22                  ( v2_funct_1 @ C ) ) =>
% 0.99/1.22                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.99/1.22                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.99/1.22    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.99/1.22  thf('0', plain,
% 0.99/1.22      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.99/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.22  thf('1', plain,
% 0.99/1.22      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.99/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.22  thf(redefinition_k1_partfun1, axiom,
% 0.99/1.22    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.99/1.22     ( ( ( v1_funct_1 @ E ) & 
% 0.99/1.22         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.99/1.22         ( v1_funct_1 @ F ) & 
% 0.99/1.22         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.99/1.22       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.99/1.22  thf('2', plain,
% 0.99/1.22      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.99/1.22         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.99/1.22          | ~ (v1_funct_1 @ X40)
% 0.99/1.22          | ~ (v1_funct_1 @ X43)
% 0.99/1.22          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 0.99/1.22          | ((k1_partfun1 @ X41 @ X42 @ X44 @ X45 @ X40 @ X43)
% 0.99/1.22              = (k5_relat_1 @ X40 @ X43)))),
% 0.99/1.22      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.99/1.22  thf('3', plain,
% 0.99/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.22         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.99/1.22            = (k5_relat_1 @ sk_C @ X0))
% 0.99/1.22          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.99/1.22          | ~ (v1_funct_1 @ X0)
% 0.99/1.22          | ~ (v1_funct_1 @ sk_C))),
% 0.99/1.22      inference('sup-', [status(thm)], ['1', '2'])).
% 0.99/1.22  thf('4', plain, ((v1_funct_1 @ sk_C)),
% 0.99/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.22  thf('5', plain,
% 0.99/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.22         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.99/1.22            = (k5_relat_1 @ sk_C @ X0))
% 0.99/1.22          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.99/1.22          | ~ (v1_funct_1 @ X0))),
% 0.99/1.22      inference('demod', [status(thm)], ['3', '4'])).
% 0.99/1.22  thf('6', plain,
% 0.99/1.22      ((~ (v1_funct_1 @ sk_D)
% 0.99/1.22        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.99/1.22            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.99/1.22      inference('sup-', [status(thm)], ['0', '5'])).
% 0.99/1.22  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 0.99/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.22  thf('8', plain,
% 0.99/1.22      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.99/1.22        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.99/1.22        (k6_partfun1 @ sk_A))),
% 0.99/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.22  thf('9', plain,
% 0.99/1.22      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.99/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.22  thf('10', plain,
% 0.99/1.22      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.99/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.22  thf(dt_k1_partfun1, axiom,
% 0.99/1.22    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.99/1.22     ( ( ( v1_funct_1 @ E ) & 
% 0.99/1.22         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.99/1.22         ( v1_funct_1 @ F ) & 
% 0.99/1.22         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.99/1.22       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.99/1.22         ( m1_subset_1 @
% 0.99/1.22           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.99/1.22           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.99/1.22  thf('11', plain,
% 0.99/1.22      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.99/1.22         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.99/1.22          | ~ (v1_funct_1 @ X32)
% 0.99/1.22          | ~ (v1_funct_1 @ X35)
% 0.99/1.22          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.99/1.22          | (m1_subset_1 @ (k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35) @ 
% 0.99/1.22             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X37))))),
% 0.99/1.22      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.99/1.22  thf('12', plain,
% 0.99/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.22         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.99/1.22           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.99/1.22          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.99/1.22          | ~ (v1_funct_1 @ X1)
% 0.99/1.22          | ~ (v1_funct_1 @ sk_C))),
% 0.99/1.22      inference('sup-', [status(thm)], ['10', '11'])).
% 0.99/1.22  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 0.99/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.22  thf('14', plain,
% 0.99/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.22         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.99/1.22           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.99/1.22          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.99/1.22          | ~ (v1_funct_1 @ X1))),
% 0.99/1.22      inference('demod', [status(thm)], ['12', '13'])).
% 0.99/1.22  thf('15', plain,
% 0.99/1.22      ((~ (v1_funct_1 @ sk_D)
% 0.99/1.22        | (m1_subset_1 @ 
% 0.99/1.22           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.99/1.22           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.99/1.22      inference('sup-', [status(thm)], ['9', '14'])).
% 0.99/1.22  thf('16', plain, ((v1_funct_1 @ sk_D)),
% 0.99/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.22  thf('17', plain,
% 0.99/1.22      ((m1_subset_1 @ 
% 0.99/1.22        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.99/1.22        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.99/1.22      inference('demod', [status(thm)], ['15', '16'])).
% 0.99/1.22  thf(redefinition_r2_relset_1, axiom,
% 0.99/1.22    (![A:$i,B:$i,C:$i,D:$i]:
% 0.99/1.22     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.99/1.22         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.99/1.22       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.99/1.22  thf('18', plain,
% 0.99/1.22      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.99/1.22         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.99/1.22          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.99/1.22          | ((X28) = (X31))
% 0.99/1.22          | ~ (r2_relset_1 @ X29 @ X30 @ X28 @ X31))),
% 0.99/1.22      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.99/1.22  thf('19', plain,
% 0.99/1.22      (![X0 : $i]:
% 0.99/1.22         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.99/1.22             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.99/1.22          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.99/1.22          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.99/1.22      inference('sup-', [status(thm)], ['17', '18'])).
% 0.99/1.22  thf('20', plain,
% 0.99/1.22      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.99/1.22           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.99/1.22        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.99/1.22            = (k6_partfun1 @ sk_A)))),
% 0.99/1.22      inference('sup-', [status(thm)], ['8', '19'])).
% 0.99/1.22  thf(dt_k6_partfun1, axiom,
% 0.99/1.22    (![A:$i]:
% 0.99/1.22     ( ( m1_subset_1 @
% 0.99/1.22         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.99/1.22       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.99/1.22  thf('21', plain,
% 0.99/1.22      (![X39 : $i]:
% 0.99/1.22         (m1_subset_1 @ (k6_partfun1 @ X39) @ 
% 0.99/1.22          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))),
% 0.99/1.22      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.99/1.22  thf('22', plain,
% 0.99/1.22      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.99/1.22         = (k6_partfun1 @ sk_A))),
% 0.99/1.22      inference('demod', [status(thm)], ['20', '21'])).
% 0.99/1.22  thf('23', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.99/1.22      inference('demod', [status(thm)], ['6', '7', '22'])).
% 0.99/1.22  thf(t64_funct_1, axiom,
% 0.99/1.22    (![A:$i]:
% 0.99/1.22     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.99/1.22       ( ![B:$i]:
% 0.99/1.22         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.99/1.22           ( ( ( v2_funct_1 @ A ) & 
% 0.99/1.22               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.99/1.22               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.99/1.22             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.99/1.22  thf('24', plain,
% 0.99/1.22      (![X16 : $i, X17 : $i]:
% 0.99/1.22         (~ (v1_relat_1 @ X16)
% 0.99/1.22          | ~ (v1_funct_1 @ X16)
% 0.99/1.22          | ((X16) = (k2_funct_1 @ X17))
% 0.99/1.22          | ((k5_relat_1 @ X16 @ X17) != (k6_relat_1 @ (k2_relat_1 @ X17)))
% 0.99/1.22          | ((k2_relat_1 @ X16) != (k1_relat_1 @ X17))
% 0.99/1.22          | ~ (v2_funct_1 @ X17)
% 0.99/1.22          | ~ (v1_funct_1 @ X17)
% 0.99/1.22          | ~ (v1_relat_1 @ X17))),
% 0.99/1.22      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.99/1.22  thf(redefinition_k6_partfun1, axiom,
% 0.99/1.22    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.99/1.22  thf('25', plain, (![X46 : $i]: ((k6_partfun1 @ X46) = (k6_relat_1 @ X46))),
% 0.99/1.22      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.99/1.22  thf('26', plain,
% 0.99/1.22      (![X16 : $i, X17 : $i]:
% 0.99/1.22         (~ (v1_relat_1 @ X16)
% 0.99/1.22          | ~ (v1_funct_1 @ X16)
% 0.99/1.22          | ((X16) = (k2_funct_1 @ X17))
% 0.99/1.22          | ((k5_relat_1 @ X16 @ X17) != (k6_partfun1 @ (k2_relat_1 @ X17)))
% 0.99/1.22          | ((k2_relat_1 @ X16) != (k1_relat_1 @ X17))
% 0.99/1.22          | ~ (v2_funct_1 @ X17)
% 0.99/1.22          | ~ (v1_funct_1 @ X17)
% 0.99/1.22          | ~ (v1_relat_1 @ X17))),
% 0.99/1.22      inference('demod', [status(thm)], ['24', '25'])).
% 0.99/1.22  thf('27', plain,
% 0.99/1.22      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 0.99/1.22        | ~ (v1_relat_1 @ sk_D)
% 0.99/1.22        | ~ (v1_funct_1 @ sk_D)
% 0.99/1.22        | ~ (v2_funct_1 @ sk_D)
% 0.99/1.22        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.99/1.22        | ((sk_C) = (k2_funct_1 @ sk_D))
% 0.99/1.22        | ~ (v1_funct_1 @ sk_C)
% 0.99/1.22        | ~ (v1_relat_1 @ sk_C))),
% 0.99/1.22      inference('sup-', [status(thm)], ['23', '26'])).
% 0.99/1.22  thf('28', plain,
% 0.99/1.22      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.99/1.22         = (k6_partfun1 @ sk_A))),
% 0.99/1.22      inference('demod', [status(thm)], ['20', '21'])).
% 0.99/1.22  thf('29', plain,
% 0.99/1.22      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.99/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.22  thf(t24_funct_2, axiom,
% 0.99/1.22    (![A:$i,B:$i,C:$i]:
% 0.99/1.22     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.99/1.22         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.99/1.22       ( ![D:$i]:
% 0.99/1.22         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.99/1.22             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.99/1.22           ( ( r2_relset_1 @
% 0.99/1.22               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.99/1.22               ( k6_partfun1 @ B ) ) =>
% 0.99/1.22             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.99/1.22  thf('30', plain,
% 0.99/1.22      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.99/1.22         (~ (v1_funct_1 @ X47)
% 0.99/1.22          | ~ (v1_funct_2 @ X47 @ X48 @ X49)
% 0.99/1.22          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 0.99/1.22          | ~ (r2_relset_1 @ X48 @ X48 @ 
% 0.99/1.22               (k1_partfun1 @ X48 @ X49 @ X49 @ X48 @ X47 @ X50) @ 
% 0.99/1.22               (k6_partfun1 @ X48))
% 0.99/1.22          | ((k2_relset_1 @ X49 @ X48 @ X50) = (X48))
% 0.99/1.22          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48)))
% 0.99/1.22          | ~ (v1_funct_2 @ X50 @ X49 @ X48)
% 0.99/1.22          | ~ (v1_funct_1 @ X50))),
% 0.99/1.22      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.99/1.22  thf('31', plain,
% 0.99/1.22      (![X0 : $i]:
% 0.99/1.22         (~ (v1_funct_1 @ X0)
% 0.99/1.22          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.99/1.22          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.99/1.22          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.99/1.22          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.99/1.22               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.99/1.22               (k6_partfun1 @ sk_A))
% 0.99/1.22          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.99/1.22          | ~ (v1_funct_1 @ sk_C))),
% 0.99/1.22      inference('sup-', [status(thm)], ['29', '30'])).
% 0.99/1.22  thf('32', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.99/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.22  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 0.99/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.22  thf('34', plain,
% 0.99/1.22      (![X0 : $i]:
% 0.99/1.22         (~ (v1_funct_1 @ X0)
% 0.99/1.22          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.99/1.22          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.99/1.22          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.99/1.22          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.99/1.22               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.99/1.22               (k6_partfun1 @ sk_A)))),
% 0.99/1.22      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.99/1.22  thf('35', plain,
% 0.99/1.22      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 0.99/1.22           (k6_partfun1 @ sk_A))
% 0.99/1.22        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.99/1.22        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.99/1.22        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.99/1.22        | ~ (v1_funct_1 @ sk_D))),
% 0.99/1.22      inference('sup-', [status(thm)], ['28', '34'])).
% 0.99/1.22  thf('36', plain,
% 0.99/1.22      (![X39 : $i]:
% 0.99/1.22         (m1_subset_1 @ (k6_partfun1 @ X39) @ 
% 0.99/1.22          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))),
% 0.99/1.22      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.99/1.22  thf('37', plain,
% 0.99/1.22      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.99/1.22         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.99/1.22          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.99/1.22          | (r2_relset_1 @ X29 @ X30 @ X28 @ X31)
% 0.99/1.22          | ((X28) != (X31)))),
% 0.99/1.22      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.99/1.22  thf('38', plain,
% 0.99/1.22      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.99/1.22         ((r2_relset_1 @ X29 @ X30 @ X31 @ X31)
% 0.99/1.22          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.99/1.22      inference('simplify', [status(thm)], ['37'])).
% 0.99/1.22  thf('39', plain,
% 0.99/1.22      (![X0 : $i]:
% 0.99/1.22         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 0.99/1.22      inference('sup-', [status(thm)], ['36', '38'])).
% 0.99/1.22  thf('40', plain,
% 0.99/1.22      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.99/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.22  thf(redefinition_k2_relset_1, axiom,
% 0.99/1.22    (![A:$i,B:$i,C:$i]:
% 0.99/1.22     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.99/1.22       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.99/1.22  thf('41', plain,
% 0.99/1.22      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.99/1.22         (((k2_relset_1 @ X26 @ X27 @ X25) = (k2_relat_1 @ X25))
% 0.99/1.22          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.99/1.22      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.99/1.22  thf('42', plain,
% 0.99/1.22      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.99/1.22      inference('sup-', [status(thm)], ['40', '41'])).
% 0.99/1.22  thf('43', plain,
% 0.99/1.22      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.99/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.22  thf('44', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.99/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.22  thf('45', plain, ((v1_funct_1 @ sk_D)),
% 0.99/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.22  thf('46', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.99/1.22      inference('demod', [status(thm)], ['35', '39', '42', '43', '44', '45'])).
% 0.99/1.22  thf('47', plain,
% 0.99/1.22      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.99/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.22  thf(cc1_relset_1, axiom,
% 0.99/1.22    (![A:$i,B:$i,C:$i]:
% 0.99/1.22     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.99/1.22       ( v1_relat_1 @ C ) ))).
% 0.99/1.22  thf('48', plain,
% 0.99/1.22      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.99/1.22         ((v1_relat_1 @ X19)
% 0.99/1.22          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.99/1.22      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.99/1.22  thf('49', plain, ((v1_relat_1 @ sk_D)),
% 0.99/1.22      inference('sup-', [status(thm)], ['47', '48'])).
% 0.99/1.22  thf('50', plain, ((v1_funct_1 @ sk_D)),
% 0.99/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.22  thf('51', plain,
% 0.99/1.22      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.99/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.22  thf('52', plain,
% 0.99/1.22      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.99/1.22         (((k2_relset_1 @ X26 @ X27 @ X25) = (k2_relat_1 @ X25))
% 0.99/1.22          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.99/1.22      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.99/1.22  thf('53', plain,
% 0.99/1.22      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.99/1.22      inference('sup-', [status(thm)], ['51', '52'])).
% 0.99/1.22  thf('54', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.99/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.22  thf('55', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.99/1.22      inference('sup+', [status(thm)], ['53', '54'])).
% 0.99/1.22  thf('56', plain, ((v1_funct_1 @ sk_C)),
% 0.99/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.22  thf('57', plain,
% 0.99/1.22      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.99/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.22  thf('58', plain,
% 0.99/1.22      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.99/1.22         ((v1_relat_1 @ X19)
% 0.99/1.22          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.99/1.22      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.99/1.22  thf('59', plain, ((v1_relat_1 @ sk_C)),
% 0.99/1.22      inference('sup-', [status(thm)], ['57', '58'])).
% 0.99/1.22  thf('60', plain,
% 0.99/1.22      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 0.99/1.22        | ~ (v2_funct_1 @ sk_D)
% 0.99/1.22        | ((sk_B) != (k1_relat_1 @ sk_D))
% 0.99/1.22        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 0.99/1.22      inference('demod', [status(thm)],
% 0.99/1.22                ['27', '46', '49', '50', '55', '56', '59'])).
% 0.99/1.22  thf('61', plain,
% 0.99/1.22      ((((sk_C) = (k2_funct_1 @ sk_D))
% 0.99/1.22        | ((sk_B) != (k1_relat_1 @ sk_D))
% 0.99/1.22        | ~ (v2_funct_1 @ sk_D))),
% 0.99/1.22      inference('simplify', [status(thm)], ['60'])).
% 0.99/1.22  thf('62', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.99/1.22      inference('demod', [status(thm)], ['6', '7', '22'])).
% 0.99/1.22  thf(t48_funct_1, axiom,
% 0.99/1.22    (![A:$i]:
% 0.99/1.22     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.99/1.22       ( ![B:$i]:
% 0.99/1.22         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.99/1.22           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.99/1.22               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.99/1.22             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.99/1.22  thf('63', plain,
% 0.99/1.22      (![X14 : $i, X15 : $i]:
% 0.99/1.22         (~ (v1_relat_1 @ X14)
% 0.99/1.22          | ~ (v1_funct_1 @ X14)
% 0.99/1.22          | (v2_funct_1 @ X15)
% 0.99/1.22          | ((k2_relat_1 @ X14) != (k1_relat_1 @ X15))
% 0.99/1.22          | ~ (v2_funct_1 @ (k5_relat_1 @ X14 @ X15))
% 0.99/1.22          | ~ (v1_funct_1 @ X15)
% 0.99/1.22          | ~ (v1_relat_1 @ X15))),
% 0.99/1.22      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.99/1.22  thf('64', plain,
% 0.99/1.22      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.99/1.22        | ~ (v1_relat_1 @ sk_D)
% 0.99/1.22        | ~ (v1_funct_1 @ sk_D)
% 0.99/1.22        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.99/1.22        | (v2_funct_1 @ sk_D)
% 0.99/1.22        | ~ (v1_funct_1 @ sk_C)
% 0.99/1.22        | ~ (v1_relat_1 @ sk_C))),
% 0.99/1.22      inference('sup-', [status(thm)], ['62', '63'])).
% 0.99/1.22  thf(fc4_funct_1, axiom,
% 0.99/1.22    (![A:$i]:
% 0.99/1.22     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.99/1.22       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.99/1.22  thf('65', plain, (![X11 : $i]: (v2_funct_1 @ (k6_relat_1 @ X11))),
% 0.99/1.22      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.99/1.22  thf('66', plain, (![X46 : $i]: ((k6_partfun1 @ X46) = (k6_relat_1 @ X46))),
% 0.99/1.22      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.99/1.22  thf('67', plain, (![X11 : $i]: (v2_funct_1 @ (k6_partfun1 @ X11))),
% 0.99/1.22      inference('demod', [status(thm)], ['65', '66'])).
% 0.99/1.22  thf('68', plain, ((v1_relat_1 @ sk_D)),
% 0.99/1.22      inference('sup-', [status(thm)], ['47', '48'])).
% 0.99/1.22  thf('69', plain, ((v1_funct_1 @ sk_D)),
% 0.99/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.22  thf('70', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.99/1.22      inference('sup+', [status(thm)], ['53', '54'])).
% 0.99/1.22  thf('71', plain, ((v1_funct_1 @ sk_C)),
% 0.99/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.22  thf('72', plain, ((v1_relat_1 @ sk_C)),
% 0.99/1.22      inference('sup-', [status(thm)], ['57', '58'])).
% 0.99/1.22  thf('73', plain, ((((sk_B) != (k1_relat_1 @ sk_D)) | (v2_funct_1 @ sk_D))),
% 0.99/1.22      inference('demod', [status(thm)],
% 0.99/1.22                ['64', '67', '68', '69', '70', '71', '72'])).
% 0.99/1.22  thf('74', plain,
% 0.99/1.22      ((((sk_B) != (k1_relat_1 @ sk_D)) | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 0.99/1.22      inference('clc', [status(thm)], ['61', '73'])).
% 0.99/1.22  thf('75', plain,
% 0.99/1.22      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.99/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.22  thf(cc2_relset_1, axiom,
% 0.99/1.22    (![A:$i,B:$i,C:$i]:
% 0.99/1.22     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.99/1.22       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.99/1.22  thf('76', plain,
% 0.99/1.22      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.99/1.22         ((v4_relat_1 @ X22 @ X23)
% 0.99/1.22          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.99/1.22      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.99/1.22  thf('77', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 0.99/1.22      inference('sup-', [status(thm)], ['75', '76'])).
% 0.99/1.22  thf(d18_relat_1, axiom,
% 0.99/1.22    (![A:$i,B:$i]:
% 0.99/1.22     ( ( v1_relat_1 @ B ) =>
% 0.99/1.22       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.99/1.22  thf('78', plain,
% 0.99/1.22      (![X0 : $i, X1 : $i]:
% 0.99/1.22         (~ (v4_relat_1 @ X0 @ X1)
% 0.99/1.22          | (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.99/1.22          | ~ (v1_relat_1 @ X0))),
% 0.99/1.22      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.99/1.22  thf('79', plain,
% 0.99/1.22      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B))),
% 0.99/1.22      inference('sup-', [status(thm)], ['77', '78'])).
% 0.99/1.22  thf('80', plain, ((v1_relat_1 @ sk_D)),
% 0.99/1.22      inference('sup-', [status(thm)], ['47', '48'])).
% 0.99/1.22  thf('81', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 0.99/1.22      inference('demod', [status(thm)], ['79', '80'])).
% 0.99/1.22  thf('82', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.99/1.22      inference('sup+', [status(thm)], ['53', '54'])).
% 0.99/1.22  thf(t147_funct_1, axiom,
% 0.99/1.22    (![A:$i,B:$i]:
% 0.99/1.22     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.99/1.22       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.99/1.22         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.99/1.22  thf('83', plain,
% 0.99/1.22      (![X12 : $i, X13 : $i]:
% 0.99/1.22         (~ (r1_tarski @ X12 @ (k2_relat_1 @ X13))
% 0.99/1.22          | ((k9_relat_1 @ X13 @ (k10_relat_1 @ X13 @ X12)) = (X12))
% 0.99/1.22          | ~ (v1_funct_1 @ X13)
% 0.99/1.22          | ~ (v1_relat_1 @ X13))),
% 0.99/1.22      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.99/1.22  thf('84', plain,
% 0.99/1.22      (![X0 : $i]:
% 0.99/1.22         (~ (r1_tarski @ X0 @ sk_B)
% 0.99/1.22          | ~ (v1_relat_1 @ sk_C)
% 0.99/1.22          | ~ (v1_funct_1 @ sk_C)
% 0.99/1.22          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.99/1.22      inference('sup-', [status(thm)], ['82', '83'])).
% 0.99/1.22  thf('85', plain, ((v1_relat_1 @ sk_C)),
% 0.99/1.22      inference('sup-', [status(thm)], ['57', '58'])).
% 0.99/1.22  thf('86', plain, ((v1_funct_1 @ sk_C)),
% 0.99/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.22  thf('87', plain,
% 0.99/1.22      (![X0 : $i]:
% 0.99/1.22         (~ (r1_tarski @ X0 @ sk_B)
% 0.99/1.22          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.99/1.22      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.99/1.22  thf('88', plain,
% 0.99/1.22      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 0.99/1.22         = (k1_relat_1 @ sk_D))),
% 0.99/1.22      inference('sup-', [status(thm)], ['81', '87'])).
% 0.99/1.22  thf('89', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.99/1.22      inference('demod', [status(thm)], ['6', '7', '22'])).
% 0.99/1.22  thf(t182_relat_1, axiom,
% 0.99/1.22    (![A:$i]:
% 0.99/1.22     ( ( v1_relat_1 @ A ) =>
% 0.99/1.22       ( ![B:$i]:
% 0.99/1.22         ( ( v1_relat_1 @ B ) =>
% 0.99/1.22           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.99/1.22             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.99/1.22  thf('90', plain,
% 0.99/1.22      (![X4 : $i, X5 : $i]:
% 0.99/1.22         (~ (v1_relat_1 @ X4)
% 0.99/1.22          | ((k1_relat_1 @ (k5_relat_1 @ X5 @ X4))
% 0.99/1.22              = (k10_relat_1 @ X5 @ (k1_relat_1 @ X4)))
% 0.99/1.22          | ~ (v1_relat_1 @ X5))),
% 0.99/1.22      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.99/1.22  thf('91', plain,
% 0.99/1.22      ((((k1_relat_1 @ (k6_partfun1 @ sk_A))
% 0.99/1.22          = (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 0.99/1.22        | ~ (v1_relat_1 @ sk_C)
% 0.99/1.22        | ~ (v1_relat_1 @ sk_D))),
% 0.99/1.22      inference('sup+', [status(thm)], ['89', '90'])).
% 0.99/1.22  thf(t71_relat_1, axiom,
% 0.99/1.22    (![A:$i]:
% 0.99/1.22     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.99/1.22       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.99/1.22  thf('92', plain, (![X8 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X8)) = (X8))),
% 0.99/1.22      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.99/1.22  thf('93', plain, (![X46 : $i]: ((k6_partfun1 @ X46) = (k6_relat_1 @ X46))),
% 0.99/1.22      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.99/1.22  thf('94', plain, (![X8 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X8)) = (X8))),
% 0.99/1.22      inference('demod', [status(thm)], ['92', '93'])).
% 0.99/1.22  thf('95', plain, ((v1_relat_1 @ sk_C)),
% 0.99/1.22      inference('sup-', [status(thm)], ['57', '58'])).
% 0.99/1.22  thf('96', plain, ((v1_relat_1 @ sk_D)),
% 0.99/1.22      inference('sup-', [status(thm)], ['47', '48'])).
% 0.99/1.22  thf('97', plain, (((sk_A) = (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))),
% 0.99/1.22      inference('demod', [status(thm)], ['91', '94', '95', '96'])).
% 0.99/1.22  thf('98', plain, (((k9_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.99/1.22      inference('demod', [status(thm)], ['88', '97'])).
% 0.99/1.22  thf('99', plain,
% 0.99/1.22      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.99/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.22  thf('100', plain,
% 0.99/1.22      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.99/1.22         ((v4_relat_1 @ X22 @ X23)
% 0.99/1.22          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.99/1.22      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.99/1.22  thf('101', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.99/1.22      inference('sup-', [status(thm)], ['99', '100'])).
% 0.99/1.22  thf(t209_relat_1, axiom,
% 0.99/1.22    (![A:$i,B:$i]:
% 0.99/1.22     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.99/1.22       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.99/1.22  thf('102', plain,
% 0.99/1.22      (![X6 : $i, X7 : $i]:
% 0.99/1.22         (((X6) = (k7_relat_1 @ X6 @ X7))
% 0.99/1.22          | ~ (v4_relat_1 @ X6 @ X7)
% 0.99/1.22          | ~ (v1_relat_1 @ X6))),
% 0.99/1.22      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.99/1.22  thf('103', plain,
% 0.99/1.22      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.99/1.22      inference('sup-', [status(thm)], ['101', '102'])).
% 0.99/1.22  thf('104', plain, ((v1_relat_1 @ sk_C)),
% 0.99/1.22      inference('sup-', [status(thm)], ['57', '58'])).
% 0.99/1.22  thf('105', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.99/1.22      inference('demod', [status(thm)], ['103', '104'])).
% 0.99/1.22  thf(t148_relat_1, axiom,
% 0.99/1.22    (![A:$i,B:$i]:
% 0.99/1.22     ( ( v1_relat_1 @ B ) =>
% 0.99/1.22       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.99/1.22  thf('106', plain,
% 0.99/1.22      (![X2 : $i, X3 : $i]:
% 0.99/1.22         (((k2_relat_1 @ (k7_relat_1 @ X2 @ X3)) = (k9_relat_1 @ X2 @ X3))
% 0.99/1.22          | ~ (v1_relat_1 @ X2))),
% 0.99/1.22      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.99/1.22  thf('107', plain,
% 0.99/1.22      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))
% 0.99/1.22        | ~ (v1_relat_1 @ sk_C))),
% 0.99/1.22      inference('sup+', [status(thm)], ['105', '106'])).
% 0.99/1.22  thf('108', plain, ((v1_relat_1 @ sk_C)),
% 0.99/1.22      inference('sup-', [status(thm)], ['57', '58'])).
% 0.99/1.22  thf('109', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.99/1.22      inference('demod', [status(thm)], ['107', '108'])).
% 0.99/1.22  thf('110', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.99/1.22      inference('sup+', [status(thm)], ['53', '54'])).
% 0.99/1.22  thf('111', plain, (((sk_B) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.99/1.22      inference('demod', [status(thm)], ['109', '110'])).
% 0.99/1.22  thf('112', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.99/1.22      inference('sup+', [status(thm)], ['98', '111'])).
% 0.99/1.22  thf('113', plain, ((((sk_B) != (sk_B)) | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 0.99/1.22      inference('demod', [status(thm)], ['74', '112'])).
% 0.99/1.22  thf('114', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.99/1.22      inference('simplify', [status(thm)], ['113'])).
% 0.99/1.22  thf(t65_funct_1, axiom,
% 0.99/1.22    (![A:$i]:
% 0.99/1.22     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.99/1.22       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.99/1.22  thf('115', plain,
% 0.99/1.22      (![X18 : $i]:
% 0.99/1.22         (~ (v2_funct_1 @ X18)
% 0.99/1.22          | ((k2_funct_1 @ (k2_funct_1 @ X18)) = (X18))
% 0.99/1.22          | ~ (v1_funct_1 @ X18)
% 0.99/1.22          | ~ (v1_relat_1 @ X18))),
% 0.99/1.22      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.99/1.22  thf('116', plain,
% 0.99/1.22      ((((k2_funct_1 @ sk_C) = (sk_D))
% 0.99/1.22        | ~ (v1_relat_1 @ sk_D)
% 0.99/1.22        | ~ (v1_funct_1 @ sk_D)
% 0.99/1.22        | ~ (v2_funct_1 @ sk_D))),
% 0.99/1.22      inference('sup+', [status(thm)], ['114', '115'])).
% 0.99/1.22  thf('117', plain, ((v1_relat_1 @ sk_D)),
% 0.99/1.22      inference('sup-', [status(thm)], ['47', '48'])).
% 0.99/1.22  thf('118', plain, ((v1_funct_1 @ sk_D)),
% 0.99/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.22  thf('119', plain, ((((k2_funct_1 @ sk_C) = (sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 0.99/1.22      inference('demod', [status(thm)], ['116', '117', '118'])).
% 0.99/1.22  thf('120', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.99/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.22  thf('121', plain, (~ (v2_funct_1 @ sk_D)),
% 0.99/1.22      inference('simplify_reflect-', [status(thm)], ['119', '120'])).
% 0.99/1.22  thf('122', plain, ((((sk_B) != (k1_relat_1 @ sk_D)) | (v2_funct_1 @ sk_D))),
% 0.99/1.22      inference('demod', [status(thm)],
% 0.99/1.22                ['64', '67', '68', '69', '70', '71', '72'])).
% 0.99/1.22  thf('123', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.99/1.22      inference('sup+', [status(thm)], ['98', '111'])).
% 0.99/1.22  thf('124', plain, ((((sk_B) != (sk_B)) | (v2_funct_1 @ sk_D))),
% 0.99/1.22      inference('demod', [status(thm)], ['122', '123'])).
% 0.99/1.22  thf('125', plain, ((v2_funct_1 @ sk_D)),
% 0.99/1.22      inference('simplify', [status(thm)], ['124'])).
% 0.99/1.22  thf('126', plain, ($false), inference('demod', [status(thm)], ['121', '125'])).
% 0.99/1.22  
% 0.99/1.22  % SZS output end Refutation
% 0.99/1.22  
% 0.99/1.23  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

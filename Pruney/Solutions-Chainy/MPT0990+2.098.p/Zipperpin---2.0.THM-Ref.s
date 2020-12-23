%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.upw9VByNY2

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:10 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  202 ( 873 expanded)
%              Number of leaves         :   43 ( 276 expanded)
%              Depth                    :   24
%              Number of atoms          : 2011 (22224 expanded)
%              Number of equality atoms :  158 (1502 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

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

thf('1',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( X44 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X44 ) ) )
      | ( ( k5_relat_1 @ X45 @ ( k2_funct_1 @ X45 ) )
        = ( k6_partfun1 @ X46 ) )
      | ~ ( v2_funct_1 @ X45 )
      | ( ( k2_relset_1 @ X46 @ X44 @ X45 )
       != X44 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('2',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('5',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
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

thf('9',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X19 @ X20 @ X22 @ X23 @ X18 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( X13 = X16 )
      | ~ ( r2_relset_1 @ X14 @ X15 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('19',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('20',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('21',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,(
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

thf('24',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( r2_relset_1 @ X32 @ X32 @ ( k1_partfun1 @ X32 @ X33 @ X33 @ X32 @ X31 @ X34 ) @ ( k6_partfun1 @ X32 ) )
      | ( ( k2_relset_1 @ X33 @ X32 @ X34 )
        = X32 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X33 @ X32 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('31',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( r2_relset_1 @ X14 @ X15 @ X13 @ X16 )
      | ( X13 != X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('32',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_relset_1 @ X14 @ X15 @ X16 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['29','33','34','35','36','37'])).

thf('39',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['5','38'])).

thf('40',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','39','40','41'])).

thf('43',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('47',plain,(
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

thf('48',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( zip_tseitin_0 @ X39 @ X42 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X43 @ X40 @ X40 @ X41 @ X42 @ X39 ) )
      | ( zip_tseitin_1 @ X41 @ X40 )
      | ( ( k2_relset_1 @ X43 @ X40 @ X42 )
       != X40 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X40 ) ) )
      | ~ ( v1_funct_2 @ X42 @ X43 @ X40 )
      | ~ ( v1_funct_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('49',plain,(
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
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['46','52'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('54',plain,(
    ! [X3: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('55',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('56',plain,(
    ! [X3: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X3 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['53','56','57','58','59','60'])).

thf('62',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X37 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('64',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X35: $i,X36: $i] :
      ( ( v2_funct_1 @ X36 )
      | ~ ( zip_tseitin_0 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('68',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['45','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
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

thf('72',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 )
        = ( k5_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['70','75'])).

thf('77',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('79',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['76','77','78'])).

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

thf('80',plain,(
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

thf('81',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('82',plain,(
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
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
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
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['29','33','34','35','36','37'])).

thf('85',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('86',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('87',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('91',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('97',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['83','84','87','88','93','94','97'])).

thf('99',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['66','67'])).

thf('101',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('102',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ X4 @ ( k2_funct_1 @ X4 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('103',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('104',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ X4 @ ( k2_funct_1 @ X4 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['45','68'])).

thf('106',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['85','86'])).

thf('108',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['66','67'])).

thf('110',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['106','107','108','109'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('112',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['110','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('116',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['101','116'])).

thf('118',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,
    ( ( k5_relat_1 @ sk_D @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['69','118'])).

thf('120',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['29','33','34','35','36','37'])).

thf('121',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['91','92'])).

thf('122',plain,(
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
    inference(demod,[status(thm)],['80','81'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ sk_C )
       != ( k6_partfun1 @ sk_B ) )
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
    inference('sup-',[status(thm)],['95','96'])).

thf('125',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ sk_C )
       != ( k6_partfun1 @ sk_B ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C ) )
      | ( X0
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['123','124','125','126'])).

thf('128',plain,
    ( ( sk_A
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ sk_D @ sk_C )
     != ( k6_partfun1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['120','127'])).

thf('129',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['85','86'])).

thf('130',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( sk_A
     != ( k1_relat_1 @ sk_C ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ sk_D @ sk_C )
     != ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('132',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( sk_A
     != ( k1_relat_1 @ sk_C ) )
    | ( ( k5_relat_1 @ sk_D @ sk_C )
     != ( k6_partfun1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ X4 @ ( k2_funct_1 @ X4 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('135',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( X44 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X44 ) ) )
      | ( ( k5_relat_1 @ X45 @ ( k2_funct_1 @ X45 ) )
        = ( k6_partfun1 @ X46 ) )
      | ~ ( v2_funct_1 @ X45 )
      | ( ( k2_relset_1 @ X46 @ X44 @ X45 )
       != X44 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('137',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['137','138','139','140','141'])).

thf('143',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['143','144'])).

thf('146',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['134','145'])).

thf('147',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['95','96'])).

thf('148',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['146','147','148','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('152',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('154',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,
    ( ( sk_A != sk_A )
    | ( ( k5_relat_1 @ sk_D @ sk_C )
     != ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['133','154'])).

thf('156',plain,(
    ( k5_relat_1 @ sk_D @ sk_C )
 != ( k6_partfun1 @ sk_B ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['119','156'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.upw9VByNY2
% 0.15/0.34  % Computer   : n014.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 19:15:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.91/1.10  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.91/1.10  % Solved by: fo/fo7.sh
% 0.91/1.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.10  % done 913 iterations in 0.643s
% 0.91/1.10  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.91/1.10  % SZS output start Refutation
% 0.91/1.10  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.91/1.10  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.91/1.10  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.91/1.10  thf(sk_C_type, type, sk_C: $i).
% 0.91/1.10  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.91/1.10  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.91/1.10  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.91/1.10  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.91/1.10  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.91/1.10  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.91/1.10  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.10  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.91/1.10  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.91/1.10  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.91/1.10  thf(sk_B_type, type, sk_B: $i).
% 0.91/1.10  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.91/1.10  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.91/1.10  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.91/1.10  thf(sk_D_type, type, sk_D: $i).
% 0.91/1.10  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.91/1.10  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.91/1.10  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.91/1.10  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.91/1.10  thf(t36_funct_2, conjecture,
% 0.91/1.10    (![A:$i,B:$i,C:$i]:
% 0.91/1.10     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.91/1.10         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.91/1.10       ( ![D:$i]:
% 0.91/1.10         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.91/1.10             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.91/1.10           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.91/1.10               ( r2_relset_1 @
% 0.91/1.10                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.91/1.10                 ( k6_partfun1 @ A ) ) & 
% 0.91/1.10               ( v2_funct_1 @ C ) ) =>
% 0.91/1.10             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.91/1.10               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.91/1.10  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.10    (~( ![A:$i,B:$i,C:$i]:
% 0.91/1.10        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.91/1.10            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.91/1.10          ( ![D:$i]:
% 0.91/1.10            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.91/1.10                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.91/1.10              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.91/1.10                  ( r2_relset_1 @
% 0.91/1.10                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.91/1.10                    ( k6_partfun1 @ A ) ) & 
% 0.91/1.10                  ( v2_funct_1 @ C ) ) =>
% 0.91/1.10                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.91/1.10                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.91/1.10    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.91/1.10  thf('0', plain,
% 0.91/1.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf(t35_funct_2, axiom,
% 0.91/1.10    (![A:$i,B:$i,C:$i]:
% 0.91/1.10     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.91/1.10         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.91/1.10       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.91/1.10         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.91/1.10           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.91/1.10             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.91/1.10  thf('1', plain,
% 0.91/1.10      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.91/1.10         (((X44) = (k1_xboole_0))
% 0.91/1.10          | ~ (v1_funct_1 @ X45)
% 0.91/1.10          | ~ (v1_funct_2 @ X45 @ X46 @ X44)
% 0.91/1.10          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X44)))
% 0.91/1.10          | ((k5_relat_1 @ X45 @ (k2_funct_1 @ X45)) = (k6_partfun1 @ X46))
% 0.91/1.10          | ~ (v2_funct_1 @ X45)
% 0.91/1.10          | ((k2_relset_1 @ X46 @ X44 @ X45) != (X44)))),
% 0.91/1.10      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.91/1.10  thf('2', plain,
% 0.91/1.10      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 0.91/1.10        | ~ (v2_funct_1 @ sk_D)
% 0.91/1.10        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.91/1.10        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.91/1.10        | ~ (v1_funct_1 @ sk_D)
% 0.91/1.10        | ((sk_A) = (k1_xboole_0)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['0', '1'])).
% 0.91/1.10  thf('3', plain,
% 0.91/1.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf(redefinition_k2_relset_1, axiom,
% 0.91/1.10    (![A:$i,B:$i,C:$i]:
% 0.91/1.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.10       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.91/1.10  thf('4', plain,
% 0.91/1.10      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.91/1.10         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 0.91/1.10          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.91/1.10      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.91/1.10  thf('5', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.91/1.10      inference('sup-', [status(thm)], ['3', '4'])).
% 0.91/1.10  thf('6', plain,
% 0.91/1.10      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.91/1.10        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.91/1.10        (k6_partfun1 @ sk_A))),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('7', plain,
% 0.91/1.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('8', plain,
% 0.91/1.10      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf(dt_k1_partfun1, axiom,
% 0.91/1.10    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.91/1.10     ( ( ( v1_funct_1 @ E ) & 
% 0.91/1.10         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.91/1.10         ( v1_funct_1 @ F ) & 
% 0.91/1.10         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.91/1.10       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.91/1.10         ( m1_subset_1 @
% 0.91/1.10           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.91/1.10           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.91/1.10  thf('9', plain,
% 0.91/1.10      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.91/1.10         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.91/1.10          | ~ (v1_funct_1 @ X18)
% 0.91/1.10          | ~ (v1_funct_1 @ X21)
% 0.91/1.10          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.91/1.10          | (m1_subset_1 @ (k1_partfun1 @ X19 @ X20 @ X22 @ X23 @ X18 @ X21) @ 
% 0.91/1.10             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X23))))),
% 0.91/1.10      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.91/1.10  thf('10', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.10         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.91/1.10           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.91/1.10          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.91/1.10          | ~ (v1_funct_1 @ X1)
% 0.91/1.10          | ~ (v1_funct_1 @ sk_C))),
% 0.91/1.10      inference('sup-', [status(thm)], ['8', '9'])).
% 0.91/1.10  thf('11', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('12', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.10         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.91/1.10           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.91/1.10          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.91/1.10          | ~ (v1_funct_1 @ X1))),
% 0.91/1.10      inference('demod', [status(thm)], ['10', '11'])).
% 0.91/1.10  thf('13', plain,
% 0.91/1.10      ((~ (v1_funct_1 @ sk_D)
% 0.91/1.10        | (m1_subset_1 @ 
% 0.91/1.10           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.91/1.10           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.91/1.10      inference('sup-', [status(thm)], ['7', '12'])).
% 0.91/1.10  thf('14', plain, ((v1_funct_1 @ sk_D)),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('15', plain,
% 0.91/1.10      ((m1_subset_1 @ 
% 0.91/1.10        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.91/1.10        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.91/1.10      inference('demod', [status(thm)], ['13', '14'])).
% 0.91/1.10  thf(redefinition_r2_relset_1, axiom,
% 0.91/1.10    (![A:$i,B:$i,C:$i,D:$i]:
% 0.91/1.10     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.91/1.10         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.91/1.10       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.91/1.10  thf('16', plain,
% 0.91/1.10      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.91/1.10         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.91/1.10          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.91/1.10          | ((X13) = (X16))
% 0.91/1.10          | ~ (r2_relset_1 @ X14 @ X15 @ X13 @ X16))),
% 0.91/1.10      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.91/1.10  thf('17', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.91/1.10             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.91/1.10          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.91/1.10          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.91/1.10      inference('sup-', [status(thm)], ['15', '16'])).
% 0.91/1.10  thf('18', plain,
% 0.91/1.10      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.91/1.10           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.91/1.10        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.91/1.10            = (k6_partfun1 @ sk_A)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['6', '17'])).
% 0.91/1.10  thf(t29_relset_1, axiom,
% 0.91/1.10    (![A:$i]:
% 0.91/1.10     ( m1_subset_1 @
% 0.91/1.10       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.91/1.10  thf('19', plain,
% 0.91/1.10      (![X17 : $i]:
% 0.91/1.10         (m1_subset_1 @ (k6_relat_1 @ X17) @ 
% 0.91/1.10          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))),
% 0.91/1.10      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.91/1.10  thf(redefinition_k6_partfun1, axiom,
% 0.91/1.10    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.91/1.10  thf('20', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.91/1.10      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.91/1.10  thf('21', plain,
% 0.91/1.10      (![X17 : $i]:
% 0.91/1.10         (m1_subset_1 @ (k6_partfun1 @ X17) @ 
% 0.91/1.10          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))),
% 0.91/1.10      inference('demod', [status(thm)], ['19', '20'])).
% 0.91/1.10  thf('22', plain,
% 0.91/1.10      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.91/1.10         = (k6_partfun1 @ sk_A))),
% 0.91/1.10      inference('demod', [status(thm)], ['18', '21'])).
% 0.91/1.10  thf('23', plain,
% 0.91/1.10      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf(t24_funct_2, axiom,
% 0.91/1.10    (![A:$i,B:$i,C:$i]:
% 0.91/1.10     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.91/1.10         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.91/1.10       ( ![D:$i]:
% 0.91/1.10         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.91/1.10             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.91/1.10           ( ( r2_relset_1 @
% 0.91/1.10               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.91/1.10               ( k6_partfun1 @ B ) ) =>
% 0.91/1.10             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.91/1.10  thf('24', plain,
% 0.91/1.10      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.91/1.10         (~ (v1_funct_1 @ X31)
% 0.91/1.10          | ~ (v1_funct_2 @ X31 @ X32 @ X33)
% 0.91/1.10          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.91/1.10          | ~ (r2_relset_1 @ X32 @ X32 @ 
% 0.91/1.10               (k1_partfun1 @ X32 @ X33 @ X33 @ X32 @ X31 @ X34) @ 
% 0.91/1.10               (k6_partfun1 @ X32))
% 0.91/1.10          | ((k2_relset_1 @ X33 @ X32 @ X34) = (X32))
% 0.91/1.10          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 0.91/1.10          | ~ (v1_funct_2 @ X34 @ X33 @ X32)
% 0.91/1.10          | ~ (v1_funct_1 @ X34))),
% 0.91/1.10      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.91/1.10  thf('25', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (~ (v1_funct_1 @ X0)
% 0.91/1.10          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.91/1.10          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.91/1.10          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.91/1.10          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.91/1.10               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.91/1.10               (k6_partfun1 @ sk_A))
% 0.91/1.10          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.91/1.10          | ~ (v1_funct_1 @ sk_C))),
% 0.91/1.10      inference('sup-', [status(thm)], ['23', '24'])).
% 0.91/1.10  thf('26', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('27', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('28', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (~ (v1_funct_1 @ X0)
% 0.91/1.10          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.91/1.10          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.91/1.10          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.91/1.10          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.91/1.10               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.91/1.10               (k6_partfun1 @ sk_A)))),
% 0.91/1.10      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.91/1.10  thf('29', plain,
% 0.91/1.10      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 0.91/1.10           (k6_partfun1 @ sk_A))
% 0.91/1.10        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.91/1.10        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.91/1.10        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.91/1.10        | ~ (v1_funct_1 @ sk_D))),
% 0.91/1.10      inference('sup-', [status(thm)], ['22', '28'])).
% 0.91/1.10  thf('30', plain,
% 0.91/1.10      (![X17 : $i]:
% 0.91/1.10         (m1_subset_1 @ (k6_partfun1 @ X17) @ 
% 0.91/1.10          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))),
% 0.91/1.10      inference('demod', [status(thm)], ['19', '20'])).
% 0.91/1.10  thf('31', plain,
% 0.91/1.10      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.91/1.10         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.91/1.10          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.91/1.10          | (r2_relset_1 @ X14 @ X15 @ X13 @ X16)
% 0.91/1.10          | ((X13) != (X16)))),
% 0.91/1.10      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.91/1.10  thf('32', plain,
% 0.91/1.10      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.91/1.10         ((r2_relset_1 @ X14 @ X15 @ X16 @ X16)
% 0.91/1.10          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.91/1.10      inference('simplify', [status(thm)], ['31'])).
% 0.91/1.10  thf('33', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['30', '32'])).
% 0.91/1.10  thf('34', plain,
% 0.91/1.10      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.91/1.10      inference('sup-', [status(thm)], ['3', '4'])).
% 0.91/1.10  thf('35', plain,
% 0.91/1.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('36', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('37', plain, ((v1_funct_1 @ sk_D)),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('38', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.91/1.10      inference('demod', [status(thm)], ['29', '33', '34', '35', '36', '37'])).
% 0.91/1.10  thf('39', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))),
% 0.91/1.10      inference('demod', [status(thm)], ['5', '38'])).
% 0.91/1.10  thf('40', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('41', plain, ((v1_funct_1 @ sk_D)),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('42', plain,
% 0.91/1.10      ((((sk_A) != (sk_A))
% 0.91/1.10        | ~ (v2_funct_1 @ sk_D)
% 0.91/1.10        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.91/1.10        | ((sk_A) = (k1_xboole_0)))),
% 0.91/1.10      inference('demod', [status(thm)], ['2', '39', '40', '41'])).
% 0.91/1.10  thf('43', plain,
% 0.91/1.10      ((((sk_A) = (k1_xboole_0))
% 0.91/1.10        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.91/1.10        | ~ (v2_funct_1 @ sk_D))),
% 0.91/1.10      inference('simplify', [status(thm)], ['42'])).
% 0.91/1.10  thf('44', plain, (((sk_A) != (k1_xboole_0))),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('45', plain,
% 0.91/1.10      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.91/1.10        | ~ (v2_funct_1 @ sk_D))),
% 0.91/1.10      inference('simplify_reflect-', [status(thm)], ['43', '44'])).
% 0.91/1.10  thf('46', plain,
% 0.91/1.10      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.91/1.10         = (k6_partfun1 @ sk_A))),
% 0.91/1.10      inference('demod', [status(thm)], ['18', '21'])).
% 0.91/1.10  thf('47', plain,
% 0.91/1.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf(t30_funct_2, axiom,
% 0.91/1.10    (![A:$i,B:$i,C:$i,D:$i]:
% 0.91/1.10     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.91/1.10         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 0.91/1.10       ( ![E:$i]:
% 0.91/1.10         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 0.91/1.10             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 0.91/1.10           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 0.91/1.10               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 0.91/1.10             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 0.91/1.10               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 0.91/1.10  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 0.91/1.10  thf(zf_stmt_2, axiom,
% 0.91/1.10    (![C:$i,B:$i]:
% 0.91/1.10     ( ( zip_tseitin_1 @ C @ B ) =>
% 0.91/1.10       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 0.91/1.10  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.91/1.10  thf(zf_stmt_4, axiom,
% 0.91/1.10    (![E:$i,D:$i]:
% 0.91/1.10     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 0.91/1.10  thf(zf_stmt_5, axiom,
% 0.91/1.10    (![A:$i,B:$i,C:$i,D:$i]:
% 0.91/1.10     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.91/1.10         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.91/1.10       ( ![E:$i]:
% 0.91/1.10         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.91/1.10             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.91/1.10           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 0.91/1.10               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 0.91/1.10             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 0.91/1.10  thf('48', plain,
% 0.91/1.10      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.91/1.10         (~ (v1_funct_1 @ X39)
% 0.91/1.10          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 0.91/1.10          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.91/1.10          | (zip_tseitin_0 @ X39 @ X42)
% 0.91/1.10          | ~ (v2_funct_1 @ (k1_partfun1 @ X43 @ X40 @ X40 @ X41 @ X42 @ X39))
% 0.91/1.10          | (zip_tseitin_1 @ X41 @ X40)
% 0.91/1.10          | ((k2_relset_1 @ X43 @ X40 @ X42) != (X40))
% 0.91/1.10          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X40)))
% 0.91/1.10          | ~ (v1_funct_2 @ X42 @ X43 @ X40)
% 0.91/1.10          | ~ (v1_funct_1 @ X42))),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.91/1.10  thf('49', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]:
% 0.91/1.10         (~ (v1_funct_1 @ X0)
% 0.91/1.10          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.91/1.10          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.91/1.10          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 0.91/1.10          | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.91/1.10          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.91/1.10          | (zip_tseitin_0 @ sk_D @ X0)
% 0.91/1.10          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.91/1.10          | ~ (v1_funct_1 @ sk_D))),
% 0.91/1.11      inference('sup-', [status(thm)], ['47', '48'])).
% 0.91/1.11  thf('50', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('51', plain, ((v1_funct_1 @ sk_D)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('52', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i]:
% 0.91/1.11         (~ (v1_funct_1 @ X0)
% 0.91/1.11          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.91/1.11          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.91/1.11          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 0.91/1.11          | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.91/1.11          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.91/1.11          | (zip_tseitin_0 @ sk_D @ X0))),
% 0.91/1.11      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.91/1.11  thf('53', plain,
% 0.91/1.11      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.91/1.11        | (zip_tseitin_0 @ sk_D @ sk_C)
% 0.91/1.11        | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.91/1.11        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.91/1.11        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.91/1.11        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.91/1.11        | ~ (v1_funct_1 @ sk_C))),
% 0.91/1.11      inference('sup-', [status(thm)], ['46', '52'])).
% 0.91/1.11  thf(fc4_funct_1, axiom,
% 0.91/1.11    (![A:$i]:
% 0.91/1.11     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.91/1.11       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.91/1.11  thf('54', plain, (![X3 : $i]: (v2_funct_1 @ (k6_relat_1 @ X3))),
% 0.91/1.11      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.91/1.11  thf('55', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.91/1.11      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.91/1.11  thf('56', plain, (![X3 : $i]: (v2_funct_1 @ (k6_partfun1 @ X3))),
% 0.91/1.11      inference('demod', [status(thm)], ['54', '55'])).
% 0.91/1.11  thf('57', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('58', plain,
% 0.91/1.11      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('59', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('60', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('61', plain,
% 0.91/1.11      (((zip_tseitin_0 @ sk_D @ sk_C)
% 0.91/1.11        | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.91/1.11        | ((sk_B) != (sk_B)))),
% 0.91/1.11      inference('demod', [status(thm)], ['53', '56', '57', '58', '59', '60'])).
% 0.91/1.11  thf('62', plain,
% 0.91/1.11      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 0.91/1.11      inference('simplify', [status(thm)], ['61'])).
% 0.91/1.11  thf('63', plain,
% 0.91/1.11      (![X37 : $i, X38 : $i]:
% 0.91/1.11         (((X37) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X37 @ X38))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.91/1.11  thf('64', plain,
% 0.91/1.11      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.91/1.11      inference('sup-', [status(thm)], ['62', '63'])).
% 0.91/1.11  thf('65', plain, (((sk_A) != (k1_xboole_0))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('66', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 0.91/1.11      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 0.91/1.11  thf('67', plain,
% 0.91/1.11      (![X35 : $i, X36 : $i]:
% 0.91/1.11         ((v2_funct_1 @ X36) | ~ (zip_tseitin_0 @ X36 @ X35))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.91/1.11  thf('68', plain, ((v2_funct_1 @ sk_D)),
% 0.91/1.11      inference('sup-', [status(thm)], ['66', '67'])).
% 0.91/1.11  thf('69', plain,
% 0.91/1.11      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 0.91/1.11      inference('demod', [status(thm)], ['45', '68'])).
% 0.91/1.11  thf('70', plain,
% 0.91/1.11      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('71', plain,
% 0.91/1.11      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf(redefinition_k1_partfun1, axiom,
% 0.91/1.11    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.91/1.11     ( ( ( v1_funct_1 @ E ) & 
% 0.91/1.11         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.91/1.11         ( v1_funct_1 @ F ) & 
% 0.91/1.11         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.91/1.11       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.91/1.11  thf('72', plain,
% 0.91/1.11      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.91/1.11         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.91/1.11          | ~ (v1_funct_1 @ X24)
% 0.91/1.11          | ~ (v1_funct_1 @ X27)
% 0.91/1.11          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.91/1.11          | ((k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27)
% 0.91/1.11              = (k5_relat_1 @ X24 @ X27)))),
% 0.91/1.11      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.91/1.11  thf('73', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.11         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.91/1.11            = (k5_relat_1 @ sk_C @ X0))
% 0.91/1.11          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.91/1.11          | ~ (v1_funct_1 @ X0)
% 0.91/1.11          | ~ (v1_funct_1 @ sk_C))),
% 0.91/1.11      inference('sup-', [status(thm)], ['71', '72'])).
% 0.91/1.11  thf('74', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('75', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.11         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.91/1.11            = (k5_relat_1 @ sk_C @ X0))
% 0.91/1.11          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.91/1.11          | ~ (v1_funct_1 @ X0))),
% 0.91/1.11      inference('demod', [status(thm)], ['73', '74'])).
% 0.91/1.11  thf('76', plain,
% 0.91/1.11      ((~ (v1_funct_1 @ sk_D)
% 0.91/1.11        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.91/1.11            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.91/1.11      inference('sup-', [status(thm)], ['70', '75'])).
% 0.91/1.11  thf('77', plain, ((v1_funct_1 @ sk_D)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('78', plain,
% 0.91/1.11      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.91/1.11         = (k6_partfun1 @ sk_A))),
% 0.91/1.11      inference('demod', [status(thm)], ['18', '21'])).
% 0.91/1.11  thf('79', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.91/1.11      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.91/1.11  thf(t64_funct_1, axiom,
% 0.91/1.11    (![A:$i]:
% 0.91/1.11     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.91/1.11       ( ![B:$i]:
% 0.91/1.11         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.91/1.11           ( ( ( v2_funct_1 @ A ) & 
% 0.91/1.11               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.91/1.11               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.91/1.11             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.91/1.11  thf('80', plain,
% 0.91/1.11      (![X5 : $i, X6 : $i]:
% 0.91/1.11         (~ (v1_relat_1 @ X5)
% 0.91/1.11          | ~ (v1_funct_1 @ X5)
% 0.91/1.11          | ((X5) = (k2_funct_1 @ X6))
% 0.91/1.11          | ((k5_relat_1 @ X5 @ X6) != (k6_relat_1 @ (k2_relat_1 @ X6)))
% 0.91/1.11          | ((k2_relat_1 @ X5) != (k1_relat_1 @ X6))
% 0.91/1.11          | ~ (v2_funct_1 @ X6)
% 0.91/1.11          | ~ (v1_funct_1 @ X6)
% 0.91/1.11          | ~ (v1_relat_1 @ X6))),
% 0.91/1.11      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.91/1.11  thf('81', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.91/1.11      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.91/1.11  thf('82', plain,
% 0.91/1.11      (![X5 : $i, X6 : $i]:
% 0.91/1.11         (~ (v1_relat_1 @ X5)
% 0.91/1.11          | ~ (v1_funct_1 @ X5)
% 0.91/1.11          | ((X5) = (k2_funct_1 @ X6))
% 0.91/1.11          | ((k5_relat_1 @ X5 @ X6) != (k6_partfun1 @ (k2_relat_1 @ X6)))
% 0.91/1.11          | ((k2_relat_1 @ X5) != (k1_relat_1 @ X6))
% 0.91/1.11          | ~ (v2_funct_1 @ X6)
% 0.91/1.11          | ~ (v1_funct_1 @ X6)
% 0.91/1.11          | ~ (v1_relat_1 @ X6))),
% 0.91/1.11      inference('demod', [status(thm)], ['80', '81'])).
% 0.91/1.11  thf('83', plain,
% 0.91/1.11      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 0.91/1.11        | ~ (v1_relat_1 @ sk_D)
% 0.91/1.11        | ~ (v1_funct_1 @ sk_D)
% 0.91/1.11        | ~ (v2_funct_1 @ sk_D)
% 0.91/1.11        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.91/1.11        | ((sk_C) = (k2_funct_1 @ sk_D))
% 0.91/1.11        | ~ (v1_funct_1 @ sk_C)
% 0.91/1.11        | ~ (v1_relat_1 @ sk_C))),
% 0.91/1.11      inference('sup-', [status(thm)], ['79', '82'])).
% 0.91/1.11  thf('84', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.91/1.11      inference('demod', [status(thm)], ['29', '33', '34', '35', '36', '37'])).
% 0.91/1.11  thf('85', plain,
% 0.91/1.11      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf(cc1_relset_1, axiom,
% 0.91/1.11    (![A:$i,B:$i,C:$i]:
% 0.91/1.11     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.11       ( v1_relat_1 @ C ) ))).
% 0.91/1.11  thf('86', plain,
% 0.91/1.11      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.91/1.11         ((v1_relat_1 @ X7)
% 0.91/1.11          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.91/1.11      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.91/1.11  thf('87', plain, ((v1_relat_1 @ sk_D)),
% 0.91/1.11      inference('sup-', [status(thm)], ['85', '86'])).
% 0.91/1.11  thf('88', plain, ((v1_funct_1 @ sk_D)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('89', plain,
% 0.91/1.11      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('90', plain,
% 0.91/1.11      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.91/1.11         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 0.91/1.11          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.91/1.11      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.91/1.11  thf('91', plain,
% 0.91/1.11      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.91/1.11      inference('sup-', [status(thm)], ['89', '90'])).
% 0.91/1.11  thf('92', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('93', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.91/1.11      inference('sup+', [status(thm)], ['91', '92'])).
% 0.91/1.11  thf('94', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('95', plain,
% 0.91/1.11      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('96', plain,
% 0.91/1.11      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.91/1.11         ((v1_relat_1 @ X7)
% 0.91/1.11          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.91/1.11      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.91/1.11  thf('97', plain, ((v1_relat_1 @ sk_C)),
% 0.91/1.11      inference('sup-', [status(thm)], ['95', '96'])).
% 0.91/1.11  thf('98', plain,
% 0.91/1.11      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 0.91/1.11        | ~ (v2_funct_1 @ sk_D)
% 0.91/1.11        | ((sk_B) != (k1_relat_1 @ sk_D))
% 0.91/1.11        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 0.91/1.11      inference('demod', [status(thm)],
% 0.91/1.11                ['83', '84', '87', '88', '93', '94', '97'])).
% 0.91/1.11  thf('99', plain,
% 0.91/1.11      ((((sk_C) = (k2_funct_1 @ sk_D))
% 0.91/1.11        | ((sk_B) != (k1_relat_1 @ sk_D))
% 0.91/1.11        | ~ (v2_funct_1 @ sk_D))),
% 0.91/1.11      inference('simplify', [status(thm)], ['98'])).
% 0.91/1.11  thf('100', plain, ((v2_funct_1 @ sk_D)),
% 0.91/1.11      inference('sup-', [status(thm)], ['66', '67'])).
% 0.91/1.11  thf('101', plain,
% 0.91/1.11      ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (k1_relat_1 @ sk_D)))),
% 0.91/1.11      inference('demod', [status(thm)], ['99', '100'])).
% 0.91/1.11  thf(t61_funct_1, axiom,
% 0.91/1.11    (![A:$i]:
% 0.91/1.11     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.91/1.11       ( ( v2_funct_1 @ A ) =>
% 0.91/1.11         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.91/1.11             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.91/1.11           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.91/1.11             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.91/1.11  thf('102', plain,
% 0.91/1.11      (![X4 : $i]:
% 0.91/1.11         (~ (v2_funct_1 @ X4)
% 0.91/1.11          | ((k5_relat_1 @ X4 @ (k2_funct_1 @ X4))
% 0.91/1.11              = (k6_relat_1 @ (k1_relat_1 @ X4)))
% 0.91/1.11          | ~ (v1_funct_1 @ X4)
% 0.91/1.11          | ~ (v1_relat_1 @ X4))),
% 0.91/1.11      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.91/1.11  thf('103', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.91/1.11      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.91/1.11  thf('104', plain,
% 0.91/1.11      (![X4 : $i]:
% 0.91/1.11         (~ (v2_funct_1 @ X4)
% 0.91/1.11          | ((k5_relat_1 @ X4 @ (k2_funct_1 @ X4))
% 0.91/1.11              = (k6_partfun1 @ (k1_relat_1 @ X4)))
% 0.91/1.11          | ~ (v1_funct_1 @ X4)
% 0.91/1.11          | ~ (v1_relat_1 @ X4))),
% 0.91/1.11      inference('demod', [status(thm)], ['102', '103'])).
% 0.91/1.11  thf('105', plain,
% 0.91/1.11      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 0.91/1.11      inference('demod', [status(thm)], ['45', '68'])).
% 0.91/1.11  thf('106', plain,
% 0.91/1.11      ((((k6_partfun1 @ (k1_relat_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.91/1.11        | ~ (v1_relat_1 @ sk_D)
% 0.91/1.11        | ~ (v1_funct_1 @ sk_D)
% 0.91/1.11        | ~ (v2_funct_1 @ sk_D))),
% 0.91/1.11      inference('sup+', [status(thm)], ['104', '105'])).
% 0.91/1.11  thf('107', plain, ((v1_relat_1 @ sk_D)),
% 0.91/1.11      inference('sup-', [status(thm)], ['85', '86'])).
% 0.91/1.11  thf('108', plain, ((v1_funct_1 @ sk_D)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('109', plain, ((v2_funct_1 @ sk_D)),
% 0.91/1.11      inference('sup-', [status(thm)], ['66', '67'])).
% 0.91/1.11  thf('110', plain,
% 0.91/1.11      (((k6_partfun1 @ (k1_relat_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 0.91/1.11      inference('demod', [status(thm)], ['106', '107', '108', '109'])).
% 0.91/1.11  thf(t71_relat_1, axiom,
% 0.91/1.11    (![A:$i]:
% 0.91/1.11     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.91/1.11       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.91/1.11  thf('111', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 0.91/1.11      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.91/1.11  thf('112', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.91/1.11      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.91/1.11  thf('113', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 0.91/1.11      inference('demod', [status(thm)], ['111', '112'])).
% 0.91/1.11  thf('114', plain,
% 0.91/1.11      (((k1_relat_1 @ (k6_partfun1 @ sk_B)) = (k1_relat_1 @ sk_D))),
% 0.91/1.11      inference('sup+', [status(thm)], ['110', '113'])).
% 0.91/1.11  thf('115', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 0.91/1.11      inference('demod', [status(thm)], ['111', '112'])).
% 0.91/1.11  thf('116', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.91/1.11      inference('demod', [status(thm)], ['114', '115'])).
% 0.91/1.11  thf('117', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (sk_B)))),
% 0.91/1.11      inference('demod', [status(thm)], ['101', '116'])).
% 0.91/1.11  thf('118', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.91/1.11      inference('simplify', [status(thm)], ['117'])).
% 0.91/1.11  thf('119', plain, (((k5_relat_1 @ sk_D @ sk_C) = (k6_partfun1 @ sk_B))),
% 0.91/1.11      inference('demod', [status(thm)], ['69', '118'])).
% 0.91/1.11  thf('120', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.91/1.11      inference('demod', [status(thm)], ['29', '33', '34', '35', '36', '37'])).
% 0.91/1.11  thf('121', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.91/1.11      inference('sup+', [status(thm)], ['91', '92'])).
% 0.91/1.11  thf('122', plain,
% 0.91/1.11      (![X5 : $i, X6 : $i]:
% 0.91/1.11         (~ (v1_relat_1 @ X5)
% 0.91/1.11          | ~ (v1_funct_1 @ X5)
% 0.91/1.11          | ((X5) = (k2_funct_1 @ X6))
% 0.91/1.11          | ((k5_relat_1 @ X5 @ X6) != (k6_partfun1 @ (k2_relat_1 @ X6)))
% 0.91/1.11          | ((k2_relat_1 @ X5) != (k1_relat_1 @ X6))
% 0.91/1.11          | ~ (v2_funct_1 @ X6)
% 0.91/1.11          | ~ (v1_funct_1 @ X6)
% 0.91/1.11          | ~ (v1_relat_1 @ X6))),
% 0.91/1.11      inference('demod', [status(thm)], ['80', '81'])).
% 0.91/1.11  thf('123', plain,
% 0.91/1.11      (![X0 : $i]:
% 0.91/1.11         (((k5_relat_1 @ X0 @ sk_C) != (k6_partfun1 @ sk_B))
% 0.91/1.11          | ~ (v1_relat_1 @ sk_C)
% 0.91/1.11          | ~ (v1_funct_1 @ sk_C)
% 0.91/1.11          | ~ (v2_funct_1 @ sk_C)
% 0.91/1.11          | ((k2_relat_1 @ X0) != (k1_relat_1 @ sk_C))
% 0.91/1.11          | ((X0) = (k2_funct_1 @ sk_C))
% 0.91/1.11          | ~ (v1_funct_1 @ X0)
% 0.91/1.11          | ~ (v1_relat_1 @ X0))),
% 0.91/1.11      inference('sup-', [status(thm)], ['121', '122'])).
% 0.91/1.11  thf('124', plain, ((v1_relat_1 @ sk_C)),
% 0.91/1.11      inference('sup-', [status(thm)], ['95', '96'])).
% 0.91/1.11  thf('125', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('126', plain, ((v2_funct_1 @ sk_C)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('127', plain,
% 0.91/1.11      (![X0 : $i]:
% 0.91/1.11         (((k5_relat_1 @ X0 @ sk_C) != (k6_partfun1 @ sk_B))
% 0.91/1.11          | ((k2_relat_1 @ X0) != (k1_relat_1 @ sk_C))
% 0.91/1.11          | ((X0) = (k2_funct_1 @ sk_C))
% 0.91/1.11          | ~ (v1_funct_1 @ X0)
% 0.91/1.11          | ~ (v1_relat_1 @ X0))),
% 0.91/1.11      inference('demod', [status(thm)], ['123', '124', '125', '126'])).
% 0.91/1.11  thf('128', plain,
% 0.91/1.11      ((((sk_A) != (k1_relat_1 @ sk_C))
% 0.91/1.11        | ~ (v1_relat_1 @ sk_D)
% 0.91/1.11        | ~ (v1_funct_1 @ sk_D)
% 0.91/1.11        | ((sk_D) = (k2_funct_1 @ sk_C))
% 0.91/1.11        | ((k5_relat_1 @ sk_D @ sk_C) != (k6_partfun1 @ sk_B)))),
% 0.91/1.11      inference('sup-', [status(thm)], ['120', '127'])).
% 0.91/1.11  thf('129', plain, ((v1_relat_1 @ sk_D)),
% 0.91/1.11      inference('sup-', [status(thm)], ['85', '86'])).
% 0.91/1.11  thf('130', plain, ((v1_funct_1 @ sk_D)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('131', plain,
% 0.91/1.11      ((((sk_A) != (k1_relat_1 @ sk_C))
% 0.91/1.11        | ((sk_D) = (k2_funct_1 @ sk_C))
% 0.91/1.11        | ((k5_relat_1 @ sk_D @ sk_C) != (k6_partfun1 @ sk_B)))),
% 0.91/1.11      inference('demod', [status(thm)], ['128', '129', '130'])).
% 0.91/1.11  thf('132', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('133', plain,
% 0.91/1.11      ((((sk_A) != (k1_relat_1 @ sk_C))
% 0.91/1.11        | ((k5_relat_1 @ sk_D @ sk_C) != (k6_partfun1 @ sk_B)))),
% 0.91/1.11      inference('simplify_reflect-', [status(thm)], ['131', '132'])).
% 0.91/1.11  thf('134', plain,
% 0.91/1.11      (![X4 : $i]:
% 0.91/1.11         (~ (v2_funct_1 @ X4)
% 0.91/1.11          | ((k5_relat_1 @ X4 @ (k2_funct_1 @ X4))
% 0.91/1.11              = (k6_partfun1 @ (k1_relat_1 @ X4)))
% 0.91/1.11          | ~ (v1_funct_1 @ X4)
% 0.91/1.11          | ~ (v1_relat_1 @ X4))),
% 0.91/1.11      inference('demod', [status(thm)], ['102', '103'])).
% 0.91/1.11  thf('135', plain,
% 0.91/1.11      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('136', plain,
% 0.91/1.11      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.91/1.11         (((X44) = (k1_xboole_0))
% 0.91/1.11          | ~ (v1_funct_1 @ X45)
% 0.91/1.11          | ~ (v1_funct_2 @ X45 @ X46 @ X44)
% 0.91/1.11          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X44)))
% 0.91/1.11          | ((k5_relat_1 @ X45 @ (k2_funct_1 @ X45)) = (k6_partfun1 @ X46))
% 0.91/1.11          | ~ (v2_funct_1 @ X45)
% 0.91/1.11          | ((k2_relset_1 @ X46 @ X44 @ X45) != (X44)))),
% 0.91/1.11      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.91/1.11  thf('137', plain,
% 0.91/1.11      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.91/1.11        | ~ (v2_funct_1 @ sk_C)
% 0.91/1.11        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.91/1.11        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.91/1.11        | ~ (v1_funct_1 @ sk_C)
% 0.91/1.11        | ((sk_B) = (k1_xboole_0)))),
% 0.91/1.11      inference('sup-', [status(thm)], ['135', '136'])).
% 0.91/1.11  thf('138', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('139', plain, ((v2_funct_1 @ sk_C)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('140', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('141', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('142', plain,
% 0.91/1.11      ((((sk_B) != (sk_B))
% 0.91/1.11        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.91/1.11        | ((sk_B) = (k1_xboole_0)))),
% 0.91/1.11      inference('demod', [status(thm)], ['137', '138', '139', '140', '141'])).
% 0.91/1.11  thf('143', plain,
% 0.91/1.11      ((((sk_B) = (k1_xboole_0))
% 0.91/1.11        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 0.91/1.11      inference('simplify', [status(thm)], ['142'])).
% 0.91/1.11  thf('144', plain, (((sk_B) != (k1_xboole_0))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('145', plain,
% 0.91/1.11      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 0.91/1.11      inference('simplify_reflect-', [status(thm)], ['143', '144'])).
% 0.91/1.11  thf('146', plain,
% 0.91/1.11      ((((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.91/1.11        | ~ (v1_relat_1 @ sk_C)
% 0.91/1.11        | ~ (v1_funct_1 @ sk_C)
% 0.91/1.11        | ~ (v2_funct_1 @ sk_C))),
% 0.91/1.11      inference('sup+', [status(thm)], ['134', '145'])).
% 0.91/1.11  thf('147', plain, ((v1_relat_1 @ sk_C)),
% 0.91/1.11      inference('sup-', [status(thm)], ['95', '96'])).
% 0.91/1.11  thf('148', plain, ((v1_funct_1 @ sk_C)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('149', plain, ((v2_funct_1 @ sk_C)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('150', plain,
% 0.91/1.11      (((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 0.91/1.11      inference('demod', [status(thm)], ['146', '147', '148', '149'])).
% 0.91/1.11  thf('151', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 0.91/1.11      inference('demod', [status(thm)], ['111', '112'])).
% 0.91/1.11  thf('152', plain,
% 0.91/1.11      (((k1_relat_1 @ (k6_partfun1 @ sk_A)) = (k1_relat_1 @ sk_C))),
% 0.91/1.11      inference('sup+', [status(thm)], ['150', '151'])).
% 0.91/1.11  thf('153', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 0.91/1.11      inference('demod', [status(thm)], ['111', '112'])).
% 0.91/1.11  thf('154', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.91/1.11      inference('demod', [status(thm)], ['152', '153'])).
% 0.91/1.11  thf('155', plain,
% 0.91/1.11      ((((sk_A) != (sk_A))
% 0.91/1.11        | ((k5_relat_1 @ sk_D @ sk_C) != (k6_partfun1 @ sk_B)))),
% 0.91/1.11      inference('demod', [status(thm)], ['133', '154'])).
% 0.91/1.11  thf('156', plain, (((k5_relat_1 @ sk_D @ sk_C) != (k6_partfun1 @ sk_B))),
% 0.91/1.11      inference('simplify', [status(thm)], ['155'])).
% 0.91/1.11  thf('157', plain, ($false),
% 0.91/1.11      inference('simplify_reflect-', [status(thm)], ['119', '156'])).
% 0.91/1.11  
% 0.91/1.11  % SZS output end Refutation
% 0.91/1.11  
% 0.91/1.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

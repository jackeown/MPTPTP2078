%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AN4iHnXVsu

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:10 EST 2020

% Result     : Theorem 0.85s
% Output     : Refutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 446 expanded)
%              Number of leaves         :   43 ( 151 expanded)
%              Depth                    :   21
%              Number of atoms          : 1838 (10840 expanded)
%              Number of equality atoms :  130 ( 757 expanded)
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

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ X4 @ ( k2_funct_1 @ X4 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ X4 @ ( k2_funct_1 @ X4 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

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

thf('3',plain,(
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

thf('4',plain,(
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

thf('5',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('8',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','8','9','10'])).

thf('12',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf('14',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
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

thf('17',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X19 @ X20 @ X22 @ X23 @ X18 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('24',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( X13 = X16 )
      | ~ ( r2_relset_1 @ X14 @ X15 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','25'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('27',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('28',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('29',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('31',plain,(
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

thf('32',plain,(
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

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('39',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( r2_relset_1 @ X14 @ X15 @ X13 @ X16 )
      | ( X13 != X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('40',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_relset_1 @ X14 @ X15 @ X16 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','7'])).

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
    inference(demod,[status(thm)],['37','41','42','43','44','45'])).

thf('47',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','46'])).

thf('48',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('50',plain,(
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

thf('51',plain,(
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

thf('52',plain,(
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
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['49','55'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('57',plain,(
    ! [X3: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('58',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('59',plain,(
    ! [X3: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X3 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['56','59','60','61','62','63'])).

thf('65',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X37 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('67',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X35: $i,X36: $i] :
      ( ( v2_funct_1 @ X36 )
      | ~ ( zip_tseitin_0 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('71',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['48','71'])).

thf('73',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['2','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('75',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('76',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['69','70'])).

thf('79',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['73','76','77','78'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('81',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['79','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('85',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
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

thf('88',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 )
        = ( k5_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['86','91'])).

thf('93',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('95',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['92','93','94'])).

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

thf('96',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ( X5
        = ( k2_funct_1 @ X6 ) )
      | ( ( k5_relat_1 @ X6 @ X5 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X6 ) ) )
      | ( ( k2_relat_1 @ X6 )
       != ( k1_relat_1 @ X5 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t63_funct_1])).

thf('97',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('98',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ( X5
        = ( k2_funct_1 @ X6 ) )
      | ( ( k5_relat_1 @ X6 @ X5 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X6 ) ) )
      | ( ( k2_relat_1 @ X6 )
       != ( k1_relat_1 @ X5 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ X4 @ ( k2_funct_1 @ X4 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('101',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
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

thf('103',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['103','104','105','106','107'])).

thf('109',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['100','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('115',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['112','115','116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('120',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('122',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['113','114'])).

thf('124',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('128',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['74','75'])).

thf('133',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['99','122','123','124','125','130','131','132'])).

thf('134',plain,
    ( ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    sk_B
 != ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['134','135'])).

thf('137',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['85','136'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AN4iHnXVsu
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:51:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.85/1.09  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.85/1.09  % Solved by: fo/fo7.sh
% 0.85/1.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.85/1.09  % done 834 iterations in 0.637s
% 0.85/1.09  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.85/1.09  % SZS output start Refutation
% 0.85/1.09  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.85/1.09  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.85/1.09  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.85/1.09  thf(sk_C_type, type, sk_C: $i).
% 0.85/1.09  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.85/1.09  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.85/1.09  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.85/1.09  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.85/1.09  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.85/1.09  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.85/1.09  thf(sk_A_type, type, sk_A: $i).
% 0.85/1.09  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.85/1.09  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.85/1.09  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.85/1.09  thf(sk_B_type, type, sk_B: $i).
% 0.85/1.09  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.85/1.09  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.85/1.09  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.85/1.09  thf(sk_D_type, type, sk_D: $i).
% 0.85/1.09  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.85/1.09  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.85/1.09  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.85/1.09  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.85/1.09  thf(t61_funct_1, axiom,
% 0.85/1.09    (![A:$i]:
% 0.85/1.09     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.85/1.09       ( ( v2_funct_1 @ A ) =>
% 0.85/1.09         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.85/1.09             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.85/1.09           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.85/1.09             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.85/1.09  thf('0', plain,
% 0.85/1.09      (![X4 : $i]:
% 0.85/1.09         (~ (v2_funct_1 @ X4)
% 0.85/1.09          | ((k5_relat_1 @ X4 @ (k2_funct_1 @ X4))
% 0.85/1.09              = (k6_relat_1 @ (k1_relat_1 @ X4)))
% 0.85/1.09          | ~ (v1_funct_1 @ X4)
% 0.85/1.09          | ~ (v1_relat_1 @ X4))),
% 0.85/1.09      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.85/1.09  thf(redefinition_k6_partfun1, axiom,
% 0.85/1.09    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.85/1.09  thf('1', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.85/1.09      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.85/1.09  thf('2', plain,
% 0.85/1.09      (![X4 : $i]:
% 0.85/1.09         (~ (v2_funct_1 @ X4)
% 0.85/1.09          | ((k5_relat_1 @ X4 @ (k2_funct_1 @ X4))
% 0.85/1.09              = (k6_partfun1 @ (k1_relat_1 @ X4)))
% 0.85/1.09          | ~ (v1_funct_1 @ X4)
% 0.85/1.09          | ~ (v1_relat_1 @ X4))),
% 0.85/1.09      inference('demod', [status(thm)], ['0', '1'])).
% 0.85/1.09  thf(t36_funct_2, conjecture,
% 0.85/1.09    (![A:$i,B:$i,C:$i]:
% 0.85/1.09     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.85/1.09         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.85/1.09       ( ![D:$i]:
% 0.85/1.09         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.85/1.09             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.85/1.09           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.85/1.09               ( r2_relset_1 @
% 0.85/1.09                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.85/1.09                 ( k6_partfun1 @ A ) ) & 
% 0.85/1.09               ( v2_funct_1 @ C ) ) =>
% 0.85/1.09             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.85/1.09               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.85/1.09  thf(zf_stmt_0, negated_conjecture,
% 0.85/1.09    (~( ![A:$i,B:$i,C:$i]:
% 0.85/1.09        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.85/1.09            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.85/1.09          ( ![D:$i]:
% 0.85/1.09            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.85/1.09                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.85/1.09              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.85/1.09                  ( r2_relset_1 @
% 0.85/1.09                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.85/1.09                    ( k6_partfun1 @ A ) ) & 
% 0.85/1.09                  ( v2_funct_1 @ C ) ) =>
% 0.85/1.09                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.85/1.09                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.85/1.09    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.85/1.09  thf('3', plain,
% 0.85/1.09      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf(t35_funct_2, axiom,
% 0.85/1.09    (![A:$i,B:$i,C:$i]:
% 0.85/1.09     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.85/1.09         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.85/1.09       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.85/1.09         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.85/1.09           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.85/1.09             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.85/1.09  thf('4', plain,
% 0.85/1.09      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.85/1.09         (((X44) = (k1_xboole_0))
% 0.85/1.09          | ~ (v1_funct_1 @ X45)
% 0.85/1.09          | ~ (v1_funct_2 @ X45 @ X46 @ X44)
% 0.85/1.09          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X44)))
% 0.85/1.09          | ((k5_relat_1 @ X45 @ (k2_funct_1 @ X45)) = (k6_partfun1 @ X46))
% 0.85/1.09          | ~ (v2_funct_1 @ X45)
% 0.85/1.09          | ((k2_relset_1 @ X46 @ X44 @ X45) != (X44)))),
% 0.85/1.09      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.85/1.09  thf('5', plain,
% 0.85/1.09      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 0.85/1.09        | ~ (v2_funct_1 @ sk_D)
% 0.85/1.09        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.85/1.09        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.85/1.09        | ~ (v1_funct_1 @ sk_D)
% 0.85/1.09        | ((sk_A) = (k1_xboole_0)))),
% 0.85/1.09      inference('sup-', [status(thm)], ['3', '4'])).
% 0.85/1.09  thf('6', plain,
% 0.85/1.09      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf(redefinition_k2_relset_1, axiom,
% 0.85/1.09    (![A:$i,B:$i,C:$i]:
% 0.85/1.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.85/1.09       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.85/1.09  thf('7', plain,
% 0.85/1.09      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.85/1.09         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 0.85/1.09          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.85/1.09      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.85/1.09  thf('8', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.85/1.09      inference('sup-', [status(thm)], ['6', '7'])).
% 0.85/1.09  thf('9', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf('11', plain,
% 0.85/1.09      ((((k2_relat_1 @ sk_D) != (sk_A))
% 0.85/1.09        | ~ (v2_funct_1 @ sk_D)
% 0.85/1.09        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.85/1.09        | ((sk_A) = (k1_xboole_0)))),
% 0.85/1.09      inference('demod', [status(thm)], ['5', '8', '9', '10'])).
% 0.85/1.09  thf('12', plain, (((sk_A) != (k1_xboole_0))),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf('13', plain,
% 0.85/1.09      ((((k2_relat_1 @ sk_D) != (sk_A))
% 0.85/1.09        | ~ (v2_funct_1 @ sk_D)
% 0.85/1.09        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 0.85/1.09      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.85/1.09  thf('14', plain,
% 0.85/1.09      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.85/1.09        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.85/1.09        (k6_partfun1 @ sk_A))),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf('15', plain,
% 0.85/1.09      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf('16', plain,
% 0.85/1.09      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf(dt_k1_partfun1, axiom,
% 0.85/1.09    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.85/1.09     ( ( ( v1_funct_1 @ E ) & 
% 0.85/1.09         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.85/1.09         ( v1_funct_1 @ F ) & 
% 0.85/1.09         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.85/1.09       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.85/1.09         ( m1_subset_1 @
% 0.85/1.09           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.85/1.09           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.85/1.09  thf('17', plain,
% 0.85/1.09      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.85/1.09         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.85/1.09          | ~ (v1_funct_1 @ X18)
% 0.85/1.09          | ~ (v1_funct_1 @ X21)
% 0.85/1.09          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.85/1.09          | (m1_subset_1 @ (k1_partfun1 @ X19 @ X20 @ X22 @ X23 @ X18 @ X21) @ 
% 0.85/1.09             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X23))))),
% 0.85/1.09      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.85/1.09  thf('18', plain,
% 0.85/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.09         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.85/1.09           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.85/1.09          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.85/1.09          | ~ (v1_funct_1 @ X1)
% 0.85/1.09          | ~ (v1_funct_1 @ sk_C))),
% 0.85/1.09      inference('sup-', [status(thm)], ['16', '17'])).
% 0.85/1.09  thf('19', plain, ((v1_funct_1 @ sk_C)),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf('20', plain,
% 0.85/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.09         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.85/1.09           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.85/1.09          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.85/1.09          | ~ (v1_funct_1 @ X1))),
% 0.85/1.09      inference('demod', [status(thm)], ['18', '19'])).
% 0.85/1.09  thf('21', plain,
% 0.85/1.09      ((~ (v1_funct_1 @ sk_D)
% 0.85/1.09        | (m1_subset_1 @ 
% 0.85/1.09           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.85/1.09           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.85/1.09      inference('sup-', [status(thm)], ['15', '20'])).
% 0.85/1.09  thf('22', plain, ((v1_funct_1 @ sk_D)),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf('23', plain,
% 0.85/1.09      ((m1_subset_1 @ 
% 0.85/1.09        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.85/1.09        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.85/1.09      inference('demod', [status(thm)], ['21', '22'])).
% 0.85/1.09  thf(redefinition_r2_relset_1, axiom,
% 0.85/1.09    (![A:$i,B:$i,C:$i,D:$i]:
% 0.85/1.09     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.85/1.09         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.85/1.09       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.85/1.09  thf('24', plain,
% 0.85/1.09      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.85/1.09         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.85/1.09          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.85/1.09          | ((X13) = (X16))
% 0.85/1.09          | ~ (r2_relset_1 @ X14 @ X15 @ X13 @ X16))),
% 0.85/1.09      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.85/1.09  thf('25', plain,
% 0.85/1.09      (![X0 : $i]:
% 0.85/1.09         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.85/1.09             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.85/1.09          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.85/1.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.85/1.09      inference('sup-', [status(thm)], ['23', '24'])).
% 0.85/1.09  thf('26', plain,
% 0.85/1.09      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.85/1.09           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.85/1.09        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.85/1.09            = (k6_partfun1 @ sk_A)))),
% 0.85/1.09      inference('sup-', [status(thm)], ['14', '25'])).
% 0.85/1.09  thf(t29_relset_1, axiom,
% 0.85/1.09    (![A:$i]:
% 0.85/1.09     ( m1_subset_1 @
% 0.85/1.09       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.85/1.09  thf('27', plain,
% 0.85/1.09      (![X17 : $i]:
% 0.85/1.09         (m1_subset_1 @ (k6_relat_1 @ X17) @ 
% 0.85/1.09          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))),
% 0.85/1.09      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.85/1.09  thf('28', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.85/1.09      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.85/1.09  thf('29', plain,
% 0.85/1.09      (![X17 : $i]:
% 0.85/1.09         (m1_subset_1 @ (k6_partfun1 @ X17) @ 
% 0.85/1.09          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))),
% 0.85/1.09      inference('demod', [status(thm)], ['27', '28'])).
% 0.85/1.09  thf('30', plain,
% 0.85/1.09      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.85/1.09         = (k6_partfun1 @ sk_A))),
% 0.85/1.09      inference('demod', [status(thm)], ['26', '29'])).
% 0.85/1.09  thf('31', plain,
% 0.85/1.09      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf(t24_funct_2, axiom,
% 0.85/1.09    (![A:$i,B:$i,C:$i]:
% 0.85/1.09     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.85/1.09         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.85/1.09       ( ![D:$i]:
% 0.85/1.09         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.85/1.09             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.85/1.09           ( ( r2_relset_1 @
% 0.85/1.09               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.85/1.09               ( k6_partfun1 @ B ) ) =>
% 0.85/1.09             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.85/1.09  thf('32', plain,
% 0.85/1.09      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.85/1.09         (~ (v1_funct_1 @ X31)
% 0.85/1.09          | ~ (v1_funct_2 @ X31 @ X32 @ X33)
% 0.85/1.09          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.85/1.09          | ~ (r2_relset_1 @ X32 @ X32 @ 
% 0.85/1.09               (k1_partfun1 @ X32 @ X33 @ X33 @ X32 @ X31 @ X34) @ 
% 0.85/1.09               (k6_partfun1 @ X32))
% 0.85/1.09          | ((k2_relset_1 @ X33 @ X32 @ X34) = (X32))
% 0.85/1.09          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 0.85/1.09          | ~ (v1_funct_2 @ X34 @ X33 @ X32)
% 0.85/1.09          | ~ (v1_funct_1 @ X34))),
% 0.85/1.09      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.85/1.09  thf('33', plain,
% 0.85/1.09      (![X0 : $i]:
% 0.85/1.09         (~ (v1_funct_1 @ X0)
% 0.85/1.09          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.85/1.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.85/1.09          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.85/1.09          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.85/1.09               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.85/1.09               (k6_partfun1 @ sk_A))
% 0.85/1.09          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.85/1.09          | ~ (v1_funct_1 @ sk_C))),
% 0.85/1.09      inference('sup-', [status(thm)], ['31', '32'])).
% 0.85/1.09  thf('34', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf('36', plain,
% 0.85/1.09      (![X0 : $i]:
% 0.85/1.09         (~ (v1_funct_1 @ X0)
% 0.85/1.09          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.85/1.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.85/1.09          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.85/1.09          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.85/1.09               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.85/1.09               (k6_partfun1 @ sk_A)))),
% 0.85/1.09      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.85/1.09  thf('37', plain,
% 0.85/1.09      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 0.85/1.09           (k6_partfun1 @ sk_A))
% 0.85/1.09        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.85/1.09        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.85/1.09        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.85/1.09        | ~ (v1_funct_1 @ sk_D))),
% 0.85/1.09      inference('sup-', [status(thm)], ['30', '36'])).
% 0.85/1.09  thf('38', plain,
% 0.85/1.09      (![X17 : $i]:
% 0.85/1.09         (m1_subset_1 @ (k6_partfun1 @ X17) @ 
% 0.85/1.09          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))),
% 0.85/1.09      inference('demod', [status(thm)], ['27', '28'])).
% 0.85/1.09  thf('39', plain,
% 0.85/1.09      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.85/1.09         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.85/1.09          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.85/1.09          | (r2_relset_1 @ X14 @ X15 @ X13 @ X16)
% 0.85/1.09          | ((X13) != (X16)))),
% 0.85/1.09      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.85/1.09  thf('40', plain,
% 0.85/1.09      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.85/1.09         ((r2_relset_1 @ X14 @ X15 @ X16 @ X16)
% 0.85/1.09          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.85/1.09      inference('simplify', [status(thm)], ['39'])).
% 0.85/1.09  thf('41', plain,
% 0.85/1.09      (![X0 : $i]:
% 0.85/1.09         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 0.85/1.09      inference('sup-', [status(thm)], ['38', '40'])).
% 0.85/1.09  thf('42', plain,
% 0.85/1.09      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.85/1.09      inference('sup-', [status(thm)], ['6', '7'])).
% 0.85/1.09  thf('43', plain,
% 0.85/1.09      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf('44', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf('45', plain, ((v1_funct_1 @ sk_D)),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf('46', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.85/1.09      inference('demod', [status(thm)], ['37', '41', '42', '43', '44', '45'])).
% 0.85/1.09  thf('47', plain,
% 0.85/1.09      ((((sk_A) != (sk_A))
% 0.85/1.09        | ~ (v2_funct_1 @ sk_D)
% 0.85/1.09        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 0.85/1.09      inference('demod', [status(thm)], ['13', '46'])).
% 0.85/1.09  thf('48', plain,
% 0.85/1.09      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.85/1.09        | ~ (v2_funct_1 @ sk_D))),
% 0.85/1.09      inference('simplify', [status(thm)], ['47'])).
% 0.85/1.09  thf('49', plain,
% 0.85/1.09      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.85/1.09         = (k6_partfun1 @ sk_A))),
% 0.85/1.09      inference('demod', [status(thm)], ['26', '29'])).
% 0.85/1.09  thf('50', plain,
% 0.85/1.09      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf(t30_funct_2, axiom,
% 0.85/1.09    (![A:$i,B:$i,C:$i,D:$i]:
% 0.85/1.09     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.85/1.09         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 0.85/1.09       ( ![E:$i]:
% 0.85/1.09         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 0.85/1.09             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 0.85/1.09           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 0.85/1.09               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 0.85/1.09             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 0.85/1.09               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 0.85/1.09  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 0.85/1.09  thf(zf_stmt_2, axiom,
% 0.85/1.09    (![C:$i,B:$i]:
% 0.85/1.09     ( ( zip_tseitin_1 @ C @ B ) =>
% 0.85/1.09       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 0.85/1.09  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.85/1.09  thf(zf_stmt_4, axiom,
% 0.85/1.09    (![E:$i,D:$i]:
% 0.85/1.09     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 0.85/1.09  thf(zf_stmt_5, axiom,
% 0.85/1.09    (![A:$i,B:$i,C:$i,D:$i]:
% 0.85/1.09     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.85/1.09         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.85/1.09       ( ![E:$i]:
% 0.85/1.09         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.85/1.09             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.85/1.09           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 0.85/1.09               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 0.85/1.09             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 0.85/1.09  thf('51', plain,
% 0.85/1.09      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.85/1.09         (~ (v1_funct_1 @ X39)
% 0.85/1.09          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 0.85/1.09          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.85/1.09          | (zip_tseitin_0 @ X39 @ X42)
% 0.85/1.09          | ~ (v2_funct_1 @ (k1_partfun1 @ X43 @ X40 @ X40 @ X41 @ X42 @ X39))
% 0.85/1.09          | (zip_tseitin_1 @ X41 @ X40)
% 0.85/1.09          | ((k2_relset_1 @ X43 @ X40 @ X42) != (X40))
% 0.85/1.09          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X40)))
% 0.85/1.09          | ~ (v1_funct_2 @ X42 @ X43 @ X40)
% 0.85/1.09          | ~ (v1_funct_1 @ X42))),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.85/1.09  thf('52', plain,
% 0.85/1.09      (![X0 : $i, X1 : $i]:
% 0.85/1.09         (~ (v1_funct_1 @ X0)
% 0.85/1.09          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.85/1.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.85/1.09          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 0.85/1.09          | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.85/1.09          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.85/1.09          | (zip_tseitin_0 @ sk_D @ X0)
% 0.85/1.09          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.85/1.09          | ~ (v1_funct_1 @ sk_D))),
% 0.85/1.09      inference('sup-', [status(thm)], ['50', '51'])).
% 0.85/1.09  thf('53', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf('54', plain, ((v1_funct_1 @ sk_D)),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf('55', plain,
% 0.85/1.09      (![X0 : $i, X1 : $i]:
% 0.85/1.09         (~ (v1_funct_1 @ X0)
% 0.85/1.09          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.85/1.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.85/1.09          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 0.85/1.09          | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.85/1.09          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.85/1.09          | (zip_tseitin_0 @ sk_D @ X0))),
% 0.85/1.09      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.85/1.09  thf('56', plain,
% 0.85/1.09      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.85/1.09        | (zip_tseitin_0 @ sk_D @ sk_C)
% 0.85/1.09        | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.85/1.09        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.85/1.09        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.85/1.09        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.85/1.09        | ~ (v1_funct_1 @ sk_C))),
% 0.85/1.09      inference('sup-', [status(thm)], ['49', '55'])).
% 0.85/1.09  thf(fc4_funct_1, axiom,
% 0.85/1.09    (![A:$i]:
% 0.85/1.09     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.85/1.09       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.85/1.09  thf('57', plain, (![X3 : $i]: (v2_funct_1 @ (k6_relat_1 @ X3))),
% 0.85/1.09      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.85/1.09  thf('58', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.85/1.09      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.85/1.09  thf('59', plain, (![X3 : $i]: (v2_funct_1 @ (k6_partfun1 @ X3))),
% 0.85/1.09      inference('demod', [status(thm)], ['57', '58'])).
% 0.85/1.09  thf('60', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf('61', plain,
% 0.85/1.09      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf('62', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf('63', plain, ((v1_funct_1 @ sk_C)),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf('64', plain,
% 0.85/1.09      (((zip_tseitin_0 @ sk_D @ sk_C)
% 0.85/1.09        | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.85/1.09        | ((sk_B) != (sk_B)))),
% 0.85/1.09      inference('demod', [status(thm)], ['56', '59', '60', '61', '62', '63'])).
% 0.85/1.09  thf('65', plain,
% 0.85/1.09      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 0.85/1.09      inference('simplify', [status(thm)], ['64'])).
% 0.85/1.09  thf('66', plain,
% 0.85/1.09      (![X37 : $i, X38 : $i]:
% 0.85/1.09         (((X37) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X37 @ X38))),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.85/1.09  thf('67', plain,
% 0.85/1.09      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.85/1.09      inference('sup-', [status(thm)], ['65', '66'])).
% 0.85/1.09  thf('68', plain, (((sk_A) != (k1_xboole_0))),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf('69', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 0.85/1.09      inference('simplify_reflect-', [status(thm)], ['67', '68'])).
% 0.85/1.09  thf('70', plain,
% 0.85/1.09      (![X35 : $i, X36 : $i]:
% 0.85/1.09         ((v2_funct_1 @ X36) | ~ (zip_tseitin_0 @ X36 @ X35))),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.85/1.09  thf('71', plain, ((v2_funct_1 @ sk_D)),
% 0.85/1.09      inference('sup-', [status(thm)], ['69', '70'])).
% 0.85/1.09  thf('72', plain,
% 0.85/1.09      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 0.85/1.09      inference('demod', [status(thm)], ['48', '71'])).
% 0.85/1.09  thf('73', plain,
% 0.85/1.09      ((((k6_partfun1 @ (k1_relat_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.85/1.09        | ~ (v1_relat_1 @ sk_D)
% 0.85/1.09        | ~ (v1_funct_1 @ sk_D)
% 0.85/1.09        | ~ (v2_funct_1 @ sk_D))),
% 0.85/1.09      inference('sup+', [status(thm)], ['2', '72'])).
% 0.85/1.09  thf('74', plain,
% 0.85/1.09      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf(cc1_relset_1, axiom,
% 0.85/1.09    (![A:$i,B:$i,C:$i]:
% 0.85/1.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.85/1.09       ( v1_relat_1 @ C ) ))).
% 0.85/1.09  thf('75', plain,
% 0.85/1.09      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.85/1.09         ((v1_relat_1 @ X7)
% 0.85/1.09          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.85/1.09      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.85/1.09  thf('76', plain, ((v1_relat_1 @ sk_D)),
% 0.85/1.09      inference('sup-', [status(thm)], ['74', '75'])).
% 0.85/1.09  thf('77', plain, ((v1_funct_1 @ sk_D)),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf('78', plain, ((v2_funct_1 @ sk_D)),
% 0.85/1.09      inference('sup-', [status(thm)], ['69', '70'])).
% 0.85/1.09  thf('79', plain,
% 0.85/1.09      (((k6_partfun1 @ (k1_relat_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 0.85/1.09      inference('demod', [status(thm)], ['73', '76', '77', '78'])).
% 0.85/1.09  thf(t71_relat_1, axiom,
% 0.85/1.09    (![A:$i]:
% 0.85/1.09     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.85/1.09       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.85/1.09  thf('80', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 0.85/1.09      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.85/1.09  thf('81', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.85/1.09      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.85/1.09  thf('82', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 0.85/1.09      inference('demod', [status(thm)], ['80', '81'])).
% 0.85/1.09  thf('83', plain,
% 0.85/1.09      (((k1_relat_1 @ (k6_partfun1 @ sk_B)) = (k1_relat_1 @ sk_D))),
% 0.85/1.09      inference('sup+', [status(thm)], ['79', '82'])).
% 0.85/1.09  thf('84', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 0.85/1.09      inference('demod', [status(thm)], ['80', '81'])).
% 0.85/1.09  thf('85', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.85/1.09      inference('demod', [status(thm)], ['83', '84'])).
% 0.85/1.09  thf('86', plain,
% 0.85/1.09      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf('87', plain,
% 0.85/1.09      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf(redefinition_k1_partfun1, axiom,
% 0.85/1.09    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.85/1.09     ( ( ( v1_funct_1 @ E ) & 
% 0.85/1.09         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.85/1.09         ( v1_funct_1 @ F ) & 
% 0.85/1.09         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.85/1.09       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.85/1.09  thf('88', plain,
% 0.85/1.09      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.85/1.09         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.85/1.09          | ~ (v1_funct_1 @ X24)
% 0.85/1.09          | ~ (v1_funct_1 @ X27)
% 0.85/1.09          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.85/1.09          | ((k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27)
% 0.85/1.09              = (k5_relat_1 @ X24 @ X27)))),
% 0.85/1.09      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.85/1.09  thf('89', plain,
% 0.85/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.09         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.85/1.09            = (k5_relat_1 @ sk_C @ X0))
% 0.85/1.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.85/1.09          | ~ (v1_funct_1 @ X0)
% 0.85/1.09          | ~ (v1_funct_1 @ sk_C))),
% 0.85/1.09      inference('sup-', [status(thm)], ['87', '88'])).
% 0.85/1.09  thf('90', plain, ((v1_funct_1 @ sk_C)),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf('91', plain,
% 0.85/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.09         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.85/1.09            = (k5_relat_1 @ sk_C @ X0))
% 0.85/1.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.85/1.09          | ~ (v1_funct_1 @ X0))),
% 0.85/1.09      inference('demod', [status(thm)], ['89', '90'])).
% 0.85/1.09  thf('92', plain,
% 0.85/1.09      ((~ (v1_funct_1 @ sk_D)
% 0.85/1.09        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.85/1.09            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.85/1.09      inference('sup-', [status(thm)], ['86', '91'])).
% 0.85/1.09  thf('93', plain, ((v1_funct_1 @ sk_D)),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf('94', plain,
% 0.85/1.09      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.85/1.09         = (k6_partfun1 @ sk_A))),
% 0.85/1.09      inference('demod', [status(thm)], ['26', '29'])).
% 0.85/1.09  thf('95', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.85/1.09      inference('demod', [status(thm)], ['92', '93', '94'])).
% 0.85/1.09  thf(t63_funct_1, axiom,
% 0.85/1.09    (![A:$i]:
% 0.85/1.09     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.85/1.09       ( ![B:$i]:
% 0.85/1.09         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.85/1.09           ( ( ( v2_funct_1 @ A ) & 
% 0.85/1.09               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.85/1.09               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.85/1.09             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.85/1.09  thf('96', plain,
% 0.85/1.09      (![X5 : $i, X6 : $i]:
% 0.85/1.09         (~ (v1_relat_1 @ X5)
% 0.85/1.09          | ~ (v1_funct_1 @ X5)
% 0.85/1.09          | ((X5) = (k2_funct_1 @ X6))
% 0.85/1.09          | ((k5_relat_1 @ X6 @ X5) != (k6_relat_1 @ (k1_relat_1 @ X6)))
% 0.85/1.09          | ((k2_relat_1 @ X6) != (k1_relat_1 @ X5))
% 0.85/1.09          | ~ (v2_funct_1 @ X6)
% 0.85/1.09          | ~ (v1_funct_1 @ X6)
% 0.85/1.09          | ~ (v1_relat_1 @ X6))),
% 0.85/1.09      inference('cnf', [status(esa)], [t63_funct_1])).
% 0.85/1.09  thf('97', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.85/1.09      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.85/1.09  thf('98', plain,
% 0.85/1.09      (![X5 : $i, X6 : $i]:
% 0.85/1.09         (~ (v1_relat_1 @ X5)
% 0.85/1.09          | ~ (v1_funct_1 @ X5)
% 0.85/1.09          | ((X5) = (k2_funct_1 @ X6))
% 0.85/1.09          | ((k5_relat_1 @ X6 @ X5) != (k6_partfun1 @ (k1_relat_1 @ X6)))
% 0.85/1.09          | ((k2_relat_1 @ X6) != (k1_relat_1 @ X5))
% 0.85/1.09          | ~ (v2_funct_1 @ X6)
% 0.85/1.09          | ~ (v1_funct_1 @ X6)
% 0.85/1.09          | ~ (v1_relat_1 @ X6))),
% 0.85/1.09      inference('demod', [status(thm)], ['96', '97'])).
% 0.85/1.09  thf('99', plain,
% 0.85/1.09      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 0.85/1.09        | ~ (v1_relat_1 @ sk_C)
% 0.85/1.09        | ~ (v1_funct_1 @ sk_C)
% 0.85/1.09        | ~ (v2_funct_1 @ sk_C)
% 0.85/1.09        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.85/1.09        | ((sk_D) = (k2_funct_1 @ sk_C))
% 0.85/1.09        | ~ (v1_funct_1 @ sk_D)
% 0.85/1.09        | ~ (v1_relat_1 @ sk_D))),
% 0.85/1.09      inference('sup-', [status(thm)], ['95', '98'])).
% 0.85/1.09  thf('100', plain,
% 0.85/1.09      (![X4 : $i]:
% 0.85/1.09         (~ (v2_funct_1 @ X4)
% 0.85/1.09          | ((k5_relat_1 @ X4 @ (k2_funct_1 @ X4))
% 0.85/1.09              = (k6_partfun1 @ (k1_relat_1 @ X4)))
% 0.85/1.09          | ~ (v1_funct_1 @ X4)
% 0.85/1.09          | ~ (v1_relat_1 @ X4))),
% 0.85/1.09      inference('demod', [status(thm)], ['0', '1'])).
% 0.85/1.09  thf('101', plain,
% 0.85/1.09      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf('102', plain,
% 0.85/1.09      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.85/1.09         (((X44) = (k1_xboole_0))
% 0.85/1.09          | ~ (v1_funct_1 @ X45)
% 0.85/1.09          | ~ (v1_funct_2 @ X45 @ X46 @ X44)
% 0.85/1.09          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X44)))
% 0.85/1.09          | ((k5_relat_1 @ X45 @ (k2_funct_1 @ X45)) = (k6_partfun1 @ X46))
% 0.85/1.09          | ~ (v2_funct_1 @ X45)
% 0.85/1.09          | ((k2_relset_1 @ X46 @ X44 @ X45) != (X44)))),
% 0.85/1.09      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.85/1.09  thf('103', plain,
% 0.85/1.09      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.85/1.09        | ~ (v2_funct_1 @ sk_C)
% 0.85/1.09        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.85/1.09        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.85/1.09        | ~ (v1_funct_1 @ sk_C)
% 0.85/1.09        | ((sk_B) = (k1_xboole_0)))),
% 0.85/1.09      inference('sup-', [status(thm)], ['101', '102'])).
% 0.85/1.09  thf('104', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf('105', plain, ((v2_funct_1 @ sk_C)),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf('106', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf('107', plain, ((v1_funct_1 @ sk_C)),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf('108', plain,
% 0.85/1.09      ((((sk_B) != (sk_B))
% 0.85/1.09        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.85/1.09        | ((sk_B) = (k1_xboole_0)))),
% 0.85/1.09      inference('demod', [status(thm)], ['103', '104', '105', '106', '107'])).
% 0.85/1.09  thf('109', plain,
% 0.85/1.09      ((((sk_B) = (k1_xboole_0))
% 0.85/1.09        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 0.85/1.09      inference('simplify', [status(thm)], ['108'])).
% 0.85/1.09  thf('110', plain, (((sk_B) != (k1_xboole_0))),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf('111', plain,
% 0.85/1.09      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 0.85/1.09      inference('simplify_reflect-', [status(thm)], ['109', '110'])).
% 0.85/1.09  thf('112', plain,
% 0.85/1.09      ((((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.85/1.09        | ~ (v1_relat_1 @ sk_C)
% 0.85/1.09        | ~ (v1_funct_1 @ sk_C)
% 0.85/1.09        | ~ (v2_funct_1 @ sk_C))),
% 0.85/1.09      inference('sup+', [status(thm)], ['100', '111'])).
% 0.85/1.09  thf('113', plain,
% 0.85/1.09      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf('114', plain,
% 0.85/1.09      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.85/1.09         ((v1_relat_1 @ X7)
% 0.85/1.09          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.85/1.09      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.85/1.09  thf('115', plain, ((v1_relat_1 @ sk_C)),
% 0.85/1.09      inference('sup-', [status(thm)], ['113', '114'])).
% 0.85/1.09  thf('116', plain, ((v1_funct_1 @ sk_C)),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf('117', plain, ((v2_funct_1 @ sk_C)),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf('118', plain,
% 0.85/1.09      (((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 0.85/1.09      inference('demod', [status(thm)], ['112', '115', '116', '117'])).
% 0.85/1.09  thf('119', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 0.85/1.09      inference('demod', [status(thm)], ['80', '81'])).
% 0.85/1.09  thf('120', plain,
% 0.85/1.09      (((k1_relat_1 @ (k6_partfun1 @ sk_A)) = (k1_relat_1 @ sk_C))),
% 0.85/1.09      inference('sup+', [status(thm)], ['118', '119'])).
% 0.85/1.09  thf('121', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 0.85/1.09      inference('demod', [status(thm)], ['80', '81'])).
% 0.85/1.09  thf('122', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.85/1.09      inference('demod', [status(thm)], ['120', '121'])).
% 0.85/1.09  thf('123', plain, ((v1_relat_1 @ sk_C)),
% 0.85/1.09      inference('sup-', [status(thm)], ['113', '114'])).
% 0.85/1.09  thf('124', plain, ((v1_funct_1 @ sk_C)),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf('125', plain, ((v2_funct_1 @ sk_C)),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf('126', plain,
% 0.85/1.09      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf('127', plain,
% 0.85/1.09      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.85/1.09         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 0.85/1.09          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.85/1.09      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.85/1.09  thf('128', plain,
% 0.85/1.09      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.85/1.09      inference('sup-', [status(thm)], ['126', '127'])).
% 0.85/1.09  thf('129', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf('130', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.85/1.09      inference('sup+', [status(thm)], ['128', '129'])).
% 0.85/1.09  thf('131', plain, ((v1_funct_1 @ sk_D)),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf('132', plain, ((v1_relat_1 @ sk_D)),
% 0.85/1.09      inference('sup-', [status(thm)], ['74', '75'])).
% 0.85/1.09  thf('133', plain,
% 0.85/1.09      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 0.85/1.09        | ((sk_B) != (k1_relat_1 @ sk_D))
% 0.85/1.09        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 0.85/1.09      inference('demod', [status(thm)],
% 0.85/1.09                ['99', '122', '123', '124', '125', '130', '131', '132'])).
% 0.85/1.09  thf('134', plain,
% 0.85/1.09      ((((sk_D) = (k2_funct_1 @ sk_C)) | ((sk_B) != (k1_relat_1 @ sk_D)))),
% 0.85/1.09      inference('simplify', [status(thm)], ['133'])).
% 0.85/1.09  thf('135', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.85/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.09  thf('136', plain, (((sk_B) != (k1_relat_1 @ sk_D))),
% 0.85/1.09      inference('simplify_reflect-', [status(thm)], ['134', '135'])).
% 0.85/1.09  thf('137', plain, ($false),
% 0.85/1.09      inference('simplify_reflect-', [status(thm)], ['85', '136'])).
% 0.85/1.09  
% 0.85/1.09  % SZS output end Refutation
% 0.85/1.09  
% 0.85/1.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

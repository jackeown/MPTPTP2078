%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.77jYBrC3iw

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:26 EST 2020

% Result     : Theorem 1.07s
% Output     : Refutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :  288 (3558 expanded)
%              Number of leaves         :   49 (1073 expanded)
%              Depth                    :   28
%              Number of atoms          : 2807 (88583 expanded)
%              Number of equality atoms :  205 (5648 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('2',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('4',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['2','3'])).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('5',plain,(
    ! [X4: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X4 ) )
        = X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('6',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) )
    = sk_D ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
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

thf('9',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( ( k1_partfun1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30 )
        = ( k5_relat_1 @ X27 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
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

thf('18',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X20 @ X21 @ X23 @ X24 @ X19 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('25',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( X15 = X18 )
      | ~ ( r2_relset_1 @ X16 @ X17 @ X15 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','26'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('28',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('29',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['13','14','29'])).

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

thf('31',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( X13
        = ( k2_funct_1 @ X14 ) )
      | ( ( k5_relat_1 @ X13 @ X14 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X14 ) ) )
      | ( ( k2_relat_1 @ X13 )
       != ( k1_relat_1 @ X14 ) )
      | ~ ( v2_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('32',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('33',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( X13
        = ( k2_funct_1 @ X14 ) )
      | ( ( k5_relat_1 @ X13 @ X14 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X14 ) ) )
      | ( ( k2_relat_1 @ X13 )
       != ( k1_relat_1 @ X14 ) )
      | ~ ( v2_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
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
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['2','3'])).

thf('36',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('38',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( X47 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_funct_2 @ X48 @ X49 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X47 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X48 ) @ X48 )
        = ( k6_partfun1 @ X47 ) )
      | ~ ( v2_funct_1 @ X48 )
      | ( ( k2_relset_1 @ X49 @ X47 @ X48 )
       != X47 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('39',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('43',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_funct_1 @ X7 )
        = ( k4_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('49',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['44','49','50'])).

thf('52',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['44','49','50'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('53',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X12 ) @ X12 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('54',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('55',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X12 ) @ X12 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['52','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('58',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf('61',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( sk_B != sk_B )
    | ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40','41','51','60','61','62'])).

thf('64',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('67',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('68',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('69',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X5 ) )
      = X5 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X5 ) )
      = X5 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('72',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('75',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['34','35','36','72','73','74'])).

thf('76',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('77',plain,(
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

thf('78',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( zip_tseitin_0 @ X42 @ X45 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X46 @ X43 @ X43 @ X44 @ X45 @ X42 ) )
      | ( zip_tseitin_1 @ X44 @ X43 )
      | ( ( k2_relset_1 @ X46 @ X43 @ X45 )
       != X43 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X43 )
      | ~ ( v1_funct_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('79',plain,(
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
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['76','82'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('84',plain,(
    ! [X10: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('85',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('86',plain,(
    ! [X10: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X10 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['83','86','87','88','89','90'])).

thf('92',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X40: $i,X41: $i] :
      ( ( X40 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('94',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X38: $i,X39: $i] :
      ( ( v2_funct_1 @ X39 )
      | ~ ( zip_tseitin_0 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('98',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['75','98'])).

thf('100',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_funct_1 @ X7 )
        = ( k4_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('102',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k2_funct_1 @ sk_D )
      = ( k4_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['2','3'])).

thf('104',plain,
    ( ( ( k2_funct_1 @ sk_D )
      = ( k4_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['96','97'])).

thf('106',plain,
    ( ( k2_funct_1 @ sk_D )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X12 ) @ X12 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('108',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ sk_D )
      = ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['2','3'])).

thf('110',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['96','97'])).

thf('112',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ sk_D )
    = ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['108','109','110','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( X47 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_funct_2 @ X48 @ X49 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X47 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X48 ) @ X48 )
        = ( k6_partfun1 @ X47 ) )
      | ~ ( v2_funct_1 @ X48 )
      | ( ( k2_relset_1 @ X49 @ X47 @ X48 )
       != X47 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('115',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_D ) @ sk_D )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_D ) @ sk_D )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('119',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_D ) @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('122',plain,(
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

thf('123',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( r2_relset_1 @ X35 @ X35 @ ( k1_partfun1 @ X35 @ X36 @ X36 @ X35 @ X34 @ X37 ) @ ( k6_partfun1 @ X35 ) )
      | ( ( k2_relset_1 @ X36 @ X35 @ X37 )
        = X35 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X37 @ X36 @ X35 )
      | ~ ( v1_funct_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['121','127'])).

thf('129',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('130',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( r2_relset_1 @ X16 @ X17 @ X15 @ X18 )
      | ( X15 != X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('131',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_relset_1 @ X16 @ X17 @ X18 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['129','131'])).

thf('133',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['128','132','133','134','135'])).

thf('137',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_D ) @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['120','136'])).

thf('138',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_D ) @ sk_D )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['96','97'])).

thf('140',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_D ) @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,
    ( ( k2_funct_1 @ sk_D )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('142',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,
    ( ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('sup+',[status(thm)],['112','142'])).

thf('144',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X5 ) )
      = X5 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('145',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X5 ) )
      = X5 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('147',plain,
    ( sk_A
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( k2_funct_1 @ sk_D )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['104','105'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('149',plain,(
    ! [X8: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('150',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('151',plain,(
    ! [X11: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('152',plain,(
    ! [X8: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('153',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('154',plain,(
    ! [X11: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('155',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('156',plain,(
    ! [X8: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('157',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_funct_1 @ X7 )
        = ( k4_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['155','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['154','160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    ! [X11: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['153','164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['152','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['151','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['170','173'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['150','175'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['149','177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['178'])).

thf('180',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k5_relat_1 @ X12 @ ( k2_funct_1 @ X12 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('181',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('182',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k5_relat_1 @ X12 @ ( k2_funct_1 @ X12 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['179','182'])).

thf('184',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k4_relat_1 @ sk_D ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) @ ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) ) ) ) ),
    inference('sup-',[status(thm)],['148','183'])).

thf('185',plain,
    ( ( k2_funct_1 @ sk_D )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('187',plain,
    ( ( ( k2_funct_1 @ ( k4_relat_1 @ sk_D ) )
      = ( k4_relat_1 @ ( k2_funct_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['185','186'])).

thf('188',plain,
    ( ( k2_funct_1 @ sk_D )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('189',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) )
    = sk_D ),
    inference('sup-',[status(thm)],['4','5'])).

thf('190',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['2','3'])).

thf('191',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['96','97'])).

thf('193',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['187','188','189','190','191','192'])).

thf('194',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['2','3'])).

thf('195',plain,
    ( ( k2_funct_1 @ sk_D )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('196',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['187','188','189','190','191','192'])).

thf('197',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['96','97'])).

thf('198',plain,
    ( ( k2_funct_1 @ sk_D )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('199',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['187','188','189','190','191','192'])).

thf('200',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['96','97'])).

thf('202',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['2','3'])).

thf('204',plain,
    ( ( k2_funct_1 @ sk_D )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('205',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['187','188','189','190','191','192'])).

thf('206',plain,
    ( ( k2_funct_1 @ sk_D )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('207',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['187','188','189','190','191','192'])).

thf('208',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( X47 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_funct_2 @ X48 @ X49 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X47 ) ) )
      | ( ( k5_relat_1 @ X48 @ ( k2_funct_1 @ X48 ) )
        = ( k6_partfun1 @ X49 ) )
      | ~ ( v2_funct_1 @ X48 )
      | ( ( k2_relset_1 @ X49 @ X47 @ X48 )
       != X47 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('210',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['210','211','212'])).

thf('214',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['213','214'])).

thf('216',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['128','132','133','134','135'])).

thf('217',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['215','216'])).

thf('218',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['217'])).

thf('219',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['96','97'])).

thf('220',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['218','219'])).

thf('221',plain,
    ( ( k2_funct_1 @ sk_D )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('222',plain,
    ( ( k5_relat_1 @ sk_D @ ( k4_relat_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['220','221'])).

thf('223',plain,
    ( ( k2_funct_1 @ sk_D )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('224',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['187','188','189','190','191','192'])).

thf('225',plain,
    ( ( k6_partfun1 @ sk_B )
    = ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['184','193','194','195','196','197','198','199','200','201','202','203','204','205','206','207','222','223','224'])).

thf('226',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X5 ) )
      = X5 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('227',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['225','226'])).

thf('228',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X5 ) )
      = X5 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('229',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['227','228'])).

thf('230',plain,
    ( ( k2_funct_1 @ sk_D )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('231',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ( sk_B != sk_B )
    | ( sk_C
      = ( k4_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['99','147','229','230'])).

thf('232',plain,
    ( sk_C
    = ( k4_relat_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['231'])).

thf('233',plain,
    ( ( k4_relat_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['6','232'])).

thf('234',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['44','49','50'])).

thf('236',plain,(
    sk_D
 != ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['234','235'])).

thf('237',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['233','236'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.77jYBrC3iw
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:12:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.07/1.30  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.07/1.30  % Solved by: fo/fo7.sh
% 1.07/1.30  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.07/1.30  % done 1085 iterations in 0.830s
% 1.07/1.30  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.07/1.30  % SZS output start Refutation
% 1.07/1.30  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.07/1.30  thf(sk_C_type, type, sk_C: $i).
% 1.07/1.30  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.07/1.30  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.07/1.30  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.07/1.30  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.07/1.30  thf(sk_A_type, type, sk_A: $i).
% 1.07/1.30  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.07/1.30  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 1.07/1.30  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.07/1.30  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 1.07/1.30  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.07/1.30  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.07/1.30  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.07/1.30  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.07/1.30  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.07/1.30  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.07/1.30  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.07/1.30  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.07/1.30  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.07/1.30  thf(sk_B_type, type, sk_B: $i).
% 1.07/1.30  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.07/1.30  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.07/1.30  thf(sk_D_type, type, sk_D: $i).
% 1.07/1.30  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.07/1.30  thf(t36_funct_2, conjecture,
% 1.07/1.30    (![A:$i,B:$i,C:$i]:
% 1.07/1.30     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.07/1.30         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.07/1.30       ( ![D:$i]:
% 1.07/1.30         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.07/1.30             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.07/1.30           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.07/1.30               ( r2_relset_1 @
% 1.07/1.30                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.07/1.30                 ( k6_partfun1 @ A ) ) & 
% 1.07/1.30               ( v2_funct_1 @ C ) ) =>
% 1.07/1.30             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.07/1.30               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.07/1.30  thf(zf_stmt_0, negated_conjecture,
% 1.07/1.30    (~( ![A:$i,B:$i,C:$i]:
% 1.07/1.30        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.07/1.30            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.07/1.30          ( ![D:$i]:
% 1.07/1.30            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.07/1.30                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.07/1.30              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.07/1.30                  ( r2_relset_1 @
% 1.07/1.30                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.07/1.30                    ( k6_partfun1 @ A ) ) & 
% 1.07/1.30                  ( v2_funct_1 @ C ) ) =>
% 1.07/1.30                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.07/1.30                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.07/1.30    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.07/1.30  thf('0', plain,
% 1.07/1.30      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf(cc2_relat_1, axiom,
% 1.07/1.30    (![A:$i]:
% 1.07/1.30     ( ( v1_relat_1 @ A ) =>
% 1.07/1.30       ( ![B:$i]:
% 1.07/1.30         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.07/1.30  thf('1', plain,
% 1.07/1.30      (![X0 : $i, X1 : $i]:
% 1.07/1.30         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.07/1.30          | (v1_relat_1 @ X0)
% 1.07/1.30          | ~ (v1_relat_1 @ X1))),
% 1.07/1.30      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.07/1.30  thf('2', plain,
% 1.07/1.30      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 1.07/1.30      inference('sup-', [status(thm)], ['0', '1'])).
% 1.07/1.30  thf(fc6_relat_1, axiom,
% 1.07/1.30    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.07/1.30  thf('3', plain,
% 1.07/1.30      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.07/1.30      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.07/1.30  thf('4', plain, ((v1_relat_1 @ sk_D)),
% 1.07/1.30      inference('demod', [status(thm)], ['2', '3'])).
% 1.07/1.30  thf(involutiveness_k4_relat_1, axiom,
% 1.07/1.30    (![A:$i]:
% 1.07/1.30     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 1.07/1.30  thf('5', plain,
% 1.07/1.30      (![X4 : $i]:
% 1.07/1.30         (((k4_relat_1 @ (k4_relat_1 @ X4)) = (X4)) | ~ (v1_relat_1 @ X4))),
% 1.07/1.30      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 1.07/1.30  thf('6', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 1.07/1.30      inference('sup-', [status(thm)], ['4', '5'])).
% 1.07/1.30  thf('7', plain,
% 1.07/1.30      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('8', plain,
% 1.07/1.30      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf(redefinition_k1_partfun1, axiom,
% 1.07/1.30    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.07/1.30     ( ( ( v1_funct_1 @ E ) & 
% 1.07/1.30         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.07/1.30         ( v1_funct_1 @ F ) & 
% 1.07/1.30         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.07/1.30       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.07/1.30  thf('9', plain,
% 1.07/1.30      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 1.07/1.30         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 1.07/1.30          | ~ (v1_funct_1 @ X27)
% 1.07/1.30          | ~ (v1_funct_1 @ X30)
% 1.07/1.30          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 1.07/1.30          | ((k1_partfun1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30)
% 1.07/1.30              = (k5_relat_1 @ X27 @ X30)))),
% 1.07/1.30      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.07/1.30  thf('10', plain,
% 1.07/1.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.30         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.07/1.30            = (k5_relat_1 @ sk_C @ X0))
% 1.07/1.30          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.07/1.30          | ~ (v1_funct_1 @ X0)
% 1.07/1.30          | ~ (v1_funct_1 @ sk_C))),
% 1.07/1.30      inference('sup-', [status(thm)], ['8', '9'])).
% 1.07/1.30  thf('11', plain, ((v1_funct_1 @ sk_C)),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('12', plain,
% 1.07/1.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.30         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.07/1.30            = (k5_relat_1 @ sk_C @ X0))
% 1.07/1.30          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.07/1.30          | ~ (v1_funct_1 @ X0))),
% 1.07/1.30      inference('demod', [status(thm)], ['10', '11'])).
% 1.07/1.30  thf('13', plain,
% 1.07/1.30      ((~ (v1_funct_1 @ sk_D)
% 1.07/1.30        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.07/1.30            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.07/1.30      inference('sup-', [status(thm)], ['7', '12'])).
% 1.07/1.30  thf('14', plain, ((v1_funct_1 @ sk_D)),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('15', plain,
% 1.07/1.30      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.07/1.30        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.07/1.30        (k6_partfun1 @ sk_A))),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('16', plain,
% 1.07/1.30      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('17', plain,
% 1.07/1.30      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf(dt_k1_partfun1, axiom,
% 1.07/1.30    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.07/1.30     ( ( ( v1_funct_1 @ E ) & 
% 1.07/1.30         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.07/1.30         ( v1_funct_1 @ F ) & 
% 1.07/1.30         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.07/1.30       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.07/1.30         ( m1_subset_1 @
% 1.07/1.30           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.07/1.30           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.07/1.30  thf('18', plain,
% 1.07/1.30      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 1.07/1.30         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.07/1.30          | ~ (v1_funct_1 @ X19)
% 1.07/1.30          | ~ (v1_funct_1 @ X22)
% 1.07/1.30          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 1.07/1.30          | (m1_subset_1 @ (k1_partfun1 @ X20 @ X21 @ X23 @ X24 @ X19 @ X22) @ 
% 1.07/1.30             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X24))))),
% 1.07/1.30      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.07/1.30  thf('19', plain,
% 1.07/1.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.30         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.07/1.30           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.07/1.30          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.07/1.30          | ~ (v1_funct_1 @ X1)
% 1.07/1.30          | ~ (v1_funct_1 @ sk_C))),
% 1.07/1.30      inference('sup-', [status(thm)], ['17', '18'])).
% 1.07/1.30  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('21', plain,
% 1.07/1.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.30         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.07/1.30           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.07/1.30          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.07/1.30          | ~ (v1_funct_1 @ X1))),
% 1.07/1.30      inference('demod', [status(thm)], ['19', '20'])).
% 1.07/1.30  thf('22', plain,
% 1.07/1.30      ((~ (v1_funct_1 @ sk_D)
% 1.07/1.30        | (m1_subset_1 @ 
% 1.07/1.30           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.07/1.30           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.07/1.30      inference('sup-', [status(thm)], ['16', '21'])).
% 1.07/1.30  thf('23', plain, ((v1_funct_1 @ sk_D)),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('24', plain,
% 1.07/1.30      ((m1_subset_1 @ 
% 1.07/1.30        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.07/1.30        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.30      inference('demod', [status(thm)], ['22', '23'])).
% 1.07/1.30  thf(redefinition_r2_relset_1, axiom,
% 1.07/1.30    (![A:$i,B:$i,C:$i,D:$i]:
% 1.07/1.30     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.07/1.30         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.07/1.30       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.07/1.30  thf('25', plain,
% 1.07/1.30      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 1.07/1.30         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 1.07/1.30          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 1.07/1.30          | ((X15) = (X18))
% 1.07/1.30          | ~ (r2_relset_1 @ X16 @ X17 @ X15 @ X18))),
% 1.07/1.30      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.07/1.30  thf('26', plain,
% 1.07/1.30      (![X0 : $i]:
% 1.07/1.30         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.07/1.30             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 1.07/1.30          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 1.07/1.30          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.07/1.30      inference('sup-', [status(thm)], ['24', '25'])).
% 1.07/1.30  thf('27', plain,
% 1.07/1.30      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.07/1.30           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.07/1.30        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.07/1.30            = (k6_partfun1 @ sk_A)))),
% 1.07/1.30      inference('sup-', [status(thm)], ['15', '26'])).
% 1.07/1.30  thf(dt_k6_partfun1, axiom,
% 1.07/1.30    (![A:$i]:
% 1.07/1.30     ( ( m1_subset_1 @
% 1.07/1.30         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 1.07/1.30       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 1.07/1.30  thf('28', plain,
% 1.07/1.30      (![X26 : $i]:
% 1.07/1.30         (m1_subset_1 @ (k6_partfun1 @ X26) @ 
% 1.07/1.30          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X26)))),
% 1.07/1.30      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.07/1.30  thf('29', plain,
% 1.07/1.30      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.07/1.30         = (k6_partfun1 @ sk_A))),
% 1.07/1.30      inference('demod', [status(thm)], ['27', '28'])).
% 1.07/1.30  thf('30', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 1.07/1.30      inference('demod', [status(thm)], ['13', '14', '29'])).
% 1.07/1.30  thf(t64_funct_1, axiom,
% 1.07/1.30    (![A:$i]:
% 1.07/1.30     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.07/1.30       ( ![B:$i]:
% 1.07/1.30         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.07/1.30           ( ( ( v2_funct_1 @ A ) & 
% 1.07/1.30               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 1.07/1.30               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 1.07/1.30             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.07/1.30  thf('31', plain,
% 1.07/1.30      (![X13 : $i, X14 : $i]:
% 1.07/1.30         (~ (v1_relat_1 @ X13)
% 1.07/1.30          | ~ (v1_funct_1 @ X13)
% 1.07/1.30          | ((X13) = (k2_funct_1 @ X14))
% 1.07/1.30          | ((k5_relat_1 @ X13 @ X14) != (k6_relat_1 @ (k2_relat_1 @ X14)))
% 1.07/1.30          | ((k2_relat_1 @ X13) != (k1_relat_1 @ X14))
% 1.07/1.30          | ~ (v2_funct_1 @ X14)
% 1.07/1.30          | ~ (v1_funct_1 @ X14)
% 1.07/1.30          | ~ (v1_relat_1 @ X14))),
% 1.07/1.30      inference('cnf', [status(esa)], [t64_funct_1])).
% 1.07/1.30  thf(redefinition_k6_partfun1, axiom,
% 1.07/1.30    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.07/1.30  thf('32', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 1.07/1.30      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.07/1.30  thf('33', plain,
% 1.07/1.30      (![X13 : $i, X14 : $i]:
% 1.07/1.30         (~ (v1_relat_1 @ X13)
% 1.07/1.30          | ~ (v1_funct_1 @ X13)
% 1.07/1.30          | ((X13) = (k2_funct_1 @ X14))
% 1.07/1.30          | ((k5_relat_1 @ X13 @ X14) != (k6_partfun1 @ (k2_relat_1 @ X14)))
% 1.07/1.30          | ((k2_relat_1 @ X13) != (k1_relat_1 @ X14))
% 1.07/1.30          | ~ (v2_funct_1 @ X14)
% 1.07/1.30          | ~ (v1_funct_1 @ X14)
% 1.07/1.30          | ~ (v1_relat_1 @ X14))),
% 1.07/1.30      inference('demod', [status(thm)], ['31', '32'])).
% 1.07/1.30  thf('34', plain,
% 1.07/1.30      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 1.07/1.30        | ~ (v1_relat_1 @ sk_D)
% 1.07/1.30        | ~ (v1_funct_1 @ sk_D)
% 1.07/1.30        | ~ (v2_funct_1 @ sk_D)
% 1.07/1.30        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 1.07/1.30        | ((sk_C) = (k2_funct_1 @ sk_D))
% 1.07/1.30        | ~ (v1_funct_1 @ sk_C)
% 1.07/1.30        | ~ (v1_relat_1 @ sk_C))),
% 1.07/1.30      inference('sup-', [status(thm)], ['30', '33'])).
% 1.07/1.30  thf('35', plain, ((v1_relat_1 @ sk_D)),
% 1.07/1.30      inference('demod', [status(thm)], ['2', '3'])).
% 1.07/1.30  thf('36', plain, ((v1_funct_1 @ sk_D)),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('37', plain,
% 1.07/1.30      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf(t35_funct_2, axiom,
% 1.07/1.30    (![A:$i,B:$i,C:$i]:
% 1.07/1.30     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.07/1.30         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.07/1.30       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.07/1.30         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.07/1.30           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 1.07/1.30             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 1.07/1.30  thf('38', plain,
% 1.07/1.30      (![X47 : $i, X48 : $i, X49 : $i]:
% 1.07/1.30         (((X47) = (k1_xboole_0))
% 1.07/1.30          | ~ (v1_funct_1 @ X48)
% 1.07/1.30          | ~ (v1_funct_2 @ X48 @ X49 @ X47)
% 1.07/1.30          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X47)))
% 1.07/1.30          | ((k5_relat_1 @ (k2_funct_1 @ X48) @ X48) = (k6_partfun1 @ X47))
% 1.07/1.30          | ~ (v2_funct_1 @ X48)
% 1.07/1.30          | ((k2_relset_1 @ X49 @ X47 @ X48) != (X47)))),
% 1.07/1.30      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.07/1.30  thf('39', plain,
% 1.07/1.30      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.07/1.30        | ~ (v2_funct_1 @ sk_C)
% 1.07/1.30        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 1.07/1.30        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.07/1.30        | ~ (v1_funct_1 @ sk_C)
% 1.07/1.30        | ((sk_B) = (k1_xboole_0)))),
% 1.07/1.30      inference('sup-', [status(thm)], ['37', '38'])).
% 1.07/1.30  thf('40', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('41', plain, ((v2_funct_1 @ sk_C)),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('42', plain, ((v1_funct_1 @ sk_C)),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf(d9_funct_1, axiom,
% 1.07/1.30    (![A:$i]:
% 1.07/1.30     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.07/1.30       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 1.07/1.30  thf('43', plain,
% 1.07/1.30      (![X7 : $i]:
% 1.07/1.30         (~ (v2_funct_1 @ X7)
% 1.07/1.30          | ((k2_funct_1 @ X7) = (k4_relat_1 @ X7))
% 1.07/1.30          | ~ (v1_funct_1 @ X7)
% 1.07/1.30          | ~ (v1_relat_1 @ X7))),
% 1.07/1.30      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.07/1.30  thf('44', plain,
% 1.07/1.30      ((~ (v1_relat_1 @ sk_C)
% 1.07/1.30        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 1.07/1.30        | ~ (v2_funct_1 @ sk_C))),
% 1.07/1.30      inference('sup-', [status(thm)], ['42', '43'])).
% 1.07/1.30  thf('45', plain,
% 1.07/1.30      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('46', plain,
% 1.07/1.30      (![X0 : $i, X1 : $i]:
% 1.07/1.30         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.07/1.30          | (v1_relat_1 @ X0)
% 1.07/1.30          | ~ (v1_relat_1 @ X1))),
% 1.07/1.30      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.07/1.30  thf('47', plain,
% 1.07/1.30      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 1.07/1.30      inference('sup-', [status(thm)], ['45', '46'])).
% 1.07/1.30  thf('48', plain,
% 1.07/1.30      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.07/1.30      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.07/1.30  thf('49', plain, ((v1_relat_1 @ sk_C)),
% 1.07/1.30      inference('demod', [status(thm)], ['47', '48'])).
% 1.07/1.30  thf('50', plain, ((v2_funct_1 @ sk_C)),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('51', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.07/1.30      inference('demod', [status(thm)], ['44', '49', '50'])).
% 1.07/1.30  thf('52', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.07/1.30      inference('demod', [status(thm)], ['44', '49', '50'])).
% 1.07/1.30  thf(t61_funct_1, axiom,
% 1.07/1.30    (![A:$i]:
% 1.07/1.30     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.07/1.30       ( ( v2_funct_1 @ A ) =>
% 1.07/1.30         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.07/1.30             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.07/1.30           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.07/1.30             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.07/1.30  thf('53', plain,
% 1.07/1.30      (![X12 : $i]:
% 1.07/1.30         (~ (v2_funct_1 @ X12)
% 1.07/1.30          | ((k5_relat_1 @ (k2_funct_1 @ X12) @ X12)
% 1.07/1.30              = (k6_relat_1 @ (k2_relat_1 @ X12)))
% 1.07/1.30          | ~ (v1_funct_1 @ X12)
% 1.07/1.30          | ~ (v1_relat_1 @ X12))),
% 1.07/1.30      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.07/1.30  thf('54', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 1.07/1.30      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.07/1.30  thf('55', plain,
% 1.07/1.30      (![X12 : $i]:
% 1.07/1.30         (~ (v2_funct_1 @ X12)
% 1.07/1.30          | ((k5_relat_1 @ (k2_funct_1 @ X12) @ X12)
% 1.07/1.30              = (k6_partfun1 @ (k2_relat_1 @ X12)))
% 1.07/1.30          | ~ (v1_funct_1 @ X12)
% 1.07/1.30          | ~ (v1_relat_1 @ X12))),
% 1.07/1.30      inference('demod', [status(thm)], ['53', '54'])).
% 1.07/1.30  thf('56', plain,
% 1.07/1.30      ((((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C)
% 1.07/1.30          = (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 1.07/1.30        | ~ (v1_relat_1 @ sk_C)
% 1.07/1.30        | ~ (v1_funct_1 @ sk_C)
% 1.07/1.30        | ~ (v2_funct_1 @ sk_C))),
% 1.07/1.30      inference('sup+', [status(thm)], ['52', '55'])).
% 1.07/1.30  thf('57', plain, ((v1_relat_1 @ sk_C)),
% 1.07/1.30      inference('demod', [status(thm)], ['47', '48'])).
% 1.07/1.30  thf('58', plain, ((v1_funct_1 @ sk_C)),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('59', plain, ((v2_funct_1 @ sk_C)),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('60', plain,
% 1.07/1.30      (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C)
% 1.07/1.30         = (k6_partfun1 @ (k2_relat_1 @ sk_C)))),
% 1.07/1.30      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 1.07/1.30  thf('61', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('62', plain, ((v1_funct_1 @ sk_C)),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('63', plain,
% 1.07/1.30      ((((sk_B) != (sk_B))
% 1.07/1.30        | ((k6_partfun1 @ (k2_relat_1 @ sk_C)) = (k6_partfun1 @ sk_B))
% 1.07/1.30        | ((sk_B) = (k1_xboole_0)))),
% 1.07/1.30      inference('demod', [status(thm)],
% 1.07/1.30                ['39', '40', '41', '51', '60', '61', '62'])).
% 1.07/1.30  thf('64', plain,
% 1.07/1.30      ((((sk_B) = (k1_xboole_0))
% 1.07/1.30        | ((k6_partfun1 @ (k2_relat_1 @ sk_C)) = (k6_partfun1 @ sk_B)))),
% 1.07/1.30      inference('simplify', [status(thm)], ['63'])).
% 1.07/1.30  thf('65', plain, (((sk_B) != (k1_xboole_0))),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('66', plain,
% 1.07/1.30      (((k6_partfun1 @ (k2_relat_1 @ sk_C)) = (k6_partfun1 @ sk_B))),
% 1.07/1.30      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 1.07/1.30  thf(t71_relat_1, axiom,
% 1.07/1.30    (![A:$i]:
% 1.07/1.30     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.07/1.30       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.07/1.30  thf('67', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 1.07/1.30      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.07/1.30  thf('68', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 1.07/1.30      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.07/1.30  thf('69', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X5)) = (X5))),
% 1.07/1.30      inference('demod', [status(thm)], ['67', '68'])).
% 1.07/1.30  thf('70', plain,
% 1.07/1.30      (((k1_relat_1 @ (k6_partfun1 @ sk_B)) = (k2_relat_1 @ sk_C))),
% 1.07/1.30      inference('sup+', [status(thm)], ['66', '69'])).
% 1.07/1.30  thf('71', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X5)) = (X5))),
% 1.07/1.30      inference('demod', [status(thm)], ['67', '68'])).
% 1.07/1.30  thf('72', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 1.07/1.30      inference('demod', [status(thm)], ['70', '71'])).
% 1.07/1.30  thf('73', plain, ((v1_funct_1 @ sk_C)),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('74', plain, ((v1_relat_1 @ sk_C)),
% 1.07/1.30      inference('demod', [status(thm)], ['47', '48'])).
% 1.07/1.30  thf('75', plain,
% 1.07/1.30      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 1.07/1.30        | ~ (v2_funct_1 @ sk_D)
% 1.07/1.30        | ((sk_B) != (k1_relat_1 @ sk_D))
% 1.07/1.30        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 1.07/1.30      inference('demod', [status(thm)], ['34', '35', '36', '72', '73', '74'])).
% 1.07/1.30  thf('76', plain,
% 1.07/1.30      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.07/1.30         = (k6_partfun1 @ sk_A))),
% 1.07/1.30      inference('demod', [status(thm)], ['27', '28'])).
% 1.07/1.30  thf('77', plain,
% 1.07/1.30      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf(t30_funct_2, axiom,
% 1.07/1.30    (![A:$i,B:$i,C:$i,D:$i]:
% 1.07/1.30     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.07/1.30         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 1.07/1.30       ( ![E:$i]:
% 1.07/1.30         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 1.07/1.30             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 1.07/1.30           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 1.07/1.30               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 1.07/1.30             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 1.07/1.30               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 1.07/1.30  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 1.07/1.30  thf(zf_stmt_2, axiom,
% 1.07/1.30    (![C:$i,B:$i]:
% 1.07/1.30     ( ( zip_tseitin_1 @ C @ B ) =>
% 1.07/1.30       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 1.07/1.30  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.07/1.30  thf(zf_stmt_4, axiom,
% 1.07/1.30    (![E:$i,D:$i]:
% 1.07/1.30     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 1.07/1.30  thf(zf_stmt_5, axiom,
% 1.07/1.30    (![A:$i,B:$i,C:$i,D:$i]:
% 1.07/1.30     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.07/1.30         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.07/1.30       ( ![E:$i]:
% 1.07/1.30         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.07/1.30             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.07/1.30           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 1.07/1.30               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 1.07/1.30             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 1.07/1.30  thf('78', plain,
% 1.07/1.30      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 1.07/1.30         (~ (v1_funct_1 @ X42)
% 1.07/1.30          | ~ (v1_funct_2 @ X42 @ X43 @ X44)
% 1.07/1.30          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 1.07/1.30          | (zip_tseitin_0 @ X42 @ X45)
% 1.07/1.30          | ~ (v2_funct_1 @ (k1_partfun1 @ X46 @ X43 @ X43 @ X44 @ X45 @ X42))
% 1.07/1.30          | (zip_tseitin_1 @ X44 @ X43)
% 1.07/1.30          | ((k2_relset_1 @ X46 @ X43 @ X45) != (X43))
% 1.07/1.30          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X43)))
% 1.07/1.30          | ~ (v1_funct_2 @ X45 @ X46 @ X43)
% 1.07/1.30          | ~ (v1_funct_1 @ X45))),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.07/1.30  thf('79', plain,
% 1.07/1.30      (![X0 : $i, X1 : $i]:
% 1.07/1.30         (~ (v1_funct_1 @ X0)
% 1.07/1.30          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.07/1.30          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.07/1.30          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.07/1.30          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.07/1.30          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.07/1.30          | (zip_tseitin_0 @ sk_D @ X0)
% 1.07/1.30          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.07/1.30          | ~ (v1_funct_1 @ sk_D))),
% 1.07/1.30      inference('sup-', [status(thm)], ['77', '78'])).
% 1.07/1.30  thf('80', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('81', plain, ((v1_funct_1 @ sk_D)),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('82', plain,
% 1.07/1.30      (![X0 : $i, X1 : $i]:
% 1.07/1.30         (~ (v1_funct_1 @ X0)
% 1.07/1.30          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.07/1.30          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.07/1.30          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.07/1.30          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.07/1.30          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.07/1.30          | (zip_tseitin_0 @ sk_D @ X0))),
% 1.07/1.30      inference('demod', [status(thm)], ['79', '80', '81'])).
% 1.07/1.30  thf('83', plain,
% 1.07/1.30      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 1.07/1.30        | (zip_tseitin_0 @ sk_D @ sk_C)
% 1.07/1.30        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.07/1.30        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.07/1.30        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.07/1.30        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.07/1.30        | ~ (v1_funct_1 @ sk_C))),
% 1.07/1.30      inference('sup-', [status(thm)], ['76', '82'])).
% 1.07/1.30  thf(fc4_funct_1, axiom,
% 1.07/1.30    (![A:$i]:
% 1.07/1.30     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.07/1.30       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.07/1.30  thf('84', plain, (![X10 : $i]: (v2_funct_1 @ (k6_relat_1 @ X10))),
% 1.07/1.30      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.07/1.30  thf('85', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 1.07/1.30      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.07/1.30  thf('86', plain, (![X10 : $i]: (v2_funct_1 @ (k6_partfun1 @ X10))),
% 1.07/1.30      inference('demod', [status(thm)], ['84', '85'])).
% 1.07/1.30  thf('87', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('88', plain,
% 1.07/1.30      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('89', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('90', plain, ((v1_funct_1 @ sk_C)),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('91', plain,
% 1.07/1.30      (((zip_tseitin_0 @ sk_D @ sk_C)
% 1.07/1.30        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.07/1.30        | ((sk_B) != (sk_B)))),
% 1.07/1.30      inference('demod', [status(thm)], ['83', '86', '87', '88', '89', '90'])).
% 1.07/1.30  thf('92', plain,
% 1.07/1.30      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 1.07/1.30      inference('simplify', [status(thm)], ['91'])).
% 1.07/1.30  thf('93', plain,
% 1.07/1.30      (![X40 : $i, X41 : $i]:
% 1.07/1.30         (((X40) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X40 @ X41))),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.07/1.30  thf('94', plain,
% 1.07/1.30      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 1.07/1.30      inference('sup-', [status(thm)], ['92', '93'])).
% 1.07/1.30  thf('95', plain, (((sk_A) != (k1_xboole_0))),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('96', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 1.07/1.30      inference('simplify_reflect-', [status(thm)], ['94', '95'])).
% 1.07/1.30  thf('97', plain,
% 1.07/1.30      (![X38 : $i, X39 : $i]:
% 1.07/1.30         ((v2_funct_1 @ X39) | ~ (zip_tseitin_0 @ X39 @ X38))),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.07/1.30  thf('98', plain, ((v2_funct_1 @ sk_D)),
% 1.07/1.30      inference('sup-', [status(thm)], ['96', '97'])).
% 1.07/1.30  thf('99', plain,
% 1.07/1.30      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 1.07/1.30        | ((sk_B) != (k1_relat_1 @ sk_D))
% 1.07/1.30        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 1.07/1.30      inference('demod', [status(thm)], ['75', '98'])).
% 1.07/1.30  thf('100', plain, ((v1_funct_1 @ sk_D)),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('101', plain,
% 1.07/1.30      (![X7 : $i]:
% 1.07/1.30         (~ (v2_funct_1 @ X7)
% 1.07/1.30          | ((k2_funct_1 @ X7) = (k4_relat_1 @ X7))
% 1.07/1.30          | ~ (v1_funct_1 @ X7)
% 1.07/1.30          | ~ (v1_relat_1 @ X7))),
% 1.07/1.30      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.07/1.30  thf('102', plain,
% 1.07/1.30      ((~ (v1_relat_1 @ sk_D)
% 1.07/1.30        | ((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))
% 1.07/1.30        | ~ (v2_funct_1 @ sk_D))),
% 1.07/1.30      inference('sup-', [status(thm)], ['100', '101'])).
% 1.07/1.30  thf('103', plain, ((v1_relat_1 @ sk_D)),
% 1.07/1.30      inference('demod', [status(thm)], ['2', '3'])).
% 1.07/1.30  thf('104', plain,
% 1.07/1.30      ((((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 1.07/1.30      inference('demod', [status(thm)], ['102', '103'])).
% 1.07/1.30  thf('105', plain, ((v2_funct_1 @ sk_D)),
% 1.07/1.30      inference('sup-', [status(thm)], ['96', '97'])).
% 1.07/1.30  thf('106', plain, (((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))),
% 1.07/1.30      inference('demod', [status(thm)], ['104', '105'])).
% 1.07/1.30  thf('107', plain,
% 1.07/1.30      (![X12 : $i]:
% 1.07/1.30         (~ (v2_funct_1 @ X12)
% 1.07/1.30          | ((k5_relat_1 @ (k2_funct_1 @ X12) @ X12)
% 1.07/1.30              = (k6_partfun1 @ (k2_relat_1 @ X12)))
% 1.07/1.30          | ~ (v1_funct_1 @ X12)
% 1.07/1.30          | ~ (v1_relat_1 @ X12))),
% 1.07/1.30      inference('demod', [status(thm)], ['53', '54'])).
% 1.07/1.30  thf('108', plain,
% 1.07/1.30      ((((k5_relat_1 @ (k4_relat_1 @ sk_D) @ sk_D)
% 1.07/1.30          = (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 1.07/1.30        | ~ (v1_relat_1 @ sk_D)
% 1.07/1.30        | ~ (v1_funct_1 @ sk_D)
% 1.07/1.30        | ~ (v2_funct_1 @ sk_D))),
% 1.07/1.30      inference('sup+', [status(thm)], ['106', '107'])).
% 1.07/1.30  thf('109', plain, ((v1_relat_1 @ sk_D)),
% 1.07/1.30      inference('demod', [status(thm)], ['2', '3'])).
% 1.07/1.30  thf('110', plain, ((v1_funct_1 @ sk_D)),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('111', plain, ((v2_funct_1 @ sk_D)),
% 1.07/1.30      inference('sup-', [status(thm)], ['96', '97'])).
% 1.07/1.30  thf('112', plain,
% 1.07/1.30      (((k5_relat_1 @ (k4_relat_1 @ sk_D) @ sk_D)
% 1.07/1.30         = (k6_partfun1 @ (k2_relat_1 @ sk_D)))),
% 1.07/1.30      inference('demod', [status(thm)], ['108', '109', '110', '111'])).
% 1.07/1.30  thf('113', plain,
% 1.07/1.30      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('114', plain,
% 1.07/1.30      (![X47 : $i, X48 : $i, X49 : $i]:
% 1.07/1.30         (((X47) = (k1_xboole_0))
% 1.07/1.30          | ~ (v1_funct_1 @ X48)
% 1.07/1.30          | ~ (v1_funct_2 @ X48 @ X49 @ X47)
% 1.07/1.30          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X47)))
% 1.07/1.30          | ((k5_relat_1 @ (k2_funct_1 @ X48) @ X48) = (k6_partfun1 @ X47))
% 1.07/1.30          | ~ (v2_funct_1 @ X48)
% 1.07/1.30          | ((k2_relset_1 @ X49 @ X47 @ X48) != (X47)))),
% 1.07/1.30      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.07/1.30  thf('115', plain,
% 1.07/1.30      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 1.07/1.30        | ~ (v2_funct_1 @ sk_D)
% 1.07/1.30        | ((k5_relat_1 @ (k2_funct_1 @ sk_D) @ sk_D) = (k6_partfun1 @ sk_A))
% 1.07/1.30        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.07/1.30        | ~ (v1_funct_1 @ sk_D)
% 1.07/1.30        | ((sk_A) = (k1_xboole_0)))),
% 1.07/1.30      inference('sup-', [status(thm)], ['113', '114'])).
% 1.07/1.30  thf('116', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('117', plain, ((v1_funct_1 @ sk_D)),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('118', plain,
% 1.07/1.30      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 1.07/1.30        | ~ (v2_funct_1 @ sk_D)
% 1.07/1.30        | ((k5_relat_1 @ (k2_funct_1 @ sk_D) @ sk_D) = (k6_partfun1 @ sk_A))
% 1.07/1.30        | ((sk_A) = (k1_xboole_0)))),
% 1.07/1.30      inference('demod', [status(thm)], ['115', '116', '117'])).
% 1.07/1.30  thf('119', plain, (((sk_A) != (k1_xboole_0))),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('120', plain,
% 1.07/1.30      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 1.07/1.30        | ~ (v2_funct_1 @ sk_D)
% 1.07/1.30        | ((k5_relat_1 @ (k2_funct_1 @ sk_D) @ sk_D) = (k6_partfun1 @ sk_A)))),
% 1.07/1.30      inference('simplify_reflect-', [status(thm)], ['118', '119'])).
% 1.07/1.30  thf('121', plain,
% 1.07/1.30      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.07/1.30         = (k6_partfun1 @ sk_A))),
% 1.07/1.30      inference('demod', [status(thm)], ['27', '28'])).
% 1.07/1.30  thf('122', plain,
% 1.07/1.30      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf(t24_funct_2, axiom,
% 1.07/1.30    (![A:$i,B:$i,C:$i]:
% 1.07/1.30     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.07/1.30         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.07/1.30       ( ![D:$i]:
% 1.07/1.30         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.07/1.30             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.07/1.30           ( ( r2_relset_1 @
% 1.07/1.30               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 1.07/1.30               ( k6_partfun1 @ B ) ) =>
% 1.07/1.30             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 1.07/1.30  thf('123', plain,
% 1.07/1.30      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 1.07/1.30         (~ (v1_funct_1 @ X34)
% 1.07/1.30          | ~ (v1_funct_2 @ X34 @ X35 @ X36)
% 1.07/1.30          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 1.07/1.30          | ~ (r2_relset_1 @ X35 @ X35 @ 
% 1.07/1.30               (k1_partfun1 @ X35 @ X36 @ X36 @ X35 @ X34 @ X37) @ 
% 1.07/1.30               (k6_partfun1 @ X35))
% 1.07/1.30          | ((k2_relset_1 @ X36 @ X35 @ X37) = (X35))
% 1.07/1.30          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 1.07/1.30          | ~ (v1_funct_2 @ X37 @ X36 @ X35)
% 1.07/1.30          | ~ (v1_funct_1 @ X37))),
% 1.07/1.30      inference('cnf', [status(esa)], [t24_funct_2])).
% 1.07/1.30  thf('124', plain,
% 1.07/1.30      (![X0 : $i]:
% 1.07/1.30         (~ (v1_funct_1 @ X0)
% 1.07/1.30          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.07/1.30          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.07/1.30          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.07/1.30          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.07/1.30               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.07/1.30               (k6_partfun1 @ sk_A))
% 1.07/1.30          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.07/1.30          | ~ (v1_funct_1 @ sk_C))),
% 1.07/1.30      inference('sup-', [status(thm)], ['122', '123'])).
% 1.07/1.30  thf('125', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('126', plain, ((v1_funct_1 @ sk_C)),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('127', plain,
% 1.07/1.30      (![X0 : $i]:
% 1.07/1.30         (~ (v1_funct_1 @ X0)
% 1.07/1.30          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.07/1.30          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.07/1.30          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.07/1.30          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.07/1.30               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.07/1.30               (k6_partfun1 @ sk_A)))),
% 1.07/1.30      inference('demod', [status(thm)], ['124', '125', '126'])).
% 1.07/1.30  thf('128', plain,
% 1.07/1.30      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 1.07/1.30           (k6_partfun1 @ sk_A))
% 1.07/1.30        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 1.07/1.30        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.07/1.30        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.07/1.30        | ~ (v1_funct_1 @ sk_D))),
% 1.07/1.30      inference('sup-', [status(thm)], ['121', '127'])).
% 1.07/1.30  thf('129', plain,
% 1.07/1.30      (![X26 : $i]:
% 1.07/1.30         (m1_subset_1 @ (k6_partfun1 @ X26) @ 
% 1.07/1.30          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X26)))),
% 1.07/1.30      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.07/1.30  thf('130', plain,
% 1.07/1.30      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 1.07/1.30         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 1.07/1.30          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 1.07/1.30          | (r2_relset_1 @ X16 @ X17 @ X15 @ X18)
% 1.07/1.30          | ((X15) != (X18)))),
% 1.07/1.30      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.07/1.30  thf('131', plain,
% 1.07/1.30      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.07/1.30         ((r2_relset_1 @ X16 @ X17 @ X18 @ X18)
% 1.07/1.30          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 1.07/1.30      inference('simplify', [status(thm)], ['130'])).
% 1.07/1.30  thf('132', plain,
% 1.07/1.30      (![X0 : $i]:
% 1.07/1.30         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 1.07/1.30      inference('sup-', [status(thm)], ['129', '131'])).
% 1.07/1.30  thf('133', plain,
% 1.07/1.30      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('134', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('135', plain, ((v1_funct_1 @ sk_D)),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('136', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))),
% 1.07/1.30      inference('demod', [status(thm)], ['128', '132', '133', '134', '135'])).
% 1.07/1.30  thf('137', plain,
% 1.07/1.30      ((((sk_A) != (sk_A))
% 1.07/1.30        | ~ (v2_funct_1 @ sk_D)
% 1.07/1.30        | ((k5_relat_1 @ (k2_funct_1 @ sk_D) @ sk_D) = (k6_partfun1 @ sk_A)))),
% 1.07/1.30      inference('demod', [status(thm)], ['120', '136'])).
% 1.07/1.30  thf('138', plain,
% 1.07/1.30      ((((k5_relat_1 @ (k2_funct_1 @ sk_D) @ sk_D) = (k6_partfun1 @ sk_A))
% 1.07/1.30        | ~ (v2_funct_1 @ sk_D))),
% 1.07/1.30      inference('simplify', [status(thm)], ['137'])).
% 1.07/1.30  thf('139', plain, ((v2_funct_1 @ sk_D)),
% 1.07/1.30      inference('sup-', [status(thm)], ['96', '97'])).
% 1.07/1.30  thf('140', plain,
% 1.07/1.30      (((k5_relat_1 @ (k2_funct_1 @ sk_D) @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.07/1.30      inference('demod', [status(thm)], ['138', '139'])).
% 1.07/1.30  thf('141', plain, (((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))),
% 1.07/1.30      inference('demod', [status(thm)], ['104', '105'])).
% 1.07/1.30  thf('142', plain,
% 1.07/1.30      (((k5_relat_1 @ (k4_relat_1 @ sk_D) @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.07/1.30      inference('demod', [status(thm)], ['140', '141'])).
% 1.07/1.30  thf('143', plain,
% 1.07/1.30      (((k6_partfun1 @ (k2_relat_1 @ sk_D)) = (k6_partfun1 @ sk_A))),
% 1.07/1.30      inference('sup+', [status(thm)], ['112', '142'])).
% 1.07/1.30  thf('144', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X5)) = (X5))),
% 1.07/1.30      inference('demod', [status(thm)], ['67', '68'])).
% 1.07/1.30  thf('145', plain,
% 1.07/1.30      (((k1_relat_1 @ (k6_partfun1 @ sk_A)) = (k2_relat_1 @ sk_D))),
% 1.07/1.30      inference('sup+', [status(thm)], ['143', '144'])).
% 1.07/1.30  thf('146', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X5)) = (X5))),
% 1.07/1.30      inference('demod', [status(thm)], ['67', '68'])).
% 1.07/1.30  thf('147', plain, (((sk_A) = (k2_relat_1 @ sk_D))),
% 1.07/1.30      inference('demod', [status(thm)], ['145', '146'])).
% 1.07/1.30  thf('148', plain, (((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))),
% 1.07/1.30      inference('demod', [status(thm)], ['104', '105'])).
% 1.07/1.30  thf(dt_k2_funct_1, axiom,
% 1.07/1.30    (![A:$i]:
% 1.07/1.30     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.07/1.30       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.07/1.30         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.07/1.30  thf('149', plain,
% 1.07/1.30      (![X8 : $i]:
% 1.07/1.30         ((v1_funct_1 @ (k2_funct_1 @ X8))
% 1.07/1.30          | ~ (v1_funct_1 @ X8)
% 1.07/1.30          | ~ (v1_relat_1 @ X8))),
% 1.07/1.30      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.07/1.30  thf('150', plain,
% 1.07/1.30      (![X8 : $i]:
% 1.07/1.30         ((v1_relat_1 @ (k2_funct_1 @ X8))
% 1.07/1.30          | ~ (v1_funct_1 @ X8)
% 1.07/1.30          | ~ (v1_relat_1 @ X8))),
% 1.07/1.30      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.07/1.30  thf(fc6_funct_1, axiom,
% 1.07/1.30    (![A:$i]:
% 1.07/1.30     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 1.07/1.30       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.07/1.30         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 1.07/1.30         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.07/1.30  thf('151', plain,
% 1.07/1.30      (![X11 : $i]:
% 1.07/1.30         ((v2_funct_1 @ (k2_funct_1 @ X11))
% 1.07/1.30          | ~ (v2_funct_1 @ X11)
% 1.07/1.30          | ~ (v1_funct_1 @ X11)
% 1.07/1.30          | ~ (v1_relat_1 @ X11))),
% 1.07/1.30      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.07/1.30  thf('152', plain,
% 1.07/1.30      (![X8 : $i]:
% 1.07/1.30         ((v1_funct_1 @ (k2_funct_1 @ X8))
% 1.07/1.30          | ~ (v1_funct_1 @ X8)
% 1.07/1.30          | ~ (v1_relat_1 @ X8))),
% 1.07/1.30      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.07/1.30  thf('153', plain,
% 1.07/1.30      (![X8 : $i]:
% 1.07/1.30         ((v1_relat_1 @ (k2_funct_1 @ X8))
% 1.07/1.30          | ~ (v1_funct_1 @ X8)
% 1.07/1.30          | ~ (v1_relat_1 @ X8))),
% 1.07/1.30      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.07/1.30  thf('154', plain,
% 1.07/1.30      (![X11 : $i]:
% 1.07/1.30         ((v2_funct_1 @ (k2_funct_1 @ X11))
% 1.07/1.30          | ~ (v2_funct_1 @ X11)
% 1.07/1.30          | ~ (v1_funct_1 @ X11)
% 1.07/1.30          | ~ (v1_relat_1 @ X11))),
% 1.07/1.30      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.07/1.30  thf('155', plain,
% 1.07/1.30      (![X8 : $i]:
% 1.07/1.30         ((v1_relat_1 @ (k2_funct_1 @ X8))
% 1.07/1.30          | ~ (v1_funct_1 @ X8)
% 1.07/1.30          | ~ (v1_relat_1 @ X8))),
% 1.07/1.30      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.07/1.30  thf('156', plain,
% 1.07/1.30      (![X8 : $i]:
% 1.07/1.30         ((v1_funct_1 @ (k2_funct_1 @ X8))
% 1.07/1.30          | ~ (v1_funct_1 @ X8)
% 1.07/1.30          | ~ (v1_relat_1 @ X8))),
% 1.07/1.30      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.07/1.30  thf('157', plain,
% 1.07/1.30      (![X7 : $i]:
% 1.07/1.30         (~ (v2_funct_1 @ X7)
% 1.07/1.30          | ((k2_funct_1 @ X7) = (k4_relat_1 @ X7))
% 1.07/1.30          | ~ (v1_funct_1 @ X7)
% 1.07/1.30          | ~ (v1_relat_1 @ X7))),
% 1.07/1.30      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.07/1.30  thf('158', plain,
% 1.07/1.30      (![X0 : $i]:
% 1.07/1.30         (~ (v1_relat_1 @ X0)
% 1.07/1.30          | ~ (v1_funct_1 @ X0)
% 1.07/1.30          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.07/1.30          | ((k2_funct_1 @ (k2_funct_1 @ X0))
% 1.07/1.30              = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 1.07/1.30          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 1.07/1.30      inference('sup-', [status(thm)], ['156', '157'])).
% 1.07/1.30  thf('159', plain,
% 1.07/1.30      (![X0 : $i]:
% 1.07/1.30         (~ (v1_relat_1 @ X0)
% 1.07/1.30          | ~ (v1_funct_1 @ X0)
% 1.07/1.30          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.07/1.30          | ((k2_funct_1 @ (k2_funct_1 @ X0))
% 1.07/1.30              = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 1.07/1.30          | ~ (v1_funct_1 @ X0)
% 1.07/1.30          | ~ (v1_relat_1 @ X0))),
% 1.07/1.30      inference('sup-', [status(thm)], ['155', '158'])).
% 1.07/1.30  thf('160', plain,
% 1.07/1.30      (![X0 : $i]:
% 1.07/1.30         (((k2_funct_1 @ (k2_funct_1 @ X0)) = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 1.07/1.30          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.07/1.30          | ~ (v1_funct_1 @ X0)
% 1.07/1.30          | ~ (v1_relat_1 @ X0))),
% 1.07/1.30      inference('simplify', [status(thm)], ['159'])).
% 1.07/1.30  thf('161', plain,
% 1.07/1.30      (![X0 : $i]:
% 1.07/1.30         (~ (v1_relat_1 @ X0)
% 1.07/1.30          | ~ (v1_funct_1 @ X0)
% 1.07/1.30          | ~ (v2_funct_1 @ X0)
% 1.07/1.30          | ~ (v1_relat_1 @ X0)
% 1.07/1.30          | ~ (v1_funct_1 @ X0)
% 1.07/1.30          | ((k2_funct_1 @ (k2_funct_1 @ X0))
% 1.07/1.30              = (k4_relat_1 @ (k2_funct_1 @ X0))))),
% 1.07/1.30      inference('sup-', [status(thm)], ['154', '160'])).
% 1.07/1.30  thf('162', plain,
% 1.07/1.30      (![X0 : $i]:
% 1.07/1.30         (((k2_funct_1 @ (k2_funct_1 @ X0)) = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 1.07/1.30          | ~ (v2_funct_1 @ X0)
% 1.07/1.30          | ~ (v1_funct_1 @ X0)
% 1.07/1.30          | ~ (v1_relat_1 @ X0))),
% 1.07/1.30      inference('simplify', [status(thm)], ['161'])).
% 1.07/1.30  thf('163', plain,
% 1.07/1.30      (![X11 : $i]:
% 1.07/1.30         ((v2_funct_1 @ (k2_funct_1 @ X11))
% 1.07/1.30          | ~ (v2_funct_1 @ X11)
% 1.07/1.30          | ~ (v1_funct_1 @ X11)
% 1.07/1.30          | ~ (v1_relat_1 @ X11))),
% 1.07/1.30      inference('cnf', [status(esa)], [fc6_funct_1])).
% 1.07/1.30  thf('164', plain,
% 1.07/1.30      (![X0 : $i]:
% 1.07/1.30         ((v2_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ X0)))
% 1.07/1.30          | ~ (v1_relat_1 @ X0)
% 1.07/1.30          | ~ (v1_funct_1 @ X0)
% 1.07/1.30          | ~ (v2_funct_1 @ X0)
% 1.07/1.30          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.07/1.30          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.07/1.30          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 1.07/1.30      inference('sup+', [status(thm)], ['162', '163'])).
% 1.07/1.30  thf('165', plain,
% 1.07/1.30      (![X0 : $i]:
% 1.07/1.30         (~ (v1_relat_1 @ X0)
% 1.07/1.30          | ~ (v1_funct_1 @ X0)
% 1.07/1.30          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.07/1.30          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.07/1.30          | ~ (v2_funct_1 @ X0)
% 1.07/1.30          | ~ (v1_funct_1 @ X0)
% 1.07/1.30          | ~ (v1_relat_1 @ X0)
% 1.07/1.30          | (v2_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ X0))))),
% 1.07/1.30      inference('sup-', [status(thm)], ['153', '164'])).
% 1.07/1.30  thf('166', plain,
% 1.07/1.30      (![X0 : $i]:
% 1.07/1.30         ((v2_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ X0)))
% 1.07/1.30          | ~ (v2_funct_1 @ X0)
% 1.07/1.30          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.07/1.30          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.07/1.30          | ~ (v1_funct_1 @ X0)
% 1.07/1.30          | ~ (v1_relat_1 @ X0))),
% 1.07/1.30      inference('simplify', [status(thm)], ['165'])).
% 1.07/1.30  thf('167', plain,
% 1.07/1.30      (![X0 : $i]:
% 1.07/1.30         (~ (v1_relat_1 @ X0)
% 1.07/1.30          | ~ (v1_funct_1 @ X0)
% 1.07/1.30          | ~ (v1_relat_1 @ X0)
% 1.07/1.30          | ~ (v1_funct_1 @ X0)
% 1.07/1.30          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.07/1.30          | ~ (v2_funct_1 @ X0)
% 1.07/1.30          | (v2_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ X0))))),
% 1.07/1.30      inference('sup-', [status(thm)], ['152', '166'])).
% 1.07/1.30  thf('168', plain,
% 1.07/1.30      (![X0 : $i]:
% 1.07/1.30         ((v2_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ X0)))
% 1.07/1.30          | ~ (v2_funct_1 @ X0)
% 1.07/1.30          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.07/1.30          | ~ (v1_funct_1 @ X0)
% 1.07/1.30          | ~ (v1_relat_1 @ X0))),
% 1.07/1.30      inference('simplify', [status(thm)], ['167'])).
% 1.07/1.30  thf('169', plain,
% 1.07/1.30      (![X0 : $i]:
% 1.07/1.30         (~ (v1_relat_1 @ X0)
% 1.07/1.30          | ~ (v1_funct_1 @ X0)
% 1.07/1.30          | ~ (v2_funct_1 @ X0)
% 1.07/1.30          | ~ (v1_relat_1 @ X0)
% 1.07/1.30          | ~ (v1_funct_1 @ X0)
% 1.07/1.30          | ~ (v2_funct_1 @ X0)
% 1.07/1.30          | (v2_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ X0))))),
% 1.07/1.30      inference('sup-', [status(thm)], ['151', '168'])).
% 1.07/1.30  thf('170', plain,
% 1.07/1.30      (![X0 : $i]:
% 1.07/1.30         ((v2_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ X0)))
% 1.07/1.30          | ~ (v2_funct_1 @ X0)
% 1.07/1.30          | ~ (v1_funct_1 @ X0)
% 1.07/1.30          | ~ (v1_relat_1 @ X0))),
% 1.07/1.30      inference('simplify', [status(thm)], ['169'])).
% 1.07/1.30  thf('171', plain,
% 1.07/1.30      (![X0 : $i]:
% 1.07/1.30         (((k2_funct_1 @ (k2_funct_1 @ X0)) = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 1.07/1.30          | ~ (v2_funct_1 @ X0)
% 1.07/1.30          | ~ (v1_funct_1 @ X0)
% 1.07/1.30          | ~ (v1_relat_1 @ X0))),
% 1.07/1.30      inference('simplify', [status(thm)], ['161'])).
% 1.07/1.30  thf('172', plain,
% 1.07/1.30      (![X0 : $i]:
% 1.07/1.30         (((k2_funct_1 @ (k2_funct_1 @ X0)) = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 1.07/1.30          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.07/1.30          | ~ (v1_funct_1 @ X0)
% 1.07/1.30          | ~ (v1_relat_1 @ X0))),
% 1.07/1.30      inference('simplify', [status(thm)], ['159'])).
% 1.07/1.30  thf('173', plain,
% 1.07/1.30      (![X0 : $i]:
% 1.07/1.30         (~ (v2_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ X0)))
% 1.07/1.30          | ~ (v1_relat_1 @ X0)
% 1.07/1.30          | ~ (v1_funct_1 @ X0)
% 1.07/1.30          | ~ (v2_funct_1 @ X0)
% 1.07/1.30          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.07/1.30          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.07/1.30          | ((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.07/1.30              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 1.07/1.30      inference('sup-', [status(thm)], ['171', '172'])).
% 1.07/1.30  thf('174', plain,
% 1.07/1.30      (![X0 : $i]:
% 1.07/1.30         (~ (v1_relat_1 @ X0)
% 1.07/1.30          | ~ (v1_funct_1 @ X0)
% 1.07/1.30          | ~ (v2_funct_1 @ X0)
% 1.07/1.30          | ((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.07/1.30              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 1.07/1.30          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.07/1.30          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.07/1.30          | ~ (v2_funct_1 @ X0)
% 1.07/1.30          | ~ (v1_funct_1 @ X0)
% 1.07/1.30          | ~ (v1_relat_1 @ X0))),
% 1.07/1.30      inference('sup-', [status(thm)], ['170', '173'])).
% 1.07/1.30  thf('175', plain,
% 1.07/1.30      (![X0 : $i]:
% 1.07/1.30         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.07/1.30          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.07/1.30          | ((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.07/1.30              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 1.07/1.30          | ~ (v2_funct_1 @ X0)
% 1.07/1.30          | ~ (v1_funct_1 @ X0)
% 1.07/1.30          | ~ (v1_relat_1 @ X0))),
% 1.07/1.30      inference('simplify', [status(thm)], ['174'])).
% 1.07/1.30  thf('176', plain,
% 1.07/1.30      (![X0 : $i]:
% 1.07/1.30         (~ (v1_relat_1 @ X0)
% 1.07/1.30          | ~ (v1_funct_1 @ X0)
% 1.07/1.30          | ~ (v1_relat_1 @ X0)
% 1.07/1.30          | ~ (v1_funct_1 @ X0)
% 1.07/1.30          | ~ (v2_funct_1 @ X0)
% 1.07/1.30          | ((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.07/1.30              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 1.07/1.30          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 1.07/1.30      inference('sup-', [status(thm)], ['150', '175'])).
% 1.07/1.30  thf('177', plain,
% 1.07/1.30      (![X0 : $i]:
% 1.07/1.30         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.07/1.30          | ((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.07/1.30              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 1.07/1.30          | ~ (v2_funct_1 @ X0)
% 1.07/1.30          | ~ (v1_funct_1 @ X0)
% 1.07/1.30          | ~ (v1_relat_1 @ X0))),
% 1.07/1.30      inference('simplify', [status(thm)], ['176'])).
% 1.07/1.30  thf('178', plain,
% 1.07/1.30      (![X0 : $i]:
% 1.07/1.30         (~ (v1_relat_1 @ X0)
% 1.07/1.30          | ~ (v1_funct_1 @ X0)
% 1.07/1.30          | ~ (v1_relat_1 @ X0)
% 1.07/1.30          | ~ (v1_funct_1 @ X0)
% 1.07/1.30          | ~ (v2_funct_1 @ X0)
% 1.07/1.30          | ((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.07/1.30              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 1.07/1.30      inference('sup-', [status(thm)], ['149', '177'])).
% 1.07/1.30  thf('179', plain,
% 1.07/1.30      (![X0 : $i]:
% 1.07/1.30         (((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.07/1.30            = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 1.07/1.30          | ~ (v2_funct_1 @ X0)
% 1.07/1.30          | ~ (v1_funct_1 @ X0)
% 1.07/1.30          | ~ (v1_relat_1 @ X0))),
% 1.07/1.30      inference('simplify', [status(thm)], ['178'])).
% 1.07/1.30  thf('180', plain,
% 1.07/1.30      (![X12 : $i]:
% 1.07/1.30         (~ (v2_funct_1 @ X12)
% 1.07/1.30          | ((k5_relat_1 @ X12 @ (k2_funct_1 @ X12))
% 1.07/1.30              = (k6_relat_1 @ (k1_relat_1 @ X12)))
% 1.07/1.30          | ~ (v1_funct_1 @ X12)
% 1.07/1.30          | ~ (v1_relat_1 @ X12))),
% 1.07/1.30      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.07/1.30  thf('181', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 1.07/1.30      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.07/1.30  thf('182', plain,
% 1.07/1.30      (![X12 : $i]:
% 1.07/1.30         (~ (v2_funct_1 @ X12)
% 1.07/1.30          | ((k5_relat_1 @ X12 @ (k2_funct_1 @ X12))
% 1.07/1.30              = (k6_partfun1 @ (k1_relat_1 @ X12)))
% 1.07/1.30          | ~ (v1_funct_1 @ X12)
% 1.07/1.30          | ~ (v1_relat_1 @ X12))),
% 1.07/1.30      inference('demod', [status(thm)], ['180', '181'])).
% 1.07/1.30  thf('183', plain,
% 1.07/1.30      (![X0 : $i]:
% 1.07/1.30         (((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 1.07/1.30            (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 1.07/1.30            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 1.07/1.30          | ~ (v1_relat_1 @ X0)
% 1.07/1.30          | ~ (v1_funct_1 @ X0)
% 1.07/1.30          | ~ (v2_funct_1 @ X0)
% 1.07/1.30          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.07/1.30          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.07/1.30          | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 1.07/1.30      inference('sup+', [status(thm)], ['179', '182'])).
% 1.07/1.30  thf('184', plain,
% 1.07/1.30      ((~ (v1_relat_1 @ (k2_funct_1 @ (k4_relat_1 @ sk_D)))
% 1.07/1.30        | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_D)))
% 1.07/1.30        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_D)))
% 1.07/1.30        | ~ (v2_funct_1 @ sk_D)
% 1.07/1.30        | ~ (v1_funct_1 @ sk_D)
% 1.07/1.30        | ~ (v1_relat_1 @ sk_D)
% 1.07/1.30        | ((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_D)) @ 
% 1.07/1.30            (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_D))))
% 1.07/1.30            = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_D))))))),
% 1.07/1.30      inference('sup-', [status(thm)], ['148', '183'])).
% 1.07/1.30  thf('185', plain, (((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))),
% 1.07/1.30      inference('demod', [status(thm)], ['104', '105'])).
% 1.07/1.30  thf('186', plain,
% 1.07/1.30      (![X0 : $i]:
% 1.07/1.30         (((k2_funct_1 @ (k2_funct_1 @ X0)) = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 1.07/1.30          | ~ (v2_funct_1 @ X0)
% 1.07/1.30          | ~ (v1_funct_1 @ X0)
% 1.07/1.30          | ~ (v1_relat_1 @ X0))),
% 1.07/1.30      inference('simplify', [status(thm)], ['161'])).
% 1.07/1.30  thf('187', plain,
% 1.07/1.30      ((((k2_funct_1 @ (k4_relat_1 @ sk_D))
% 1.07/1.30          = (k4_relat_1 @ (k2_funct_1 @ sk_D)))
% 1.07/1.30        | ~ (v1_relat_1 @ sk_D)
% 1.07/1.30        | ~ (v1_funct_1 @ sk_D)
% 1.07/1.30        | ~ (v2_funct_1 @ sk_D))),
% 1.07/1.30      inference('sup+', [status(thm)], ['185', '186'])).
% 1.07/1.30  thf('188', plain, (((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))),
% 1.07/1.30      inference('demod', [status(thm)], ['104', '105'])).
% 1.07/1.30  thf('189', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 1.07/1.30      inference('sup-', [status(thm)], ['4', '5'])).
% 1.07/1.30  thf('190', plain, ((v1_relat_1 @ sk_D)),
% 1.07/1.30      inference('demod', [status(thm)], ['2', '3'])).
% 1.07/1.30  thf('191', plain, ((v1_funct_1 @ sk_D)),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('192', plain, ((v2_funct_1 @ sk_D)),
% 1.07/1.30      inference('sup-', [status(thm)], ['96', '97'])).
% 1.07/1.30  thf('193', plain, (((k2_funct_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 1.07/1.30      inference('demod', [status(thm)],
% 1.07/1.30                ['187', '188', '189', '190', '191', '192'])).
% 1.07/1.30  thf('194', plain, ((v1_relat_1 @ sk_D)),
% 1.07/1.30      inference('demod', [status(thm)], ['2', '3'])).
% 1.07/1.30  thf('195', plain, (((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))),
% 1.07/1.30      inference('demod', [status(thm)], ['104', '105'])).
% 1.07/1.30  thf('196', plain, (((k2_funct_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 1.07/1.30      inference('demod', [status(thm)],
% 1.07/1.30                ['187', '188', '189', '190', '191', '192'])).
% 1.07/1.30  thf('197', plain, ((v2_funct_1 @ sk_D)),
% 1.07/1.30      inference('sup-', [status(thm)], ['96', '97'])).
% 1.07/1.30  thf('198', plain, (((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))),
% 1.07/1.30      inference('demod', [status(thm)], ['104', '105'])).
% 1.07/1.30  thf('199', plain, (((k2_funct_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 1.07/1.30      inference('demod', [status(thm)],
% 1.07/1.30                ['187', '188', '189', '190', '191', '192'])).
% 1.07/1.30  thf('200', plain, ((v1_funct_1 @ sk_D)),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('201', plain, ((v2_funct_1 @ sk_D)),
% 1.07/1.30      inference('sup-', [status(thm)], ['96', '97'])).
% 1.07/1.30  thf('202', plain, ((v1_funct_1 @ sk_D)),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('203', plain, ((v1_relat_1 @ sk_D)),
% 1.07/1.30      inference('demod', [status(thm)], ['2', '3'])).
% 1.07/1.30  thf('204', plain, (((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))),
% 1.07/1.30      inference('demod', [status(thm)], ['104', '105'])).
% 1.07/1.30  thf('205', plain, (((k2_funct_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 1.07/1.30      inference('demod', [status(thm)],
% 1.07/1.30                ['187', '188', '189', '190', '191', '192'])).
% 1.07/1.30  thf('206', plain, (((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))),
% 1.07/1.30      inference('demod', [status(thm)], ['104', '105'])).
% 1.07/1.30  thf('207', plain, (((k2_funct_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 1.07/1.30      inference('demod', [status(thm)],
% 1.07/1.30                ['187', '188', '189', '190', '191', '192'])).
% 1.07/1.30  thf('208', plain,
% 1.07/1.30      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('209', plain,
% 1.07/1.30      (![X47 : $i, X48 : $i, X49 : $i]:
% 1.07/1.30         (((X47) = (k1_xboole_0))
% 1.07/1.30          | ~ (v1_funct_1 @ X48)
% 1.07/1.30          | ~ (v1_funct_2 @ X48 @ X49 @ X47)
% 1.07/1.30          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X47)))
% 1.07/1.30          | ((k5_relat_1 @ X48 @ (k2_funct_1 @ X48)) = (k6_partfun1 @ X49))
% 1.07/1.30          | ~ (v2_funct_1 @ X48)
% 1.07/1.30          | ((k2_relset_1 @ X49 @ X47 @ X48) != (X47)))),
% 1.07/1.30      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.07/1.30  thf('210', plain,
% 1.07/1.30      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 1.07/1.30        | ~ (v2_funct_1 @ sk_D)
% 1.07/1.30        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.07/1.30        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.07/1.30        | ~ (v1_funct_1 @ sk_D)
% 1.07/1.30        | ((sk_A) = (k1_xboole_0)))),
% 1.07/1.30      inference('sup-', [status(thm)], ['208', '209'])).
% 1.07/1.30  thf('211', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('212', plain, ((v1_funct_1 @ sk_D)),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('213', plain,
% 1.07/1.30      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 1.07/1.30        | ~ (v2_funct_1 @ sk_D)
% 1.07/1.30        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.07/1.30        | ((sk_A) = (k1_xboole_0)))),
% 1.07/1.30      inference('demod', [status(thm)], ['210', '211', '212'])).
% 1.07/1.30  thf('214', plain, (((sk_A) != (k1_xboole_0))),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('215', plain,
% 1.07/1.30      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 1.07/1.30        | ~ (v2_funct_1 @ sk_D)
% 1.07/1.30        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 1.07/1.30      inference('simplify_reflect-', [status(thm)], ['213', '214'])).
% 1.07/1.30  thf('216', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))),
% 1.07/1.30      inference('demod', [status(thm)], ['128', '132', '133', '134', '135'])).
% 1.07/1.30  thf('217', plain,
% 1.07/1.30      ((((sk_A) != (sk_A))
% 1.07/1.30        | ~ (v2_funct_1 @ sk_D)
% 1.07/1.30        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 1.07/1.30      inference('demod', [status(thm)], ['215', '216'])).
% 1.07/1.30  thf('218', plain,
% 1.07/1.30      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.07/1.30        | ~ (v2_funct_1 @ sk_D))),
% 1.07/1.30      inference('simplify', [status(thm)], ['217'])).
% 1.07/1.30  thf('219', plain, ((v2_funct_1 @ sk_D)),
% 1.07/1.30      inference('sup-', [status(thm)], ['96', '97'])).
% 1.07/1.30  thf('220', plain,
% 1.07/1.30      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 1.07/1.30      inference('demod', [status(thm)], ['218', '219'])).
% 1.07/1.30  thf('221', plain, (((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))),
% 1.07/1.30      inference('demod', [status(thm)], ['104', '105'])).
% 1.07/1.30  thf('222', plain,
% 1.07/1.30      (((k5_relat_1 @ sk_D @ (k4_relat_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 1.07/1.30      inference('demod', [status(thm)], ['220', '221'])).
% 1.07/1.30  thf('223', plain, (((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))),
% 1.07/1.30      inference('demod', [status(thm)], ['104', '105'])).
% 1.07/1.30  thf('224', plain, (((k2_funct_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 1.07/1.30      inference('demod', [status(thm)],
% 1.07/1.30                ['187', '188', '189', '190', '191', '192'])).
% 1.07/1.30  thf('225', plain,
% 1.07/1.30      (((k6_partfun1 @ sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_D)))),
% 1.07/1.30      inference('demod', [status(thm)],
% 1.07/1.30                ['184', '193', '194', '195', '196', '197', '198', '199', 
% 1.07/1.30                 '200', '201', '202', '203', '204', '205', '206', '207', 
% 1.07/1.30                 '222', '223', '224'])).
% 1.07/1.30  thf('226', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X5)) = (X5))),
% 1.07/1.30      inference('demod', [status(thm)], ['67', '68'])).
% 1.07/1.30  thf('227', plain,
% 1.07/1.30      (((k1_relat_1 @ (k6_partfun1 @ sk_B)) = (k1_relat_1 @ sk_D))),
% 1.07/1.30      inference('sup+', [status(thm)], ['225', '226'])).
% 1.07/1.30  thf('228', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X5)) = (X5))),
% 1.07/1.30      inference('demod', [status(thm)], ['67', '68'])).
% 1.07/1.30  thf('229', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.07/1.30      inference('demod', [status(thm)], ['227', '228'])).
% 1.07/1.30  thf('230', plain, (((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))),
% 1.07/1.30      inference('demod', [status(thm)], ['104', '105'])).
% 1.07/1.30  thf('231', plain,
% 1.07/1.30      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 1.07/1.30        | ((sk_B) != (sk_B))
% 1.07/1.30        | ((sk_C) = (k4_relat_1 @ sk_D)))),
% 1.07/1.30      inference('demod', [status(thm)], ['99', '147', '229', '230'])).
% 1.07/1.30  thf('232', plain, (((sk_C) = (k4_relat_1 @ sk_D))),
% 1.07/1.30      inference('simplify', [status(thm)], ['231'])).
% 1.07/1.30  thf('233', plain, (((k4_relat_1 @ sk_C) = (sk_D))),
% 1.07/1.30      inference('demod', [status(thm)], ['6', '232'])).
% 1.07/1.30  thf('234', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('235', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.07/1.30      inference('demod', [status(thm)], ['44', '49', '50'])).
% 1.07/1.30  thf('236', plain, (((sk_D) != (k4_relat_1 @ sk_C))),
% 1.07/1.30      inference('demod', [status(thm)], ['234', '235'])).
% 1.07/1.30  thf('237', plain, ($false),
% 1.07/1.30      inference('simplify_reflect-', [status(thm)], ['233', '236'])).
% 1.07/1.30  
% 1.07/1.30  % SZS output end Refutation
% 1.07/1.30  
% 1.07/1.31  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

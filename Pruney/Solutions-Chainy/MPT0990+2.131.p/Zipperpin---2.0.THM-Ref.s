%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KKXt2XeVdV

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:17 EST 2020

% Result     : Theorem 1.13s
% Output     : Refutation 1.13s
% Verified   : 
% Statistics : Number of formulae       :  212 (1017 expanded)
%              Number of leaves         :   53 ( 329 expanded)
%              Depth                    :   19
%              Number of atoms          : 1840 (23715 expanded)
%              Number of equality atoms :  116 (1623 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

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
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('8',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ X5 )
        = ( k4_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k2_funct_1 @ sk_D )
      = ( k4_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['2','3'])).

thf('11',plain,
    ( ( ( k2_funct_1 @ sk_D )
      = ( k4_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
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
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
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

thf('23',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('30',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( X21 = X24 )
      | ~ ( r2_relset_1 @ X22 @ X23 @ X21 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','31'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('33',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('34',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('35',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('37',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['18','19','36'])).

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

thf('38',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X9 )
       != ( k1_relat_1 @ X10 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('39',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('40',plain,(
    ! [X8: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('41',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('42',plain,(
    ! [X8: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X8 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['2','3'])).

thf('44',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf('46',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ~ ( v2_funct_1 @ X53 )
      | ( ( k2_relset_1 @ X55 @ X54 @ X53 )
       != X54 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X53 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X55 ) ) )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X54 ) ) )
      | ~ ( v1_funct_2 @ X53 @ X55 @ X54 )
      | ~ ( v1_funct_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('47',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ X5 )
        = ( k4_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('52',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('55',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('57',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['52','57','58'])).

thf('60',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['47','48','49','59','60','61'])).

thf('63',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('64',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('65',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['52','57','58'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('67',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_relat_1 @ X11 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('68',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['55','56'])).

thf('70',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['68','69','70','71'])).

thf('73',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['65','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ~ ( v2_funct_1 @ X53 )
      | ( ( k2_relset_1 @ X55 @ X54 @ X53 )
       != X54 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X53 ) @ X54 @ X55 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X54 ) ) )
      | ~ ( v1_funct_2 @ X53 @ X55 @ X54 )
      | ~ ( v1_funct_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('76',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['52','57','58'])).

thf('80',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['76','77','78','79','80','81'])).

thf('83',plain,(
    v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['82'])).

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

thf('84',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('85',plain,
    ( ~ ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('86',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('87',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['62'])).

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

thf('88',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('89',plain,
    ( ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['90','91'])).

thf('93',plain,
    ( sk_B
    = ( k1_relset_1 @ sk_B @ sk_A @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['85','92'])).

thf('94',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['73','93'])).

thf('95',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('97',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('99',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('101',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['102','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('107',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['97','104','107'])).

thf('109',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['55','56'])).

thf('111',plain,
    ( ( sk_B != sk_B )
    | ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['39','42','43','44','94','108','109','110'])).

thf('112',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,
    ( ( k2_funct_1 @ sk_D )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['11','112'])).

thf('114',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['18','19','36'])).

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

thf('115',plain,(
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

thf('116',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('117',plain,(
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
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
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
    inference('sup-',[status(thm)],['114','117'])).

thf('119',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('120',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
           => ( ( v2_funct_1 @ C )
              & ( v2_funct_2 @ D @ A ) ) ) ) ) )).

thf('121',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X51 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ( v2_funct_2 @ X49 @ X51 )
      | ~ ( r2_relset_1 @ X51 @ X51 @ ( k1_partfun1 @ X51 @ X50 @ X50 @ X51 @ X52 @ X49 ) @ ( k6_partfun1 @ X51 ) )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X50 ) ) )
      | ~ ( v1_funct_2 @ X52 @ X51 @ X50 )
      | ~ ( v1_funct_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t29_funct_2])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) @ ( k6_partfun1 @ sk_A ) )
      | ( v2_funct_2 @ sk_D @ sk_A )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) @ ( k6_partfun1 @ sk_A ) )
      | ( v2_funct_2 @ sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('126',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['119','125'])).

thf('127',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('128',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( r2_relset_1 @ X22 @ X23 @ X21 @ X24 )
      | ( X21 != X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('129',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_relset_1 @ X22 @ X23 @ X24 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['127','129'])).

thf('131',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['126','130','131','132','133'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('135',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( v2_funct_2 @ X35 @ X34 )
      | ( ( k2_relat_1 @ X35 )
        = X34 )
      | ~ ( v5_relat_1 @ X35 @ X34 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('136',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( ( k2_relat_1 @ sk_D )
      = sk_A ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['2','3'])).

thf('138',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('139',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v5_relat_1 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('140',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['136','137','140'])).

thf('142',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['2','3'])).

thf('143',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['73','93'])).

thf('145',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['97','104','107'])).

thf('146',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['55','56'])).

thf('148',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B != sk_B )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['118','141','142','143','144','145','146','147'])).

thf('149',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['111'])).

thf('151',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,
    ( sk_C
    = ( k4_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['113','151'])).

thf('153',plain,
    ( ( k4_relat_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['6','152'])).

thf('154',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['52','57','58'])).

thf('156',plain,(
    sk_D
 != ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['153','156'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KKXt2XeVdV
% 0.16/0.37  % Computer   : n023.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 17:15:36 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 1.13/1.32  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.13/1.32  % Solved by: fo/fo7.sh
% 1.13/1.32  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.13/1.32  % done 502 iterations in 0.837s
% 1.13/1.32  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.13/1.32  % SZS output start Refutation
% 1.13/1.32  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.13/1.32  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 1.13/1.32  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.13/1.32  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.13/1.32  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.13/1.32  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.13/1.32  thf(sk_A_type, type, sk_A: $i).
% 1.13/1.32  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 1.13/1.32  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.13/1.32  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.13/1.32  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.13/1.32  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.13/1.32  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.13/1.32  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.13/1.32  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.13/1.32  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.13/1.32  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.13/1.32  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.13/1.32  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.13/1.32  thf(sk_C_type, type, sk_C: $i).
% 1.13/1.32  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.13/1.32  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.13/1.32  thf(sk_D_type, type, sk_D: $i).
% 1.13/1.32  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.13/1.32  thf(sk_B_type, type, sk_B: $i).
% 1.13/1.32  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.13/1.32  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.13/1.32  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.13/1.32  thf(t36_funct_2, conjecture,
% 1.13/1.32    (![A:$i,B:$i,C:$i]:
% 1.13/1.32     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.13/1.32         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.13/1.32       ( ![D:$i]:
% 1.13/1.32         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.13/1.32             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.13/1.32           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.13/1.32               ( r2_relset_1 @
% 1.13/1.32                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.13/1.32                 ( k6_partfun1 @ A ) ) & 
% 1.13/1.32               ( v2_funct_1 @ C ) ) =>
% 1.13/1.32             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.13/1.32               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.13/1.32  thf(zf_stmt_0, negated_conjecture,
% 1.13/1.32    (~( ![A:$i,B:$i,C:$i]:
% 1.13/1.32        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.13/1.32            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.13/1.32          ( ![D:$i]:
% 1.13/1.32            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.13/1.32                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.13/1.32              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.13/1.32                  ( r2_relset_1 @
% 1.13/1.32                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.13/1.32                    ( k6_partfun1 @ A ) ) & 
% 1.13/1.32                  ( v2_funct_1 @ C ) ) =>
% 1.13/1.32                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.13/1.32                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.13/1.32    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.13/1.32  thf('0', plain,
% 1.13/1.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf(cc2_relat_1, axiom,
% 1.13/1.32    (![A:$i]:
% 1.13/1.32     ( ( v1_relat_1 @ A ) =>
% 1.13/1.32       ( ![B:$i]:
% 1.13/1.32         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.13/1.32  thf('1', plain,
% 1.13/1.32      (![X0 : $i, X1 : $i]:
% 1.13/1.32         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.13/1.32          | (v1_relat_1 @ X0)
% 1.13/1.32          | ~ (v1_relat_1 @ X1))),
% 1.13/1.32      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.13/1.32  thf('2', plain,
% 1.13/1.32      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 1.13/1.32      inference('sup-', [status(thm)], ['0', '1'])).
% 1.13/1.32  thf(fc6_relat_1, axiom,
% 1.13/1.32    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.13/1.32  thf('3', plain,
% 1.13/1.32      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.13/1.32      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.13/1.32  thf('4', plain, ((v1_relat_1 @ sk_D)),
% 1.13/1.32      inference('demod', [status(thm)], ['2', '3'])).
% 1.13/1.32  thf(involutiveness_k4_relat_1, axiom,
% 1.13/1.32    (![A:$i]:
% 1.13/1.32     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 1.13/1.32  thf('5', plain,
% 1.13/1.32      (![X4 : $i]:
% 1.13/1.32         (((k4_relat_1 @ (k4_relat_1 @ X4)) = (X4)) | ~ (v1_relat_1 @ X4))),
% 1.13/1.32      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 1.13/1.32  thf('6', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 1.13/1.32      inference('sup-', [status(thm)], ['4', '5'])).
% 1.13/1.32  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf(d9_funct_1, axiom,
% 1.13/1.32    (![A:$i]:
% 1.13/1.32     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.13/1.32       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 1.13/1.32  thf('8', plain,
% 1.13/1.32      (![X5 : $i]:
% 1.13/1.32         (~ (v2_funct_1 @ X5)
% 1.13/1.32          | ((k2_funct_1 @ X5) = (k4_relat_1 @ X5))
% 1.13/1.32          | ~ (v1_funct_1 @ X5)
% 1.13/1.32          | ~ (v1_relat_1 @ X5))),
% 1.13/1.32      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.13/1.32  thf('9', plain,
% 1.13/1.32      ((~ (v1_relat_1 @ sk_D)
% 1.13/1.32        | ((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))
% 1.13/1.32        | ~ (v2_funct_1 @ sk_D))),
% 1.13/1.32      inference('sup-', [status(thm)], ['7', '8'])).
% 1.13/1.32  thf('10', plain, ((v1_relat_1 @ sk_D)),
% 1.13/1.32      inference('demod', [status(thm)], ['2', '3'])).
% 1.13/1.32  thf('11', plain,
% 1.13/1.32      ((((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 1.13/1.32      inference('demod', [status(thm)], ['9', '10'])).
% 1.13/1.32  thf('12', plain,
% 1.13/1.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf('13', plain,
% 1.13/1.32      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf(redefinition_k1_partfun1, axiom,
% 1.13/1.32    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.13/1.32     ( ( ( v1_funct_1 @ E ) & 
% 1.13/1.32         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.13/1.32         ( v1_funct_1 @ F ) & 
% 1.13/1.32         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.13/1.32       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.13/1.32  thf('14', plain,
% 1.13/1.32      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 1.13/1.32         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 1.13/1.32          | ~ (v1_funct_1 @ X42)
% 1.13/1.32          | ~ (v1_funct_1 @ X45)
% 1.13/1.32          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 1.13/1.32          | ((k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45)
% 1.13/1.32              = (k5_relat_1 @ X42 @ X45)))),
% 1.13/1.32      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.13/1.32  thf('15', plain,
% 1.13/1.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.13/1.32         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.13/1.32            = (k5_relat_1 @ sk_C @ X0))
% 1.13/1.32          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.13/1.32          | ~ (v1_funct_1 @ X0)
% 1.13/1.32          | ~ (v1_funct_1 @ sk_C))),
% 1.13/1.32      inference('sup-', [status(thm)], ['13', '14'])).
% 1.13/1.32  thf('16', plain, ((v1_funct_1 @ sk_C)),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf('17', plain,
% 1.13/1.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.13/1.32         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.13/1.32            = (k5_relat_1 @ sk_C @ X0))
% 1.13/1.32          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.13/1.32          | ~ (v1_funct_1 @ X0))),
% 1.13/1.32      inference('demod', [status(thm)], ['15', '16'])).
% 1.13/1.32  thf('18', plain,
% 1.13/1.32      ((~ (v1_funct_1 @ sk_D)
% 1.13/1.32        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.13/1.32            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.13/1.32      inference('sup-', [status(thm)], ['12', '17'])).
% 1.13/1.32  thf('19', plain, ((v1_funct_1 @ sk_D)),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf('20', plain,
% 1.13/1.32      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.13/1.32        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.13/1.32        (k6_partfun1 @ sk_A))),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf('21', plain,
% 1.13/1.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf('22', plain,
% 1.13/1.32      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf(dt_k1_partfun1, axiom,
% 1.13/1.32    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.13/1.32     ( ( ( v1_funct_1 @ E ) & 
% 1.13/1.32         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.13/1.32         ( v1_funct_1 @ F ) & 
% 1.13/1.32         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.13/1.32       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.13/1.32         ( m1_subset_1 @
% 1.13/1.32           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.13/1.32           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.13/1.32  thf('23', plain,
% 1.13/1.32      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 1.13/1.32         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 1.13/1.32          | ~ (v1_funct_1 @ X36)
% 1.13/1.32          | ~ (v1_funct_1 @ X39)
% 1.13/1.32          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 1.13/1.32          | (m1_subset_1 @ (k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39) @ 
% 1.13/1.32             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X41))))),
% 1.13/1.32      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.13/1.32  thf('24', plain,
% 1.13/1.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.13/1.32         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.13/1.32           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.13/1.32          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.13/1.32          | ~ (v1_funct_1 @ X1)
% 1.13/1.32          | ~ (v1_funct_1 @ sk_C))),
% 1.13/1.32      inference('sup-', [status(thm)], ['22', '23'])).
% 1.13/1.32  thf('25', plain, ((v1_funct_1 @ sk_C)),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf('26', plain,
% 1.13/1.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.13/1.32         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.13/1.32           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.13/1.32          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.13/1.32          | ~ (v1_funct_1 @ X1))),
% 1.13/1.32      inference('demod', [status(thm)], ['24', '25'])).
% 1.13/1.32  thf('27', plain,
% 1.13/1.32      ((~ (v1_funct_1 @ sk_D)
% 1.13/1.32        | (m1_subset_1 @ 
% 1.13/1.32           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.13/1.32           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.13/1.32      inference('sup-', [status(thm)], ['21', '26'])).
% 1.13/1.32  thf('28', plain, ((v1_funct_1 @ sk_D)),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf('29', plain,
% 1.13/1.32      ((m1_subset_1 @ 
% 1.13/1.32        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.13/1.32        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.13/1.32      inference('demod', [status(thm)], ['27', '28'])).
% 1.13/1.32  thf(redefinition_r2_relset_1, axiom,
% 1.13/1.32    (![A:$i,B:$i,C:$i,D:$i]:
% 1.13/1.32     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.13/1.32         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.13/1.32       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.13/1.32  thf('30', plain,
% 1.13/1.32      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 1.13/1.32         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 1.13/1.32          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 1.13/1.32          | ((X21) = (X24))
% 1.13/1.32          | ~ (r2_relset_1 @ X22 @ X23 @ X21 @ X24))),
% 1.13/1.32      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.13/1.32  thf('31', plain,
% 1.13/1.32      (![X0 : $i]:
% 1.13/1.32         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.13/1.32             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 1.13/1.32          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 1.13/1.32          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.13/1.32      inference('sup-', [status(thm)], ['29', '30'])).
% 1.13/1.32  thf('32', plain,
% 1.13/1.32      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.13/1.32           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.13/1.32        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.13/1.32            = (k6_partfun1 @ sk_A)))),
% 1.13/1.32      inference('sup-', [status(thm)], ['20', '31'])).
% 1.13/1.32  thf(t29_relset_1, axiom,
% 1.13/1.32    (![A:$i]:
% 1.13/1.32     ( m1_subset_1 @
% 1.13/1.32       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.13/1.32  thf('33', plain,
% 1.13/1.32      (![X25 : $i]:
% 1.13/1.32         (m1_subset_1 @ (k6_relat_1 @ X25) @ 
% 1.13/1.32          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))),
% 1.13/1.32      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.13/1.32  thf(redefinition_k6_partfun1, axiom,
% 1.13/1.32    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.13/1.32  thf('34', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 1.13/1.32      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.13/1.32  thf('35', plain,
% 1.13/1.32      (![X25 : $i]:
% 1.13/1.32         (m1_subset_1 @ (k6_partfun1 @ X25) @ 
% 1.13/1.32          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))),
% 1.13/1.32      inference('demod', [status(thm)], ['33', '34'])).
% 1.13/1.32  thf('36', plain,
% 1.13/1.32      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.13/1.32         = (k6_partfun1 @ sk_A))),
% 1.13/1.32      inference('demod', [status(thm)], ['32', '35'])).
% 1.13/1.32  thf('37', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 1.13/1.32      inference('demod', [status(thm)], ['18', '19', '36'])).
% 1.13/1.32  thf(t48_funct_1, axiom,
% 1.13/1.32    (![A:$i]:
% 1.13/1.32     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.13/1.32       ( ![B:$i]:
% 1.13/1.32         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.13/1.32           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 1.13/1.32               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 1.13/1.32             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 1.13/1.32  thf('38', plain,
% 1.13/1.32      (![X9 : $i, X10 : $i]:
% 1.13/1.32         (~ (v1_relat_1 @ X9)
% 1.13/1.32          | ~ (v1_funct_1 @ X9)
% 1.13/1.32          | (v2_funct_1 @ X10)
% 1.13/1.32          | ((k2_relat_1 @ X9) != (k1_relat_1 @ X10))
% 1.13/1.32          | ~ (v2_funct_1 @ (k5_relat_1 @ X9 @ X10))
% 1.13/1.32          | ~ (v1_funct_1 @ X10)
% 1.13/1.32          | ~ (v1_relat_1 @ X10))),
% 1.13/1.32      inference('cnf', [status(esa)], [t48_funct_1])).
% 1.13/1.32  thf('39', plain,
% 1.13/1.32      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 1.13/1.32        | ~ (v1_relat_1 @ sk_D)
% 1.13/1.32        | ~ (v1_funct_1 @ sk_D)
% 1.13/1.32        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 1.13/1.32        | (v2_funct_1 @ sk_D)
% 1.13/1.32        | ~ (v1_funct_1 @ sk_C)
% 1.13/1.32        | ~ (v1_relat_1 @ sk_C))),
% 1.13/1.32      inference('sup-', [status(thm)], ['37', '38'])).
% 1.13/1.32  thf(fc4_funct_1, axiom,
% 1.13/1.32    (![A:$i]:
% 1.13/1.32     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.13/1.32       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.13/1.32  thf('40', plain, (![X8 : $i]: (v2_funct_1 @ (k6_relat_1 @ X8))),
% 1.13/1.32      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.13/1.32  thf('41', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 1.13/1.32      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.13/1.32  thf('42', plain, (![X8 : $i]: (v2_funct_1 @ (k6_partfun1 @ X8))),
% 1.13/1.32      inference('demod', [status(thm)], ['40', '41'])).
% 1.13/1.32  thf('43', plain, ((v1_relat_1 @ sk_D)),
% 1.13/1.32      inference('demod', [status(thm)], ['2', '3'])).
% 1.13/1.32  thf('44', plain, ((v1_funct_1 @ sk_D)),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf('45', plain,
% 1.13/1.32      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf(t31_funct_2, axiom,
% 1.13/1.32    (![A:$i,B:$i,C:$i]:
% 1.13/1.32     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.13/1.32         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.13/1.32       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.13/1.32         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.13/1.32           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.13/1.32           ( m1_subset_1 @
% 1.13/1.32             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.13/1.32  thf('46', plain,
% 1.13/1.32      (![X53 : $i, X54 : $i, X55 : $i]:
% 1.13/1.32         (~ (v2_funct_1 @ X53)
% 1.13/1.32          | ((k2_relset_1 @ X55 @ X54 @ X53) != (X54))
% 1.13/1.32          | (m1_subset_1 @ (k2_funct_1 @ X53) @ 
% 1.13/1.32             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X55)))
% 1.13/1.32          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X54)))
% 1.13/1.32          | ~ (v1_funct_2 @ X53 @ X55 @ X54)
% 1.13/1.32          | ~ (v1_funct_1 @ X53))),
% 1.13/1.32      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.13/1.32  thf('47', plain,
% 1.13/1.32      ((~ (v1_funct_1 @ sk_C)
% 1.13/1.32        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.13/1.32        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.13/1.32           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.13/1.32        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.13/1.32        | ~ (v2_funct_1 @ sk_C))),
% 1.13/1.32      inference('sup-', [status(thm)], ['45', '46'])).
% 1.13/1.32  thf('48', plain, ((v1_funct_1 @ sk_C)),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf('49', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf('50', plain, ((v1_funct_1 @ sk_C)),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf('51', plain,
% 1.13/1.32      (![X5 : $i]:
% 1.13/1.32         (~ (v2_funct_1 @ X5)
% 1.13/1.32          | ((k2_funct_1 @ X5) = (k4_relat_1 @ X5))
% 1.13/1.32          | ~ (v1_funct_1 @ X5)
% 1.13/1.32          | ~ (v1_relat_1 @ X5))),
% 1.13/1.32      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.13/1.32  thf('52', plain,
% 1.13/1.32      ((~ (v1_relat_1 @ sk_C)
% 1.13/1.32        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 1.13/1.32        | ~ (v2_funct_1 @ sk_C))),
% 1.13/1.32      inference('sup-', [status(thm)], ['50', '51'])).
% 1.13/1.32  thf('53', plain,
% 1.13/1.32      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf('54', plain,
% 1.13/1.32      (![X0 : $i, X1 : $i]:
% 1.13/1.32         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.13/1.32          | (v1_relat_1 @ X0)
% 1.13/1.32          | ~ (v1_relat_1 @ X1))),
% 1.13/1.32      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.13/1.32  thf('55', plain,
% 1.13/1.32      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 1.13/1.32      inference('sup-', [status(thm)], ['53', '54'])).
% 1.13/1.32  thf('56', plain,
% 1.13/1.32      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.13/1.32      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.13/1.32  thf('57', plain, ((v1_relat_1 @ sk_C)),
% 1.13/1.32      inference('demod', [status(thm)], ['55', '56'])).
% 1.13/1.32  thf('58', plain, ((v2_funct_1 @ sk_C)),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf('59', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.13/1.32      inference('demod', [status(thm)], ['52', '57', '58'])).
% 1.13/1.32  thf('60', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf('61', plain, ((v2_funct_1 @ sk_C)),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf('62', plain,
% 1.13/1.32      (((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.13/1.32         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.13/1.32        | ((sk_B) != (sk_B)))),
% 1.13/1.32      inference('demod', [status(thm)], ['47', '48', '49', '59', '60', '61'])).
% 1.13/1.32  thf('63', plain,
% 1.13/1.32      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.13/1.32        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.13/1.32      inference('simplify', [status(thm)], ['62'])).
% 1.13/1.32  thf(redefinition_k1_relset_1, axiom,
% 1.13/1.32    (![A:$i,B:$i,C:$i]:
% 1.13/1.32     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.13/1.32       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.13/1.32  thf('64', plain,
% 1.13/1.32      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.13/1.32         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 1.13/1.32          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.13/1.32      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.13/1.32  thf('65', plain,
% 1.13/1.32      (((k1_relset_1 @ sk_B @ sk_A @ (k4_relat_1 @ sk_C))
% 1.13/1.32         = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.13/1.32      inference('sup-', [status(thm)], ['63', '64'])).
% 1.13/1.32  thf('66', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.13/1.32      inference('demod', [status(thm)], ['52', '57', '58'])).
% 1.13/1.32  thf(t55_funct_1, axiom,
% 1.13/1.32    (![A:$i]:
% 1.13/1.32     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.13/1.32       ( ( v2_funct_1 @ A ) =>
% 1.13/1.32         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.13/1.32           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.13/1.32  thf('67', plain,
% 1.13/1.32      (![X11 : $i]:
% 1.13/1.32         (~ (v2_funct_1 @ X11)
% 1.13/1.32          | ((k2_relat_1 @ X11) = (k1_relat_1 @ (k2_funct_1 @ X11)))
% 1.13/1.32          | ~ (v1_funct_1 @ X11)
% 1.13/1.32          | ~ (v1_relat_1 @ X11))),
% 1.13/1.32      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.13/1.32  thf('68', plain,
% 1.13/1.32      ((((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))
% 1.13/1.32        | ~ (v1_relat_1 @ sk_C)
% 1.13/1.32        | ~ (v1_funct_1 @ sk_C)
% 1.13/1.32        | ~ (v2_funct_1 @ sk_C))),
% 1.13/1.32      inference('sup+', [status(thm)], ['66', '67'])).
% 1.13/1.32  thf('69', plain, ((v1_relat_1 @ sk_C)),
% 1.13/1.32      inference('demod', [status(thm)], ['55', '56'])).
% 1.13/1.32  thf('70', plain, ((v1_funct_1 @ sk_C)),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf('71', plain, ((v2_funct_1 @ sk_C)),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf('72', plain,
% 1.13/1.32      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.13/1.32      inference('demod', [status(thm)], ['68', '69', '70', '71'])).
% 1.13/1.32  thf('73', plain,
% 1.13/1.32      (((k1_relset_1 @ sk_B @ sk_A @ (k4_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 1.13/1.32      inference('demod', [status(thm)], ['65', '72'])).
% 1.13/1.32  thf('74', plain,
% 1.13/1.32      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf('75', plain,
% 1.13/1.32      (![X53 : $i, X54 : $i, X55 : $i]:
% 1.13/1.32         (~ (v2_funct_1 @ X53)
% 1.13/1.32          | ((k2_relset_1 @ X55 @ X54 @ X53) != (X54))
% 1.13/1.32          | (v1_funct_2 @ (k2_funct_1 @ X53) @ X54 @ X55)
% 1.13/1.32          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X54)))
% 1.13/1.32          | ~ (v1_funct_2 @ X53 @ X55 @ X54)
% 1.13/1.32          | ~ (v1_funct_1 @ X53))),
% 1.13/1.32      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.13/1.32  thf('76', plain,
% 1.13/1.32      ((~ (v1_funct_1 @ sk_C)
% 1.13/1.32        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.13/1.32        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 1.13/1.32        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.13/1.32        | ~ (v2_funct_1 @ sk_C))),
% 1.13/1.32      inference('sup-', [status(thm)], ['74', '75'])).
% 1.13/1.32  thf('77', plain, ((v1_funct_1 @ sk_C)),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf('78', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf('79', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.13/1.32      inference('demod', [status(thm)], ['52', '57', '58'])).
% 1.13/1.32  thf('80', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf('81', plain, ((v2_funct_1 @ sk_C)),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf('82', plain,
% 1.13/1.32      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A) | ((sk_B) != (sk_B)))),
% 1.13/1.32      inference('demod', [status(thm)], ['76', '77', '78', '79', '80', '81'])).
% 1.13/1.32  thf('83', plain, ((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A)),
% 1.13/1.32      inference('simplify', [status(thm)], ['82'])).
% 1.13/1.32  thf(d1_funct_2, axiom,
% 1.13/1.32    (![A:$i,B:$i,C:$i]:
% 1.13/1.32     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.13/1.32       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.13/1.32           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.13/1.32             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.13/1.32         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.13/1.32           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.13/1.32             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.13/1.32  thf(zf_stmt_1, axiom,
% 1.13/1.32    (![C:$i,B:$i,A:$i]:
% 1.13/1.32     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.13/1.32       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.13/1.32  thf('84', plain,
% 1.13/1.32      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.13/1.32         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 1.13/1.32          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 1.13/1.32          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.13/1.32  thf('85', plain,
% 1.13/1.32      ((~ (zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B)
% 1.13/1.32        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ (k4_relat_1 @ sk_C))))),
% 1.13/1.32      inference('sup-', [status(thm)], ['83', '84'])).
% 1.13/1.32  thf(zf_stmt_2, axiom,
% 1.13/1.32    (![B:$i,A:$i]:
% 1.13/1.32     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.13/1.32       ( zip_tseitin_0 @ B @ A ) ))).
% 1.13/1.32  thf('86', plain,
% 1.13/1.32      (![X26 : $i, X27 : $i]:
% 1.13/1.32         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.13/1.32  thf('87', plain,
% 1.13/1.32      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.13/1.32        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.13/1.32      inference('simplify', [status(thm)], ['62'])).
% 1.13/1.32  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.13/1.32  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.13/1.32  thf(zf_stmt_5, axiom,
% 1.13/1.32    (![A:$i,B:$i,C:$i]:
% 1.13/1.32     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.13/1.32       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.13/1.32         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.13/1.32           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.13/1.32             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.13/1.32  thf('88', plain,
% 1.13/1.32      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.13/1.32         (~ (zip_tseitin_0 @ X31 @ X32)
% 1.13/1.32          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 1.13/1.32          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.13/1.32  thf('89', plain,
% 1.13/1.32      (((zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B)
% 1.13/1.32        | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 1.13/1.32      inference('sup-', [status(thm)], ['87', '88'])).
% 1.13/1.32  thf('90', plain,
% 1.13/1.32      ((((sk_A) = (k1_xboole_0))
% 1.13/1.32        | (zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B))),
% 1.13/1.32      inference('sup-', [status(thm)], ['86', '89'])).
% 1.13/1.32  thf('91', plain, (((sk_A) != (k1_xboole_0))),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf('92', plain, ((zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B)),
% 1.13/1.32      inference('simplify_reflect-', [status(thm)], ['90', '91'])).
% 1.13/1.32  thf('93', plain,
% 1.13/1.32      (((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ (k4_relat_1 @ sk_C)))),
% 1.13/1.32      inference('demod', [status(thm)], ['85', '92'])).
% 1.13/1.32  thf('94', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 1.13/1.32      inference('sup+', [status(thm)], ['73', '93'])).
% 1.13/1.32  thf('95', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf('96', plain,
% 1.13/1.32      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.13/1.32         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 1.13/1.32          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 1.13/1.32          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.13/1.32  thf('97', plain,
% 1.13/1.32      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 1.13/1.32        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 1.13/1.32      inference('sup-', [status(thm)], ['95', '96'])).
% 1.13/1.32  thf('98', plain,
% 1.13/1.32      (![X26 : $i, X27 : $i]:
% 1.13/1.32         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.13/1.32  thf('99', plain,
% 1.13/1.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf('100', plain,
% 1.13/1.32      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.13/1.32         (~ (zip_tseitin_0 @ X31 @ X32)
% 1.13/1.32          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 1.13/1.32          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.13/1.32  thf('101', plain,
% 1.13/1.32      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 1.13/1.32      inference('sup-', [status(thm)], ['99', '100'])).
% 1.13/1.32  thf('102', plain,
% 1.13/1.32      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 1.13/1.32      inference('sup-', [status(thm)], ['98', '101'])).
% 1.13/1.32  thf('103', plain, (((sk_A) != (k1_xboole_0))),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf('104', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 1.13/1.32      inference('simplify_reflect-', [status(thm)], ['102', '103'])).
% 1.13/1.32  thf('105', plain,
% 1.13/1.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf('106', plain,
% 1.13/1.32      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.13/1.32         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 1.13/1.32          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.13/1.32      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.13/1.32  thf('107', plain,
% 1.13/1.32      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.13/1.32      inference('sup-', [status(thm)], ['105', '106'])).
% 1.13/1.32  thf('108', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.13/1.32      inference('demod', [status(thm)], ['97', '104', '107'])).
% 1.13/1.32  thf('109', plain, ((v1_funct_1 @ sk_C)),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf('110', plain, ((v1_relat_1 @ sk_C)),
% 1.13/1.32      inference('demod', [status(thm)], ['55', '56'])).
% 1.13/1.32  thf('111', plain, ((((sk_B) != (sk_B)) | (v2_funct_1 @ sk_D))),
% 1.13/1.32      inference('demod', [status(thm)],
% 1.13/1.32                ['39', '42', '43', '44', '94', '108', '109', '110'])).
% 1.13/1.32  thf('112', plain, ((v2_funct_1 @ sk_D)),
% 1.13/1.32      inference('simplify', [status(thm)], ['111'])).
% 1.13/1.32  thf('113', plain, (((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))),
% 1.13/1.32      inference('demod', [status(thm)], ['11', '112'])).
% 1.13/1.32  thf('114', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 1.13/1.32      inference('demod', [status(thm)], ['18', '19', '36'])).
% 1.13/1.32  thf(t64_funct_1, axiom,
% 1.13/1.32    (![A:$i]:
% 1.13/1.32     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.13/1.32       ( ![B:$i]:
% 1.13/1.32         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.13/1.32           ( ( ( v2_funct_1 @ A ) & 
% 1.13/1.32               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 1.13/1.32               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 1.13/1.32             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.13/1.32  thf('115', plain,
% 1.13/1.32      (![X13 : $i, X14 : $i]:
% 1.13/1.32         (~ (v1_relat_1 @ X13)
% 1.13/1.32          | ~ (v1_funct_1 @ X13)
% 1.13/1.32          | ((X13) = (k2_funct_1 @ X14))
% 1.13/1.32          | ((k5_relat_1 @ X13 @ X14) != (k6_relat_1 @ (k2_relat_1 @ X14)))
% 1.13/1.32          | ((k2_relat_1 @ X13) != (k1_relat_1 @ X14))
% 1.13/1.32          | ~ (v2_funct_1 @ X14)
% 1.13/1.32          | ~ (v1_funct_1 @ X14)
% 1.13/1.32          | ~ (v1_relat_1 @ X14))),
% 1.13/1.32      inference('cnf', [status(esa)], [t64_funct_1])).
% 1.13/1.32  thf('116', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 1.13/1.32      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.13/1.32  thf('117', plain,
% 1.13/1.32      (![X13 : $i, X14 : $i]:
% 1.13/1.32         (~ (v1_relat_1 @ X13)
% 1.13/1.32          | ~ (v1_funct_1 @ X13)
% 1.13/1.32          | ((X13) = (k2_funct_1 @ X14))
% 1.13/1.32          | ((k5_relat_1 @ X13 @ X14) != (k6_partfun1 @ (k2_relat_1 @ X14)))
% 1.13/1.32          | ((k2_relat_1 @ X13) != (k1_relat_1 @ X14))
% 1.13/1.32          | ~ (v2_funct_1 @ X14)
% 1.13/1.32          | ~ (v1_funct_1 @ X14)
% 1.13/1.32          | ~ (v1_relat_1 @ X14))),
% 1.13/1.32      inference('demod', [status(thm)], ['115', '116'])).
% 1.13/1.32  thf('118', plain,
% 1.13/1.32      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 1.13/1.32        | ~ (v1_relat_1 @ sk_D)
% 1.13/1.32        | ~ (v1_funct_1 @ sk_D)
% 1.13/1.32        | ~ (v2_funct_1 @ sk_D)
% 1.13/1.32        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 1.13/1.32        | ((sk_C) = (k2_funct_1 @ sk_D))
% 1.13/1.32        | ~ (v1_funct_1 @ sk_C)
% 1.13/1.32        | ~ (v1_relat_1 @ sk_C))),
% 1.13/1.32      inference('sup-', [status(thm)], ['114', '117'])).
% 1.13/1.32  thf('119', plain,
% 1.13/1.32      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.13/1.32         = (k6_partfun1 @ sk_A))),
% 1.13/1.32      inference('demod', [status(thm)], ['32', '35'])).
% 1.13/1.32  thf('120', plain,
% 1.13/1.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf(t29_funct_2, axiom,
% 1.13/1.32    (![A:$i,B:$i,C:$i]:
% 1.13/1.32     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.13/1.32         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.13/1.32       ( ![D:$i]:
% 1.13/1.32         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.13/1.32             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.13/1.32           ( ( r2_relset_1 @
% 1.13/1.32               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.13/1.32               ( k6_partfun1 @ A ) ) =>
% 1.13/1.32             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 1.13/1.32  thf('121', plain,
% 1.13/1.32      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 1.13/1.32         (~ (v1_funct_1 @ X49)
% 1.13/1.32          | ~ (v1_funct_2 @ X49 @ X50 @ X51)
% 1.13/1.32          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 1.13/1.32          | (v2_funct_2 @ X49 @ X51)
% 1.13/1.32          | ~ (r2_relset_1 @ X51 @ X51 @ 
% 1.13/1.32               (k1_partfun1 @ X51 @ X50 @ X50 @ X51 @ X52 @ X49) @ 
% 1.13/1.32               (k6_partfun1 @ X51))
% 1.13/1.32          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X50)))
% 1.13/1.32          | ~ (v1_funct_2 @ X52 @ X51 @ X50)
% 1.13/1.32          | ~ (v1_funct_1 @ X52))),
% 1.13/1.32      inference('cnf', [status(esa)], [t29_funct_2])).
% 1.13/1.32  thf('122', plain,
% 1.13/1.32      (![X0 : $i]:
% 1.13/1.32         (~ (v1_funct_1 @ X0)
% 1.13/1.32          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_B)
% 1.13/1.32          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.13/1.32          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.13/1.32               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ X0 @ sk_D) @ 
% 1.13/1.32               (k6_partfun1 @ sk_A))
% 1.13/1.32          | (v2_funct_2 @ sk_D @ sk_A)
% 1.13/1.32          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.13/1.32          | ~ (v1_funct_1 @ sk_D))),
% 1.13/1.32      inference('sup-', [status(thm)], ['120', '121'])).
% 1.13/1.32  thf('123', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf('124', plain, ((v1_funct_1 @ sk_D)),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf('125', plain,
% 1.13/1.32      (![X0 : $i]:
% 1.13/1.32         (~ (v1_funct_1 @ X0)
% 1.13/1.32          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_B)
% 1.13/1.32          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.13/1.32          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.13/1.32               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ X0 @ sk_D) @ 
% 1.13/1.32               (k6_partfun1 @ sk_A))
% 1.13/1.32          | (v2_funct_2 @ sk_D @ sk_A))),
% 1.13/1.32      inference('demod', [status(thm)], ['122', '123', '124'])).
% 1.13/1.32  thf('126', plain,
% 1.13/1.32      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 1.13/1.32           (k6_partfun1 @ sk_A))
% 1.13/1.32        | (v2_funct_2 @ sk_D @ sk_A)
% 1.13/1.32        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.13/1.32        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.13/1.32        | ~ (v1_funct_1 @ sk_C))),
% 1.13/1.32      inference('sup-', [status(thm)], ['119', '125'])).
% 1.13/1.32  thf('127', plain,
% 1.13/1.32      (![X25 : $i]:
% 1.13/1.32         (m1_subset_1 @ (k6_partfun1 @ X25) @ 
% 1.13/1.32          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))),
% 1.13/1.32      inference('demod', [status(thm)], ['33', '34'])).
% 1.13/1.32  thf('128', plain,
% 1.13/1.32      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 1.13/1.32         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 1.13/1.32          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 1.13/1.32          | (r2_relset_1 @ X22 @ X23 @ X21 @ X24)
% 1.13/1.32          | ((X21) != (X24)))),
% 1.13/1.32      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.13/1.32  thf('129', plain,
% 1.13/1.32      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.13/1.32         ((r2_relset_1 @ X22 @ X23 @ X24 @ X24)
% 1.13/1.32          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 1.13/1.32      inference('simplify', [status(thm)], ['128'])).
% 1.13/1.32  thf('130', plain,
% 1.13/1.32      (![X0 : $i]:
% 1.13/1.32         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 1.13/1.32      inference('sup-', [status(thm)], ['127', '129'])).
% 1.13/1.32  thf('131', plain,
% 1.13/1.32      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf('132', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf('133', plain, ((v1_funct_1 @ sk_C)),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf('134', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 1.13/1.32      inference('demod', [status(thm)], ['126', '130', '131', '132', '133'])).
% 1.13/1.32  thf(d3_funct_2, axiom,
% 1.13/1.32    (![A:$i,B:$i]:
% 1.13/1.32     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 1.13/1.32       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 1.13/1.32  thf('135', plain,
% 1.13/1.32      (![X34 : $i, X35 : $i]:
% 1.13/1.32         (~ (v2_funct_2 @ X35 @ X34)
% 1.13/1.32          | ((k2_relat_1 @ X35) = (X34))
% 1.13/1.32          | ~ (v5_relat_1 @ X35 @ X34)
% 1.13/1.32          | ~ (v1_relat_1 @ X35))),
% 1.13/1.32      inference('cnf', [status(esa)], [d3_funct_2])).
% 1.13/1.32  thf('136', plain,
% 1.13/1.32      ((~ (v1_relat_1 @ sk_D)
% 1.13/1.32        | ~ (v5_relat_1 @ sk_D @ sk_A)
% 1.13/1.32        | ((k2_relat_1 @ sk_D) = (sk_A)))),
% 1.13/1.32      inference('sup-', [status(thm)], ['134', '135'])).
% 1.13/1.32  thf('137', plain, ((v1_relat_1 @ sk_D)),
% 1.13/1.32      inference('demod', [status(thm)], ['2', '3'])).
% 1.13/1.32  thf('138', plain,
% 1.13/1.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf(cc2_relset_1, axiom,
% 1.13/1.32    (![A:$i,B:$i,C:$i]:
% 1.13/1.32     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.13/1.32       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.13/1.32  thf('139', plain,
% 1.13/1.32      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.13/1.32         ((v5_relat_1 @ X15 @ X17)
% 1.13/1.32          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 1.13/1.32      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.13/1.32  thf('140', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 1.13/1.32      inference('sup-', [status(thm)], ['138', '139'])).
% 1.13/1.32  thf('141', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.13/1.32      inference('demod', [status(thm)], ['136', '137', '140'])).
% 1.13/1.32  thf('142', plain, ((v1_relat_1 @ sk_D)),
% 1.13/1.32      inference('demod', [status(thm)], ['2', '3'])).
% 1.13/1.32  thf('143', plain, ((v1_funct_1 @ sk_D)),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf('144', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 1.13/1.32      inference('sup+', [status(thm)], ['73', '93'])).
% 1.13/1.32  thf('145', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.13/1.32      inference('demod', [status(thm)], ['97', '104', '107'])).
% 1.13/1.32  thf('146', plain, ((v1_funct_1 @ sk_C)),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf('147', plain, ((v1_relat_1 @ sk_C)),
% 1.13/1.32      inference('demod', [status(thm)], ['55', '56'])).
% 1.13/1.32  thf('148', plain,
% 1.13/1.32      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 1.13/1.32        | ~ (v2_funct_1 @ sk_D)
% 1.13/1.32        | ((sk_B) != (sk_B))
% 1.13/1.32        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 1.13/1.32      inference('demod', [status(thm)],
% 1.13/1.32                ['118', '141', '142', '143', '144', '145', '146', '147'])).
% 1.13/1.32  thf('149', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 1.13/1.32      inference('simplify', [status(thm)], ['148'])).
% 1.13/1.32  thf('150', plain, ((v2_funct_1 @ sk_D)),
% 1.13/1.32      inference('simplify', [status(thm)], ['111'])).
% 1.13/1.32  thf('151', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.13/1.32      inference('demod', [status(thm)], ['149', '150'])).
% 1.13/1.32  thf('152', plain, (((sk_C) = (k4_relat_1 @ sk_D))),
% 1.13/1.32      inference('sup+', [status(thm)], ['113', '151'])).
% 1.13/1.32  thf('153', plain, (((k4_relat_1 @ sk_C) = (sk_D))),
% 1.13/1.32      inference('demod', [status(thm)], ['6', '152'])).
% 1.13/1.32  thf('154', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.13/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.32  thf('155', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.13/1.32      inference('demod', [status(thm)], ['52', '57', '58'])).
% 1.13/1.32  thf('156', plain, (((sk_D) != (k4_relat_1 @ sk_C))),
% 1.13/1.32      inference('demod', [status(thm)], ['154', '155'])).
% 1.13/1.32  thf('157', plain, ($false),
% 1.13/1.32      inference('simplify_reflect-', [status(thm)], ['153', '156'])).
% 1.13/1.32  
% 1.13/1.32  % SZS output end Refutation
% 1.13/1.32  
% 1.13/1.33  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

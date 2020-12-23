%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HmxUMJM9pi

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:17 EST 2020

% Result     : Theorem 6.44s
% Output     : Refutation 6.44s
% Verified   : 
% Statistics : Number of formulae       :  196 ( 763 expanded)
%              Number of leaves         :   55 ( 254 expanded)
%              Depth                    :   19
%              Number of atoms          : 1755 (17225 expanded)
%              Number of equality atoms :  119 (1201 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

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
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_funct_1 @ X7 )
        = ( k4_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
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
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( ( k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46 )
        = ( k5_relat_1 @ X43 @ X46 ) ) ) ),
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

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('21',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('22',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
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

thf('25',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('32',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( X21 = X24 )
      | ~ ( r2_relset_1 @ X22 @ X23 @ X21 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','33'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('35',plain,(
    ! [X42: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('36',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('37',plain,(
    ! [X42: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X42 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('39',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['18','19','38'])).

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

thf('40',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( v2_funct_1 @ X11 )
      | ( ( k2_relat_1 @ X10 )
       != ( k1_relat_1 @ X11 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X10 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('41',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('42',plain,(
    ! [X9: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('43',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['2','3'])).

thf('44',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_funct_1 @ X7 )
        = ( k4_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('50',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('52',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['47','52','53'])).

thf(t59_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
            = ( k2_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
            = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('55',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X12 ) @ X12 ) )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t59_funct_1])).

thf('56',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['50','51'])).

thf('58',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf('61',plain,(
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

thf('62',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ( X54 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_funct_2 @ X55 @ X56 @ X54 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X54 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X55 ) @ X55 )
        = ( k6_partfun1 @ X54 ) )
      | ~ ( v2_funct_1 @ X55 )
      | ( ( k2_relset_1 @ X56 @ X54 @ X55 )
       != X54 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('63',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('64',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ( X54 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_funct_2 @ X55 @ X56 @ X54 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X54 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X55 ) @ X55 )
        = ( k6_relat_1 @ X54 ) )
      | ~ ( v2_funct_1 @ X55 )
      | ( ( k2_relset_1 @ X56 @ X54 @ X55 )
       != X54 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['47','52','53'])).

thf('69',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66','67','68','69','70'])).

thf('72',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['72','73'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('75',plain,(
    ! [X6: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('76',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','74','75'])).

thf('77',plain,(
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

thf('78',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ( X27
        = ( k1_relset_1 @ X27 @ X28 @ X29 ) )
      | ~ ( zip_tseitin_1 @ X29 @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('79',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('80',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('81',plain,(
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

thf('82',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('83',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('88',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('89',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['79','86','89'])).

thf('91',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['50','51'])).

thf('93',plain,
    ( ( sk_B != sk_B )
    | ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['41','42','43','44','76','90','91','92'])).

thf('94',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,
    ( ( k2_funct_1 @ sk_D )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['11','94'])).

thf('96',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['18','19','38'])).

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

thf('97',plain,(
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

thf('98',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('100',plain,(
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

thf('101',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X52 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) )
      | ( v2_funct_2 @ X50 @ X52 )
      | ~ ( r2_relset_1 @ X52 @ X52 @ ( k1_partfun1 @ X52 @ X51 @ X51 @ X52 @ X53 @ X50 ) @ ( k6_partfun1 @ X52 ) )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X51 ) ) )
      | ~ ( v1_funct_2 @ X53 @ X52 @ X51 )
      | ~ ( v1_funct_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t29_funct_2])).

thf('102',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('103',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X52 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) )
      | ( v2_funct_2 @ X50 @ X52 )
      | ~ ( r2_relset_1 @ X52 @ X52 @ ( k1_partfun1 @ X52 @ X51 @ X51 @ X52 @ X53 @ X50 ) @ ( k6_relat_1 @ X52 ) )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X51 ) ) )
      | ~ ( v1_funct_2 @ X53 @ X52 @ X51 )
      | ~ ( v1_funct_1 @ X53 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) @ ( k6_relat_1 @ sk_A ) )
      | ( v2_funct_2 @ sk_D @ sk_A )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['100','103'])).

thf('105',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) @ ( k6_relat_1 @ sk_A ) )
      | ( v2_funct_2 @ sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['99','107'])).

thf('109',plain,(
    ! [X42: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X42 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('110',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( r2_relset_1 @ X22 @ X23 @ X21 @ X24 )
      | ( X21 != X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('111',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_relset_1 @ X22 @ X23 @ X24 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['108','112','113','114','115'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('117',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v2_funct_2 @ X34 @ X33 )
      | ( ( k2_relat_1 @ X34 )
        = X33 )
      | ~ ( v5_relat_1 @ X34 @ X33 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('118',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( ( k2_relat_1 @ sk_D )
      = sk_A ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['2','3'])).

thf('120',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('121',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v5_relat_1 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('122',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['118','119','122'])).

thf('124',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['2','3'])).

thf('125',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','74','75'])).

thf('127',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['79','86','89'])).

thf('128',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['50','51'])).

thf('130',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B != sk_B )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['98','123','124','125','126','127','128','129'])).

thf('131',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['93'])).

thf('133',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,
    ( sk_C
    = ( k4_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['95','133'])).

thf('135',plain,
    ( ( k4_relat_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['6','134'])).

thf('136',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['47','52','53'])).

thf('138',plain,(
    sk_D
 != ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['135','138'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HmxUMJM9pi
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:15:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 6.44/6.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.44/6.67  % Solved by: fo/fo7.sh
% 6.44/6.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.44/6.67  % done 1505 iterations in 6.210s
% 6.44/6.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.44/6.67  % SZS output start Refutation
% 6.44/6.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 6.44/6.67  thf(sk_D_type, type, sk_D: $i).
% 6.44/6.67  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 6.44/6.67  thf(sk_C_type, type, sk_C: $i).
% 6.44/6.67  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 6.44/6.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.44/6.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.44/6.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.44/6.67  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 6.44/6.67  thf(sk_B_type, type, sk_B: $i).
% 6.44/6.67  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 6.44/6.67  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 6.44/6.67  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 6.44/6.67  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 6.44/6.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.44/6.67  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 6.44/6.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.44/6.67  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 6.44/6.67  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 6.44/6.67  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 6.44/6.67  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 6.44/6.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 6.44/6.67  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 6.44/6.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 6.44/6.67  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 6.44/6.67  thf(sk_A_type, type, sk_A: $i).
% 6.44/6.67  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 6.44/6.67  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 6.44/6.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 6.44/6.67  thf(t36_funct_2, conjecture,
% 6.44/6.67    (![A:$i,B:$i,C:$i]:
% 6.44/6.67     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.44/6.67         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.44/6.67       ( ![D:$i]:
% 6.44/6.67         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 6.44/6.67             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 6.44/6.67           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 6.44/6.67               ( r2_relset_1 @
% 6.44/6.67                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 6.44/6.67                 ( k6_partfun1 @ A ) ) & 
% 6.44/6.67               ( v2_funct_1 @ C ) ) =>
% 6.44/6.67             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 6.44/6.67               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 6.44/6.67  thf(zf_stmt_0, negated_conjecture,
% 6.44/6.67    (~( ![A:$i,B:$i,C:$i]:
% 6.44/6.67        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.44/6.67            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.44/6.67          ( ![D:$i]:
% 6.44/6.67            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 6.44/6.67                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 6.44/6.67              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 6.44/6.67                  ( r2_relset_1 @
% 6.44/6.67                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 6.44/6.67                    ( k6_partfun1 @ A ) ) & 
% 6.44/6.67                  ( v2_funct_1 @ C ) ) =>
% 6.44/6.67                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 6.44/6.67                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 6.44/6.67    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 6.44/6.67  thf('0', plain,
% 6.44/6.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf(cc2_relat_1, axiom,
% 6.44/6.67    (![A:$i]:
% 6.44/6.67     ( ( v1_relat_1 @ A ) =>
% 6.44/6.67       ( ![B:$i]:
% 6.44/6.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 6.44/6.67  thf('1', plain,
% 6.44/6.67      (![X0 : $i, X1 : $i]:
% 6.44/6.67         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 6.44/6.67          | (v1_relat_1 @ X0)
% 6.44/6.67          | ~ (v1_relat_1 @ X1))),
% 6.44/6.67      inference('cnf', [status(esa)], [cc2_relat_1])).
% 6.44/6.67  thf('2', plain,
% 6.44/6.67      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 6.44/6.67      inference('sup-', [status(thm)], ['0', '1'])).
% 6.44/6.67  thf(fc6_relat_1, axiom,
% 6.44/6.67    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 6.44/6.67  thf('3', plain,
% 6.44/6.67      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 6.44/6.67      inference('cnf', [status(esa)], [fc6_relat_1])).
% 6.44/6.67  thf('4', plain, ((v1_relat_1 @ sk_D)),
% 6.44/6.67      inference('demod', [status(thm)], ['2', '3'])).
% 6.44/6.67  thf(involutiveness_k4_relat_1, axiom,
% 6.44/6.67    (![A:$i]:
% 6.44/6.67     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 6.44/6.67  thf('5', plain,
% 6.44/6.67      (![X4 : $i]:
% 6.44/6.67         (((k4_relat_1 @ (k4_relat_1 @ X4)) = (X4)) | ~ (v1_relat_1 @ X4))),
% 6.44/6.67      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 6.44/6.67  thf('6', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 6.44/6.67      inference('sup-', [status(thm)], ['4', '5'])).
% 6.44/6.67  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf(d9_funct_1, axiom,
% 6.44/6.67    (![A:$i]:
% 6.44/6.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.44/6.67       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 6.44/6.67  thf('8', plain,
% 6.44/6.67      (![X7 : $i]:
% 6.44/6.67         (~ (v2_funct_1 @ X7)
% 6.44/6.67          | ((k2_funct_1 @ X7) = (k4_relat_1 @ X7))
% 6.44/6.67          | ~ (v1_funct_1 @ X7)
% 6.44/6.67          | ~ (v1_relat_1 @ X7))),
% 6.44/6.67      inference('cnf', [status(esa)], [d9_funct_1])).
% 6.44/6.67  thf('9', plain,
% 6.44/6.67      ((~ (v1_relat_1 @ sk_D)
% 6.44/6.67        | ((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))
% 6.44/6.67        | ~ (v2_funct_1 @ sk_D))),
% 6.44/6.67      inference('sup-', [status(thm)], ['7', '8'])).
% 6.44/6.67  thf('10', plain, ((v1_relat_1 @ sk_D)),
% 6.44/6.67      inference('demod', [status(thm)], ['2', '3'])).
% 6.44/6.67  thf('11', plain,
% 6.44/6.67      ((((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 6.44/6.67      inference('demod', [status(thm)], ['9', '10'])).
% 6.44/6.67  thf('12', plain,
% 6.44/6.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf('13', plain,
% 6.44/6.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf(redefinition_k1_partfun1, axiom,
% 6.44/6.67    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 6.44/6.67     ( ( ( v1_funct_1 @ E ) & 
% 6.44/6.67         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.44/6.67         ( v1_funct_1 @ F ) & 
% 6.44/6.67         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 6.44/6.67       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 6.44/6.67  thf('14', plain,
% 6.44/6.67      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 6.44/6.67         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 6.44/6.67          | ~ (v1_funct_1 @ X43)
% 6.44/6.67          | ~ (v1_funct_1 @ X46)
% 6.44/6.67          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 6.44/6.67          | ((k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46)
% 6.44/6.67              = (k5_relat_1 @ X43 @ X46)))),
% 6.44/6.67      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 6.44/6.67  thf('15', plain,
% 6.44/6.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.44/6.67         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 6.44/6.67            = (k5_relat_1 @ sk_C @ X0))
% 6.44/6.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 6.44/6.67          | ~ (v1_funct_1 @ X0)
% 6.44/6.67          | ~ (v1_funct_1 @ sk_C))),
% 6.44/6.67      inference('sup-', [status(thm)], ['13', '14'])).
% 6.44/6.67  thf('16', plain, ((v1_funct_1 @ sk_C)),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf('17', plain,
% 6.44/6.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.44/6.67         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 6.44/6.67            = (k5_relat_1 @ sk_C @ X0))
% 6.44/6.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 6.44/6.67          | ~ (v1_funct_1 @ X0))),
% 6.44/6.67      inference('demod', [status(thm)], ['15', '16'])).
% 6.44/6.67  thf('18', plain,
% 6.44/6.67      ((~ (v1_funct_1 @ sk_D)
% 6.44/6.67        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 6.44/6.67            = (k5_relat_1 @ sk_C @ sk_D)))),
% 6.44/6.67      inference('sup-', [status(thm)], ['12', '17'])).
% 6.44/6.67  thf('19', plain, ((v1_funct_1 @ sk_D)),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf('20', plain,
% 6.44/6.67      ((r2_relset_1 @ sk_A @ sk_A @ 
% 6.44/6.67        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 6.44/6.67        (k6_partfun1 @ sk_A))),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf(redefinition_k6_partfun1, axiom,
% 6.44/6.67    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 6.44/6.67  thf('21', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 6.44/6.67      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 6.44/6.67  thf('22', plain,
% 6.44/6.67      ((r2_relset_1 @ sk_A @ sk_A @ 
% 6.44/6.67        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 6.44/6.67        (k6_relat_1 @ sk_A))),
% 6.44/6.67      inference('demod', [status(thm)], ['20', '21'])).
% 6.44/6.67  thf('23', plain,
% 6.44/6.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf('24', plain,
% 6.44/6.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf(dt_k1_partfun1, axiom,
% 6.44/6.67    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 6.44/6.67     ( ( ( v1_funct_1 @ E ) & 
% 6.44/6.67         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.44/6.67         ( v1_funct_1 @ F ) & 
% 6.44/6.67         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 6.44/6.67       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 6.44/6.67         ( m1_subset_1 @
% 6.44/6.67           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 6.44/6.67           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 6.44/6.67  thf('25', plain,
% 6.44/6.67      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 6.44/6.67         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 6.44/6.67          | ~ (v1_funct_1 @ X35)
% 6.44/6.67          | ~ (v1_funct_1 @ X38)
% 6.44/6.67          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 6.44/6.67          | (m1_subset_1 @ (k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38) @ 
% 6.44/6.67             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X40))))),
% 6.44/6.67      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 6.44/6.67  thf('26', plain,
% 6.44/6.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.44/6.67         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 6.44/6.67           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 6.44/6.67          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 6.44/6.67          | ~ (v1_funct_1 @ X1)
% 6.44/6.67          | ~ (v1_funct_1 @ sk_C))),
% 6.44/6.67      inference('sup-', [status(thm)], ['24', '25'])).
% 6.44/6.67  thf('27', plain, ((v1_funct_1 @ sk_C)),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf('28', plain,
% 6.44/6.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.44/6.67         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 6.44/6.67           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 6.44/6.67          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 6.44/6.67          | ~ (v1_funct_1 @ X1))),
% 6.44/6.67      inference('demod', [status(thm)], ['26', '27'])).
% 6.44/6.67  thf('29', plain,
% 6.44/6.67      ((~ (v1_funct_1 @ sk_D)
% 6.44/6.67        | (m1_subset_1 @ 
% 6.44/6.67           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 6.44/6.67           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 6.44/6.67      inference('sup-', [status(thm)], ['23', '28'])).
% 6.44/6.67  thf('30', plain, ((v1_funct_1 @ sk_D)),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf('31', plain,
% 6.44/6.67      ((m1_subset_1 @ 
% 6.44/6.67        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 6.44/6.67        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.44/6.67      inference('demod', [status(thm)], ['29', '30'])).
% 6.44/6.67  thf(redefinition_r2_relset_1, axiom,
% 6.44/6.67    (![A:$i,B:$i,C:$i,D:$i]:
% 6.44/6.67     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.44/6.67         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.44/6.67       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 6.44/6.67  thf('32', plain,
% 6.44/6.67      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 6.44/6.67         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 6.44/6.67          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 6.44/6.67          | ((X21) = (X24))
% 6.44/6.67          | ~ (r2_relset_1 @ X22 @ X23 @ X21 @ X24))),
% 6.44/6.67      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 6.44/6.67  thf('33', plain,
% 6.44/6.67      (![X0 : $i]:
% 6.44/6.67         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 6.44/6.67             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 6.44/6.67          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 6.44/6.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 6.44/6.67      inference('sup-', [status(thm)], ['31', '32'])).
% 6.44/6.67  thf('34', plain,
% 6.44/6.67      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 6.44/6.67           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 6.44/6.67        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 6.44/6.67            = (k6_relat_1 @ sk_A)))),
% 6.44/6.67      inference('sup-', [status(thm)], ['22', '33'])).
% 6.44/6.67  thf(dt_k6_partfun1, axiom,
% 6.44/6.67    (![A:$i]:
% 6.44/6.67     ( ( m1_subset_1 @
% 6.44/6.67         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 6.44/6.67       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 6.44/6.67  thf('35', plain,
% 6.44/6.67      (![X42 : $i]:
% 6.44/6.67         (m1_subset_1 @ (k6_partfun1 @ X42) @ 
% 6.44/6.67          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X42)))),
% 6.44/6.67      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 6.44/6.67  thf('36', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 6.44/6.67      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 6.44/6.67  thf('37', plain,
% 6.44/6.67      (![X42 : $i]:
% 6.44/6.67         (m1_subset_1 @ (k6_relat_1 @ X42) @ 
% 6.44/6.67          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X42)))),
% 6.44/6.67      inference('demod', [status(thm)], ['35', '36'])).
% 6.44/6.67  thf('38', plain,
% 6.44/6.67      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 6.44/6.67         = (k6_relat_1 @ sk_A))),
% 6.44/6.67      inference('demod', [status(thm)], ['34', '37'])).
% 6.44/6.67  thf('39', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 6.44/6.67      inference('demod', [status(thm)], ['18', '19', '38'])).
% 6.44/6.67  thf(t48_funct_1, axiom,
% 6.44/6.67    (![A:$i]:
% 6.44/6.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.44/6.67       ( ![B:$i]:
% 6.44/6.67         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 6.44/6.67           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 6.44/6.67               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 6.44/6.67             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 6.44/6.67  thf('40', plain,
% 6.44/6.67      (![X10 : $i, X11 : $i]:
% 6.44/6.67         (~ (v1_relat_1 @ X10)
% 6.44/6.67          | ~ (v1_funct_1 @ X10)
% 6.44/6.67          | (v2_funct_1 @ X11)
% 6.44/6.67          | ((k2_relat_1 @ X10) != (k1_relat_1 @ X11))
% 6.44/6.67          | ~ (v2_funct_1 @ (k5_relat_1 @ X10 @ X11))
% 6.44/6.67          | ~ (v1_funct_1 @ X11)
% 6.44/6.67          | ~ (v1_relat_1 @ X11))),
% 6.44/6.67      inference('cnf', [status(esa)], [t48_funct_1])).
% 6.44/6.67  thf('41', plain,
% 6.44/6.67      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 6.44/6.67        | ~ (v1_relat_1 @ sk_D)
% 6.44/6.67        | ~ (v1_funct_1 @ sk_D)
% 6.44/6.67        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 6.44/6.67        | (v2_funct_1 @ sk_D)
% 6.44/6.67        | ~ (v1_funct_1 @ sk_C)
% 6.44/6.67        | ~ (v1_relat_1 @ sk_C))),
% 6.44/6.67      inference('sup-', [status(thm)], ['39', '40'])).
% 6.44/6.67  thf(fc4_funct_1, axiom,
% 6.44/6.67    (![A:$i]:
% 6.44/6.67     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 6.44/6.67       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 6.44/6.67  thf('42', plain, (![X9 : $i]: (v2_funct_1 @ (k6_relat_1 @ X9))),
% 6.44/6.67      inference('cnf', [status(esa)], [fc4_funct_1])).
% 6.44/6.67  thf('43', plain, ((v1_relat_1 @ sk_D)),
% 6.44/6.67      inference('demod', [status(thm)], ['2', '3'])).
% 6.44/6.67  thf('44', plain, ((v1_funct_1 @ sk_D)),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf('45', plain, ((v1_funct_1 @ sk_C)),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf('46', plain,
% 6.44/6.67      (![X7 : $i]:
% 6.44/6.67         (~ (v2_funct_1 @ X7)
% 6.44/6.67          | ((k2_funct_1 @ X7) = (k4_relat_1 @ X7))
% 6.44/6.67          | ~ (v1_funct_1 @ X7)
% 6.44/6.67          | ~ (v1_relat_1 @ X7))),
% 6.44/6.67      inference('cnf', [status(esa)], [d9_funct_1])).
% 6.44/6.67  thf('47', plain,
% 6.44/6.67      ((~ (v1_relat_1 @ sk_C)
% 6.44/6.67        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 6.44/6.67        | ~ (v2_funct_1 @ sk_C))),
% 6.44/6.67      inference('sup-', [status(thm)], ['45', '46'])).
% 6.44/6.67  thf('48', plain,
% 6.44/6.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf('49', plain,
% 6.44/6.67      (![X0 : $i, X1 : $i]:
% 6.44/6.67         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 6.44/6.67          | (v1_relat_1 @ X0)
% 6.44/6.67          | ~ (v1_relat_1 @ X1))),
% 6.44/6.67      inference('cnf', [status(esa)], [cc2_relat_1])).
% 6.44/6.67  thf('50', plain,
% 6.44/6.67      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 6.44/6.67      inference('sup-', [status(thm)], ['48', '49'])).
% 6.44/6.67  thf('51', plain,
% 6.44/6.67      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 6.44/6.67      inference('cnf', [status(esa)], [fc6_relat_1])).
% 6.44/6.67  thf('52', plain, ((v1_relat_1 @ sk_C)),
% 6.44/6.67      inference('demod', [status(thm)], ['50', '51'])).
% 6.44/6.67  thf('53', plain, ((v2_funct_1 @ sk_C)),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf('54', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 6.44/6.67      inference('demod', [status(thm)], ['47', '52', '53'])).
% 6.44/6.67  thf(t59_funct_1, axiom,
% 6.44/6.67    (![A:$i]:
% 6.44/6.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.44/6.67       ( ( v2_funct_1 @ A ) =>
% 6.44/6.67         ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 6.44/6.67             ( k2_relat_1 @ A ) ) & 
% 6.44/6.67           ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 6.44/6.67             ( k2_relat_1 @ A ) ) ) ) ))).
% 6.44/6.67  thf('55', plain,
% 6.44/6.67      (![X12 : $i]:
% 6.44/6.67         (~ (v2_funct_1 @ X12)
% 6.44/6.67          | ((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X12) @ X12))
% 6.44/6.67              = (k2_relat_1 @ X12))
% 6.44/6.67          | ~ (v1_funct_1 @ X12)
% 6.44/6.67          | ~ (v1_relat_1 @ X12))),
% 6.44/6.67      inference('cnf', [status(esa)], [t59_funct_1])).
% 6.44/6.67  thf('56', plain,
% 6.44/6.67      ((((k2_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C))
% 6.44/6.67          = (k2_relat_1 @ sk_C))
% 6.44/6.67        | ~ (v1_relat_1 @ sk_C)
% 6.44/6.67        | ~ (v1_funct_1 @ sk_C)
% 6.44/6.67        | ~ (v2_funct_1 @ sk_C))),
% 6.44/6.67      inference('sup+', [status(thm)], ['54', '55'])).
% 6.44/6.67  thf('57', plain, ((v1_relat_1 @ sk_C)),
% 6.44/6.67      inference('demod', [status(thm)], ['50', '51'])).
% 6.44/6.67  thf('58', plain, ((v1_funct_1 @ sk_C)),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf('59', plain, ((v2_funct_1 @ sk_C)),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf('60', plain,
% 6.44/6.67      (((k2_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C))
% 6.44/6.67         = (k2_relat_1 @ sk_C))),
% 6.44/6.67      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 6.44/6.67  thf('61', plain,
% 6.44/6.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf(t35_funct_2, axiom,
% 6.44/6.67    (![A:$i,B:$i,C:$i]:
% 6.44/6.67     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.44/6.67         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.44/6.67       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 6.44/6.67         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 6.44/6.67           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 6.44/6.67             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 6.44/6.67  thf('62', plain,
% 6.44/6.67      (![X54 : $i, X55 : $i, X56 : $i]:
% 6.44/6.67         (((X54) = (k1_xboole_0))
% 6.44/6.67          | ~ (v1_funct_1 @ X55)
% 6.44/6.67          | ~ (v1_funct_2 @ X55 @ X56 @ X54)
% 6.44/6.67          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X54)))
% 6.44/6.67          | ((k5_relat_1 @ (k2_funct_1 @ X55) @ X55) = (k6_partfun1 @ X54))
% 6.44/6.67          | ~ (v2_funct_1 @ X55)
% 6.44/6.67          | ((k2_relset_1 @ X56 @ X54 @ X55) != (X54)))),
% 6.44/6.67      inference('cnf', [status(esa)], [t35_funct_2])).
% 6.44/6.67  thf('63', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 6.44/6.67      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 6.44/6.67  thf('64', plain,
% 6.44/6.67      (![X54 : $i, X55 : $i, X56 : $i]:
% 6.44/6.67         (((X54) = (k1_xboole_0))
% 6.44/6.67          | ~ (v1_funct_1 @ X55)
% 6.44/6.67          | ~ (v1_funct_2 @ X55 @ X56 @ X54)
% 6.44/6.67          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X54)))
% 6.44/6.67          | ((k5_relat_1 @ (k2_funct_1 @ X55) @ X55) = (k6_relat_1 @ X54))
% 6.44/6.67          | ~ (v2_funct_1 @ X55)
% 6.44/6.67          | ((k2_relset_1 @ X56 @ X54 @ X55) != (X54)))),
% 6.44/6.67      inference('demod', [status(thm)], ['62', '63'])).
% 6.44/6.67  thf('65', plain,
% 6.44/6.67      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 6.44/6.67        | ~ (v2_funct_1 @ sk_C)
% 6.44/6.67        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 6.44/6.67        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 6.44/6.67        | ~ (v1_funct_1 @ sk_C)
% 6.44/6.67        | ((sk_B) = (k1_xboole_0)))),
% 6.44/6.67      inference('sup-', [status(thm)], ['61', '64'])).
% 6.44/6.67  thf('66', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf('67', plain, ((v2_funct_1 @ sk_C)),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf('68', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 6.44/6.67      inference('demod', [status(thm)], ['47', '52', '53'])).
% 6.44/6.67  thf('69', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf('70', plain, ((v1_funct_1 @ sk_C)),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf('71', plain,
% 6.44/6.67      ((((sk_B) != (sk_B))
% 6.44/6.67        | ((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 6.44/6.67        | ((sk_B) = (k1_xboole_0)))),
% 6.44/6.67      inference('demod', [status(thm)], ['65', '66', '67', '68', '69', '70'])).
% 6.44/6.67  thf('72', plain,
% 6.44/6.67      ((((sk_B) = (k1_xboole_0))
% 6.44/6.67        | ((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B)))),
% 6.44/6.67      inference('simplify', [status(thm)], ['71'])).
% 6.44/6.67  thf('73', plain, (((sk_B) != (k1_xboole_0))),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf('74', plain,
% 6.44/6.67      (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))),
% 6.44/6.67      inference('simplify_reflect-', [status(thm)], ['72', '73'])).
% 6.44/6.67  thf(t71_relat_1, axiom,
% 6.44/6.67    (![A:$i]:
% 6.44/6.67     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 6.44/6.67       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 6.44/6.67  thf('75', plain, (![X6 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X6)) = (X6))),
% 6.44/6.67      inference('cnf', [status(esa)], [t71_relat_1])).
% 6.44/6.67  thf('76', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 6.44/6.67      inference('demod', [status(thm)], ['60', '74', '75'])).
% 6.44/6.67  thf('77', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf(d1_funct_2, axiom,
% 6.44/6.67    (![A:$i,B:$i,C:$i]:
% 6.44/6.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.44/6.67       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.44/6.67           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 6.44/6.67             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 6.44/6.67         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.44/6.67           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 6.44/6.67             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 6.44/6.67  thf(zf_stmt_1, axiom,
% 6.44/6.67    (![C:$i,B:$i,A:$i]:
% 6.44/6.67     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 6.44/6.67       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 6.44/6.67  thf('78', plain,
% 6.44/6.67      (![X27 : $i, X28 : $i, X29 : $i]:
% 6.44/6.67         (~ (v1_funct_2 @ X29 @ X27 @ X28)
% 6.44/6.67          | ((X27) = (k1_relset_1 @ X27 @ X28 @ X29))
% 6.44/6.67          | ~ (zip_tseitin_1 @ X29 @ X28 @ X27))),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.44/6.67  thf('79', plain,
% 6.44/6.67      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 6.44/6.67        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 6.44/6.67      inference('sup-', [status(thm)], ['77', '78'])).
% 6.44/6.67  thf(zf_stmt_2, axiom,
% 6.44/6.67    (![B:$i,A:$i]:
% 6.44/6.67     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.44/6.67       ( zip_tseitin_0 @ B @ A ) ))).
% 6.44/6.67  thf('80', plain,
% 6.44/6.67      (![X25 : $i, X26 : $i]:
% 6.44/6.67         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_2])).
% 6.44/6.67  thf('81', plain,
% 6.44/6.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 6.44/6.67  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 6.44/6.67  thf(zf_stmt_5, axiom,
% 6.44/6.67    (![A:$i,B:$i,C:$i]:
% 6.44/6.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.44/6.67       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 6.44/6.67         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.44/6.67           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 6.44/6.67             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 6.44/6.67  thf('82', plain,
% 6.44/6.67      (![X30 : $i, X31 : $i, X32 : $i]:
% 6.44/6.67         (~ (zip_tseitin_0 @ X30 @ X31)
% 6.44/6.67          | (zip_tseitin_1 @ X32 @ X30 @ X31)
% 6.44/6.67          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_5])).
% 6.44/6.67  thf('83', plain,
% 6.44/6.67      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 6.44/6.67      inference('sup-', [status(thm)], ['81', '82'])).
% 6.44/6.67  thf('84', plain,
% 6.44/6.67      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 6.44/6.67      inference('sup-', [status(thm)], ['80', '83'])).
% 6.44/6.67  thf('85', plain, (((sk_A) != (k1_xboole_0))),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf('86', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 6.44/6.67      inference('simplify_reflect-', [status(thm)], ['84', '85'])).
% 6.44/6.67  thf('87', plain,
% 6.44/6.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf(redefinition_k1_relset_1, axiom,
% 6.44/6.67    (![A:$i,B:$i,C:$i]:
% 6.44/6.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.44/6.67       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 6.44/6.67  thf('88', plain,
% 6.44/6.67      (![X18 : $i, X19 : $i, X20 : $i]:
% 6.44/6.67         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 6.44/6.67          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 6.44/6.67      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.44/6.67  thf('89', plain,
% 6.44/6.67      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 6.44/6.67      inference('sup-', [status(thm)], ['87', '88'])).
% 6.44/6.67  thf('90', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 6.44/6.67      inference('demod', [status(thm)], ['79', '86', '89'])).
% 6.44/6.67  thf('91', plain, ((v1_funct_1 @ sk_C)),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf('92', plain, ((v1_relat_1 @ sk_C)),
% 6.44/6.67      inference('demod', [status(thm)], ['50', '51'])).
% 6.44/6.67  thf('93', plain, ((((sk_B) != (sk_B)) | (v2_funct_1 @ sk_D))),
% 6.44/6.67      inference('demod', [status(thm)],
% 6.44/6.67                ['41', '42', '43', '44', '76', '90', '91', '92'])).
% 6.44/6.67  thf('94', plain, ((v2_funct_1 @ sk_D)),
% 6.44/6.67      inference('simplify', [status(thm)], ['93'])).
% 6.44/6.67  thf('95', plain, (((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))),
% 6.44/6.67      inference('demod', [status(thm)], ['11', '94'])).
% 6.44/6.67  thf('96', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 6.44/6.67      inference('demod', [status(thm)], ['18', '19', '38'])).
% 6.44/6.67  thf(t64_funct_1, axiom,
% 6.44/6.67    (![A:$i]:
% 6.44/6.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.44/6.67       ( ![B:$i]:
% 6.44/6.67         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 6.44/6.67           ( ( ( v2_funct_1 @ A ) & 
% 6.44/6.67               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 6.44/6.67               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 6.44/6.67             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 6.44/6.67  thf('97', plain,
% 6.44/6.67      (![X13 : $i, X14 : $i]:
% 6.44/6.67         (~ (v1_relat_1 @ X13)
% 6.44/6.67          | ~ (v1_funct_1 @ X13)
% 6.44/6.67          | ((X13) = (k2_funct_1 @ X14))
% 6.44/6.67          | ((k5_relat_1 @ X13 @ X14) != (k6_relat_1 @ (k2_relat_1 @ X14)))
% 6.44/6.67          | ((k2_relat_1 @ X13) != (k1_relat_1 @ X14))
% 6.44/6.67          | ~ (v2_funct_1 @ X14)
% 6.44/6.67          | ~ (v1_funct_1 @ X14)
% 6.44/6.67          | ~ (v1_relat_1 @ X14))),
% 6.44/6.67      inference('cnf', [status(esa)], [t64_funct_1])).
% 6.44/6.67  thf('98', plain,
% 6.44/6.67      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ (k2_relat_1 @ sk_D)))
% 6.44/6.67        | ~ (v1_relat_1 @ sk_D)
% 6.44/6.67        | ~ (v1_funct_1 @ sk_D)
% 6.44/6.67        | ~ (v2_funct_1 @ sk_D)
% 6.44/6.67        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 6.44/6.67        | ((sk_C) = (k2_funct_1 @ sk_D))
% 6.44/6.67        | ~ (v1_funct_1 @ sk_C)
% 6.44/6.67        | ~ (v1_relat_1 @ sk_C))),
% 6.44/6.67      inference('sup-', [status(thm)], ['96', '97'])).
% 6.44/6.67  thf('99', plain,
% 6.44/6.67      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 6.44/6.67         = (k6_relat_1 @ sk_A))),
% 6.44/6.67      inference('demod', [status(thm)], ['34', '37'])).
% 6.44/6.67  thf('100', plain,
% 6.44/6.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf(t29_funct_2, axiom,
% 6.44/6.67    (![A:$i,B:$i,C:$i]:
% 6.44/6.67     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.44/6.67         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.44/6.67       ( ![D:$i]:
% 6.44/6.67         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 6.44/6.67             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 6.44/6.67           ( ( r2_relset_1 @
% 6.44/6.67               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 6.44/6.67               ( k6_partfun1 @ A ) ) =>
% 6.44/6.67             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 6.44/6.67  thf('101', plain,
% 6.44/6.67      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 6.44/6.67         (~ (v1_funct_1 @ X50)
% 6.44/6.67          | ~ (v1_funct_2 @ X50 @ X51 @ X52)
% 6.44/6.67          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 6.44/6.67          | (v2_funct_2 @ X50 @ X52)
% 6.44/6.67          | ~ (r2_relset_1 @ X52 @ X52 @ 
% 6.44/6.67               (k1_partfun1 @ X52 @ X51 @ X51 @ X52 @ X53 @ X50) @ 
% 6.44/6.67               (k6_partfun1 @ X52))
% 6.44/6.67          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X51)))
% 6.44/6.67          | ~ (v1_funct_2 @ X53 @ X52 @ X51)
% 6.44/6.67          | ~ (v1_funct_1 @ X53))),
% 6.44/6.67      inference('cnf', [status(esa)], [t29_funct_2])).
% 6.44/6.67  thf('102', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 6.44/6.67      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 6.44/6.67  thf('103', plain,
% 6.44/6.67      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 6.44/6.67         (~ (v1_funct_1 @ X50)
% 6.44/6.67          | ~ (v1_funct_2 @ X50 @ X51 @ X52)
% 6.44/6.67          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 6.44/6.67          | (v2_funct_2 @ X50 @ X52)
% 6.44/6.67          | ~ (r2_relset_1 @ X52 @ X52 @ 
% 6.44/6.67               (k1_partfun1 @ X52 @ X51 @ X51 @ X52 @ X53 @ X50) @ 
% 6.44/6.67               (k6_relat_1 @ X52))
% 6.44/6.67          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X51)))
% 6.44/6.67          | ~ (v1_funct_2 @ X53 @ X52 @ X51)
% 6.44/6.67          | ~ (v1_funct_1 @ X53))),
% 6.44/6.67      inference('demod', [status(thm)], ['101', '102'])).
% 6.44/6.67  thf('104', plain,
% 6.44/6.67      (![X0 : $i]:
% 6.44/6.67         (~ (v1_funct_1 @ X0)
% 6.44/6.67          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_B)
% 6.44/6.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 6.44/6.67          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 6.44/6.67               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ X0 @ sk_D) @ 
% 6.44/6.67               (k6_relat_1 @ sk_A))
% 6.44/6.67          | (v2_funct_2 @ sk_D @ sk_A)
% 6.44/6.67          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 6.44/6.67          | ~ (v1_funct_1 @ sk_D))),
% 6.44/6.67      inference('sup-', [status(thm)], ['100', '103'])).
% 6.44/6.67  thf('105', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf('106', plain, ((v1_funct_1 @ sk_D)),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf('107', plain,
% 6.44/6.67      (![X0 : $i]:
% 6.44/6.67         (~ (v1_funct_1 @ X0)
% 6.44/6.67          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_B)
% 6.44/6.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 6.44/6.67          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 6.44/6.67               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ X0 @ sk_D) @ 
% 6.44/6.67               (k6_relat_1 @ sk_A))
% 6.44/6.67          | (v2_funct_2 @ sk_D @ sk_A))),
% 6.44/6.67      inference('demod', [status(thm)], ['104', '105', '106'])).
% 6.44/6.67  thf('108', plain,
% 6.44/6.67      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 6.44/6.67           (k6_relat_1 @ sk_A))
% 6.44/6.67        | (v2_funct_2 @ sk_D @ sk_A)
% 6.44/6.67        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 6.44/6.67        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 6.44/6.67        | ~ (v1_funct_1 @ sk_C))),
% 6.44/6.67      inference('sup-', [status(thm)], ['99', '107'])).
% 6.44/6.67  thf('109', plain,
% 6.44/6.67      (![X42 : $i]:
% 6.44/6.67         (m1_subset_1 @ (k6_relat_1 @ X42) @ 
% 6.44/6.67          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X42)))),
% 6.44/6.67      inference('demod', [status(thm)], ['35', '36'])).
% 6.44/6.67  thf('110', plain,
% 6.44/6.67      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 6.44/6.67         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 6.44/6.67          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 6.44/6.67          | (r2_relset_1 @ X22 @ X23 @ X21 @ X24)
% 6.44/6.67          | ((X21) != (X24)))),
% 6.44/6.67      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 6.44/6.67  thf('111', plain,
% 6.44/6.67      (![X22 : $i, X23 : $i, X24 : $i]:
% 6.44/6.67         ((r2_relset_1 @ X22 @ X23 @ X24 @ X24)
% 6.44/6.67          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 6.44/6.67      inference('simplify', [status(thm)], ['110'])).
% 6.44/6.67  thf('112', plain,
% 6.44/6.67      (![X0 : $i]:
% 6.44/6.67         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 6.44/6.67      inference('sup-', [status(thm)], ['109', '111'])).
% 6.44/6.67  thf('113', plain,
% 6.44/6.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf('114', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf('115', plain, ((v1_funct_1 @ sk_C)),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf('116', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 6.44/6.67      inference('demod', [status(thm)], ['108', '112', '113', '114', '115'])).
% 6.44/6.67  thf(d3_funct_2, axiom,
% 6.44/6.67    (![A:$i,B:$i]:
% 6.44/6.67     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 6.44/6.67       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 6.44/6.67  thf('117', plain,
% 6.44/6.67      (![X33 : $i, X34 : $i]:
% 6.44/6.67         (~ (v2_funct_2 @ X34 @ X33)
% 6.44/6.67          | ((k2_relat_1 @ X34) = (X33))
% 6.44/6.67          | ~ (v5_relat_1 @ X34 @ X33)
% 6.44/6.67          | ~ (v1_relat_1 @ X34))),
% 6.44/6.67      inference('cnf', [status(esa)], [d3_funct_2])).
% 6.44/6.67  thf('118', plain,
% 6.44/6.67      ((~ (v1_relat_1 @ sk_D)
% 6.44/6.67        | ~ (v5_relat_1 @ sk_D @ sk_A)
% 6.44/6.67        | ((k2_relat_1 @ sk_D) = (sk_A)))),
% 6.44/6.67      inference('sup-', [status(thm)], ['116', '117'])).
% 6.44/6.67  thf('119', plain, ((v1_relat_1 @ sk_D)),
% 6.44/6.67      inference('demod', [status(thm)], ['2', '3'])).
% 6.44/6.67  thf('120', plain,
% 6.44/6.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf(cc2_relset_1, axiom,
% 6.44/6.67    (![A:$i,B:$i,C:$i]:
% 6.44/6.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.44/6.67       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 6.44/6.67  thf('121', plain,
% 6.44/6.67      (![X15 : $i, X16 : $i, X17 : $i]:
% 6.44/6.67         ((v5_relat_1 @ X15 @ X17)
% 6.44/6.67          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 6.44/6.67      inference('cnf', [status(esa)], [cc2_relset_1])).
% 6.44/6.67  thf('122', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 6.44/6.67      inference('sup-', [status(thm)], ['120', '121'])).
% 6.44/6.67  thf('123', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 6.44/6.67      inference('demod', [status(thm)], ['118', '119', '122'])).
% 6.44/6.67  thf('124', plain, ((v1_relat_1 @ sk_D)),
% 6.44/6.67      inference('demod', [status(thm)], ['2', '3'])).
% 6.44/6.67  thf('125', plain, ((v1_funct_1 @ sk_D)),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf('126', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 6.44/6.67      inference('demod', [status(thm)], ['60', '74', '75'])).
% 6.44/6.67  thf('127', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 6.44/6.67      inference('demod', [status(thm)], ['79', '86', '89'])).
% 6.44/6.67  thf('128', plain, ((v1_funct_1 @ sk_C)),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf('129', plain, ((v1_relat_1 @ sk_C)),
% 6.44/6.67      inference('demod', [status(thm)], ['50', '51'])).
% 6.44/6.67  thf('130', plain,
% 6.44/6.67      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ sk_A))
% 6.44/6.67        | ~ (v2_funct_1 @ sk_D)
% 6.44/6.67        | ((sk_B) != (sk_B))
% 6.44/6.67        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 6.44/6.67      inference('demod', [status(thm)],
% 6.44/6.67                ['98', '123', '124', '125', '126', '127', '128', '129'])).
% 6.44/6.67  thf('131', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 6.44/6.67      inference('simplify', [status(thm)], ['130'])).
% 6.44/6.67  thf('132', plain, ((v2_funct_1 @ sk_D)),
% 6.44/6.67      inference('simplify', [status(thm)], ['93'])).
% 6.44/6.67  thf('133', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 6.44/6.67      inference('demod', [status(thm)], ['131', '132'])).
% 6.44/6.67  thf('134', plain, (((sk_C) = (k4_relat_1 @ sk_D))),
% 6.44/6.67      inference('sup+', [status(thm)], ['95', '133'])).
% 6.44/6.67  thf('135', plain, (((k4_relat_1 @ sk_C) = (sk_D))),
% 6.44/6.67      inference('demod', [status(thm)], ['6', '134'])).
% 6.44/6.67  thf('136', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 6.44/6.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.44/6.67  thf('137', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 6.44/6.67      inference('demod', [status(thm)], ['47', '52', '53'])).
% 6.44/6.67  thf('138', plain, (((sk_D) != (k4_relat_1 @ sk_C))),
% 6.44/6.67      inference('demod', [status(thm)], ['136', '137'])).
% 6.44/6.67  thf('139', plain, ($false),
% 6.44/6.67      inference('simplify_reflect-', [status(thm)], ['135', '138'])).
% 6.44/6.67  
% 6.44/6.67  % SZS output end Refutation
% 6.44/6.67  
% 6.44/6.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

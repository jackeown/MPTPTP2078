%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aUAbaIBrb9

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:27 EST 2020

% Result     : Theorem 3.07s
% Output     : Refutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :  342 (3069 expanded)
%              Number of leaves         :   47 ( 929 expanded)
%              Depth                    :   32
%              Number of atoms          : 3594 (74171 expanded)
%              Number of equality atoms :  217 (4882 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('3',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( X17 = X20 )
      | ~ ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('13',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('14',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('15',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,(
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

thf('18',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( r2_relset_1 @ X36 @ X36 @ ( k1_partfun1 @ X36 @ X37 @ X37 @ X36 @ X35 @ X38 ) @ ( k6_partfun1 @ X36 ) )
      | ( ( k2_relset_1 @ X37 @ X36 @ X38 )
        = X36 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X36 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('25',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 )
      | ( X17 != X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('26',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_relset_1 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('29',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('30',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['23','27','30','31','32','33'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('35',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) @ X6 )
        = ( k5_relat_1 @ X5 @ ( k5_relat_1 @ X4 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('36',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) @ X6 )
        = ( k5_relat_1 @ X5 @ ( k5_relat_1 @ X4 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('37',plain,(
    ! [X9: $i] :
      ( ( ( k5_relat_1 @ X9 @ ( k6_relat_1 @ ( k2_relat_1 @ X9 ) ) )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('38',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('39',plain,(
    ! [X9: $i] :
      ( ( ( k5_relat_1 @ X9 @ ( k6_partfun1 @ ( k2_relat_1 @ X9 ) ) )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X9: $i] :
      ( ( ( k5_relat_1 @ X9 @ ( k6_partfun1 @ ( k2_relat_1 @ X9 ) ) )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('41',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) @ X6 )
        = ( k5_relat_1 @ X5 @ ( k5_relat_1 @ X4 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('46',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['42','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X9: $i] :
      ( ( ( k5_relat_1 @ X9 @ ( k6_partfun1 @ ( k2_relat_1 @ X9 ) ) )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('51',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) @ X6 )
        = ( k5_relat_1 @ X5 @ ( k5_relat_1 @ X4 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('52',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) @ X6 )
        = ( k5_relat_1 @ X5 @ ( k5_relat_1 @ X4 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ ( k5_relat_1 @ X0 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ ( k5_relat_1 @ X0 @ X3 ) ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X2 ) ) @ X1 )
        = ( k5_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['50','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X2 ) ) @ X1 )
        = ( k5_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X2 ) ) @ X1 )
        = ( k5_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ ( k2_relat_1 @ X1 ) ) ) @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['49','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ ( k2_relat_1 @ X1 ) ) ) @ ( k5_relat_1 @ X0 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ ( k2_relat_1 @ X1 ) ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['39','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ ( k2_relat_1 @ X1 ) ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ ( k2_relat_1 @ X1 ) ) ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ ( k2_relat_1 @ X1 ) ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ ( k2_relat_1 @ X1 ) ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ ( k2_relat_1 @ X1 ) ) ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X1 ) ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X1 ) ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X1 ) ) @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ sk_A ) ) )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ sk_D ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['34','72'])).

thf('74',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['23','27','30','31','32','33'])).

thf('75',plain,(
    ! [X9: $i] :
      ( ( ( k5_relat_1 @ X9 @ ( k6_partfun1 @ ( k2_relat_1 @ X9 ) ) )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('76',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ sk_A ) )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('79',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('81',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ sk_A ) )
    = sk_D ),
    inference(demod,[status(thm)],['76','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['79','80'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ sk_D )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ sk_D ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['73','82','83'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('85',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('86',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('87',plain,(
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

thf('88',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( X48 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X48 ) ) )
      | ( ( k5_relat_1 @ X49 @ ( k2_funct_1 @ X49 ) )
        = ( k6_partfun1 @ X50 ) )
      | ~ ( v2_funct_1 @ X49 )
      | ( ( k2_relset_1 @ X50 @ X48 @ X49 )
       != X48 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('89',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('91',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['89','90','91','92'])).

thf('94',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['23','27','30','31','32','33'])).

thf('97',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('100',plain,(
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

thf('101',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ( zip_tseitin_0 @ X43 @ X46 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X47 @ X44 @ X44 @ X45 @ X46 @ X43 ) )
      | ( zip_tseitin_1 @ X45 @ X44 )
      | ( ( k2_relset_1 @ X47 @ X44 @ X46 )
       != X44 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X44 )
      | ~ ( v1_funct_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('102',plain,(
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
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['99','105'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('107',plain,(
    ! [X11: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('108',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('109',plain,(
    ! [X11: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X11 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['106','109','110','111','112','113'])).

thf('115',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ! [X41: $i,X42: $i] :
      ( ( X41 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('117',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X39: $i,X40: $i] :
      ( ( v2_funct_1 @ X40 )
      | ~ ( zip_tseitin_0 @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('121',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['98','121'])).

thf('123',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
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

thf('125',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 )
        = ( k5_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('126',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['123','128'])).

thf('130',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('132',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) @ X6 )
        = ( k5_relat_1 @ X5 @ ( k5_relat_1 @ X4 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('137',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('139',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['79','80'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['134','139','140'])).

thf('142',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k2_funct_1 @ sk_D ) )
      = ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['122','141'])).

thf('143',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('145',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X9: $i] :
      ( ( ( k5_relat_1 @ X9 @ ( k6_partfun1 @ ( k2_relat_1 @ X9 ) ) )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('149',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('150',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['137','138'])).

thf('151',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k2_funct_1 @ sk_D ) )
      = sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['142','151'])).

thf('153',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k2_funct_1 @ sk_D ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['86','152'])).

thf('154',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['79','80'])).

thf('155',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k2_funct_1 @ sk_D ) )
    = sk_C ),
    inference(demod,[status(thm)],['153','154','155'])).

thf('157',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['23','27','30','31','32','33'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['157','158'])).

thf('160',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['79','80'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k5_relat_1 @ sk_D @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['156','161'])).

thf('163',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['98','121'])).

thf('164',plain,
    ( ( ( k6_partfun1 @ sk_B )
      = ( k5_relat_1 @ sk_D @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k6_partfun1 @ sk_B )
      = ( k5_relat_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['85','164'])).

thf('166',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['79','80'])).

thf('167',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( k6_partfun1 @ sk_B )
    = ( k5_relat_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['165','166','167'])).

thf('169',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) @ X6 )
        = ( k5_relat_1 @ X5 @ ( k5_relat_1 @ X4 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ sk_D @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['168','169'])).

thf('171',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['79','80'])).

thf('172',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['137','138'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ sk_D @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['170','171','172'])).

thf('174',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) @ sk_D ) )
      = ( k5_relat_1 @ sk_D @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) @ sk_D ) ) ),
    inference('sup+',[status(thm)],['84','173'])).

thf('175',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['145','146'])).

thf('176',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('177',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('178',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( X48 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X48 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X49 ) @ X49 )
        = ( k6_partfun1 @ X48 ) )
      | ~ ( v2_funct_1 @ X49 )
      | ( ( k2_relset_1 @ X50 @ X48 @ X49 )
       != X48 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('180',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['180','181','182','183','184'])).

thf('186',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['185'])).

thf('187',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) @ X6 )
        = ( k5_relat_1 @ X5 @ ( k5_relat_1 @ X4 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['188','189'])).

thf('191',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['137','138'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['190','191'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['177','192'])).

thf('194',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['137','138'])).

thf('195',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['193','194','195'])).

thf('197',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['176','196'])).

thf('198',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( X48 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X48 ) ) )
      | ( ( k5_relat_1 @ X49 @ ( k2_funct_1 @ X49 ) )
        = ( k6_partfun1 @ X50 ) )
      | ~ ( v2_funct_1 @ X49 )
      | ( ( k2_relset_1 @ X50 @ X48 @ X49 )
       != X48 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('200',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['200','201','202','203','204'])).

thf('206',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['205'])).

thf('207',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['206','207'])).

thf(t58_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('209',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X13 @ ( k2_funct_1 @ X13 ) ) )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('210',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ sk_A ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['208','209'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('211',plain,(
    ! [X8: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('212',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('213',plain,(
    ! [X8: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X8 ) )
      = X8 ) ),
    inference(demod,[status(thm)],['211','212'])).

thf('214',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['137','138'])).

thf('215',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['210','213','214','215','216'])).

thf('218',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('219',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k1_relat_1 @ X12 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('220',plain,(
    ! [X9: $i] :
      ( ( ( k5_relat_1 @ X9 @ ( k6_partfun1 @ ( k2_relat_1 @ X9 ) ) )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('221',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['219','220'])).

thf('222',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['218','221'])).

thf('223',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['222'])).

thf('224',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['217','223'])).

thf('225',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['137','138'])).

thf('226',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['224','225','226','227'])).

thf('229',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['79','80'])).

thf('230',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['197','228','229'])).

thf('231',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('232',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['206','207'])).

thf('233',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['193','194','195'])).

thf('234',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['232','233'])).

thf('235',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['224','225','226','227'])).

thf('236',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['234','235'])).

thf('237',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['231','236'])).

thf('238',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['137','138'])).

thf('239',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['237','238','239'])).

thf('241',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('242',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ sk_A ) )
    = sk_D ),
    inference(demod,[status(thm)],['76','81'])).

thf('243',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['137','138'])).

thf('244',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['145','146'])).

thf('245',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['197','228','229'])).

thf('246',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( v1_funct_1 @ ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('249',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['247','248'])).

thf('250',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['249','250'])).

thf('252',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( v1_funct_1 @ ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['246','251'])).

thf('253',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,(
    v1_funct_1 @ ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['252','253'])).

thf('255',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 )
        = ( k5_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('258',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['256','257'])).

thf('259',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('260',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['258','259'])).

thf('261',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
      = ( k5_relat_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['255','260'])).

thf('262',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,
    ( ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
    = ( k5_relat_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['261','262'])).

thf('264',plain,(
    v1_funct_1 @ ( k5_relat_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['254','263'])).

thf('265',plain,
    ( ( k6_partfun1 @ sk_B )
    = ( k5_relat_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['165','166','167'])).

thf('266',plain,(
    v1_funct_1 @ ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['264','265'])).

thf('267',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('268',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('269',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('270',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ X0 @ X0 @ X3 @ X1 @ ( k6_partfun1 @ X0 ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['268','269'])).

thf('271',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( m1_subset_1 @ ( k1_partfun1 @ X0 @ X0 @ sk_B @ sk_A @ ( k6_partfun1 @ X0 ) @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['267','270'])).

thf('272',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('273',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X0 @ X0 @ sk_B @ sk_A @ ( k6_partfun1 @ X0 ) @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['271','272'])).

thf('274',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_B @ sk_B @ sk_B @ sk_A @ ( k6_partfun1 @ sk_B ) @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['266','273'])).

thf('275',plain,(
    v1_funct_1 @ ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['264','265'])).

thf('276',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('277',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('278',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 )
        = ( k5_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('279',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_partfun1 @ X0 @ X0 @ X3 @ X2 @ ( k6_partfun1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['277','278'])).

thf('280',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k1_partfun1 @ X0 @ X0 @ sk_B @ sk_A @ ( k6_partfun1 @ X0 ) @ sk_D )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['276','279'])).

thf('281',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('282',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k1_partfun1 @ X0 @ X0 @ sk_B @ sk_A @ ( k6_partfun1 @ X0 ) @ sk_D )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['280','281'])).

thf('283',plain,
    ( ( k1_partfun1 @ sk_B @ sk_B @ sk_B @ sk_A @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D ) ),
    inference('sup-',[status(thm)],['275','282'])).

thf('284',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['197','228','229'])).

thf('285',plain,
    ( ( k1_partfun1 @ sk_B @ sk_B @ sk_B @ sk_A @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['283','284'])).

thf('286',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['274','285'])).

thf('287',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('288',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['286','287'])).

thf('289',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('290',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['288','289'])).

thf('291',plain,
    ( ( k2_funct_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['174','175','230','240','241','242','243','244','245','290'])).

thf('292',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('293',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['291','292'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aUAbaIBrb9
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:35:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 3.07/3.29  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.07/3.29  % Solved by: fo/fo7.sh
% 3.07/3.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.07/3.29  % done 1985 iterations in 2.866s
% 3.07/3.29  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.07/3.29  % SZS output start Refutation
% 3.07/3.29  thf(sk_C_type, type, sk_C: $i).
% 3.07/3.29  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.07/3.29  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.07/3.29  thf(sk_A_type, type, sk_A: $i).
% 3.07/3.29  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.07/3.29  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.07/3.29  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.07/3.29  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.07/3.29  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.07/3.29  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.07/3.29  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.07/3.29  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.07/3.29  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 3.07/3.29  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.07/3.29  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.07/3.29  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.07/3.29  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 3.07/3.29  thf(sk_B_type, type, sk_B: $i).
% 3.07/3.29  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.07/3.29  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.07/3.29  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.07/3.29  thf(sk_D_type, type, sk_D: $i).
% 3.07/3.29  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.07/3.29  thf(t36_funct_2, conjecture,
% 3.07/3.29    (![A:$i,B:$i,C:$i]:
% 3.07/3.29     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.07/3.29         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.07/3.29       ( ![D:$i]:
% 3.07/3.29         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.07/3.29             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.07/3.29           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 3.07/3.29               ( r2_relset_1 @
% 3.07/3.29                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.07/3.29                 ( k6_partfun1 @ A ) ) & 
% 3.07/3.29               ( v2_funct_1 @ C ) ) =>
% 3.07/3.29             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.07/3.29               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 3.07/3.29  thf(zf_stmt_0, negated_conjecture,
% 3.07/3.29    (~( ![A:$i,B:$i,C:$i]:
% 3.07/3.29        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.07/3.29            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.07/3.29          ( ![D:$i]:
% 3.07/3.29            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.07/3.29                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.07/3.29              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 3.07/3.29                  ( r2_relset_1 @
% 3.07/3.29                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.07/3.29                    ( k6_partfun1 @ A ) ) & 
% 3.07/3.29                  ( v2_funct_1 @ C ) ) =>
% 3.07/3.29                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.07/3.29                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 3.07/3.29    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 3.07/3.29  thf('0', plain,
% 3.07/3.29      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.07/3.29        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.07/3.29        (k6_partfun1 @ sk_A))),
% 3.07/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.29  thf('1', plain,
% 3.07/3.29      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.07/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.29  thf('2', plain,
% 3.07/3.29      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.07/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.29  thf(dt_k1_partfun1, axiom,
% 3.07/3.29    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.07/3.29     ( ( ( v1_funct_1 @ E ) & 
% 3.07/3.29         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.07/3.29         ( v1_funct_1 @ F ) & 
% 3.07/3.29         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.07/3.29       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 3.07/3.29         ( m1_subset_1 @
% 3.07/3.29           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.07/3.29           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 3.07/3.29  thf('3', plain,
% 3.07/3.29      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 3.07/3.29         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 3.07/3.29          | ~ (v1_funct_1 @ X22)
% 3.07/3.29          | ~ (v1_funct_1 @ X25)
% 3.07/3.29          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 3.07/3.29          | (m1_subset_1 @ (k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25) @ 
% 3.07/3.29             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X27))))),
% 3.07/3.29      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.07/3.29  thf('4', plain,
% 3.07/3.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.07/3.29         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.07/3.29           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.07/3.29          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.07/3.29          | ~ (v1_funct_1 @ X1)
% 3.07/3.29          | ~ (v1_funct_1 @ sk_C))),
% 3.07/3.29      inference('sup-', [status(thm)], ['2', '3'])).
% 3.07/3.29  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 3.07/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.29  thf('6', plain,
% 3.07/3.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.07/3.29         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.07/3.29           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.07/3.29          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.07/3.29          | ~ (v1_funct_1 @ X1))),
% 3.07/3.29      inference('demod', [status(thm)], ['4', '5'])).
% 3.07/3.29  thf('7', plain,
% 3.07/3.29      ((~ (v1_funct_1 @ sk_D)
% 3.07/3.29        | (m1_subset_1 @ 
% 3.07/3.29           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.07/3.29           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.07/3.29      inference('sup-', [status(thm)], ['1', '6'])).
% 3.07/3.29  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 3.07/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.29  thf('9', plain,
% 3.07/3.29      ((m1_subset_1 @ 
% 3.07/3.29        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.07/3.29        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.07/3.29      inference('demod', [status(thm)], ['7', '8'])).
% 3.07/3.29  thf(redefinition_r2_relset_1, axiom,
% 3.07/3.29    (![A:$i,B:$i,C:$i,D:$i]:
% 3.07/3.29     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.07/3.29         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.07/3.29       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.07/3.29  thf('10', plain,
% 3.07/3.29      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 3.07/3.29         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 3.07/3.29          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 3.07/3.29          | ((X17) = (X20))
% 3.07/3.29          | ~ (r2_relset_1 @ X18 @ X19 @ X17 @ X20))),
% 3.07/3.29      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.07/3.29  thf('11', plain,
% 3.07/3.29      (![X0 : $i]:
% 3.07/3.29         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.07/3.29             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 3.07/3.29          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 3.07/3.29          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.07/3.29      inference('sup-', [status(thm)], ['9', '10'])).
% 3.07/3.29  thf('12', plain,
% 3.07/3.29      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 3.07/3.29           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.07/3.29        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.07/3.29            = (k6_partfun1 @ sk_A)))),
% 3.07/3.29      inference('sup-', [status(thm)], ['0', '11'])).
% 3.07/3.29  thf(t29_relset_1, axiom,
% 3.07/3.29    (![A:$i]:
% 3.07/3.29     ( m1_subset_1 @
% 3.07/3.29       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 3.07/3.29  thf('13', plain,
% 3.07/3.29      (![X21 : $i]:
% 3.07/3.29         (m1_subset_1 @ (k6_relat_1 @ X21) @ 
% 3.07/3.29          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 3.07/3.29      inference('cnf', [status(esa)], [t29_relset_1])).
% 3.07/3.29  thf(redefinition_k6_partfun1, axiom,
% 3.07/3.29    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 3.07/3.29  thf('14', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 3.07/3.29      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.07/3.29  thf('15', plain,
% 3.07/3.29      (![X21 : $i]:
% 3.07/3.29         (m1_subset_1 @ (k6_partfun1 @ X21) @ 
% 3.07/3.29          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 3.07/3.29      inference('demod', [status(thm)], ['13', '14'])).
% 3.07/3.29  thf('16', plain,
% 3.07/3.29      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.07/3.29         = (k6_partfun1 @ sk_A))),
% 3.07/3.29      inference('demod', [status(thm)], ['12', '15'])).
% 3.07/3.29  thf('17', plain,
% 3.07/3.29      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.07/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.29  thf(t24_funct_2, axiom,
% 3.07/3.29    (![A:$i,B:$i,C:$i]:
% 3.07/3.29     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.07/3.29         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.07/3.29       ( ![D:$i]:
% 3.07/3.29         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.07/3.29             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.07/3.29           ( ( r2_relset_1 @
% 3.07/3.29               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 3.07/3.29               ( k6_partfun1 @ B ) ) =>
% 3.07/3.29             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 3.07/3.29  thf('18', plain,
% 3.07/3.29      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 3.07/3.29         (~ (v1_funct_1 @ X35)
% 3.07/3.29          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 3.07/3.29          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 3.07/3.29          | ~ (r2_relset_1 @ X36 @ X36 @ 
% 3.07/3.29               (k1_partfun1 @ X36 @ X37 @ X37 @ X36 @ X35 @ X38) @ 
% 3.07/3.29               (k6_partfun1 @ X36))
% 3.07/3.29          | ((k2_relset_1 @ X37 @ X36 @ X38) = (X36))
% 3.07/3.29          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 3.07/3.29          | ~ (v1_funct_2 @ X38 @ X37 @ X36)
% 3.07/3.29          | ~ (v1_funct_1 @ X38))),
% 3.07/3.29      inference('cnf', [status(esa)], [t24_funct_2])).
% 3.07/3.29  thf('19', plain,
% 3.07/3.29      (![X0 : $i]:
% 3.07/3.29         (~ (v1_funct_1 @ X0)
% 3.07/3.29          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 3.07/3.29          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.07/3.29          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 3.07/3.29          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.07/3.29               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 3.07/3.29               (k6_partfun1 @ sk_A))
% 3.07/3.29          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.07/3.29          | ~ (v1_funct_1 @ sk_C))),
% 3.07/3.29      inference('sup-', [status(thm)], ['17', '18'])).
% 3.07/3.29  thf('20', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.07/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.29  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 3.07/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.29  thf('22', plain,
% 3.07/3.29      (![X0 : $i]:
% 3.07/3.29         (~ (v1_funct_1 @ X0)
% 3.07/3.29          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 3.07/3.29          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.07/3.29          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 3.07/3.29          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.07/3.29               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 3.07/3.29               (k6_partfun1 @ sk_A)))),
% 3.07/3.29      inference('demod', [status(thm)], ['19', '20', '21'])).
% 3.07/3.29  thf('23', plain,
% 3.07/3.29      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 3.07/3.29           (k6_partfun1 @ sk_A))
% 3.07/3.29        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 3.07/3.29        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 3.07/3.29        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.07/3.29        | ~ (v1_funct_1 @ sk_D))),
% 3.07/3.29      inference('sup-', [status(thm)], ['16', '22'])).
% 3.07/3.29  thf('24', plain,
% 3.07/3.29      (![X21 : $i]:
% 3.07/3.29         (m1_subset_1 @ (k6_partfun1 @ X21) @ 
% 3.07/3.29          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 3.07/3.29      inference('demod', [status(thm)], ['13', '14'])).
% 3.07/3.29  thf('25', plain,
% 3.07/3.29      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 3.07/3.29         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 3.07/3.29          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 3.07/3.29          | (r2_relset_1 @ X18 @ X19 @ X17 @ X20)
% 3.07/3.29          | ((X17) != (X20)))),
% 3.07/3.29      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.07/3.29  thf('26', plain,
% 3.07/3.29      (![X18 : $i, X19 : $i, X20 : $i]:
% 3.07/3.29         ((r2_relset_1 @ X18 @ X19 @ X20 @ X20)
% 3.07/3.29          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 3.07/3.29      inference('simplify', [status(thm)], ['25'])).
% 3.07/3.29  thf('27', plain,
% 3.07/3.29      (![X0 : $i]:
% 3.07/3.29         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 3.07/3.29      inference('sup-', [status(thm)], ['24', '26'])).
% 3.07/3.29  thf('28', plain,
% 3.07/3.29      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.07/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.29  thf(redefinition_k2_relset_1, axiom,
% 3.07/3.29    (![A:$i,B:$i,C:$i]:
% 3.07/3.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.07/3.29       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.07/3.29  thf('29', plain,
% 3.07/3.29      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.07/3.29         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 3.07/3.29          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 3.07/3.29      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.07/3.29  thf('30', plain,
% 3.07/3.29      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 3.07/3.29      inference('sup-', [status(thm)], ['28', '29'])).
% 3.07/3.29  thf('31', plain,
% 3.07/3.29      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.07/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.29  thf('32', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.07/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.29  thf('33', plain, ((v1_funct_1 @ sk_D)),
% 3.07/3.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.29  thf('34', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.07/3.29      inference('demod', [status(thm)], ['23', '27', '30', '31', '32', '33'])).
% 3.07/3.29  thf(t55_relat_1, axiom,
% 3.07/3.29    (![A:$i]:
% 3.07/3.29     ( ( v1_relat_1 @ A ) =>
% 3.07/3.29       ( ![B:$i]:
% 3.07/3.29         ( ( v1_relat_1 @ B ) =>
% 3.07/3.29           ( ![C:$i]:
% 3.07/3.29             ( ( v1_relat_1 @ C ) =>
% 3.07/3.29               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 3.07/3.29                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 3.07/3.29  thf('35', plain,
% 3.07/3.29      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.07/3.29         (~ (v1_relat_1 @ X4)
% 3.07/3.29          | ((k5_relat_1 @ (k5_relat_1 @ X5 @ X4) @ X6)
% 3.07/3.29              = (k5_relat_1 @ X5 @ (k5_relat_1 @ X4 @ X6)))
% 3.07/3.29          | ~ (v1_relat_1 @ X6)
% 3.07/3.29          | ~ (v1_relat_1 @ X5))),
% 3.07/3.29      inference('cnf', [status(esa)], [t55_relat_1])).
% 3.07/3.29  thf('36', plain,
% 3.07/3.29      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.07/3.29         (~ (v1_relat_1 @ X4)
% 3.07/3.29          | ((k5_relat_1 @ (k5_relat_1 @ X5 @ X4) @ X6)
% 3.07/3.29              = (k5_relat_1 @ X5 @ (k5_relat_1 @ X4 @ X6)))
% 3.07/3.29          | ~ (v1_relat_1 @ X6)
% 3.07/3.29          | ~ (v1_relat_1 @ X5))),
% 3.07/3.29      inference('cnf', [status(esa)], [t55_relat_1])).
% 3.07/3.29  thf(t80_relat_1, axiom,
% 3.07/3.29    (![A:$i]:
% 3.07/3.29     ( ( v1_relat_1 @ A ) =>
% 3.07/3.29       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 3.07/3.29  thf('37', plain,
% 3.07/3.29      (![X9 : $i]:
% 3.07/3.29         (((k5_relat_1 @ X9 @ (k6_relat_1 @ (k2_relat_1 @ X9))) = (X9))
% 3.07/3.29          | ~ (v1_relat_1 @ X9))),
% 3.07/3.29      inference('cnf', [status(esa)], [t80_relat_1])).
% 3.07/3.29  thf('38', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 3.07/3.29      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.07/3.29  thf('39', plain,
% 3.07/3.29      (![X9 : $i]:
% 3.07/3.29         (((k5_relat_1 @ X9 @ (k6_partfun1 @ (k2_relat_1 @ X9))) = (X9))
% 3.07/3.29          | ~ (v1_relat_1 @ X9))),
% 3.07/3.29      inference('demod', [status(thm)], ['37', '38'])).
% 3.07/3.29  thf('40', plain,
% 3.07/3.29      (![X9 : $i]:
% 3.07/3.29         (((k5_relat_1 @ X9 @ (k6_partfun1 @ (k2_relat_1 @ X9))) = (X9))
% 3.07/3.29          | ~ (v1_relat_1 @ X9))),
% 3.07/3.29      inference('demod', [status(thm)], ['37', '38'])).
% 3.07/3.29  thf('41', plain,
% 3.07/3.29      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.07/3.29         (~ (v1_relat_1 @ X4)
% 3.07/3.29          | ((k5_relat_1 @ (k5_relat_1 @ X5 @ X4) @ X6)
% 3.07/3.29              = (k5_relat_1 @ X5 @ (k5_relat_1 @ X4 @ X6)))
% 3.07/3.29          | ~ (v1_relat_1 @ X6)
% 3.07/3.29          | ~ (v1_relat_1 @ X5))),
% 3.07/3.29      inference('cnf', [status(esa)], [t55_relat_1])).
% 3.07/3.29  thf('42', plain,
% 3.07/3.29      (![X0 : $i, X1 : $i]:
% 3.07/3.29         (((k5_relat_1 @ X0 @ X1)
% 3.07/3.29            = (k5_relat_1 @ X0 @ 
% 3.07/3.29               (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)))
% 3.07/3.29          | ~ (v1_relat_1 @ X0)
% 3.07/3.29          | ~ (v1_relat_1 @ X0)
% 3.07/3.29          | ~ (v1_relat_1 @ X1)
% 3.07/3.29          | ~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0))))),
% 3.07/3.29      inference('sup+', [status(thm)], ['40', '41'])).
% 3.07/3.29  thf('43', plain,
% 3.07/3.29      (![X21 : $i]:
% 3.07/3.29         (m1_subset_1 @ (k6_partfun1 @ X21) @ 
% 3.07/3.29          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 3.07/3.29      inference('demod', [status(thm)], ['13', '14'])).
% 3.07/3.29  thf(cc2_relat_1, axiom,
% 3.07/3.29    (![A:$i]:
% 3.07/3.29     ( ( v1_relat_1 @ A ) =>
% 3.07/3.29       ( ![B:$i]:
% 3.07/3.29         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 3.07/3.29  thf('44', plain,
% 3.07/3.29      (![X0 : $i, X1 : $i]:
% 3.07/3.29         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 3.07/3.29          | (v1_relat_1 @ X0)
% 3.07/3.29          | ~ (v1_relat_1 @ X1))),
% 3.07/3.29      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.07/3.29  thf('45', plain,
% 3.07/3.29      (![X0 : $i]:
% 3.07/3.29         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X0))
% 3.07/3.29          | (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 3.07/3.29      inference('sup-', [status(thm)], ['43', '44'])).
% 3.07/3.29  thf(fc6_relat_1, axiom,
% 3.07/3.29    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 3.07/3.29  thf('46', plain,
% 3.07/3.29      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 3.07/3.29      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.07/3.29  thf('47', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 3.07/3.29      inference('demod', [status(thm)], ['45', '46'])).
% 3.07/3.29  thf('48', plain,
% 3.07/3.29      (![X0 : $i, X1 : $i]:
% 3.07/3.29         (((k5_relat_1 @ X0 @ X1)
% 3.07/3.29            = (k5_relat_1 @ X0 @ 
% 3.07/3.29               (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)))
% 3.07/3.29          | ~ (v1_relat_1 @ X0)
% 3.07/3.29          | ~ (v1_relat_1 @ X0)
% 3.07/3.29          | ~ (v1_relat_1 @ X1))),
% 3.07/3.29      inference('demod', [status(thm)], ['42', '47'])).
% 3.07/3.29  thf('49', plain,
% 3.07/3.29      (![X0 : $i, X1 : $i]:
% 3.07/3.29         (~ (v1_relat_1 @ X1)
% 3.07/3.29          | ~ (v1_relat_1 @ X0)
% 3.07/3.29          | ((k5_relat_1 @ X0 @ X1)
% 3.07/3.29              = (k5_relat_1 @ X0 @ 
% 3.07/3.29                 (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1))))),
% 3.07/3.29      inference('simplify', [status(thm)], ['48'])).
% 3.07/3.29  thf('50', plain,
% 3.07/3.29      (![X9 : $i]:
% 3.07/3.29         (((k5_relat_1 @ X9 @ (k6_partfun1 @ (k2_relat_1 @ X9))) = (X9))
% 3.07/3.29          | ~ (v1_relat_1 @ X9))),
% 3.07/3.29      inference('demod', [status(thm)], ['37', '38'])).
% 3.07/3.29  thf('51', plain,
% 3.07/3.29      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.07/3.29         (~ (v1_relat_1 @ X4)
% 3.07/3.29          | ((k5_relat_1 @ (k5_relat_1 @ X5 @ X4) @ X6)
% 3.07/3.29              = (k5_relat_1 @ X5 @ (k5_relat_1 @ X4 @ X6)))
% 3.07/3.29          | ~ (v1_relat_1 @ X6)
% 3.07/3.29          | ~ (v1_relat_1 @ X5))),
% 3.07/3.29      inference('cnf', [status(esa)], [t55_relat_1])).
% 3.07/3.29  thf('52', plain,
% 3.07/3.29      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.07/3.29         (~ (v1_relat_1 @ X4)
% 3.07/3.29          | ((k5_relat_1 @ (k5_relat_1 @ X5 @ X4) @ X6)
% 3.07/3.29              = (k5_relat_1 @ X5 @ (k5_relat_1 @ X4 @ X6)))
% 3.07/3.29          | ~ (v1_relat_1 @ X6)
% 3.07/3.29          | ~ (v1_relat_1 @ X5))),
% 3.07/3.29      inference('cnf', [status(esa)], [t55_relat_1])).
% 3.07/3.29  thf('53', plain,
% 3.07/3.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.07/3.29         (((k5_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X3)
% 3.07/3.29            = (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ (k5_relat_1 @ X0 @ X3)))
% 3.07/3.29          | ~ (v1_relat_1 @ X2)
% 3.07/3.29          | ~ (v1_relat_1 @ X0)
% 3.07/3.29          | ~ (v1_relat_1 @ X1)
% 3.07/3.29          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 3.07/3.29          | ~ (v1_relat_1 @ X3)
% 3.07/3.29          | ~ (v1_relat_1 @ X0))),
% 3.07/3.29      inference('sup+', [status(thm)], ['51', '52'])).
% 3.07/3.29  thf('54', plain,
% 3.07/3.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.07/3.29         (~ (v1_relat_1 @ X3)
% 3.07/3.29          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 3.07/3.29          | ~ (v1_relat_1 @ X1)
% 3.07/3.29          | ~ (v1_relat_1 @ X0)
% 3.07/3.29          | ~ (v1_relat_1 @ X2)
% 3.07/3.29          | ((k5_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X3)
% 3.07/3.29              = (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ (k5_relat_1 @ X0 @ X3))))),
% 3.07/3.29      inference('simplify', [status(thm)], ['53'])).
% 3.07/3.29  thf('55', plain,
% 3.07/3.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.07/3.29         (~ (v1_relat_1 @ X0)
% 3.07/3.29          | ~ (v1_relat_1 @ X0)
% 3.07/3.29          | ((k5_relat_1 @ 
% 3.07/3.29              (k5_relat_1 @ X0 @ 
% 3.07/3.29               (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X2)) @ 
% 3.07/3.29              X1)
% 3.07/3.29              = (k5_relat_1 @ 
% 3.07/3.29                 (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) @ 
% 3.07/3.29                 (k5_relat_1 @ X2 @ X1)))
% 3.07/3.29          | ~ (v1_relat_1 @ X0)
% 3.07/3.29          | ~ (v1_relat_1 @ X2)
% 3.07/3.29          | ~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 3.07/3.29          | ~ (v1_relat_1 @ X1))),
% 3.07/3.29      inference('sup-', [status(thm)], ['50', '54'])).
% 3.07/3.29  thf('56', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 3.07/3.29      inference('demod', [status(thm)], ['45', '46'])).
% 3.07/3.30  thf('57', plain,
% 3.07/3.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.07/3.30         (~ (v1_relat_1 @ X0)
% 3.07/3.30          | ~ (v1_relat_1 @ X0)
% 3.07/3.30          | ((k5_relat_1 @ 
% 3.07/3.30              (k5_relat_1 @ X0 @ 
% 3.07/3.30               (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X2)) @ 
% 3.07/3.30              X1)
% 3.07/3.30              = (k5_relat_1 @ 
% 3.07/3.30                 (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) @ 
% 3.07/3.30                 (k5_relat_1 @ X2 @ X1)))
% 3.07/3.30          | ~ (v1_relat_1 @ X0)
% 3.07/3.30          | ~ (v1_relat_1 @ X2)
% 3.07/3.30          | ~ (v1_relat_1 @ X1))),
% 3.07/3.30      inference('demod', [status(thm)], ['55', '56'])).
% 3.07/3.30  thf('58', plain,
% 3.07/3.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.07/3.30         (~ (v1_relat_1 @ X1)
% 3.07/3.30          | ~ (v1_relat_1 @ X2)
% 3.07/3.30          | ((k5_relat_1 @ 
% 3.07/3.30              (k5_relat_1 @ X0 @ 
% 3.07/3.30               (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X2)) @ 
% 3.07/3.30              X1)
% 3.07/3.30              = (k5_relat_1 @ 
% 3.07/3.30                 (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) @ 
% 3.07/3.30                 (k5_relat_1 @ X2 @ X1)))
% 3.07/3.30          | ~ (v1_relat_1 @ X0))),
% 3.07/3.30      inference('simplify', [status(thm)], ['57'])).
% 3.07/3.30  thf('59', plain,
% 3.07/3.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.07/3.30         (((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 3.07/3.30            = (k5_relat_1 @ 
% 3.07/3.30               (k5_relat_1 @ X1 @ (k6_partfun1 @ (k2_relat_1 @ X1))) @ 
% 3.07/3.30               (k5_relat_1 @ X0 @ X2)))
% 3.07/3.30          | ~ (v1_relat_1 @ X1)
% 3.07/3.30          | ~ (v1_relat_1 @ X0)
% 3.07/3.30          | ~ (v1_relat_1 @ X1)
% 3.07/3.30          | ~ (v1_relat_1 @ X0)
% 3.07/3.30          | ~ (v1_relat_1 @ X2))),
% 3.07/3.30      inference('sup+', [status(thm)], ['49', '58'])).
% 3.07/3.30  thf('60', plain,
% 3.07/3.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.07/3.30         (~ (v1_relat_1 @ X2)
% 3.07/3.30          | ~ (v1_relat_1 @ X0)
% 3.07/3.30          | ~ (v1_relat_1 @ X1)
% 3.07/3.30          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 3.07/3.30              = (k5_relat_1 @ 
% 3.07/3.30                 (k5_relat_1 @ X1 @ (k6_partfun1 @ (k2_relat_1 @ X1))) @ 
% 3.07/3.30                 (k5_relat_1 @ X0 @ X2))))),
% 3.07/3.30      inference('simplify', [status(thm)], ['59'])).
% 3.07/3.30  thf('61', plain,
% 3.07/3.30      (![X0 : $i, X1 : $i]:
% 3.07/3.30         (((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 3.07/3.30            (k6_partfun1 @ (k2_relat_1 @ X0)))
% 3.07/3.30            = (k5_relat_1 @ 
% 3.07/3.30               (k5_relat_1 @ X1 @ (k6_partfun1 @ (k2_relat_1 @ X1))) @ X0))
% 3.07/3.30          | ~ (v1_relat_1 @ X0)
% 3.07/3.30          | ~ (v1_relat_1 @ X1)
% 3.07/3.30          | ~ (v1_relat_1 @ X0)
% 3.07/3.30          | ~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0))))),
% 3.07/3.30      inference('sup+', [status(thm)], ['39', '60'])).
% 3.07/3.30  thf('62', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 3.07/3.30      inference('demod', [status(thm)], ['45', '46'])).
% 3.07/3.30  thf('63', plain,
% 3.07/3.30      (![X0 : $i, X1 : $i]:
% 3.07/3.30         (((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 3.07/3.30            (k6_partfun1 @ (k2_relat_1 @ X0)))
% 3.07/3.30            = (k5_relat_1 @ 
% 3.07/3.30               (k5_relat_1 @ X1 @ (k6_partfun1 @ (k2_relat_1 @ X1))) @ X0))
% 3.07/3.30          | ~ (v1_relat_1 @ X0)
% 3.07/3.30          | ~ (v1_relat_1 @ X1)
% 3.07/3.30          | ~ (v1_relat_1 @ X0))),
% 3.07/3.30      inference('demod', [status(thm)], ['61', '62'])).
% 3.07/3.30  thf('64', plain,
% 3.07/3.30      (![X0 : $i, X1 : $i]:
% 3.07/3.30         (~ (v1_relat_1 @ X1)
% 3.07/3.30          | ~ (v1_relat_1 @ X0)
% 3.07/3.30          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 3.07/3.30              (k6_partfun1 @ (k2_relat_1 @ X0)))
% 3.07/3.30              = (k5_relat_1 @ 
% 3.07/3.30                 (k5_relat_1 @ X1 @ (k6_partfun1 @ (k2_relat_1 @ X1))) @ X0)))),
% 3.07/3.30      inference('simplify', [status(thm)], ['63'])).
% 3.07/3.30  thf('65', plain,
% 3.07/3.30      (![X0 : $i, X1 : $i]:
% 3.07/3.30         (((k5_relat_1 @ X1 @ 
% 3.07/3.30            (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))
% 3.07/3.30            = (k5_relat_1 @ 
% 3.07/3.30               (k5_relat_1 @ X1 @ (k6_partfun1 @ (k2_relat_1 @ X1))) @ X0))
% 3.07/3.30          | ~ (v1_relat_1 @ X1)
% 3.07/3.30          | ~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 3.07/3.30          | ~ (v1_relat_1 @ X0)
% 3.07/3.30          | ~ (v1_relat_1 @ X0)
% 3.07/3.30          | ~ (v1_relat_1 @ X1))),
% 3.07/3.30      inference('sup+', [status(thm)], ['36', '64'])).
% 3.07/3.30  thf('66', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 3.07/3.30      inference('demod', [status(thm)], ['45', '46'])).
% 3.07/3.30  thf('67', plain,
% 3.07/3.30      (![X0 : $i, X1 : $i]:
% 3.07/3.30         (((k5_relat_1 @ X1 @ 
% 3.07/3.30            (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))
% 3.07/3.30            = (k5_relat_1 @ 
% 3.07/3.30               (k5_relat_1 @ X1 @ (k6_partfun1 @ (k2_relat_1 @ X1))) @ X0))
% 3.07/3.30          | ~ (v1_relat_1 @ X1)
% 3.07/3.30          | ~ (v1_relat_1 @ X0)
% 3.07/3.30          | ~ (v1_relat_1 @ X0)
% 3.07/3.30          | ~ (v1_relat_1 @ X1))),
% 3.07/3.30      inference('demod', [status(thm)], ['65', '66'])).
% 3.07/3.30  thf('68', plain,
% 3.07/3.30      (![X0 : $i, X1 : $i]:
% 3.07/3.30         (~ (v1_relat_1 @ X0)
% 3.07/3.30          | ~ (v1_relat_1 @ X1)
% 3.07/3.30          | ((k5_relat_1 @ X1 @ 
% 3.07/3.30              (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))
% 3.07/3.30              = (k5_relat_1 @ 
% 3.07/3.30                 (k5_relat_1 @ X1 @ (k6_partfun1 @ (k2_relat_1 @ X1))) @ X0)))),
% 3.07/3.30      inference('simplify', [status(thm)], ['67'])).
% 3.07/3.30  thf('69', plain,
% 3.07/3.30      (![X0 : $i, X1 : $i]:
% 3.07/3.30         (((k5_relat_1 @ X1 @ 
% 3.07/3.30            (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))
% 3.07/3.30            = (k5_relat_1 @ X1 @ 
% 3.07/3.30               (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X1)) @ X0)))
% 3.07/3.30          | ~ (v1_relat_1 @ X1)
% 3.07/3.30          | ~ (v1_relat_1 @ X0)
% 3.07/3.30          | ~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X1)))
% 3.07/3.30          | ~ (v1_relat_1 @ X1)
% 3.07/3.30          | ~ (v1_relat_1 @ X0))),
% 3.07/3.30      inference('sup+', [status(thm)], ['35', '68'])).
% 3.07/3.30  thf('70', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 3.07/3.30      inference('demod', [status(thm)], ['45', '46'])).
% 3.07/3.30  thf('71', plain,
% 3.07/3.30      (![X0 : $i, X1 : $i]:
% 3.07/3.30         (((k5_relat_1 @ X1 @ 
% 3.07/3.30            (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))
% 3.07/3.30            = (k5_relat_1 @ X1 @ 
% 3.07/3.30               (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X1)) @ X0)))
% 3.07/3.30          | ~ (v1_relat_1 @ X1)
% 3.07/3.30          | ~ (v1_relat_1 @ X0)
% 3.07/3.30          | ~ (v1_relat_1 @ X1)
% 3.07/3.30          | ~ (v1_relat_1 @ X0))),
% 3.07/3.30      inference('demod', [status(thm)], ['69', '70'])).
% 3.07/3.30  thf('72', plain,
% 3.07/3.30      (![X0 : $i, X1 : $i]:
% 3.07/3.30         (~ (v1_relat_1 @ X0)
% 3.07/3.30          | ~ (v1_relat_1 @ X1)
% 3.07/3.30          | ((k5_relat_1 @ X1 @ 
% 3.07/3.30              (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))
% 3.07/3.30              = (k5_relat_1 @ X1 @ 
% 3.07/3.30                 (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X1)) @ X0))))),
% 3.07/3.30      inference('simplify', [status(thm)], ['71'])).
% 3.07/3.30  thf('73', plain,
% 3.07/3.30      (![X0 : $i]:
% 3.07/3.30         (((k5_relat_1 @ X0 @ (k5_relat_1 @ sk_D @ (k6_partfun1 @ sk_A)))
% 3.07/3.30            = (k5_relat_1 @ X0 @ 
% 3.07/3.30               (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ sk_D)))
% 3.07/3.30          | ~ (v1_relat_1 @ X0)
% 3.07/3.30          | ~ (v1_relat_1 @ sk_D))),
% 3.07/3.30      inference('sup+', [status(thm)], ['34', '72'])).
% 3.07/3.30  thf('74', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.07/3.30      inference('demod', [status(thm)], ['23', '27', '30', '31', '32', '33'])).
% 3.07/3.30  thf('75', plain,
% 3.07/3.30      (![X9 : $i]:
% 3.07/3.30         (((k5_relat_1 @ X9 @ (k6_partfun1 @ (k2_relat_1 @ X9))) = (X9))
% 3.07/3.30          | ~ (v1_relat_1 @ X9))),
% 3.07/3.30      inference('demod', [status(thm)], ['37', '38'])).
% 3.07/3.30  thf('76', plain,
% 3.07/3.30      ((((k5_relat_1 @ sk_D @ (k6_partfun1 @ sk_A)) = (sk_D))
% 3.07/3.30        | ~ (v1_relat_1 @ sk_D))),
% 3.07/3.30      inference('sup+', [status(thm)], ['74', '75'])).
% 3.07/3.30  thf('77', plain,
% 3.07/3.30      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('78', plain,
% 3.07/3.30      (![X0 : $i, X1 : $i]:
% 3.07/3.30         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 3.07/3.30          | (v1_relat_1 @ X0)
% 3.07/3.30          | ~ (v1_relat_1 @ X1))),
% 3.07/3.30      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.07/3.30  thf('79', plain,
% 3.07/3.30      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 3.07/3.30      inference('sup-', [status(thm)], ['77', '78'])).
% 3.07/3.30  thf('80', plain,
% 3.07/3.30      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 3.07/3.30      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.07/3.30  thf('81', plain, ((v1_relat_1 @ sk_D)),
% 3.07/3.30      inference('demod', [status(thm)], ['79', '80'])).
% 3.07/3.30  thf('82', plain, (((k5_relat_1 @ sk_D @ (k6_partfun1 @ sk_A)) = (sk_D))),
% 3.07/3.30      inference('demod', [status(thm)], ['76', '81'])).
% 3.07/3.30  thf('83', plain, ((v1_relat_1 @ sk_D)),
% 3.07/3.30      inference('demod', [status(thm)], ['79', '80'])).
% 3.07/3.30  thf('84', plain,
% 3.07/3.30      (![X0 : $i]:
% 3.07/3.30         (((k5_relat_1 @ X0 @ sk_D)
% 3.07/3.30            = (k5_relat_1 @ X0 @ 
% 3.07/3.30               (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ sk_D)))
% 3.07/3.30          | ~ (v1_relat_1 @ X0))),
% 3.07/3.30      inference('demod', [status(thm)], ['73', '82', '83'])).
% 3.07/3.30  thf(dt_k2_funct_1, axiom,
% 3.07/3.30    (![A:$i]:
% 3.07/3.30     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.07/3.30       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 3.07/3.30         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 3.07/3.30  thf('85', plain,
% 3.07/3.30      (![X10 : $i]:
% 3.07/3.30         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 3.07/3.30          | ~ (v1_funct_1 @ X10)
% 3.07/3.30          | ~ (v1_relat_1 @ X10))),
% 3.07/3.30      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.07/3.30  thf('86', plain,
% 3.07/3.30      (![X10 : $i]:
% 3.07/3.30         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 3.07/3.30          | ~ (v1_funct_1 @ X10)
% 3.07/3.30          | ~ (v1_relat_1 @ X10))),
% 3.07/3.30      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.07/3.30  thf('87', plain,
% 3.07/3.30      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf(t35_funct_2, axiom,
% 3.07/3.30    (![A:$i,B:$i,C:$i]:
% 3.07/3.30     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.07/3.30         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.07/3.30       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 3.07/3.30         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.07/3.30           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 3.07/3.30             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 3.07/3.30  thf('88', plain,
% 3.07/3.30      (![X48 : $i, X49 : $i, X50 : $i]:
% 3.07/3.30         (((X48) = (k1_xboole_0))
% 3.07/3.30          | ~ (v1_funct_1 @ X49)
% 3.07/3.30          | ~ (v1_funct_2 @ X49 @ X50 @ X48)
% 3.07/3.30          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X48)))
% 3.07/3.30          | ((k5_relat_1 @ X49 @ (k2_funct_1 @ X49)) = (k6_partfun1 @ X50))
% 3.07/3.30          | ~ (v2_funct_1 @ X49)
% 3.07/3.30          | ((k2_relset_1 @ X50 @ X48 @ X49) != (X48)))),
% 3.07/3.30      inference('cnf', [status(esa)], [t35_funct_2])).
% 3.07/3.30  thf('89', plain,
% 3.07/3.30      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 3.07/3.30        | ~ (v2_funct_1 @ sk_D)
% 3.07/3.30        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 3.07/3.30        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.07/3.30        | ~ (v1_funct_1 @ sk_D)
% 3.07/3.30        | ((sk_A) = (k1_xboole_0)))),
% 3.07/3.30      inference('sup-', [status(thm)], ['87', '88'])).
% 3.07/3.30  thf('90', plain,
% 3.07/3.30      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 3.07/3.30      inference('sup-', [status(thm)], ['28', '29'])).
% 3.07/3.30  thf('91', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('92', plain, ((v1_funct_1 @ sk_D)),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('93', plain,
% 3.07/3.30      ((((k2_relat_1 @ sk_D) != (sk_A))
% 3.07/3.30        | ~ (v2_funct_1 @ sk_D)
% 3.07/3.30        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 3.07/3.30        | ((sk_A) = (k1_xboole_0)))),
% 3.07/3.30      inference('demod', [status(thm)], ['89', '90', '91', '92'])).
% 3.07/3.30  thf('94', plain, (((sk_A) != (k1_xboole_0))),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('95', plain,
% 3.07/3.30      ((((k2_relat_1 @ sk_D) != (sk_A))
% 3.07/3.30        | ~ (v2_funct_1 @ sk_D)
% 3.07/3.30        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 3.07/3.30      inference('simplify_reflect-', [status(thm)], ['93', '94'])).
% 3.07/3.30  thf('96', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.07/3.30      inference('demod', [status(thm)], ['23', '27', '30', '31', '32', '33'])).
% 3.07/3.30  thf('97', plain,
% 3.07/3.30      ((((sk_A) != (sk_A))
% 3.07/3.30        | ~ (v2_funct_1 @ sk_D)
% 3.07/3.30        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 3.07/3.30      inference('demod', [status(thm)], ['95', '96'])).
% 3.07/3.30  thf('98', plain,
% 3.07/3.30      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 3.07/3.30        | ~ (v2_funct_1 @ sk_D))),
% 3.07/3.30      inference('simplify', [status(thm)], ['97'])).
% 3.07/3.30  thf('99', plain,
% 3.07/3.30      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.07/3.30         = (k6_partfun1 @ sk_A))),
% 3.07/3.30      inference('demod', [status(thm)], ['12', '15'])).
% 3.07/3.30  thf('100', plain,
% 3.07/3.30      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf(t30_funct_2, axiom,
% 3.07/3.30    (![A:$i,B:$i,C:$i,D:$i]:
% 3.07/3.30     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.07/3.30         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 3.07/3.30       ( ![E:$i]:
% 3.07/3.30         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 3.07/3.30             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 3.07/3.30           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 3.07/3.30               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 3.07/3.30             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 3.07/3.30               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 3.07/3.30  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 3.07/3.30  thf(zf_stmt_2, axiom,
% 3.07/3.30    (![C:$i,B:$i]:
% 3.07/3.30     ( ( zip_tseitin_1 @ C @ B ) =>
% 3.07/3.30       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 3.07/3.30  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 3.07/3.30  thf(zf_stmt_4, axiom,
% 3.07/3.30    (![E:$i,D:$i]:
% 3.07/3.30     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 3.07/3.30  thf(zf_stmt_5, axiom,
% 3.07/3.30    (![A:$i,B:$i,C:$i,D:$i]:
% 3.07/3.30     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.07/3.30         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.07/3.30       ( ![E:$i]:
% 3.07/3.30         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.07/3.30             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.07/3.30           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 3.07/3.30               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 3.07/3.30             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 3.07/3.30  thf('101', plain,
% 3.07/3.30      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 3.07/3.30         (~ (v1_funct_1 @ X43)
% 3.07/3.30          | ~ (v1_funct_2 @ X43 @ X44 @ X45)
% 3.07/3.30          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 3.07/3.30          | (zip_tseitin_0 @ X43 @ X46)
% 3.07/3.30          | ~ (v2_funct_1 @ (k1_partfun1 @ X47 @ X44 @ X44 @ X45 @ X46 @ X43))
% 3.07/3.30          | (zip_tseitin_1 @ X45 @ X44)
% 3.07/3.30          | ((k2_relset_1 @ X47 @ X44 @ X46) != (X44))
% 3.07/3.30          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X44)))
% 3.07/3.30          | ~ (v1_funct_2 @ X46 @ X47 @ X44)
% 3.07/3.30          | ~ (v1_funct_1 @ X46))),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.07/3.30  thf('102', plain,
% 3.07/3.30      (![X0 : $i, X1 : $i]:
% 3.07/3.30         (~ (v1_funct_1 @ X0)
% 3.07/3.30          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.07/3.30          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.07/3.30          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 3.07/3.30          | (zip_tseitin_1 @ sk_A @ sk_B)
% 3.07/3.30          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 3.07/3.30          | (zip_tseitin_0 @ sk_D @ X0)
% 3.07/3.30          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.07/3.30          | ~ (v1_funct_1 @ sk_D))),
% 3.07/3.30      inference('sup-', [status(thm)], ['100', '101'])).
% 3.07/3.30  thf('103', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('104', plain, ((v1_funct_1 @ sk_D)),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('105', plain,
% 3.07/3.30      (![X0 : $i, X1 : $i]:
% 3.07/3.30         (~ (v1_funct_1 @ X0)
% 3.07/3.30          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.07/3.30          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.07/3.30          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 3.07/3.30          | (zip_tseitin_1 @ sk_A @ sk_B)
% 3.07/3.30          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 3.07/3.30          | (zip_tseitin_0 @ sk_D @ X0))),
% 3.07/3.30      inference('demod', [status(thm)], ['102', '103', '104'])).
% 3.07/3.30  thf('106', plain,
% 3.07/3.30      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 3.07/3.30        | (zip_tseitin_0 @ sk_D @ sk_C)
% 3.07/3.30        | (zip_tseitin_1 @ sk_A @ sk_B)
% 3.07/3.30        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 3.07/3.30        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 3.07/3.30        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.07/3.30        | ~ (v1_funct_1 @ sk_C))),
% 3.07/3.30      inference('sup-', [status(thm)], ['99', '105'])).
% 3.07/3.30  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 3.07/3.30  thf('107', plain, (![X11 : $i]: (v2_funct_1 @ (k6_relat_1 @ X11))),
% 3.07/3.30      inference('cnf', [status(esa)], [t52_funct_1])).
% 3.07/3.30  thf('108', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 3.07/3.30      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.07/3.30  thf('109', plain, (![X11 : $i]: (v2_funct_1 @ (k6_partfun1 @ X11))),
% 3.07/3.30      inference('demod', [status(thm)], ['107', '108'])).
% 3.07/3.30  thf('110', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('111', plain,
% 3.07/3.30      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('112', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('113', plain, ((v1_funct_1 @ sk_C)),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('114', plain,
% 3.07/3.30      (((zip_tseitin_0 @ sk_D @ sk_C)
% 3.07/3.30        | (zip_tseitin_1 @ sk_A @ sk_B)
% 3.07/3.30        | ((sk_B) != (sk_B)))),
% 3.07/3.30      inference('demod', [status(thm)],
% 3.07/3.30                ['106', '109', '110', '111', '112', '113'])).
% 3.07/3.30  thf('115', plain,
% 3.07/3.30      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 3.07/3.30      inference('simplify', [status(thm)], ['114'])).
% 3.07/3.30  thf('116', plain,
% 3.07/3.30      (![X41 : $i, X42 : $i]:
% 3.07/3.30         (((X41) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X41 @ X42))),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.07/3.30  thf('117', plain,
% 3.07/3.30      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 3.07/3.30      inference('sup-', [status(thm)], ['115', '116'])).
% 3.07/3.30  thf('118', plain, (((sk_A) != (k1_xboole_0))),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('119', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 3.07/3.30      inference('simplify_reflect-', [status(thm)], ['117', '118'])).
% 3.07/3.30  thf('120', plain,
% 3.07/3.30      (![X39 : $i, X40 : $i]:
% 3.07/3.30         ((v2_funct_1 @ X40) | ~ (zip_tseitin_0 @ X40 @ X39))),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_4])).
% 3.07/3.30  thf('121', plain, ((v2_funct_1 @ sk_D)),
% 3.07/3.30      inference('sup-', [status(thm)], ['119', '120'])).
% 3.07/3.30  thf('122', plain,
% 3.07/3.30      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 3.07/3.30      inference('demod', [status(thm)], ['98', '121'])).
% 3.07/3.30  thf('123', plain,
% 3.07/3.30      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('124', plain,
% 3.07/3.30      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf(redefinition_k1_partfun1, axiom,
% 3.07/3.30    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.07/3.30     ( ( ( v1_funct_1 @ E ) & 
% 3.07/3.30         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.07/3.30         ( v1_funct_1 @ F ) & 
% 3.07/3.30         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.07/3.30       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 3.07/3.30  thf('125', plain,
% 3.07/3.30      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 3.07/3.30         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 3.07/3.30          | ~ (v1_funct_1 @ X28)
% 3.07/3.30          | ~ (v1_funct_1 @ X31)
% 3.07/3.30          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 3.07/3.30          | ((k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31)
% 3.07/3.30              = (k5_relat_1 @ X28 @ X31)))),
% 3.07/3.30      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 3.07/3.30  thf('126', plain,
% 3.07/3.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.07/3.30         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 3.07/3.30            = (k5_relat_1 @ sk_C @ X0))
% 3.07/3.30          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.07/3.30          | ~ (v1_funct_1 @ X0)
% 3.07/3.30          | ~ (v1_funct_1 @ sk_C))),
% 3.07/3.30      inference('sup-', [status(thm)], ['124', '125'])).
% 3.07/3.30  thf('127', plain, ((v1_funct_1 @ sk_C)),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('128', plain,
% 3.07/3.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.07/3.30         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 3.07/3.30            = (k5_relat_1 @ sk_C @ X0))
% 3.07/3.30          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.07/3.30          | ~ (v1_funct_1 @ X0))),
% 3.07/3.30      inference('demod', [status(thm)], ['126', '127'])).
% 3.07/3.30  thf('129', plain,
% 3.07/3.30      ((~ (v1_funct_1 @ sk_D)
% 3.07/3.30        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.07/3.30            = (k5_relat_1 @ sk_C @ sk_D)))),
% 3.07/3.30      inference('sup-', [status(thm)], ['123', '128'])).
% 3.07/3.30  thf('130', plain, ((v1_funct_1 @ sk_D)),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('131', plain,
% 3.07/3.30      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.07/3.30         = (k6_partfun1 @ sk_A))),
% 3.07/3.30      inference('demod', [status(thm)], ['12', '15'])).
% 3.07/3.30  thf('132', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 3.07/3.30      inference('demod', [status(thm)], ['129', '130', '131'])).
% 3.07/3.30  thf('133', plain,
% 3.07/3.30      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.07/3.30         (~ (v1_relat_1 @ X4)
% 3.07/3.30          | ((k5_relat_1 @ (k5_relat_1 @ X5 @ X4) @ X6)
% 3.07/3.30              = (k5_relat_1 @ X5 @ (k5_relat_1 @ X4 @ X6)))
% 3.07/3.30          | ~ (v1_relat_1 @ X6)
% 3.07/3.30          | ~ (v1_relat_1 @ X5))),
% 3.07/3.30      inference('cnf', [status(esa)], [t55_relat_1])).
% 3.07/3.30  thf('134', plain,
% 3.07/3.30      (![X0 : $i]:
% 3.07/3.30         (((k5_relat_1 @ (k6_partfun1 @ sk_A) @ X0)
% 3.07/3.30            = (k5_relat_1 @ sk_C @ (k5_relat_1 @ sk_D @ X0)))
% 3.07/3.30          | ~ (v1_relat_1 @ sk_C)
% 3.07/3.30          | ~ (v1_relat_1 @ X0)
% 3.07/3.30          | ~ (v1_relat_1 @ sk_D))),
% 3.07/3.30      inference('sup+', [status(thm)], ['132', '133'])).
% 3.07/3.30  thf('135', plain,
% 3.07/3.30      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('136', plain,
% 3.07/3.30      (![X0 : $i, X1 : $i]:
% 3.07/3.30         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 3.07/3.30          | (v1_relat_1 @ X0)
% 3.07/3.30          | ~ (v1_relat_1 @ X1))),
% 3.07/3.30      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.07/3.30  thf('137', plain,
% 3.07/3.30      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 3.07/3.30      inference('sup-', [status(thm)], ['135', '136'])).
% 3.07/3.30  thf('138', plain,
% 3.07/3.30      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 3.07/3.30      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.07/3.30  thf('139', plain, ((v1_relat_1 @ sk_C)),
% 3.07/3.30      inference('demod', [status(thm)], ['137', '138'])).
% 3.07/3.30  thf('140', plain, ((v1_relat_1 @ sk_D)),
% 3.07/3.30      inference('demod', [status(thm)], ['79', '80'])).
% 3.07/3.30  thf('141', plain,
% 3.07/3.30      (![X0 : $i]:
% 3.07/3.30         (((k5_relat_1 @ (k6_partfun1 @ sk_A) @ X0)
% 3.07/3.30            = (k5_relat_1 @ sk_C @ (k5_relat_1 @ sk_D @ X0)))
% 3.07/3.30          | ~ (v1_relat_1 @ X0))),
% 3.07/3.30      inference('demod', [status(thm)], ['134', '139', '140'])).
% 3.07/3.30  thf('142', plain,
% 3.07/3.30      ((((k5_relat_1 @ (k6_partfun1 @ sk_A) @ (k2_funct_1 @ sk_D))
% 3.07/3.30          = (k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)))
% 3.07/3.30        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D)))),
% 3.07/3.30      inference('sup+', [status(thm)], ['122', '141'])).
% 3.07/3.30  thf('143', plain,
% 3.07/3.30      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('144', plain,
% 3.07/3.30      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.07/3.30         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 3.07/3.30          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 3.07/3.30      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.07/3.30  thf('145', plain,
% 3.07/3.30      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 3.07/3.30      inference('sup-', [status(thm)], ['143', '144'])).
% 3.07/3.30  thf('146', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('147', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 3.07/3.30      inference('sup+', [status(thm)], ['145', '146'])).
% 3.07/3.30  thf('148', plain,
% 3.07/3.30      (![X9 : $i]:
% 3.07/3.30         (((k5_relat_1 @ X9 @ (k6_partfun1 @ (k2_relat_1 @ X9))) = (X9))
% 3.07/3.30          | ~ (v1_relat_1 @ X9))),
% 3.07/3.30      inference('demod', [status(thm)], ['37', '38'])).
% 3.07/3.30  thf('149', plain,
% 3.07/3.30      ((((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))
% 3.07/3.30        | ~ (v1_relat_1 @ sk_C))),
% 3.07/3.30      inference('sup+', [status(thm)], ['147', '148'])).
% 3.07/3.30  thf('150', plain, ((v1_relat_1 @ sk_C)),
% 3.07/3.30      inference('demod', [status(thm)], ['137', '138'])).
% 3.07/3.30  thf('151', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 3.07/3.30      inference('demod', [status(thm)], ['149', '150'])).
% 3.07/3.30  thf('152', plain,
% 3.07/3.30      ((((k5_relat_1 @ (k6_partfun1 @ sk_A) @ (k2_funct_1 @ sk_D)) = (sk_C))
% 3.07/3.30        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D)))),
% 3.07/3.30      inference('demod', [status(thm)], ['142', '151'])).
% 3.07/3.30  thf('153', plain,
% 3.07/3.30      ((~ (v1_relat_1 @ sk_D)
% 3.07/3.30        | ~ (v1_funct_1 @ sk_D)
% 3.07/3.30        | ((k5_relat_1 @ (k6_partfun1 @ sk_A) @ (k2_funct_1 @ sk_D)) = (sk_C)))),
% 3.07/3.30      inference('sup-', [status(thm)], ['86', '152'])).
% 3.07/3.30  thf('154', plain, ((v1_relat_1 @ sk_D)),
% 3.07/3.30      inference('demod', [status(thm)], ['79', '80'])).
% 3.07/3.30  thf('155', plain, ((v1_funct_1 @ sk_D)),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('156', plain,
% 3.07/3.30      (((k5_relat_1 @ (k6_partfun1 @ sk_A) @ (k2_funct_1 @ sk_D)) = (sk_C))),
% 3.07/3.30      inference('demod', [status(thm)], ['153', '154', '155'])).
% 3.07/3.30  thf('157', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.07/3.30      inference('demod', [status(thm)], ['23', '27', '30', '31', '32', '33'])).
% 3.07/3.30  thf('158', plain,
% 3.07/3.30      (![X0 : $i, X1 : $i]:
% 3.07/3.30         (~ (v1_relat_1 @ X1)
% 3.07/3.30          | ~ (v1_relat_1 @ X0)
% 3.07/3.30          | ((k5_relat_1 @ X0 @ X1)
% 3.07/3.30              = (k5_relat_1 @ X0 @ 
% 3.07/3.30                 (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1))))),
% 3.07/3.30      inference('simplify', [status(thm)], ['48'])).
% 3.07/3.30  thf('159', plain,
% 3.07/3.30      (![X0 : $i]:
% 3.07/3.30         (((k5_relat_1 @ sk_D @ X0)
% 3.07/3.30            = (k5_relat_1 @ sk_D @ (k5_relat_1 @ (k6_partfun1 @ sk_A) @ X0)))
% 3.07/3.30          | ~ (v1_relat_1 @ sk_D)
% 3.07/3.30          | ~ (v1_relat_1 @ X0))),
% 3.07/3.30      inference('sup+', [status(thm)], ['157', '158'])).
% 3.07/3.30  thf('160', plain, ((v1_relat_1 @ sk_D)),
% 3.07/3.30      inference('demod', [status(thm)], ['79', '80'])).
% 3.07/3.30  thf('161', plain,
% 3.07/3.30      (![X0 : $i]:
% 3.07/3.30         (((k5_relat_1 @ sk_D @ X0)
% 3.07/3.30            = (k5_relat_1 @ sk_D @ (k5_relat_1 @ (k6_partfun1 @ sk_A) @ X0)))
% 3.07/3.30          | ~ (v1_relat_1 @ X0))),
% 3.07/3.30      inference('demod', [status(thm)], ['159', '160'])).
% 3.07/3.30  thf('162', plain,
% 3.07/3.30      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k5_relat_1 @ sk_D @ sk_C))
% 3.07/3.30        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D)))),
% 3.07/3.30      inference('sup+', [status(thm)], ['156', '161'])).
% 3.07/3.30  thf('163', plain,
% 3.07/3.30      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 3.07/3.30      inference('demod', [status(thm)], ['98', '121'])).
% 3.07/3.30  thf('164', plain,
% 3.07/3.30      ((((k6_partfun1 @ sk_B) = (k5_relat_1 @ sk_D @ sk_C))
% 3.07/3.30        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D)))),
% 3.07/3.30      inference('demod', [status(thm)], ['162', '163'])).
% 3.07/3.30  thf('165', plain,
% 3.07/3.30      ((~ (v1_relat_1 @ sk_D)
% 3.07/3.30        | ~ (v1_funct_1 @ sk_D)
% 3.07/3.30        | ((k6_partfun1 @ sk_B) = (k5_relat_1 @ sk_D @ sk_C)))),
% 3.07/3.30      inference('sup-', [status(thm)], ['85', '164'])).
% 3.07/3.30  thf('166', plain, ((v1_relat_1 @ sk_D)),
% 3.07/3.30      inference('demod', [status(thm)], ['79', '80'])).
% 3.07/3.30  thf('167', plain, ((v1_funct_1 @ sk_D)),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('168', plain, (((k6_partfun1 @ sk_B) = (k5_relat_1 @ sk_D @ sk_C))),
% 3.07/3.30      inference('demod', [status(thm)], ['165', '166', '167'])).
% 3.07/3.30  thf('169', plain,
% 3.07/3.30      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.07/3.30         (~ (v1_relat_1 @ X4)
% 3.07/3.30          | ((k5_relat_1 @ (k5_relat_1 @ X5 @ X4) @ X6)
% 3.07/3.30              = (k5_relat_1 @ X5 @ (k5_relat_1 @ X4 @ X6)))
% 3.07/3.30          | ~ (v1_relat_1 @ X6)
% 3.07/3.30          | ~ (v1_relat_1 @ X5))),
% 3.07/3.30      inference('cnf', [status(esa)], [t55_relat_1])).
% 3.07/3.30  thf('170', plain,
% 3.07/3.30      (![X0 : $i]:
% 3.07/3.30         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 3.07/3.30            = (k5_relat_1 @ sk_D @ (k5_relat_1 @ sk_C @ X0)))
% 3.07/3.30          | ~ (v1_relat_1 @ sk_D)
% 3.07/3.30          | ~ (v1_relat_1 @ X0)
% 3.07/3.30          | ~ (v1_relat_1 @ sk_C))),
% 3.07/3.30      inference('sup+', [status(thm)], ['168', '169'])).
% 3.07/3.30  thf('171', plain, ((v1_relat_1 @ sk_D)),
% 3.07/3.30      inference('demod', [status(thm)], ['79', '80'])).
% 3.07/3.30  thf('172', plain, ((v1_relat_1 @ sk_C)),
% 3.07/3.30      inference('demod', [status(thm)], ['137', '138'])).
% 3.07/3.30  thf('173', plain,
% 3.07/3.30      (![X0 : $i]:
% 3.07/3.30         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 3.07/3.30            = (k5_relat_1 @ sk_D @ (k5_relat_1 @ sk_C @ X0)))
% 3.07/3.30          | ~ (v1_relat_1 @ X0))),
% 3.07/3.30      inference('demod', [status(thm)], ['170', '171', '172'])).
% 3.07/3.30  thf('174', plain,
% 3.07/3.30      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 3.07/3.30          (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)) @ sk_D))
% 3.07/3.30          = (k5_relat_1 @ sk_D @ (k5_relat_1 @ sk_C @ sk_D)))
% 3.07/3.30        | ~ (v1_relat_1 @ sk_C)
% 3.07/3.30        | ~ (v1_relat_1 @ 
% 3.07/3.30             (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)) @ sk_D)))),
% 3.07/3.30      inference('sup+', [status(thm)], ['84', '173'])).
% 3.07/3.30  thf('175', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 3.07/3.30      inference('sup+', [status(thm)], ['145', '146'])).
% 3.07/3.30  thf('176', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 3.07/3.30      inference('demod', [status(thm)], ['129', '130', '131'])).
% 3.07/3.30  thf('177', plain,
% 3.07/3.30      (![X10 : $i]:
% 3.07/3.30         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 3.07/3.30          | ~ (v1_funct_1 @ X10)
% 3.07/3.30          | ~ (v1_relat_1 @ X10))),
% 3.07/3.30      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.07/3.30  thf('178', plain,
% 3.07/3.30      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('179', plain,
% 3.07/3.30      (![X48 : $i, X49 : $i, X50 : $i]:
% 3.07/3.30         (((X48) = (k1_xboole_0))
% 3.07/3.30          | ~ (v1_funct_1 @ X49)
% 3.07/3.30          | ~ (v1_funct_2 @ X49 @ X50 @ X48)
% 3.07/3.30          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X48)))
% 3.07/3.30          | ((k5_relat_1 @ (k2_funct_1 @ X49) @ X49) = (k6_partfun1 @ X48))
% 3.07/3.30          | ~ (v2_funct_1 @ X49)
% 3.07/3.30          | ((k2_relset_1 @ X50 @ X48 @ X49) != (X48)))),
% 3.07/3.30      inference('cnf', [status(esa)], [t35_funct_2])).
% 3.07/3.30  thf('180', plain,
% 3.07/3.30      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 3.07/3.30        | ~ (v2_funct_1 @ sk_C)
% 3.07/3.30        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 3.07/3.30        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.07/3.30        | ~ (v1_funct_1 @ sk_C)
% 3.07/3.30        | ((sk_B) = (k1_xboole_0)))),
% 3.07/3.30      inference('sup-', [status(thm)], ['178', '179'])).
% 3.07/3.30  thf('181', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('182', plain, ((v2_funct_1 @ sk_C)),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('183', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('184', plain, ((v1_funct_1 @ sk_C)),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('185', plain,
% 3.07/3.30      ((((sk_B) != (sk_B))
% 3.07/3.30        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 3.07/3.30        | ((sk_B) = (k1_xboole_0)))),
% 3.07/3.30      inference('demod', [status(thm)], ['180', '181', '182', '183', '184'])).
% 3.07/3.30  thf('186', plain,
% 3.07/3.30      ((((sk_B) = (k1_xboole_0))
% 3.07/3.30        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 3.07/3.30      inference('simplify', [status(thm)], ['185'])).
% 3.07/3.30  thf('187', plain, (((sk_B) != (k1_xboole_0))),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('188', plain,
% 3.07/3.30      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 3.07/3.30      inference('simplify_reflect-', [status(thm)], ['186', '187'])).
% 3.07/3.30  thf('189', plain,
% 3.07/3.30      (![X4 : $i, X5 : $i, X6 : $i]:
% 3.07/3.30         (~ (v1_relat_1 @ X4)
% 3.07/3.30          | ((k5_relat_1 @ (k5_relat_1 @ X5 @ X4) @ X6)
% 3.07/3.30              = (k5_relat_1 @ X5 @ (k5_relat_1 @ X4 @ X6)))
% 3.07/3.30          | ~ (v1_relat_1 @ X6)
% 3.07/3.30          | ~ (v1_relat_1 @ X5))),
% 3.07/3.30      inference('cnf', [status(esa)], [t55_relat_1])).
% 3.07/3.30  thf('190', plain,
% 3.07/3.30      (![X0 : $i]:
% 3.07/3.30         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 3.07/3.30            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 3.07/3.30          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 3.07/3.30          | ~ (v1_relat_1 @ X0)
% 3.07/3.30          | ~ (v1_relat_1 @ sk_C))),
% 3.07/3.30      inference('sup+', [status(thm)], ['188', '189'])).
% 3.07/3.30  thf('191', plain, ((v1_relat_1 @ sk_C)),
% 3.07/3.30      inference('demod', [status(thm)], ['137', '138'])).
% 3.07/3.30  thf('192', plain,
% 3.07/3.30      (![X0 : $i]:
% 3.07/3.30         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 3.07/3.30            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 3.07/3.30          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 3.07/3.30          | ~ (v1_relat_1 @ X0))),
% 3.07/3.30      inference('demod', [status(thm)], ['190', '191'])).
% 3.07/3.30  thf('193', plain,
% 3.07/3.30      (![X0 : $i]:
% 3.07/3.30         (~ (v1_relat_1 @ sk_C)
% 3.07/3.30          | ~ (v1_funct_1 @ sk_C)
% 3.07/3.30          | ~ (v1_relat_1 @ X0)
% 3.07/3.30          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 3.07/3.30              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 3.07/3.30      inference('sup-', [status(thm)], ['177', '192'])).
% 3.07/3.30  thf('194', plain, ((v1_relat_1 @ sk_C)),
% 3.07/3.30      inference('demod', [status(thm)], ['137', '138'])).
% 3.07/3.30  thf('195', plain, ((v1_funct_1 @ sk_C)),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('196', plain,
% 3.07/3.30      (![X0 : $i]:
% 3.07/3.30         (~ (v1_relat_1 @ X0)
% 3.07/3.30          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 3.07/3.30              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 3.07/3.30      inference('demod', [status(thm)], ['193', '194', '195'])).
% 3.07/3.30  thf('197', plain,
% 3.07/3.30      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 3.07/3.30          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 3.07/3.30        | ~ (v1_relat_1 @ sk_D))),
% 3.07/3.30      inference('sup+', [status(thm)], ['176', '196'])).
% 3.07/3.30  thf('198', plain,
% 3.07/3.30      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('199', plain,
% 3.07/3.30      (![X48 : $i, X49 : $i, X50 : $i]:
% 3.07/3.30         (((X48) = (k1_xboole_0))
% 3.07/3.30          | ~ (v1_funct_1 @ X49)
% 3.07/3.30          | ~ (v1_funct_2 @ X49 @ X50 @ X48)
% 3.07/3.30          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X48)))
% 3.07/3.30          | ((k5_relat_1 @ X49 @ (k2_funct_1 @ X49)) = (k6_partfun1 @ X50))
% 3.07/3.30          | ~ (v2_funct_1 @ X49)
% 3.07/3.30          | ((k2_relset_1 @ X50 @ X48 @ X49) != (X48)))),
% 3.07/3.30      inference('cnf', [status(esa)], [t35_funct_2])).
% 3.07/3.30  thf('200', plain,
% 3.07/3.30      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 3.07/3.30        | ~ (v2_funct_1 @ sk_C)
% 3.07/3.30        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 3.07/3.30        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.07/3.30        | ~ (v1_funct_1 @ sk_C)
% 3.07/3.30        | ((sk_B) = (k1_xboole_0)))),
% 3.07/3.30      inference('sup-', [status(thm)], ['198', '199'])).
% 3.07/3.30  thf('201', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('202', plain, ((v2_funct_1 @ sk_C)),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('203', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('204', plain, ((v1_funct_1 @ sk_C)),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('205', plain,
% 3.07/3.30      ((((sk_B) != (sk_B))
% 3.07/3.30        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 3.07/3.30        | ((sk_B) = (k1_xboole_0)))),
% 3.07/3.30      inference('demod', [status(thm)], ['200', '201', '202', '203', '204'])).
% 3.07/3.30  thf('206', plain,
% 3.07/3.30      ((((sk_B) = (k1_xboole_0))
% 3.07/3.30        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 3.07/3.30      inference('simplify', [status(thm)], ['205'])).
% 3.07/3.30  thf('207', plain, (((sk_B) != (k1_xboole_0))),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('208', plain,
% 3.07/3.30      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 3.07/3.30      inference('simplify_reflect-', [status(thm)], ['206', '207'])).
% 3.07/3.30  thf(t58_funct_1, axiom,
% 3.07/3.30    (![A:$i]:
% 3.07/3.30     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.07/3.30       ( ( v2_funct_1 @ A ) =>
% 3.07/3.30         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 3.07/3.30             ( k1_relat_1 @ A ) ) & 
% 3.07/3.30           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 3.07/3.30             ( k1_relat_1 @ A ) ) ) ) ))).
% 3.07/3.30  thf('209', plain,
% 3.07/3.30      (![X13 : $i]:
% 3.07/3.30         (~ (v2_funct_1 @ X13)
% 3.07/3.30          | ((k2_relat_1 @ (k5_relat_1 @ X13 @ (k2_funct_1 @ X13)))
% 3.07/3.30              = (k1_relat_1 @ X13))
% 3.07/3.30          | ~ (v1_funct_1 @ X13)
% 3.07/3.30          | ~ (v1_relat_1 @ X13))),
% 3.07/3.30      inference('cnf', [status(esa)], [t58_funct_1])).
% 3.07/3.30  thf('210', plain,
% 3.07/3.30      ((((k2_relat_1 @ (k6_partfun1 @ sk_A)) = (k1_relat_1 @ sk_C))
% 3.07/3.30        | ~ (v1_relat_1 @ sk_C)
% 3.07/3.30        | ~ (v1_funct_1 @ sk_C)
% 3.07/3.30        | ~ (v2_funct_1 @ sk_C))),
% 3.07/3.30      inference('sup+', [status(thm)], ['208', '209'])).
% 3.07/3.30  thf(t71_relat_1, axiom,
% 3.07/3.30    (![A:$i]:
% 3.07/3.30     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 3.07/3.30       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 3.07/3.30  thf('211', plain, (![X8 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X8)) = (X8))),
% 3.07/3.30      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.07/3.30  thf('212', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 3.07/3.30      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.07/3.30  thf('213', plain, (![X8 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X8)) = (X8))),
% 3.07/3.30      inference('demod', [status(thm)], ['211', '212'])).
% 3.07/3.30  thf('214', plain, ((v1_relat_1 @ sk_C)),
% 3.07/3.30      inference('demod', [status(thm)], ['137', '138'])).
% 3.07/3.30  thf('215', plain, ((v1_funct_1 @ sk_C)),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('216', plain, ((v2_funct_1 @ sk_C)),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('217', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 3.07/3.30      inference('demod', [status(thm)], ['210', '213', '214', '215', '216'])).
% 3.07/3.30  thf('218', plain,
% 3.07/3.30      (![X10 : $i]:
% 3.07/3.30         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 3.07/3.30          | ~ (v1_funct_1 @ X10)
% 3.07/3.30          | ~ (v1_relat_1 @ X10))),
% 3.07/3.30      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.07/3.30  thf(t55_funct_1, axiom,
% 3.07/3.30    (![A:$i]:
% 3.07/3.30     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.07/3.30       ( ( v2_funct_1 @ A ) =>
% 3.07/3.30         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 3.07/3.30           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 3.07/3.30  thf('219', plain,
% 3.07/3.30      (![X12 : $i]:
% 3.07/3.30         (~ (v2_funct_1 @ X12)
% 3.07/3.30          | ((k1_relat_1 @ X12) = (k2_relat_1 @ (k2_funct_1 @ X12)))
% 3.07/3.30          | ~ (v1_funct_1 @ X12)
% 3.07/3.30          | ~ (v1_relat_1 @ X12))),
% 3.07/3.30      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.07/3.30  thf('220', plain,
% 3.07/3.30      (![X9 : $i]:
% 3.07/3.30         (((k5_relat_1 @ X9 @ (k6_partfun1 @ (k2_relat_1 @ X9))) = (X9))
% 3.07/3.30          | ~ (v1_relat_1 @ X9))),
% 3.07/3.30      inference('demod', [status(thm)], ['37', '38'])).
% 3.07/3.30  thf('221', plain,
% 3.07/3.30      (![X0 : $i]:
% 3.07/3.30         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 3.07/3.30            = (k2_funct_1 @ X0))
% 3.07/3.30          | ~ (v1_relat_1 @ X0)
% 3.07/3.30          | ~ (v1_funct_1 @ X0)
% 3.07/3.30          | ~ (v2_funct_1 @ X0)
% 3.07/3.30          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 3.07/3.30      inference('sup+', [status(thm)], ['219', '220'])).
% 3.07/3.30  thf('222', plain,
% 3.07/3.30      (![X0 : $i]:
% 3.07/3.30         (~ (v1_relat_1 @ X0)
% 3.07/3.30          | ~ (v1_funct_1 @ X0)
% 3.07/3.30          | ~ (v2_funct_1 @ X0)
% 3.07/3.30          | ~ (v1_funct_1 @ X0)
% 3.07/3.30          | ~ (v1_relat_1 @ X0)
% 3.07/3.30          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 3.07/3.30              (k6_partfun1 @ (k1_relat_1 @ X0))) = (k2_funct_1 @ X0)))),
% 3.07/3.30      inference('sup-', [status(thm)], ['218', '221'])).
% 3.07/3.30  thf('223', plain,
% 3.07/3.30      (![X0 : $i]:
% 3.07/3.30         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 3.07/3.30            = (k2_funct_1 @ X0))
% 3.07/3.30          | ~ (v2_funct_1 @ X0)
% 3.07/3.30          | ~ (v1_funct_1 @ X0)
% 3.07/3.30          | ~ (v1_relat_1 @ X0))),
% 3.07/3.30      inference('simplify', [status(thm)], ['222'])).
% 3.07/3.30  thf('224', plain,
% 3.07/3.30      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 3.07/3.30          = (k2_funct_1 @ sk_C))
% 3.07/3.30        | ~ (v1_relat_1 @ sk_C)
% 3.07/3.30        | ~ (v1_funct_1 @ sk_C)
% 3.07/3.30        | ~ (v2_funct_1 @ sk_C))),
% 3.07/3.30      inference('sup+', [status(thm)], ['217', '223'])).
% 3.07/3.30  thf('225', plain, ((v1_relat_1 @ sk_C)),
% 3.07/3.30      inference('demod', [status(thm)], ['137', '138'])).
% 3.07/3.30  thf('226', plain, ((v1_funct_1 @ sk_C)),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('227', plain, ((v2_funct_1 @ sk_C)),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('228', plain,
% 3.07/3.30      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 3.07/3.30         = (k2_funct_1 @ sk_C))),
% 3.07/3.30      inference('demod', [status(thm)], ['224', '225', '226', '227'])).
% 3.07/3.30  thf('229', plain, ((v1_relat_1 @ sk_D)),
% 3.07/3.30      inference('demod', [status(thm)], ['79', '80'])).
% 3.07/3.30  thf('230', plain,
% 3.07/3.30      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (k2_funct_1 @ sk_C))),
% 3.07/3.30      inference('demod', [status(thm)], ['197', '228', '229'])).
% 3.07/3.30  thf('231', plain,
% 3.07/3.30      (![X10 : $i]:
% 3.07/3.30         ((v1_relat_1 @ (k2_funct_1 @ X10))
% 3.07/3.30          | ~ (v1_funct_1 @ X10)
% 3.07/3.30          | ~ (v1_relat_1 @ X10))),
% 3.07/3.30      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.07/3.30  thf('232', plain,
% 3.07/3.30      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 3.07/3.30      inference('simplify_reflect-', [status(thm)], ['206', '207'])).
% 3.07/3.30  thf('233', plain,
% 3.07/3.30      (![X0 : $i]:
% 3.07/3.30         (~ (v1_relat_1 @ X0)
% 3.07/3.30          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 3.07/3.30              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 3.07/3.30      inference('demod', [status(thm)], ['193', '194', '195'])).
% 3.07/3.30  thf('234', plain,
% 3.07/3.30      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 3.07/3.30          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 3.07/3.30        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 3.07/3.30      inference('sup+', [status(thm)], ['232', '233'])).
% 3.07/3.30  thf('235', plain,
% 3.07/3.30      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 3.07/3.30         = (k2_funct_1 @ sk_C))),
% 3.07/3.30      inference('demod', [status(thm)], ['224', '225', '226', '227'])).
% 3.07/3.30  thf('236', plain,
% 3.07/3.30      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 3.07/3.30          = (k2_funct_1 @ sk_C))
% 3.07/3.30        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 3.07/3.30      inference('demod', [status(thm)], ['234', '235'])).
% 3.07/3.30  thf('237', plain,
% 3.07/3.30      ((~ (v1_relat_1 @ sk_C)
% 3.07/3.30        | ~ (v1_funct_1 @ sk_C)
% 3.07/3.30        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 3.07/3.30            = (k2_funct_1 @ sk_C)))),
% 3.07/3.30      inference('sup-', [status(thm)], ['231', '236'])).
% 3.07/3.30  thf('238', plain, ((v1_relat_1 @ sk_C)),
% 3.07/3.30      inference('demod', [status(thm)], ['137', '138'])).
% 3.07/3.30  thf('239', plain, ((v1_funct_1 @ sk_C)),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('240', plain,
% 3.07/3.30      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 3.07/3.30         = (k2_funct_1 @ sk_C))),
% 3.07/3.30      inference('demod', [status(thm)], ['237', '238', '239'])).
% 3.07/3.30  thf('241', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 3.07/3.30      inference('demod', [status(thm)], ['129', '130', '131'])).
% 3.07/3.30  thf('242', plain, (((k5_relat_1 @ sk_D @ (k6_partfun1 @ sk_A)) = (sk_D))),
% 3.07/3.30      inference('demod', [status(thm)], ['76', '81'])).
% 3.07/3.30  thf('243', plain, ((v1_relat_1 @ sk_C)),
% 3.07/3.30      inference('demod', [status(thm)], ['137', '138'])).
% 3.07/3.30  thf('244', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 3.07/3.30      inference('sup+', [status(thm)], ['145', '146'])).
% 3.07/3.30  thf('245', plain,
% 3.07/3.30      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (k2_funct_1 @ sk_C))),
% 3.07/3.30      inference('demod', [status(thm)], ['197', '228', '229'])).
% 3.07/3.30  thf('246', plain,
% 3.07/3.30      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('247', plain,
% 3.07/3.30      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('248', plain,
% 3.07/3.30      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 3.07/3.30         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 3.07/3.30          | ~ (v1_funct_1 @ X22)
% 3.07/3.30          | ~ (v1_funct_1 @ X25)
% 3.07/3.30          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 3.07/3.30          | (v1_funct_1 @ (k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25)))),
% 3.07/3.30      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.07/3.30  thf('249', plain,
% 3.07/3.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.07/3.30         ((v1_funct_1 @ (k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0))
% 3.07/3.30          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.07/3.30          | ~ (v1_funct_1 @ X0)
% 3.07/3.30          | ~ (v1_funct_1 @ sk_D))),
% 3.07/3.30      inference('sup-', [status(thm)], ['247', '248'])).
% 3.07/3.30  thf('250', plain, ((v1_funct_1 @ sk_D)),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('251', plain,
% 3.07/3.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.07/3.30         ((v1_funct_1 @ (k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0))
% 3.07/3.30          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.07/3.30          | ~ (v1_funct_1 @ X0))),
% 3.07/3.30      inference('demod', [status(thm)], ['249', '250'])).
% 3.07/3.30  thf('252', plain,
% 3.07/3.30      ((~ (v1_funct_1 @ sk_C)
% 3.07/3.30        | (v1_funct_1 @ (k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)))),
% 3.07/3.30      inference('sup-', [status(thm)], ['246', '251'])).
% 3.07/3.30  thf('253', plain, ((v1_funct_1 @ sk_C)),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('254', plain,
% 3.07/3.30      ((v1_funct_1 @ (k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C))),
% 3.07/3.30      inference('demod', [status(thm)], ['252', '253'])).
% 3.07/3.30  thf('255', plain,
% 3.07/3.30      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('256', plain,
% 3.07/3.30      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('257', plain,
% 3.07/3.30      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 3.07/3.30         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 3.07/3.30          | ~ (v1_funct_1 @ X28)
% 3.07/3.30          | ~ (v1_funct_1 @ X31)
% 3.07/3.30          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 3.07/3.30          | ((k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31)
% 3.07/3.30              = (k5_relat_1 @ X28 @ X31)))),
% 3.07/3.30      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 3.07/3.30  thf('258', plain,
% 3.07/3.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.07/3.30         (((k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0)
% 3.07/3.30            = (k5_relat_1 @ sk_D @ X0))
% 3.07/3.30          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.07/3.30          | ~ (v1_funct_1 @ X0)
% 3.07/3.30          | ~ (v1_funct_1 @ sk_D))),
% 3.07/3.30      inference('sup-', [status(thm)], ['256', '257'])).
% 3.07/3.30  thf('259', plain, ((v1_funct_1 @ sk_D)),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('260', plain,
% 3.07/3.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.07/3.30         (((k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0)
% 3.07/3.30            = (k5_relat_1 @ sk_D @ X0))
% 3.07/3.30          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.07/3.30          | ~ (v1_funct_1 @ X0))),
% 3.07/3.30      inference('demod', [status(thm)], ['258', '259'])).
% 3.07/3.30  thf('261', plain,
% 3.07/3.30      ((~ (v1_funct_1 @ sk_C)
% 3.07/3.30        | ((k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)
% 3.07/3.30            = (k5_relat_1 @ sk_D @ sk_C)))),
% 3.07/3.30      inference('sup-', [status(thm)], ['255', '260'])).
% 3.07/3.30  thf('262', plain, ((v1_funct_1 @ sk_C)),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('263', plain,
% 3.07/3.30      (((k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)
% 3.07/3.30         = (k5_relat_1 @ sk_D @ sk_C))),
% 3.07/3.30      inference('demod', [status(thm)], ['261', '262'])).
% 3.07/3.30  thf('264', plain, ((v1_funct_1 @ (k5_relat_1 @ sk_D @ sk_C))),
% 3.07/3.30      inference('demod', [status(thm)], ['254', '263'])).
% 3.07/3.30  thf('265', plain, (((k6_partfun1 @ sk_B) = (k5_relat_1 @ sk_D @ sk_C))),
% 3.07/3.30      inference('demod', [status(thm)], ['165', '166', '167'])).
% 3.07/3.30  thf('266', plain, ((v1_funct_1 @ (k6_partfun1 @ sk_B))),
% 3.07/3.30      inference('demod', [status(thm)], ['264', '265'])).
% 3.07/3.30  thf('267', plain,
% 3.07/3.30      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('268', plain,
% 3.07/3.30      (![X21 : $i]:
% 3.07/3.30         (m1_subset_1 @ (k6_partfun1 @ X21) @ 
% 3.07/3.30          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 3.07/3.30      inference('demod', [status(thm)], ['13', '14'])).
% 3.07/3.30  thf('269', plain,
% 3.07/3.30      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 3.07/3.30         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 3.07/3.30          | ~ (v1_funct_1 @ X22)
% 3.07/3.30          | ~ (v1_funct_1 @ X25)
% 3.07/3.30          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 3.07/3.30          | (m1_subset_1 @ (k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25) @ 
% 3.07/3.30             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X27))))),
% 3.07/3.30      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.07/3.30  thf('270', plain,
% 3.07/3.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.07/3.30         ((m1_subset_1 @ 
% 3.07/3.30           (k1_partfun1 @ X0 @ X0 @ X3 @ X1 @ (k6_partfun1 @ X0) @ X2) @ 
% 3.07/3.30           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 3.07/3.30          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X1)))
% 3.07/3.30          | ~ (v1_funct_1 @ X2)
% 3.07/3.30          | ~ (v1_funct_1 @ (k6_partfun1 @ X0)))),
% 3.07/3.30      inference('sup-', [status(thm)], ['268', '269'])).
% 3.07/3.30  thf('271', plain,
% 3.07/3.30      (![X0 : $i]:
% 3.07/3.30         (~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 3.07/3.30          | ~ (v1_funct_1 @ sk_D)
% 3.07/3.30          | (m1_subset_1 @ 
% 3.07/3.30             (k1_partfun1 @ X0 @ X0 @ sk_B @ sk_A @ (k6_partfun1 @ X0) @ sk_D) @ 
% 3.07/3.30             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A))))),
% 3.07/3.30      inference('sup-', [status(thm)], ['267', '270'])).
% 3.07/3.30  thf('272', plain, ((v1_funct_1 @ sk_D)),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('273', plain,
% 3.07/3.30      (![X0 : $i]:
% 3.07/3.30         (~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 3.07/3.30          | (m1_subset_1 @ 
% 3.07/3.30             (k1_partfun1 @ X0 @ X0 @ sk_B @ sk_A @ (k6_partfun1 @ X0) @ sk_D) @ 
% 3.07/3.30             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A))))),
% 3.07/3.30      inference('demod', [status(thm)], ['271', '272'])).
% 3.07/3.30  thf('274', plain,
% 3.07/3.30      ((m1_subset_1 @ 
% 3.07/3.30        (k1_partfun1 @ sk_B @ sk_B @ sk_B @ sk_A @ (k6_partfun1 @ sk_B) @ sk_D) @ 
% 3.07/3.30        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.07/3.30      inference('sup-', [status(thm)], ['266', '273'])).
% 3.07/3.30  thf('275', plain, ((v1_funct_1 @ (k6_partfun1 @ sk_B))),
% 3.07/3.30      inference('demod', [status(thm)], ['264', '265'])).
% 3.07/3.30  thf('276', plain,
% 3.07/3.30      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('277', plain,
% 3.07/3.30      (![X21 : $i]:
% 3.07/3.30         (m1_subset_1 @ (k6_partfun1 @ X21) @ 
% 3.07/3.30          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 3.07/3.30      inference('demod', [status(thm)], ['13', '14'])).
% 3.07/3.30  thf('278', plain,
% 3.07/3.30      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 3.07/3.30         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 3.07/3.30          | ~ (v1_funct_1 @ X28)
% 3.07/3.30          | ~ (v1_funct_1 @ X31)
% 3.07/3.30          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 3.07/3.30          | ((k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31)
% 3.07/3.30              = (k5_relat_1 @ X28 @ X31)))),
% 3.07/3.30      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 3.07/3.30  thf('279', plain,
% 3.07/3.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.07/3.30         (((k1_partfun1 @ X0 @ X0 @ X3 @ X2 @ (k6_partfun1 @ X0) @ X1)
% 3.07/3.30            = (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 3.07/3.30          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2)))
% 3.07/3.30          | ~ (v1_funct_1 @ X1)
% 3.07/3.30          | ~ (v1_funct_1 @ (k6_partfun1 @ X0)))),
% 3.07/3.30      inference('sup-', [status(thm)], ['277', '278'])).
% 3.07/3.30  thf('280', plain,
% 3.07/3.30      (![X0 : $i]:
% 3.07/3.30         (~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 3.07/3.30          | ~ (v1_funct_1 @ sk_D)
% 3.07/3.30          | ((k1_partfun1 @ X0 @ X0 @ sk_B @ sk_A @ (k6_partfun1 @ X0) @ sk_D)
% 3.07/3.30              = (k5_relat_1 @ (k6_partfun1 @ X0) @ sk_D)))),
% 3.07/3.30      inference('sup-', [status(thm)], ['276', '279'])).
% 3.07/3.30  thf('281', plain, ((v1_funct_1 @ sk_D)),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('282', plain,
% 3.07/3.30      (![X0 : $i]:
% 3.07/3.30         (~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 3.07/3.30          | ((k1_partfun1 @ X0 @ X0 @ sk_B @ sk_A @ (k6_partfun1 @ X0) @ sk_D)
% 3.07/3.30              = (k5_relat_1 @ (k6_partfun1 @ X0) @ sk_D)))),
% 3.07/3.30      inference('demod', [status(thm)], ['280', '281'])).
% 3.07/3.30  thf('283', plain,
% 3.07/3.30      (((k1_partfun1 @ sk_B @ sk_B @ sk_B @ sk_A @ (k6_partfun1 @ sk_B) @ sk_D)
% 3.07/3.30         = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D))),
% 3.07/3.30      inference('sup-', [status(thm)], ['275', '282'])).
% 3.07/3.30  thf('284', plain,
% 3.07/3.30      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (k2_funct_1 @ sk_C))),
% 3.07/3.30      inference('demod', [status(thm)], ['197', '228', '229'])).
% 3.07/3.30  thf('285', plain,
% 3.07/3.30      (((k1_partfun1 @ sk_B @ sk_B @ sk_B @ sk_A @ (k6_partfun1 @ sk_B) @ sk_D)
% 3.07/3.30         = (k2_funct_1 @ sk_C))),
% 3.07/3.30      inference('demod', [status(thm)], ['283', '284'])).
% 3.07/3.30  thf('286', plain,
% 3.07/3.30      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.07/3.30        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.07/3.30      inference('demod', [status(thm)], ['274', '285'])).
% 3.07/3.30  thf('287', plain,
% 3.07/3.30      (![X0 : $i, X1 : $i]:
% 3.07/3.30         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 3.07/3.30          | (v1_relat_1 @ X0)
% 3.07/3.30          | ~ (v1_relat_1 @ X1))),
% 3.07/3.30      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.07/3.30  thf('288', plain,
% 3.07/3.30      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))
% 3.07/3.30        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 3.07/3.30      inference('sup-', [status(thm)], ['286', '287'])).
% 3.07/3.30  thf('289', plain,
% 3.07/3.30      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 3.07/3.30      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.07/3.30  thf('290', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 3.07/3.30      inference('demod', [status(thm)], ['288', '289'])).
% 3.07/3.30  thf('291', plain, (((k2_funct_1 @ sk_C) = (sk_D))),
% 3.07/3.30      inference('demod', [status(thm)],
% 3.07/3.30                ['174', '175', '230', '240', '241', '242', '243', '244', 
% 3.07/3.30                 '245', '290'])).
% 3.07/3.30  thf('292', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 3.07/3.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.07/3.30  thf('293', plain, ($false),
% 3.07/3.30      inference('simplify_reflect-', [status(thm)], ['291', '292'])).
% 3.07/3.30  
% 3.07/3.30  % SZS output end Refutation
% 3.07/3.30  
% 3.07/3.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

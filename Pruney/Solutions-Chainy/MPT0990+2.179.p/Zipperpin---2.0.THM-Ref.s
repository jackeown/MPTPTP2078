%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.avrCzVXNG1

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:25 EST 2020

% Result     : Theorem 2.50s
% Output     : Refutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :  367 (5180 expanded)
%              Number of leaves         :   51 (1532 expanded)
%              Depth                    :   28
%              Number of atoms          : 3487 (130924 expanded)
%              Number of equality atoms :  261 (8783 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

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
    ! [X3: $i,X4: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('4',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['2','3'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X5: $i] :
      ( ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('6',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
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
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ X13 )
        = ( k4_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( ( k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33 )
        = ( k5_relat_1 @ X30 @ X33 ) ) ) ),
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

thf('20',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('23',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
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

thf('26',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('33',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('34',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( X18 = X21 )
      | ~ ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','35'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('37',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('38',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','38'])).

thf('40',plain,(
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

thf('41',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ( zip_tseitin_0 @ X45 @ X48 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X49 @ X46 @ X46 @ X47 @ X48 @ X45 ) )
      | ( zip_tseitin_1 @ X47 @ X46 )
      | ( ( k2_relset_1 @ X49 @ X46 @ X48 )
       != X46 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X46 ) ) )
      | ~ ( v1_funct_2 @ X48 @ X49 @ X46 )
      | ~ ( v1_funct_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('42',plain,(
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
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('47',plain,(
    ! [X16: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('48',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('49',plain,(
    ! [X16: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X16 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['46','49','50','51','52','53'])).

thf('55',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X43: $i,X44: $i] :
      ( ( X43 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('57',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X41: $i,X42: $i] :
      ( ( v2_funct_1 @ X42 )
      | ~ ( zip_tseitin_0 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('61',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k2_funct_1 @ sk_D )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['11','61'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('63',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X17 ) @ X17 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('64',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('65',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X17 ) @ X17 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ sk_D )
      = ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['62','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['2','3'])).

thf('68',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['59','60'])).

thf('70',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ sk_D )
    = ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('71',plain,(
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

thf('72',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( X50 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_2 @ X51 @ X52 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X50 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X51 ) @ X51 )
        = ( k6_partfun1 @ X50 ) )
      | ~ ( v2_funct_1 @ X51 )
      | ( ( k2_relset_1 @ X52 @ X50 @ X51 )
       != X50 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('73',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_D ) @ sk_D )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
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

thf('76',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( r2_relset_1 @ X38 @ X38 @ ( k1_partfun1 @ X38 @ X39 @ X39 @ X38 @ X37 @ X40 ) @ ( k6_partfun1 @ X38 ) )
      | ( ( k2_relset_1 @ X39 @ X38 @ X40 )
        = X38 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X38 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['74','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('86',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_D ) @ sk_D )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','85','86','87'])).

thf('89',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_D ) @ sk_D )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_D ) @ sk_D )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['89','90'])).

thf('92',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['59','60'])).

thf('93',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_D ) @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( k2_funct_1 @ sk_D )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['11','61'])).

thf('95',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('sup+',[status(thm)],['70','95'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('97',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('98',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k5_relat_1 @ X17 @ ( k2_funct_1 @ X17 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('99',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('100',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k5_relat_1 @ X17 @ ( k2_funct_1 @ X17 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('102',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X17 ) @ X17 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('103',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) @ X8 )
        = ( k5_relat_1 @ X7 @ ( k5_relat_1 @ X6 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['101','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['100','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('113',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k5_relat_1 @ X17 @ ( k2_funct_1 @ X17 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('114',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) @ X8 )
        = ( k5_relat_1 @ X7 @ ( k5_relat_1 @ X6 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['112','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['111','118'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('120',plain,(
    ! [X9: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('121',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('122',plain,(
    ! [X9: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X9 ) )
      = X9 ) ),
    inference(demod,[status(thm)],['120','121'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('123',plain,(
    ! [X11: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X11 ) ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('124',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('125',plain,(
    ! [X11: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X11 ) ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['122','125'])).

thf('127',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('128',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('129',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X15 ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['126','129'])).

thf('131',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X15 ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['119','130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k2_funct_1 @ sk_D ) ) )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) @ ( k2_funct_1 @ sk_D ) ) )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_D ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['96','136'])).

thf('138',plain,
    ( ( k2_funct_1 @ sk_D )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['11','61'])).

thf('139',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( X50 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_2 @ X51 @ X52 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X50 ) ) )
      | ( ( k5_relat_1 @ X51 @ ( k2_funct_1 @ X51 ) )
        = ( k6_partfun1 @ X52 ) )
      | ~ ( v2_funct_1 @ X51 )
      | ( ( k2_relset_1 @ X52 @ X50 @ X51 )
       != X50 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('141',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('143',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['141','142','143','144'])).

thf('146',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['146','147'])).

thf('149',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['59','60'])).

thf('150',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,
    ( ( k2_funct_1 @ sk_D )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['11','61'])).

thf('152',plain,
    ( ( k5_relat_1 @ sk_D @ ( k4_relat_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('154',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) @ X8 )
        = ( k5_relat_1 @ X7 @ ( k5_relat_1 @ X6 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['153','154'])).

thf('156',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('158',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X3: $i,X4: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('160',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['2','3'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['155','160','161'])).

thf('163',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k4_relat_1 @ sk_D ) )
      = ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['152','162'])).

thf('164',plain,(
    ! [X11: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X11 ) ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('165',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ X13 )
        = ( k4_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('167',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['158','159'])).

thf('169',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['167','168','169'])).

thf('171',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X17 ) @ X17 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('172',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['170','171'])).

thf('173',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['158','159'])).

thf('174',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['172','173','174','175'])).

thf('177',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['167','168','169'])).

thf('178',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k5_relat_1 @ X17 @ ( k2_funct_1 @ X17 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('179',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['177','178'])).

thf('180',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['158','159'])).

thf('181',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['179','180','181','182'])).

thf('184',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) @ X8 )
        = ( k5_relat_1 @ X7 @ ( k5_relat_1 @ X6 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['183','184'])).

thf('186',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['158','159'])).

thf('187',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['167','168','169'])).

thf('188',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('189',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['187','188'])).

thf('190',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['158','159'])).

thf('191',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['189','190','191'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['185','186','192'])).

thf('194',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ sk_C )
      = ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['176','193'])).

thf('195',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['158','159'])).

thf('196',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ sk_C )
    = ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['194','195'])).

thf('197',plain,
    ( ( sk_C
      = ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['164','196'])).

thf('198',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['158','159'])).

thf('199',plain,
    ( sk_C
    = ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['197','198'])).

thf('200',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( X50 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_2 @ X51 @ X52 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X50 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X51 ) @ X51 )
        = ( k6_partfun1 @ X50 ) )
      | ~ ( v2_funct_1 @ X51 )
      | ( ( k2_relset_1 @ X52 @ X50 @ X51 )
       != X50 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('202',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['167','168','169'])).

thf('206',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['172','173','174','175'])).

thf('207',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,
    ( ( sk_B != sk_B )
    | ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['202','203','204','205','206','207','208'])).

thf('210',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['209'])).

thf('211',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,
    ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['210','211'])).

thf('213',plain,
    ( sk_C
    = ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['199','212'])).

thf('214',plain,
    ( ( k2_funct_1 @ sk_D )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['11','61'])).

thf('215',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('216',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['214','215'])).

thf('217',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['2','3'])).

thf('218',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['216','217','218'])).

thf('220',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k4_relat_1 @ sk_D ) )
    = sk_C ),
    inference(demod,[status(thm)],['163','213','219'])).

thf('221',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['158','159'])).

thf('222',plain,
    ( ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('sup+',[status(thm)],['70','95'])).

thf('223',plain,
    ( ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('sup+',[status(thm)],['70','95'])).

thf('224',plain,
    ( ( k2_funct_1 @ sk_D )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['11','61'])).

thf('225',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k4_relat_1 @ sk_D ) )
    = sk_C ),
    inference(demod,[status(thm)],['163','213','219'])).

thf('226',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ sk_C )
    = ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['194','195'])).

thf('227',plain,
    ( sk_C
    = ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['197','198'])).

thf('228',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['226','227'])).

thf('229',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( X50 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_2 @ X51 @ X52 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X50 ) ) )
      | ( ( k5_relat_1 @ X51 @ ( k2_funct_1 @ X51 ) )
        = ( k6_partfun1 @ X52 ) )
      | ~ ( v2_funct_1 @ X51 )
      | ( ( k2_relset_1 @ X52 @ X50 @ X51 )
       != X50 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('231',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['229','230'])).

thf('232',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['167','168','169'])).

thf('235',plain,
    ( ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['179','180','181','182'])).

thf('236',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,
    ( ( sk_B != sk_B )
    | ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['231','232','233','234','235','236','237'])).

thf('239',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['238'])).

thf('240',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['239','240'])).

thf('242',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['228','241'])).

thf('243',plain,
    ( ( k2_funct_1 @ sk_D )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['11','61'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('244',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('245',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('246',plain,(
    ! [X12: $i] :
      ( ( ( k5_relat_1 @ X12 @ ( k6_relat_1 @ ( k2_relat_1 @ X12 ) ) )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('247',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('248',plain,(
    ! [X12: $i] :
      ( ( ( k5_relat_1 @ X12 @ ( k6_partfun1 @ ( k2_relat_1 @ X12 ) ) )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['246','247'])).

thf('249',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) )
      = ( k4_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['245','248'])).

thf('250',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) )
      = ( k4_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['244','249'])).

thf('251',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['2','3'])).

thf('252',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['250','251'])).

thf('253',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['2','3'])).

thf('254',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['59','60'])).

thf('256',plain,
    ( sk_C
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['137','138','220','221','222','223','224','225','242','243','252','253','254','255'])).

thf('257',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','256'])).

thf('258',plain,
    ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['210','211'])).

thf('259',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X15 ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('260',plain,(
    ! [X5: $i] :
      ( ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('261',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X0 ) )
      = ( k1_relat_1 @ ( k4_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['259','260'])).

thf('262',plain,(
    ! [X10: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('263',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('264',plain,(
    ! [X10: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X10 ) )
      = X10 ) ),
    inference(demod,[status(thm)],['262','263'])).

thf('265',plain,(
    ! [X0: $i] :
      ( X0
      = ( k1_relat_1 @ ( k4_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['261','264'])).

thf('266',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k4_relat_1 @ ( k6_partfun1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['258','265'])).

thf('267',plain,(
    ! [X0: $i] :
      ( X0
      = ( k1_relat_1 @ ( k4_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['261','264'])).

thf('268',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['266','267'])).

thf('269',plain,
    ( ( k1_relat_1 @ sk_D )
    = sk_B ),
    inference(demod,[status(thm)],['257','268'])).

thf('270',plain,(
    ! [X11: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X11 ) ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('271',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['269','270'])).

thf('272',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('273',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('274',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['272','273'])).

thf('275',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['266','267'])).

thf('276',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['167','168','169'])).

thf('277',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['158','159'])).

thf('278',plain,(
    ! [X5: $i] :
      ( ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('279',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['277','278'])).

thf('280',plain,(
    ! [X12: $i] :
      ( ( ( k5_relat_1 @ X12 @ ( k6_partfun1 @ ( k2_relat_1 @ X12 ) ) )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['246','247'])).

thf('281',plain,(
    ! [X11: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X11 ) ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('282',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) @ X8 )
        = ( k5_relat_1 @ X7 @ ( k5_relat_1 @ X6 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('283',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['281','282'])).

thf('284',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X15 ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('285',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['283','284'])).

thf('286',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['285'])).

thf('287',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['280','286'])).

thf('288',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X15 ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('289',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['287','288'])).

thf('290',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['289'])).

thf('291',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['279','290'])).

thf('292',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['158','159'])).

thf('293',plain,(
    ! [X5: $i] :
      ( ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('294',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['292','293'])).

thf('295',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['277','278'])).

thf('296',plain,(
    ! [X11: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X11 ) ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('297',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) @ ( k4_relat_1 @ sk_C ) )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['295','296'])).

thf('298',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['189','190','191'])).

thf('299',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) @ ( k4_relat_1 @ sk_C ) )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['297','298'])).

thf('300',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['189','190','191'])).

thf('301',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['291','294','299','300'])).

thf('302',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['239','240'])).

thf('303',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['301','302'])).

thf('304',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['158','159'])).

thf('305',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('306',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('307',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['2','3'])).

thf('308',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['274','275','276','303','304','305','306','307'])).

thf('309',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['2','3'])).

thf('310',plain,
    ( ( k4_relat_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['271','308','309'])).

thf('311',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('312',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['167','168','169'])).

thf('313',plain,(
    sk_D
 != ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['311','312'])).

thf('314',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['310','313'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.avrCzVXNG1
% 0.12/0.32  % Computer   : n001.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:55:00 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 2.50/2.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.50/2.69  % Solved by: fo/fo7.sh
% 2.50/2.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.50/2.69  % done 2166 iterations in 2.249s
% 2.50/2.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.50/2.69  % SZS output start Refutation
% 2.50/2.69  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.50/2.69  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.50/2.69  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.50/2.69  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.50/2.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.50/2.69  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.50/2.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.50/2.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.50/2.69  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 2.50/2.69  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.50/2.69  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.50/2.69  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.50/2.69  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.50/2.69  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.50/2.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.50/2.69  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 2.50/2.69  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.50/2.69  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.50/2.69  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 2.50/2.69  thf(sk_C_type, type, sk_C: $i).
% 2.50/2.69  thf(sk_D_type, type, sk_D: $i).
% 2.50/2.69  thf(sk_B_type, type, sk_B: $i).
% 2.50/2.69  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.50/2.69  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.50/2.69  thf(sk_A_type, type, sk_A: $i).
% 2.50/2.69  thf(t36_funct_2, conjecture,
% 2.50/2.69    (![A:$i,B:$i,C:$i]:
% 2.50/2.69     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.50/2.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.50/2.69       ( ![D:$i]:
% 2.50/2.69         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.50/2.69             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.50/2.69           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.50/2.69               ( r2_relset_1 @
% 2.50/2.69                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.50/2.69                 ( k6_partfun1 @ A ) ) & 
% 2.50/2.69               ( v2_funct_1 @ C ) ) =>
% 2.50/2.69             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.50/2.69               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 2.50/2.69  thf(zf_stmt_0, negated_conjecture,
% 2.50/2.69    (~( ![A:$i,B:$i,C:$i]:
% 2.50/2.69        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.50/2.69            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.50/2.69          ( ![D:$i]:
% 2.50/2.69            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.50/2.69                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.50/2.69              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.50/2.69                  ( r2_relset_1 @
% 2.50/2.69                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.50/2.69                    ( k6_partfun1 @ A ) ) & 
% 2.50/2.69                  ( v2_funct_1 @ C ) ) =>
% 2.50/2.69                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.50/2.69                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 2.50/2.69    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 2.50/2.69  thf('0', plain,
% 2.50/2.69      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.50/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.69  thf(cc2_relat_1, axiom,
% 2.50/2.69    (![A:$i]:
% 2.50/2.69     ( ( v1_relat_1 @ A ) =>
% 2.50/2.69       ( ![B:$i]:
% 2.50/2.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.50/2.69  thf('1', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i]:
% 2.50/2.69         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 2.50/2.69          | (v1_relat_1 @ X0)
% 2.50/2.69          | ~ (v1_relat_1 @ X1))),
% 2.50/2.69      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.50/2.69  thf('2', plain,
% 2.50/2.69      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 2.50/2.69      inference('sup-', [status(thm)], ['0', '1'])).
% 2.50/2.69  thf(fc6_relat_1, axiom,
% 2.50/2.69    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.50/2.69  thf('3', plain,
% 2.50/2.69      (![X3 : $i, X4 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X3 @ X4))),
% 2.50/2.69      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.50/2.69  thf('4', plain, ((v1_relat_1 @ sk_D)),
% 2.50/2.69      inference('demod', [status(thm)], ['2', '3'])).
% 2.50/2.69  thf(t37_relat_1, axiom,
% 2.50/2.69    (![A:$i]:
% 2.50/2.69     ( ( v1_relat_1 @ A ) =>
% 2.50/2.69       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 2.50/2.69         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 2.50/2.69  thf('5', plain,
% 2.50/2.69      (![X5 : $i]:
% 2.50/2.69         (((k1_relat_1 @ X5) = (k2_relat_1 @ (k4_relat_1 @ X5)))
% 2.50/2.69          | ~ (v1_relat_1 @ X5))),
% 2.50/2.69      inference('cnf', [status(esa)], [t37_relat_1])).
% 2.50/2.69  thf('6', plain, (((k1_relat_1 @ sk_D) = (k2_relat_1 @ (k4_relat_1 @ sk_D)))),
% 2.50/2.69      inference('sup-', [status(thm)], ['4', '5'])).
% 2.50/2.69  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 2.50/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.69  thf(d9_funct_1, axiom,
% 2.50/2.69    (![A:$i]:
% 2.50/2.69     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.50/2.69       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 2.50/2.69  thf('8', plain,
% 2.50/2.69      (![X13 : $i]:
% 2.50/2.69         (~ (v2_funct_1 @ X13)
% 2.50/2.69          | ((k2_funct_1 @ X13) = (k4_relat_1 @ X13))
% 2.50/2.69          | ~ (v1_funct_1 @ X13)
% 2.50/2.69          | ~ (v1_relat_1 @ X13))),
% 2.50/2.69      inference('cnf', [status(esa)], [d9_funct_1])).
% 2.50/2.69  thf('9', plain,
% 2.50/2.69      ((~ (v1_relat_1 @ sk_D)
% 2.50/2.69        | ((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))
% 2.50/2.69        | ~ (v2_funct_1 @ sk_D))),
% 2.50/2.69      inference('sup-', [status(thm)], ['7', '8'])).
% 2.50/2.69  thf('10', plain, ((v1_relat_1 @ sk_D)),
% 2.50/2.69      inference('demod', [status(thm)], ['2', '3'])).
% 2.50/2.69  thf('11', plain,
% 2.50/2.69      ((((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 2.50/2.69      inference('demod', [status(thm)], ['9', '10'])).
% 2.50/2.69  thf('12', plain,
% 2.50/2.69      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.50/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.69  thf('13', plain,
% 2.50/2.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.50/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.69  thf(redefinition_k1_partfun1, axiom,
% 2.50/2.69    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.50/2.69     ( ( ( v1_funct_1 @ E ) & 
% 2.50/2.69         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.50/2.69         ( v1_funct_1 @ F ) & 
% 2.50/2.69         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.50/2.69       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.50/2.69  thf('14', plain,
% 2.50/2.69      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 2.50/2.69         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 2.50/2.69          | ~ (v1_funct_1 @ X30)
% 2.50/2.69          | ~ (v1_funct_1 @ X33)
% 2.50/2.69          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 2.50/2.69          | ((k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33)
% 2.50/2.69              = (k5_relat_1 @ X30 @ X33)))),
% 2.50/2.69      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 2.50/2.69  thf('15', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.50/2.69         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.50/2.69            = (k5_relat_1 @ sk_C @ X0))
% 2.50/2.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.50/2.69          | ~ (v1_funct_1 @ X0)
% 2.50/2.69          | ~ (v1_funct_1 @ sk_C))),
% 2.50/2.69      inference('sup-', [status(thm)], ['13', '14'])).
% 2.50/2.69  thf('16', plain, ((v1_funct_1 @ sk_C)),
% 2.50/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.69  thf('17', plain,
% 2.50/2.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.50/2.69         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.50/2.69            = (k5_relat_1 @ sk_C @ X0))
% 2.50/2.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.50/2.69          | ~ (v1_funct_1 @ X0))),
% 2.50/2.69      inference('demod', [status(thm)], ['15', '16'])).
% 2.50/2.69  thf('18', plain,
% 2.50/2.69      ((~ (v1_funct_1 @ sk_D)
% 2.50/2.69        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.50/2.69            = (k5_relat_1 @ sk_C @ sk_D)))),
% 2.50/2.69      inference('sup-', [status(thm)], ['12', '17'])).
% 2.50/2.69  thf('19', plain, ((v1_funct_1 @ sk_D)),
% 2.50/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.69  thf('20', plain,
% 2.50/2.69      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.50/2.69         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.50/2.69      inference('demod', [status(thm)], ['18', '19'])).
% 2.50/2.69  thf('21', plain,
% 2.50/2.69      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.50/2.69        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.50/2.69        (k6_partfun1 @ sk_A))),
% 2.50/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.69  thf('22', plain,
% 2.50/2.69      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.50/2.69         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.50/2.69      inference('demod', [status(thm)], ['18', '19'])).
% 2.50/2.69  thf('23', plain,
% 2.50/2.69      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 2.50/2.69        (k6_partfun1 @ sk_A))),
% 2.50/2.69      inference('demod', [status(thm)], ['21', '22'])).
% 2.50/2.69  thf('24', plain,
% 2.50/2.69      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.50/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.69  thf('25', plain,
% 2.50/2.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.50/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.69  thf(dt_k1_partfun1, axiom,
% 2.50/2.69    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.50/2.69     ( ( ( v1_funct_1 @ E ) & 
% 2.50/2.69         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.50/2.69         ( v1_funct_1 @ F ) & 
% 2.50/2.69         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.50/2.69       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.50/2.69         ( m1_subset_1 @
% 2.50/2.69           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.50/2.69           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.50/2.69  thf('26', plain,
% 2.50/2.69      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 2.50/2.69         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 2.50/2.70          | ~ (v1_funct_1 @ X22)
% 2.50/2.70          | ~ (v1_funct_1 @ X25)
% 2.50/2.70          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 2.50/2.70          | (m1_subset_1 @ (k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25) @ 
% 2.50/2.70             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X27))))),
% 2.50/2.70      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.50/2.70  thf('27', plain,
% 2.50/2.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.50/2.70         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.50/2.70           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.50/2.70          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.50/2.70          | ~ (v1_funct_1 @ X1)
% 2.50/2.70          | ~ (v1_funct_1 @ sk_C))),
% 2.50/2.70      inference('sup-', [status(thm)], ['25', '26'])).
% 2.50/2.70  thf('28', plain, ((v1_funct_1 @ sk_C)),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('29', plain,
% 2.50/2.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.50/2.70         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.50/2.70           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.50/2.70          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.50/2.70          | ~ (v1_funct_1 @ X1))),
% 2.50/2.70      inference('demod', [status(thm)], ['27', '28'])).
% 2.50/2.70  thf('30', plain,
% 2.50/2.70      ((~ (v1_funct_1 @ sk_D)
% 2.50/2.70        | (m1_subset_1 @ 
% 2.50/2.70           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.50/2.70           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.50/2.70      inference('sup-', [status(thm)], ['24', '29'])).
% 2.50/2.70  thf('31', plain, ((v1_funct_1 @ sk_D)),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('32', plain,
% 2.50/2.70      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.50/2.70         = (k5_relat_1 @ sk_C @ sk_D))),
% 2.50/2.70      inference('demod', [status(thm)], ['18', '19'])).
% 2.50/2.70  thf('33', plain,
% 2.50/2.70      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 2.50/2.70        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.50/2.70      inference('demod', [status(thm)], ['30', '31', '32'])).
% 2.50/2.70  thf(redefinition_r2_relset_1, axiom,
% 2.50/2.70    (![A:$i,B:$i,C:$i,D:$i]:
% 2.50/2.70     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.50/2.70         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.50/2.70       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.50/2.70  thf('34', plain,
% 2.50/2.70      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 2.50/2.70         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 2.50/2.70          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 2.50/2.70          | ((X18) = (X21))
% 2.50/2.70          | ~ (r2_relset_1 @ X19 @ X20 @ X18 @ X21))),
% 2.50/2.70      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.50/2.70  thf('35', plain,
% 2.50/2.70      (![X0 : $i]:
% 2.50/2.70         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 2.50/2.70          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 2.50/2.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.50/2.70      inference('sup-', [status(thm)], ['33', '34'])).
% 2.50/2.70  thf('36', plain,
% 2.50/2.70      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 2.50/2.70           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.50/2.70        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 2.50/2.70      inference('sup-', [status(thm)], ['23', '35'])).
% 2.50/2.70  thf(dt_k6_partfun1, axiom,
% 2.50/2.70    (![A:$i]:
% 2.50/2.70     ( ( m1_subset_1 @
% 2.50/2.70         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 2.50/2.70       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 2.50/2.70  thf('37', plain,
% 2.50/2.70      (![X29 : $i]:
% 2.50/2.70         (m1_subset_1 @ (k6_partfun1 @ X29) @ 
% 2.50/2.70          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 2.50/2.70      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 2.50/2.70  thf('38', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 2.50/2.70      inference('demod', [status(thm)], ['36', '37'])).
% 2.50/2.70  thf('39', plain,
% 2.50/2.70      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.50/2.70         = (k6_partfun1 @ sk_A))),
% 2.50/2.70      inference('demod', [status(thm)], ['20', '38'])).
% 2.50/2.70  thf('40', plain,
% 2.50/2.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf(t30_funct_2, axiom,
% 2.50/2.70    (![A:$i,B:$i,C:$i,D:$i]:
% 2.50/2.70     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.50/2.70         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 2.50/2.70       ( ![E:$i]:
% 2.50/2.70         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 2.50/2.70             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 2.50/2.70           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 2.50/2.70               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 2.50/2.70             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 2.50/2.70               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 2.50/2.70  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 2.50/2.70  thf(zf_stmt_2, axiom,
% 2.50/2.70    (![C:$i,B:$i]:
% 2.50/2.70     ( ( zip_tseitin_1 @ C @ B ) =>
% 2.50/2.70       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 2.50/2.70  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 2.50/2.70  thf(zf_stmt_4, axiom,
% 2.50/2.70    (![E:$i,D:$i]:
% 2.50/2.70     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 2.50/2.70  thf(zf_stmt_5, axiom,
% 2.50/2.70    (![A:$i,B:$i,C:$i,D:$i]:
% 2.50/2.70     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.50/2.70         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.50/2.70       ( ![E:$i]:
% 2.50/2.70         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.50/2.70             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.50/2.70           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 2.50/2.70               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 2.50/2.70             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 2.50/2.70  thf('41', plain,
% 2.50/2.70      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 2.50/2.70         (~ (v1_funct_1 @ X45)
% 2.50/2.70          | ~ (v1_funct_2 @ X45 @ X46 @ X47)
% 2.50/2.70          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 2.50/2.70          | (zip_tseitin_0 @ X45 @ X48)
% 2.50/2.70          | ~ (v2_funct_1 @ (k1_partfun1 @ X49 @ X46 @ X46 @ X47 @ X48 @ X45))
% 2.50/2.70          | (zip_tseitin_1 @ X47 @ X46)
% 2.50/2.70          | ((k2_relset_1 @ X49 @ X46 @ X48) != (X46))
% 2.50/2.70          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X46)))
% 2.50/2.70          | ~ (v1_funct_2 @ X48 @ X49 @ X46)
% 2.50/2.70          | ~ (v1_funct_1 @ X48))),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.50/2.70  thf('42', plain,
% 2.50/2.70      (![X0 : $i, X1 : $i]:
% 2.50/2.70         (~ (v1_funct_1 @ X0)
% 2.50/2.70          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.50/2.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.50/2.70          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 2.50/2.70          | (zip_tseitin_1 @ sk_A @ sk_B)
% 2.50/2.70          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 2.50/2.70          | (zip_tseitin_0 @ sk_D @ X0)
% 2.50/2.70          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.50/2.70          | ~ (v1_funct_1 @ sk_D))),
% 2.50/2.70      inference('sup-', [status(thm)], ['40', '41'])).
% 2.50/2.70  thf('43', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('44', plain, ((v1_funct_1 @ sk_D)),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('45', plain,
% 2.50/2.70      (![X0 : $i, X1 : $i]:
% 2.50/2.70         (~ (v1_funct_1 @ X0)
% 2.50/2.70          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.50/2.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.50/2.70          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 2.50/2.70          | (zip_tseitin_1 @ sk_A @ sk_B)
% 2.50/2.70          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 2.50/2.70          | (zip_tseitin_0 @ sk_D @ X0))),
% 2.50/2.70      inference('demod', [status(thm)], ['42', '43', '44'])).
% 2.50/2.70  thf('46', plain,
% 2.50/2.70      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 2.50/2.70        | (zip_tseitin_0 @ sk_D @ sk_C)
% 2.50/2.70        | (zip_tseitin_1 @ sk_A @ sk_B)
% 2.50/2.70        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 2.50/2.70        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 2.50/2.70        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.50/2.70        | ~ (v1_funct_1 @ sk_C))),
% 2.50/2.70      inference('sup-', [status(thm)], ['39', '45'])).
% 2.50/2.70  thf(fc4_funct_1, axiom,
% 2.50/2.70    (![A:$i]:
% 2.50/2.70     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 2.50/2.70       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 2.50/2.70  thf('47', plain, (![X16 : $i]: (v2_funct_1 @ (k6_relat_1 @ X16))),
% 2.50/2.70      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.50/2.70  thf(redefinition_k6_partfun1, axiom,
% 2.50/2.70    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.50/2.70  thf('48', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 2.50/2.70      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.50/2.70  thf('49', plain, (![X16 : $i]: (v2_funct_1 @ (k6_partfun1 @ X16))),
% 2.50/2.70      inference('demod', [status(thm)], ['47', '48'])).
% 2.50/2.70  thf('50', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('51', plain,
% 2.50/2.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('52', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('53', plain, ((v1_funct_1 @ sk_C)),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('54', plain,
% 2.50/2.70      (((zip_tseitin_0 @ sk_D @ sk_C)
% 2.50/2.70        | (zip_tseitin_1 @ sk_A @ sk_B)
% 2.50/2.70        | ((sk_B) != (sk_B)))),
% 2.50/2.70      inference('demod', [status(thm)], ['46', '49', '50', '51', '52', '53'])).
% 2.50/2.70  thf('55', plain,
% 2.50/2.70      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 2.50/2.70      inference('simplify', [status(thm)], ['54'])).
% 2.50/2.70  thf('56', plain,
% 2.50/2.70      (![X43 : $i, X44 : $i]:
% 2.50/2.70         (((X43) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X43 @ X44))),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.50/2.70  thf('57', plain,
% 2.50/2.70      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 2.50/2.70      inference('sup-', [status(thm)], ['55', '56'])).
% 2.50/2.70  thf('58', plain, (((sk_A) != (k1_xboole_0))),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('59', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 2.50/2.70      inference('simplify_reflect-', [status(thm)], ['57', '58'])).
% 2.50/2.70  thf('60', plain,
% 2.50/2.70      (![X41 : $i, X42 : $i]:
% 2.50/2.70         ((v2_funct_1 @ X42) | ~ (zip_tseitin_0 @ X42 @ X41))),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_4])).
% 2.50/2.70  thf('61', plain, ((v2_funct_1 @ sk_D)),
% 2.50/2.70      inference('sup-', [status(thm)], ['59', '60'])).
% 2.50/2.70  thf('62', plain, (((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))),
% 2.50/2.70      inference('demod', [status(thm)], ['11', '61'])).
% 2.50/2.70  thf(t61_funct_1, axiom,
% 2.50/2.70    (![A:$i]:
% 2.50/2.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.50/2.70       ( ( v2_funct_1 @ A ) =>
% 2.50/2.70         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 2.50/2.70             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 2.50/2.70           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 2.50/2.70             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 2.50/2.70  thf('63', plain,
% 2.50/2.70      (![X17 : $i]:
% 2.50/2.70         (~ (v2_funct_1 @ X17)
% 2.50/2.70          | ((k5_relat_1 @ (k2_funct_1 @ X17) @ X17)
% 2.50/2.70              = (k6_relat_1 @ (k2_relat_1 @ X17)))
% 2.50/2.70          | ~ (v1_funct_1 @ X17)
% 2.50/2.70          | ~ (v1_relat_1 @ X17))),
% 2.50/2.70      inference('cnf', [status(esa)], [t61_funct_1])).
% 2.50/2.70  thf('64', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 2.50/2.70      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.50/2.70  thf('65', plain,
% 2.50/2.70      (![X17 : $i]:
% 2.50/2.70         (~ (v2_funct_1 @ X17)
% 2.50/2.70          | ((k5_relat_1 @ (k2_funct_1 @ X17) @ X17)
% 2.50/2.70              = (k6_partfun1 @ (k2_relat_1 @ X17)))
% 2.50/2.70          | ~ (v1_funct_1 @ X17)
% 2.50/2.70          | ~ (v1_relat_1 @ X17))),
% 2.50/2.70      inference('demod', [status(thm)], ['63', '64'])).
% 2.50/2.70  thf('66', plain,
% 2.50/2.70      ((((k5_relat_1 @ (k4_relat_1 @ sk_D) @ sk_D)
% 2.50/2.70          = (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 2.50/2.70        | ~ (v1_relat_1 @ sk_D)
% 2.50/2.70        | ~ (v1_funct_1 @ sk_D)
% 2.50/2.70        | ~ (v2_funct_1 @ sk_D))),
% 2.50/2.70      inference('sup+', [status(thm)], ['62', '65'])).
% 2.50/2.70  thf('67', plain, ((v1_relat_1 @ sk_D)),
% 2.50/2.70      inference('demod', [status(thm)], ['2', '3'])).
% 2.50/2.70  thf('68', plain, ((v1_funct_1 @ sk_D)),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('69', plain, ((v2_funct_1 @ sk_D)),
% 2.50/2.70      inference('sup-', [status(thm)], ['59', '60'])).
% 2.50/2.70  thf('70', plain,
% 2.50/2.70      (((k5_relat_1 @ (k4_relat_1 @ sk_D) @ sk_D)
% 2.50/2.70         = (k6_partfun1 @ (k2_relat_1 @ sk_D)))),
% 2.50/2.70      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 2.50/2.70  thf('71', plain,
% 2.50/2.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf(t35_funct_2, axiom,
% 2.50/2.70    (![A:$i,B:$i,C:$i]:
% 2.50/2.70     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.50/2.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.50/2.70       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 2.50/2.70         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.50/2.70           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 2.50/2.70             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 2.50/2.70  thf('72', plain,
% 2.50/2.70      (![X50 : $i, X51 : $i, X52 : $i]:
% 2.50/2.70         (((X50) = (k1_xboole_0))
% 2.50/2.70          | ~ (v1_funct_1 @ X51)
% 2.50/2.70          | ~ (v1_funct_2 @ X51 @ X52 @ X50)
% 2.50/2.70          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 2.50/2.70          | ((k5_relat_1 @ (k2_funct_1 @ X51) @ X51) = (k6_partfun1 @ X50))
% 2.50/2.70          | ~ (v2_funct_1 @ X51)
% 2.50/2.70          | ((k2_relset_1 @ X52 @ X50 @ X51) != (X50)))),
% 2.50/2.70      inference('cnf', [status(esa)], [t35_funct_2])).
% 2.50/2.70  thf('73', plain,
% 2.50/2.70      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 2.50/2.70        | ~ (v2_funct_1 @ sk_D)
% 2.50/2.70        | ((k5_relat_1 @ (k2_funct_1 @ sk_D) @ sk_D) = (k6_partfun1 @ sk_A))
% 2.50/2.70        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.50/2.70        | ~ (v1_funct_1 @ sk_D)
% 2.50/2.70        | ((sk_A) = (k1_xboole_0)))),
% 2.50/2.70      inference('sup-', [status(thm)], ['71', '72'])).
% 2.50/2.70  thf('74', plain,
% 2.50/2.70      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.50/2.70        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.50/2.70        (k6_partfun1 @ sk_A))),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('75', plain,
% 2.50/2.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf(t24_funct_2, axiom,
% 2.50/2.70    (![A:$i,B:$i,C:$i]:
% 2.50/2.70     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.50/2.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.50/2.70       ( ![D:$i]:
% 2.50/2.70         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.50/2.70             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.50/2.70           ( ( r2_relset_1 @
% 2.50/2.70               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 2.50/2.70               ( k6_partfun1 @ B ) ) =>
% 2.50/2.70             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 2.50/2.70  thf('76', plain,
% 2.50/2.70      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 2.50/2.70         (~ (v1_funct_1 @ X37)
% 2.50/2.70          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 2.50/2.70          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 2.50/2.70          | ~ (r2_relset_1 @ X38 @ X38 @ 
% 2.50/2.70               (k1_partfun1 @ X38 @ X39 @ X39 @ X38 @ X37 @ X40) @ 
% 2.50/2.70               (k6_partfun1 @ X38))
% 2.50/2.70          | ((k2_relset_1 @ X39 @ X38 @ X40) = (X38))
% 2.50/2.70          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 2.50/2.70          | ~ (v1_funct_2 @ X40 @ X39 @ X38)
% 2.50/2.70          | ~ (v1_funct_1 @ X40))),
% 2.50/2.70      inference('cnf', [status(esa)], [t24_funct_2])).
% 2.50/2.70  thf('77', plain,
% 2.50/2.70      (![X0 : $i]:
% 2.50/2.70         (~ (v1_funct_1 @ X0)
% 2.50/2.70          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.50/2.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.50/2.70          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.50/2.70          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.50/2.70               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.50/2.70               (k6_partfun1 @ sk_A))
% 2.50/2.70          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.50/2.70          | ~ (v1_funct_1 @ sk_C))),
% 2.50/2.70      inference('sup-', [status(thm)], ['75', '76'])).
% 2.50/2.70  thf('78', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('79', plain, ((v1_funct_1 @ sk_C)),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('80', plain,
% 2.50/2.70      (![X0 : $i]:
% 2.50/2.70         (~ (v1_funct_1 @ X0)
% 2.50/2.70          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.50/2.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.50/2.70          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.50/2.70          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.50/2.70               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.50/2.70               (k6_partfun1 @ sk_A)))),
% 2.50/2.70      inference('demod', [status(thm)], ['77', '78', '79'])).
% 2.50/2.70  thf('81', plain,
% 2.50/2.70      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 2.50/2.70        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.50/2.70        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.50/2.70        | ~ (v1_funct_1 @ sk_D))),
% 2.50/2.70      inference('sup-', [status(thm)], ['74', '80'])).
% 2.50/2.70  thf('82', plain,
% 2.50/2.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('83', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('84', plain, ((v1_funct_1 @ sk_D)),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('85', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))),
% 2.50/2.70      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 2.50/2.70  thf('86', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('87', plain, ((v1_funct_1 @ sk_D)),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('88', plain,
% 2.50/2.70      ((((sk_A) != (sk_A))
% 2.50/2.70        | ~ (v2_funct_1 @ sk_D)
% 2.50/2.70        | ((k5_relat_1 @ (k2_funct_1 @ sk_D) @ sk_D) = (k6_partfun1 @ sk_A))
% 2.50/2.70        | ((sk_A) = (k1_xboole_0)))),
% 2.50/2.70      inference('demod', [status(thm)], ['73', '85', '86', '87'])).
% 2.50/2.70  thf('89', plain,
% 2.50/2.70      ((((sk_A) = (k1_xboole_0))
% 2.50/2.70        | ((k5_relat_1 @ (k2_funct_1 @ sk_D) @ sk_D) = (k6_partfun1 @ sk_A))
% 2.50/2.70        | ~ (v2_funct_1 @ sk_D))),
% 2.50/2.70      inference('simplify', [status(thm)], ['88'])).
% 2.50/2.70  thf('90', plain, (((sk_A) != (k1_xboole_0))),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('91', plain,
% 2.50/2.70      ((((k5_relat_1 @ (k2_funct_1 @ sk_D) @ sk_D) = (k6_partfun1 @ sk_A))
% 2.50/2.70        | ~ (v2_funct_1 @ sk_D))),
% 2.50/2.70      inference('simplify_reflect-', [status(thm)], ['89', '90'])).
% 2.50/2.70  thf('92', plain, ((v2_funct_1 @ sk_D)),
% 2.50/2.70      inference('sup-', [status(thm)], ['59', '60'])).
% 2.50/2.70  thf('93', plain,
% 2.50/2.70      (((k5_relat_1 @ (k2_funct_1 @ sk_D) @ sk_D) = (k6_partfun1 @ sk_A))),
% 2.50/2.70      inference('demod', [status(thm)], ['91', '92'])).
% 2.50/2.70  thf('94', plain, (((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))),
% 2.50/2.70      inference('demod', [status(thm)], ['11', '61'])).
% 2.50/2.70  thf('95', plain,
% 2.50/2.70      (((k5_relat_1 @ (k4_relat_1 @ sk_D) @ sk_D) = (k6_partfun1 @ sk_A))),
% 2.50/2.70      inference('demod', [status(thm)], ['93', '94'])).
% 2.50/2.70  thf('96', plain,
% 2.50/2.70      (((k6_partfun1 @ (k2_relat_1 @ sk_D)) = (k6_partfun1 @ sk_A))),
% 2.50/2.70      inference('sup+', [status(thm)], ['70', '95'])).
% 2.50/2.70  thf(dt_k2_funct_1, axiom,
% 2.50/2.70    (![A:$i]:
% 2.50/2.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.50/2.70       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 2.50/2.70         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 2.50/2.70  thf('97', plain,
% 2.50/2.70      (![X14 : $i]:
% 2.50/2.70         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 2.50/2.70          | ~ (v1_funct_1 @ X14)
% 2.50/2.70          | ~ (v1_relat_1 @ X14))),
% 2.50/2.70      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.50/2.70  thf('98', plain,
% 2.50/2.70      (![X17 : $i]:
% 2.50/2.70         (~ (v2_funct_1 @ X17)
% 2.50/2.70          | ((k5_relat_1 @ X17 @ (k2_funct_1 @ X17))
% 2.50/2.70              = (k6_relat_1 @ (k1_relat_1 @ X17)))
% 2.50/2.70          | ~ (v1_funct_1 @ X17)
% 2.50/2.70          | ~ (v1_relat_1 @ X17))),
% 2.50/2.70      inference('cnf', [status(esa)], [t61_funct_1])).
% 2.50/2.70  thf('99', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 2.50/2.70      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.50/2.70  thf('100', plain,
% 2.50/2.70      (![X17 : $i]:
% 2.50/2.70         (~ (v2_funct_1 @ X17)
% 2.50/2.70          | ((k5_relat_1 @ X17 @ (k2_funct_1 @ X17))
% 2.50/2.70              = (k6_partfun1 @ (k1_relat_1 @ X17)))
% 2.50/2.70          | ~ (v1_funct_1 @ X17)
% 2.50/2.70          | ~ (v1_relat_1 @ X17))),
% 2.50/2.70      inference('demod', [status(thm)], ['98', '99'])).
% 2.50/2.70  thf('101', plain,
% 2.50/2.70      (![X14 : $i]:
% 2.50/2.70         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 2.50/2.70          | ~ (v1_funct_1 @ X14)
% 2.50/2.70          | ~ (v1_relat_1 @ X14))),
% 2.50/2.70      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.50/2.70  thf('102', plain,
% 2.50/2.70      (![X17 : $i]:
% 2.50/2.70         (~ (v2_funct_1 @ X17)
% 2.50/2.70          | ((k5_relat_1 @ (k2_funct_1 @ X17) @ X17)
% 2.50/2.70              = (k6_partfun1 @ (k2_relat_1 @ X17)))
% 2.50/2.70          | ~ (v1_funct_1 @ X17)
% 2.50/2.70          | ~ (v1_relat_1 @ X17))),
% 2.50/2.70      inference('demod', [status(thm)], ['63', '64'])).
% 2.50/2.70  thf(t55_relat_1, axiom,
% 2.50/2.70    (![A:$i]:
% 2.50/2.70     ( ( v1_relat_1 @ A ) =>
% 2.50/2.70       ( ![B:$i]:
% 2.50/2.70         ( ( v1_relat_1 @ B ) =>
% 2.50/2.70           ( ![C:$i]:
% 2.50/2.70             ( ( v1_relat_1 @ C ) =>
% 2.50/2.70               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 2.50/2.70                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 2.50/2.70  thf('103', plain,
% 2.50/2.70      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.50/2.70         (~ (v1_relat_1 @ X6)
% 2.50/2.70          | ((k5_relat_1 @ (k5_relat_1 @ X7 @ X6) @ X8)
% 2.50/2.70              = (k5_relat_1 @ X7 @ (k5_relat_1 @ X6 @ X8)))
% 2.50/2.70          | ~ (v1_relat_1 @ X8)
% 2.50/2.70          | ~ (v1_relat_1 @ X7))),
% 2.50/2.70      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.50/2.70  thf('104', plain,
% 2.50/2.70      (![X0 : $i, X1 : $i]:
% 2.50/2.70         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 2.50/2.70            = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 2.50/2.70          | ~ (v1_relat_1 @ X0)
% 2.50/2.70          | ~ (v1_funct_1 @ X0)
% 2.50/2.70          | ~ (v2_funct_1 @ X0)
% 2.50/2.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.50/2.70          | ~ (v1_relat_1 @ X1)
% 2.50/2.70          | ~ (v1_relat_1 @ X0))),
% 2.50/2.70      inference('sup+', [status(thm)], ['102', '103'])).
% 2.50/2.70  thf('105', plain,
% 2.50/2.70      (![X0 : $i, X1 : $i]:
% 2.50/2.70         (~ (v1_relat_1 @ X1)
% 2.50/2.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.50/2.70          | ~ (v2_funct_1 @ X0)
% 2.50/2.70          | ~ (v1_funct_1 @ X0)
% 2.50/2.70          | ~ (v1_relat_1 @ X0)
% 2.50/2.70          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 2.50/2.70              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1))))),
% 2.50/2.70      inference('simplify', [status(thm)], ['104'])).
% 2.50/2.70  thf('106', plain,
% 2.50/2.70      (![X0 : $i, X1 : $i]:
% 2.50/2.70         (~ (v1_relat_1 @ X0)
% 2.50/2.70          | ~ (v1_funct_1 @ X0)
% 2.50/2.70          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 2.50/2.70              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 2.50/2.70          | ~ (v1_relat_1 @ X0)
% 2.50/2.70          | ~ (v1_funct_1 @ X0)
% 2.50/2.70          | ~ (v2_funct_1 @ X0)
% 2.50/2.70          | ~ (v1_relat_1 @ X1))),
% 2.50/2.70      inference('sup-', [status(thm)], ['101', '105'])).
% 2.50/2.70  thf('107', plain,
% 2.50/2.70      (![X0 : $i, X1 : $i]:
% 2.50/2.70         (~ (v1_relat_1 @ X1)
% 2.50/2.70          | ~ (v2_funct_1 @ X0)
% 2.50/2.70          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 2.50/2.70              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 2.50/2.70          | ~ (v1_funct_1 @ X0)
% 2.50/2.70          | ~ (v1_relat_1 @ X0))),
% 2.50/2.70      inference('simplify', [status(thm)], ['106'])).
% 2.50/2.70  thf('108', plain,
% 2.50/2.70      (![X0 : $i]:
% 2.50/2.70         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 2.50/2.70            = (k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 2.50/2.70               (k6_partfun1 @ (k1_relat_1 @ X0))))
% 2.50/2.70          | ~ (v1_relat_1 @ X0)
% 2.50/2.70          | ~ (v1_funct_1 @ X0)
% 2.50/2.70          | ~ (v2_funct_1 @ X0)
% 2.50/2.70          | ~ (v1_relat_1 @ X0)
% 2.50/2.70          | ~ (v1_funct_1 @ X0)
% 2.50/2.70          | ~ (v2_funct_1 @ X0)
% 2.50/2.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 2.50/2.70      inference('sup+', [status(thm)], ['100', '107'])).
% 2.50/2.70  thf('109', plain,
% 2.50/2.70      (![X0 : $i]:
% 2.50/2.70         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.50/2.70          | ~ (v2_funct_1 @ X0)
% 2.50/2.70          | ~ (v1_funct_1 @ X0)
% 2.50/2.70          | ~ (v1_relat_1 @ X0)
% 2.50/2.70          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 2.50/2.70              (k2_funct_1 @ X0))
% 2.50/2.70              = (k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 2.50/2.70                 (k6_partfun1 @ (k1_relat_1 @ X0)))))),
% 2.50/2.70      inference('simplify', [status(thm)], ['108'])).
% 2.50/2.70  thf('110', plain,
% 2.50/2.70      (![X0 : $i]:
% 2.50/2.70         (~ (v1_relat_1 @ X0)
% 2.50/2.70          | ~ (v1_funct_1 @ X0)
% 2.50/2.70          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 2.50/2.70              (k2_funct_1 @ X0))
% 2.50/2.70              = (k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 2.50/2.70                 (k6_partfun1 @ (k1_relat_1 @ X0))))
% 2.50/2.70          | ~ (v1_relat_1 @ X0)
% 2.50/2.70          | ~ (v1_funct_1 @ X0)
% 2.50/2.70          | ~ (v2_funct_1 @ X0))),
% 2.50/2.70      inference('sup-', [status(thm)], ['97', '109'])).
% 2.50/2.70  thf('111', plain,
% 2.50/2.70      (![X0 : $i]:
% 2.50/2.70         (~ (v2_funct_1 @ X0)
% 2.50/2.70          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 2.50/2.70              (k2_funct_1 @ X0))
% 2.50/2.70              = (k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 2.50/2.70                 (k6_partfun1 @ (k1_relat_1 @ X0))))
% 2.50/2.70          | ~ (v1_funct_1 @ X0)
% 2.50/2.70          | ~ (v1_relat_1 @ X0))),
% 2.50/2.70      inference('simplify', [status(thm)], ['110'])).
% 2.50/2.70  thf('112', plain,
% 2.50/2.70      (![X14 : $i]:
% 2.50/2.70         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 2.50/2.70          | ~ (v1_funct_1 @ X14)
% 2.50/2.70          | ~ (v1_relat_1 @ X14))),
% 2.50/2.70      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.50/2.70  thf('113', plain,
% 2.50/2.70      (![X17 : $i]:
% 2.50/2.70         (~ (v2_funct_1 @ X17)
% 2.50/2.70          | ((k5_relat_1 @ X17 @ (k2_funct_1 @ X17))
% 2.50/2.70              = (k6_partfun1 @ (k1_relat_1 @ X17)))
% 2.50/2.70          | ~ (v1_funct_1 @ X17)
% 2.50/2.70          | ~ (v1_relat_1 @ X17))),
% 2.50/2.70      inference('demod', [status(thm)], ['98', '99'])).
% 2.50/2.70  thf('114', plain,
% 2.50/2.70      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.50/2.70         (~ (v1_relat_1 @ X6)
% 2.50/2.70          | ((k5_relat_1 @ (k5_relat_1 @ X7 @ X6) @ X8)
% 2.50/2.70              = (k5_relat_1 @ X7 @ (k5_relat_1 @ X6 @ X8)))
% 2.50/2.70          | ~ (v1_relat_1 @ X8)
% 2.50/2.70          | ~ (v1_relat_1 @ X7))),
% 2.50/2.70      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.50/2.70  thf('115', plain,
% 2.50/2.70      (![X0 : $i, X1 : $i]:
% 2.50/2.70         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X1)
% 2.50/2.70            = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1)))
% 2.50/2.70          | ~ (v1_relat_1 @ X0)
% 2.50/2.70          | ~ (v1_funct_1 @ X0)
% 2.50/2.70          | ~ (v2_funct_1 @ X0)
% 2.50/2.70          | ~ (v1_relat_1 @ X0)
% 2.50/2.70          | ~ (v1_relat_1 @ X1)
% 2.50/2.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 2.50/2.70      inference('sup+', [status(thm)], ['113', '114'])).
% 2.50/2.70  thf('116', plain,
% 2.50/2.70      (![X0 : $i, X1 : $i]:
% 2.50/2.70         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.50/2.70          | ~ (v1_relat_1 @ X1)
% 2.50/2.70          | ~ (v2_funct_1 @ X0)
% 2.50/2.70          | ~ (v1_funct_1 @ X0)
% 2.50/2.70          | ~ (v1_relat_1 @ X0)
% 2.50/2.70          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X1)
% 2.50/2.70              = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1))))),
% 2.50/2.70      inference('simplify', [status(thm)], ['115'])).
% 2.50/2.70  thf('117', plain,
% 2.50/2.70      (![X0 : $i, X1 : $i]:
% 2.50/2.70         (~ (v1_relat_1 @ X0)
% 2.50/2.70          | ~ (v1_funct_1 @ X0)
% 2.50/2.70          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X1)
% 2.50/2.70              = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1)))
% 2.50/2.70          | ~ (v1_relat_1 @ X0)
% 2.50/2.70          | ~ (v1_funct_1 @ X0)
% 2.50/2.70          | ~ (v2_funct_1 @ X0)
% 2.50/2.70          | ~ (v1_relat_1 @ X1))),
% 2.50/2.70      inference('sup-', [status(thm)], ['112', '116'])).
% 2.50/2.70  thf('118', plain,
% 2.50/2.70      (![X0 : $i, X1 : $i]:
% 2.50/2.70         (~ (v1_relat_1 @ X1)
% 2.50/2.70          | ~ (v2_funct_1 @ X0)
% 2.50/2.70          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X1)
% 2.50/2.70              = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1)))
% 2.50/2.70          | ~ (v1_funct_1 @ X0)
% 2.50/2.70          | ~ (v1_relat_1 @ X0))),
% 2.50/2.70      inference('simplify', [status(thm)], ['117'])).
% 2.50/2.70  thf('119', plain,
% 2.50/2.70      (![X0 : $i]:
% 2.50/2.70         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 2.50/2.70            (k6_partfun1 @ (k1_relat_1 @ X0)))
% 2.50/2.70            = (k5_relat_1 @ X0 @ 
% 2.50/2.70               (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 2.50/2.70                (k2_funct_1 @ X0))))
% 2.50/2.70          | ~ (v1_relat_1 @ X0)
% 2.50/2.70          | ~ (v1_funct_1 @ X0)
% 2.50/2.70          | ~ (v2_funct_1 @ X0)
% 2.50/2.70          | ~ (v1_relat_1 @ X0)
% 2.50/2.70          | ~ (v1_funct_1 @ X0)
% 2.50/2.70          | ~ (v2_funct_1 @ X0)
% 2.50/2.70          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0))))),
% 2.50/2.70      inference('sup+', [status(thm)], ['111', '118'])).
% 2.50/2.70  thf(t71_relat_1, axiom,
% 2.50/2.70    (![A:$i]:
% 2.50/2.70     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 2.50/2.70       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 2.50/2.70  thf('120', plain, (![X9 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 2.50/2.70      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.50/2.70  thf('121', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 2.50/2.70      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.50/2.70  thf('122', plain, (![X9 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X9)) = (X9))),
% 2.50/2.70      inference('demod', [status(thm)], ['120', '121'])).
% 2.50/2.70  thf(t78_relat_1, axiom,
% 2.50/2.70    (![A:$i]:
% 2.50/2.70     ( ( v1_relat_1 @ A ) =>
% 2.50/2.70       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 2.50/2.70  thf('123', plain,
% 2.50/2.70      (![X11 : $i]:
% 2.50/2.70         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X11)) @ X11) = (X11))
% 2.50/2.70          | ~ (v1_relat_1 @ X11))),
% 2.50/2.70      inference('cnf', [status(esa)], [t78_relat_1])).
% 2.50/2.70  thf('124', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 2.50/2.70      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.50/2.70  thf('125', plain,
% 2.50/2.70      (![X11 : $i]:
% 2.50/2.70         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X11)) @ X11) = (X11))
% 2.50/2.70          | ~ (v1_relat_1 @ X11))),
% 2.50/2.70      inference('demod', [status(thm)], ['123', '124'])).
% 2.50/2.70  thf('126', plain,
% 2.50/2.70      (![X0 : $i]:
% 2.50/2.70         (((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 2.50/2.70            = (k6_partfun1 @ X0))
% 2.50/2.70          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 2.50/2.70      inference('sup+', [status(thm)], ['122', '125'])).
% 2.50/2.70  thf('127', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 2.50/2.70      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.50/2.70  thf('128', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 2.50/2.70      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.50/2.70  thf('129', plain, (![X15 : $i]: (v1_relat_1 @ (k6_partfun1 @ X15))),
% 2.50/2.70      inference('demod', [status(thm)], ['127', '128'])).
% 2.50/2.70  thf('130', plain,
% 2.50/2.70      (![X0 : $i]:
% 2.50/2.70         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 2.50/2.70           = (k6_partfun1 @ X0))),
% 2.50/2.70      inference('demod', [status(thm)], ['126', '129'])).
% 2.50/2.70  thf('131', plain, (![X15 : $i]: (v1_relat_1 @ (k6_partfun1 @ X15))),
% 2.50/2.70      inference('demod', [status(thm)], ['127', '128'])).
% 2.50/2.70  thf('132', plain,
% 2.50/2.70      (![X0 : $i]:
% 2.50/2.70         (((k6_partfun1 @ (k1_relat_1 @ X0))
% 2.50/2.70            = (k5_relat_1 @ X0 @ 
% 2.50/2.70               (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 2.50/2.70                (k2_funct_1 @ X0))))
% 2.50/2.70          | ~ (v1_relat_1 @ X0)
% 2.50/2.70          | ~ (v1_funct_1 @ X0)
% 2.50/2.70          | ~ (v2_funct_1 @ X0)
% 2.50/2.70          | ~ (v1_relat_1 @ X0)
% 2.50/2.70          | ~ (v1_funct_1 @ X0)
% 2.50/2.70          | ~ (v2_funct_1 @ X0))),
% 2.50/2.70      inference('demod', [status(thm)], ['119', '130', '131'])).
% 2.50/2.70  thf('133', plain,
% 2.50/2.70      (![X0 : $i]:
% 2.50/2.70         (~ (v2_funct_1 @ X0)
% 2.50/2.70          | ~ (v1_funct_1 @ X0)
% 2.50/2.70          | ~ (v1_relat_1 @ X0)
% 2.50/2.70          | ((k6_partfun1 @ (k1_relat_1 @ X0))
% 2.50/2.70              = (k5_relat_1 @ X0 @ 
% 2.50/2.70                 (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 2.50/2.70                  (k2_funct_1 @ X0)))))),
% 2.50/2.70      inference('simplify', [status(thm)], ['132'])).
% 2.50/2.70  thf('134', plain,
% 2.50/2.70      (![X0 : $i, X1 : $i]:
% 2.50/2.70         (~ (v1_relat_1 @ X1)
% 2.50/2.70          | ~ (v2_funct_1 @ X0)
% 2.50/2.70          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 2.50/2.70              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 2.50/2.70          | ~ (v1_funct_1 @ X0)
% 2.50/2.70          | ~ (v1_relat_1 @ X0))),
% 2.50/2.70      inference('simplify', [status(thm)], ['106'])).
% 2.50/2.70  thf('135', plain,
% 2.50/2.70      (![X0 : $i]:
% 2.50/2.70         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 2.50/2.70            (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0)))
% 2.50/2.70            = (k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 2.50/2.70               (k6_partfun1 @ (k1_relat_1 @ X0))))
% 2.50/2.70          | ~ (v1_relat_1 @ X0)
% 2.50/2.70          | ~ (v1_funct_1 @ X0)
% 2.50/2.70          | ~ (v2_funct_1 @ X0)
% 2.50/2.70          | ~ (v1_relat_1 @ X0)
% 2.50/2.70          | ~ (v1_funct_1 @ X0)
% 2.50/2.70          | ~ (v2_funct_1 @ X0)
% 2.50/2.70          | ~ (v1_relat_1 @ 
% 2.50/2.70               (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 2.50/2.70                (k2_funct_1 @ X0))))),
% 2.50/2.70      inference('sup+', [status(thm)], ['133', '134'])).
% 2.50/2.70  thf('136', plain,
% 2.50/2.70      (![X0 : $i]:
% 2.50/2.70         (~ (v1_relat_1 @ 
% 2.50/2.70             (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 2.50/2.70              (k2_funct_1 @ X0)))
% 2.50/2.70          | ~ (v2_funct_1 @ X0)
% 2.50/2.70          | ~ (v1_funct_1 @ X0)
% 2.50/2.70          | ~ (v1_relat_1 @ X0)
% 2.50/2.70          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 2.50/2.70              (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 2.50/2.70               (k2_funct_1 @ X0)))
% 2.50/2.70              = (k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 2.50/2.70                 (k6_partfun1 @ (k1_relat_1 @ X0)))))),
% 2.50/2.70      inference('simplify', [status(thm)], ['135'])).
% 2.50/2.70  thf('137', plain,
% 2.50/2.70      ((~ (v1_relat_1 @ 
% 2.50/2.70           (k5_relat_1 @ (k6_partfun1 @ sk_A) @ (k2_funct_1 @ sk_D)))
% 2.50/2.70        | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_D)) @ 
% 2.50/2.70            (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_D)) @ 
% 2.50/2.70             (k2_funct_1 @ sk_D)))
% 2.50/2.70            = (k5_relat_1 @ (k2_funct_1 @ sk_D) @ 
% 2.50/2.70               (k6_partfun1 @ (k1_relat_1 @ sk_D))))
% 2.50/2.70        | ~ (v1_relat_1 @ sk_D)
% 2.50/2.70        | ~ (v1_funct_1 @ sk_D)
% 2.50/2.70        | ~ (v2_funct_1 @ sk_D))),
% 2.50/2.70      inference('sup-', [status(thm)], ['96', '136'])).
% 2.50/2.70  thf('138', plain, (((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))),
% 2.50/2.70      inference('demod', [status(thm)], ['11', '61'])).
% 2.50/2.70  thf('139', plain,
% 2.50/2.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('140', plain,
% 2.50/2.70      (![X50 : $i, X51 : $i, X52 : $i]:
% 2.50/2.70         (((X50) = (k1_xboole_0))
% 2.50/2.70          | ~ (v1_funct_1 @ X51)
% 2.50/2.70          | ~ (v1_funct_2 @ X51 @ X52 @ X50)
% 2.50/2.70          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 2.50/2.70          | ((k5_relat_1 @ X51 @ (k2_funct_1 @ X51)) = (k6_partfun1 @ X52))
% 2.50/2.70          | ~ (v2_funct_1 @ X51)
% 2.50/2.70          | ((k2_relset_1 @ X52 @ X50 @ X51) != (X50)))),
% 2.50/2.70      inference('cnf', [status(esa)], [t35_funct_2])).
% 2.50/2.70  thf('141', plain,
% 2.50/2.70      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 2.50/2.70        | ~ (v2_funct_1 @ sk_D)
% 2.50/2.70        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 2.50/2.70        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.50/2.70        | ~ (v1_funct_1 @ sk_D)
% 2.50/2.70        | ((sk_A) = (k1_xboole_0)))),
% 2.50/2.70      inference('sup-', [status(thm)], ['139', '140'])).
% 2.50/2.70  thf('142', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))),
% 2.50/2.70      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 2.50/2.70  thf('143', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('144', plain, ((v1_funct_1 @ sk_D)),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('145', plain,
% 2.50/2.70      ((((sk_A) != (sk_A))
% 2.50/2.70        | ~ (v2_funct_1 @ sk_D)
% 2.50/2.70        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 2.50/2.70        | ((sk_A) = (k1_xboole_0)))),
% 2.50/2.70      inference('demod', [status(thm)], ['141', '142', '143', '144'])).
% 2.50/2.70  thf('146', plain,
% 2.50/2.70      ((((sk_A) = (k1_xboole_0))
% 2.50/2.70        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 2.50/2.70        | ~ (v2_funct_1 @ sk_D))),
% 2.50/2.70      inference('simplify', [status(thm)], ['145'])).
% 2.50/2.70  thf('147', plain, (((sk_A) != (k1_xboole_0))),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('148', plain,
% 2.50/2.70      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 2.50/2.70        | ~ (v2_funct_1 @ sk_D))),
% 2.50/2.70      inference('simplify_reflect-', [status(thm)], ['146', '147'])).
% 2.50/2.70  thf('149', plain, ((v2_funct_1 @ sk_D)),
% 2.50/2.70      inference('sup-', [status(thm)], ['59', '60'])).
% 2.50/2.70  thf('150', plain,
% 2.50/2.70      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 2.50/2.70      inference('demod', [status(thm)], ['148', '149'])).
% 2.50/2.70  thf('151', plain, (((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))),
% 2.50/2.70      inference('demod', [status(thm)], ['11', '61'])).
% 2.50/2.70  thf('152', plain,
% 2.50/2.70      (((k5_relat_1 @ sk_D @ (k4_relat_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 2.50/2.70      inference('demod', [status(thm)], ['150', '151'])).
% 2.50/2.70  thf('153', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 2.50/2.70      inference('demod', [status(thm)], ['36', '37'])).
% 2.50/2.70  thf('154', plain,
% 2.50/2.70      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.50/2.70         (~ (v1_relat_1 @ X6)
% 2.50/2.70          | ((k5_relat_1 @ (k5_relat_1 @ X7 @ X6) @ X8)
% 2.50/2.70              = (k5_relat_1 @ X7 @ (k5_relat_1 @ X6 @ X8)))
% 2.50/2.70          | ~ (v1_relat_1 @ X8)
% 2.50/2.70          | ~ (v1_relat_1 @ X7))),
% 2.50/2.70      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.50/2.70  thf('155', plain,
% 2.50/2.70      (![X0 : $i]:
% 2.50/2.70         (((k5_relat_1 @ (k6_partfun1 @ sk_A) @ X0)
% 2.50/2.70            = (k5_relat_1 @ sk_C @ (k5_relat_1 @ sk_D @ X0)))
% 2.50/2.70          | ~ (v1_relat_1 @ sk_C)
% 2.50/2.70          | ~ (v1_relat_1 @ X0)
% 2.50/2.70          | ~ (v1_relat_1 @ sk_D))),
% 2.50/2.70      inference('sup+', [status(thm)], ['153', '154'])).
% 2.50/2.70  thf('156', plain,
% 2.50/2.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('157', plain,
% 2.50/2.70      (![X0 : $i, X1 : $i]:
% 2.50/2.70         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 2.50/2.70          | (v1_relat_1 @ X0)
% 2.50/2.70          | ~ (v1_relat_1 @ X1))),
% 2.50/2.70      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.50/2.70  thf('158', plain,
% 2.50/2.70      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 2.50/2.70      inference('sup-', [status(thm)], ['156', '157'])).
% 2.50/2.70  thf('159', plain,
% 2.50/2.70      (![X3 : $i, X4 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X3 @ X4))),
% 2.50/2.70      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.50/2.70  thf('160', plain, ((v1_relat_1 @ sk_C)),
% 2.50/2.70      inference('demod', [status(thm)], ['158', '159'])).
% 2.50/2.70  thf('161', plain, ((v1_relat_1 @ sk_D)),
% 2.50/2.70      inference('demod', [status(thm)], ['2', '3'])).
% 2.50/2.70  thf('162', plain,
% 2.50/2.70      (![X0 : $i]:
% 2.50/2.70         (((k5_relat_1 @ (k6_partfun1 @ sk_A) @ X0)
% 2.50/2.70            = (k5_relat_1 @ sk_C @ (k5_relat_1 @ sk_D @ X0)))
% 2.50/2.70          | ~ (v1_relat_1 @ X0))),
% 2.50/2.70      inference('demod', [status(thm)], ['155', '160', '161'])).
% 2.50/2.70  thf('163', plain,
% 2.50/2.70      ((((k5_relat_1 @ (k6_partfun1 @ sk_A) @ (k4_relat_1 @ sk_D))
% 2.50/2.70          = (k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)))
% 2.50/2.70        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_D)))),
% 2.50/2.70      inference('sup+', [status(thm)], ['152', '162'])).
% 2.50/2.70  thf('164', plain,
% 2.50/2.70      (![X11 : $i]:
% 2.50/2.70         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X11)) @ X11) = (X11))
% 2.50/2.70          | ~ (v1_relat_1 @ X11))),
% 2.50/2.70      inference('demod', [status(thm)], ['123', '124'])).
% 2.50/2.70  thf('165', plain, ((v1_funct_1 @ sk_C)),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('166', plain,
% 2.50/2.70      (![X13 : $i]:
% 2.50/2.70         (~ (v2_funct_1 @ X13)
% 2.50/2.70          | ((k2_funct_1 @ X13) = (k4_relat_1 @ X13))
% 2.50/2.70          | ~ (v1_funct_1 @ X13)
% 2.50/2.70          | ~ (v1_relat_1 @ X13))),
% 2.50/2.70      inference('cnf', [status(esa)], [d9_funct_1])).
% 2.50/2.70  thf('167', plain,
% 2.50/2.70      ((~ (v1_relat_1 @ sk_C)
% 2.50/2.70        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 2.50/2.70        | ~ (v2_funct_1 @ sk_C))),
% 2.50/2.70      inference('sup-', [status(thm)], ['165', '166'])).
% 2.50/2.70  thf('168', plain, ((v1_relat_1 @ sk_C)),
% 2.50/2.70      inference('demod', [status(thm)], ['158', '159'])).
% 2.50/2.70  thf('169', plain, ((v2_funct_1 @ sk_C)),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('170', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 2.50/2.70      inference('demod', [status(thm)], ['167', '168', '169'])).
% 2.50/2.70  thf('171', plain,
% 2.50/2.70      (![X17 : $i]:
% 2.50/2.70         (~ (v2_funct_1 @ X17)
% 2.50/2.70          | ((k5_relat_1 @ (k2_funct_1 @ X17) @ X17)
% 2.50/2.70              = (k6_partfun1 @ (k2_relat_1 @ X17)))
% 2.50/2.70          | ~ (v1_funct_1 @ X17)
% 2.50/2.70          | ~ (v1_relat_1 @ X17))),
% 2.50/2.70      inference('demod', [status(thm)], ['63', '64'])).
% 2.50/2.70  thf('172', plain,
% 2.50/2.70      ((((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C)
% 2.50/2.70          = (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 2.50/2.70        | ~ (v1_relat_1 @ sk_C)
% 2.50/2.70        | ~ (v1_funct_1 @ sk_C)
% 2.50/2.70        | ~ (v2_funct_1 @ sk_C))),
% 2.50/2.70      inference('sup+', [status(thm)], ['170', '171'])).
% 2.50/2.70  thf('173', plain, ((v1_relat_1 @ sk_C)),
% 2.50/2.70      inference('demod', [status(thm)], ['158', '159'])).
% 2.50/2.70  thf('174', plain, ((v1_funct_1 @ sk_C)),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('175', plain, ((v2_funct_1 @ sk_C)),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('176', plain,
% 2.50/2.70      (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C)
% 2.50/2.70         = (k6_partfun1 @ (k2_relat_1 @ sk_C)))),
% 2.50/2.70      inference('demod', [status(thm)], ['172', '173', '174', '175'])).
% 2.50/2.70  thf('177', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 2.50/2.70      inference('demod', [status(thm)], ['167', '168', '169'])).
% 2.50/2.70  thf('178', plain,
% 2.50/2.70      (![X17 : $i]:
% 2.50/2.70         (~ (v2_funct_1 @ X17)
% 2.50/2.70          | ((k5_relat_1 @ X17 @ (k2_funct_1 @ X17))
% 2.50/2.70              = (k6_partfun1 @ (k1_relat_1 @ X17)))
% 2.50/2.70          | ~ (v1_funct_1 @ X17)
% 2.50/2.70          | ~ (v1_relat_1 @ X17))),
% 2.50/2.70      inference('demod', [status(thm)], ['98', '99'])).
% 2.50/2.70  thf('179', plain,
% 2.50/2.70      ((((k5_relat_1 @ sk_C @ (k4_relat_1 @ sk_C))
% 2.50/2.70          = (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 2.50/2.70        | ~ (v1_relat_1 @ sk_C)
% 2.50/2.70        | ~ (v1_funct_1 @ sk_C)
% 2.50/2.70        | ~ (v2_funct_1 @ sk_C))),
% 2.50/2.70      inference('sup+', [status(thm)], ['177', '178'])).
% 2.50/2.70  thf('180', plain, ((v1_relat_1 @ sk_C)),
% 2.50/2.70      inference('demod', [status(thm)], ['158', '159'])).
% 2.50/2.70  thf('181', plain, ((v1_funct_1 @ sk_C)),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('182', plain, ((v2_funct_1 @ sk_C)),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('183', plain,
% 2.50/2.70      (((k5_relat_1 @ sk_C @ (k4_relat_1 @ sk_C))
% 2.50/2.70         = (k6_partfun1 @ (k1_relat_1 @ sk_C)))),
% 2.50/2.70      inference('demod', [status(thm)], ['179', '180', '181', '182'])).
% 2.50/2.70  thf('184', plain,
% 2.50/2.70      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.50/2.70         (~ (v1_relat_1 @ X6)
% 2.50/2.70          | ((k5_relat_1 @ (k5_relat_1 @ X7 @ X6) @ X8)
% 2.50/2.70              = (k5_relat_1 @ X7 @ (k5_relat_1 @ X6 @ X8)))
% 2.50/2.70          | ~ (v1_relat_1 @ X8)
% 2.50/2.70          | ~ (v1_relat_1 @ X7))),
% 2.50/2.70      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.50/2.70  thf('185', plain,
% 2.50/2.70      (![X0 : $i]:
% 2.50/2.70         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ X0)
% 2.50/2.70            = (k5_relat_1 @ sk_C @ (k5_relat_1 @ (k4_relat_1 @ sk_C) @ X0)))
% 2.50/2.70          | ~ (v1_relat_1 @ sk_C)
% 2.50/2.70          | ~ (v1_relat_1 @ X0)
% 2.50/2.70          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 2.50/2.70      inference('sup+', [status(thm)], ['183', '184'])).
% 2.50/2.70  thf('186', plain, ((v1_relat_1 @ sk_C)),
% 2.50/2.70      inference('demod', [status(thm)], ['158', '159'])).
% 2.50/2.70  thf('187', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 2.50/2.70      inference('demod', [status(thm)], ['167', '168', '169'])).
% 2.50/2.70  thf('188', plain,
% 2.50/2.70      (![X14 : $i]:
% 2.50/2.70         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 2.50/2.70          | ~ (v1_funct_1 @ X14)
% 2.50/2.70          | ~ (v1_relat_1 @ X14))),
% 2.50/2.70      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.50/2.70  thf('189', plain,
% 2.50/2.70      (((v1_relat_1 @ (k4_relat_1 @ sk_C))
% 2.50/2.70        | ~ (v1_relat_1 @ sk_C)
% 2.50/2.70        | ~ (v1_funct_1 @ sk_C))),
% 2.50/2.70      inference('sup+', [status(thm)], ['187', '188'])).
% 2.50/2.70  thf('190', plain, ((v1_relat_1 @ sk_C)),
% 2.50/2.70      inference('demod', [status(thm)], ['158', '159'])).
% 2.50/2.70  thf('191', plain, ((v1_funct_1 @ sk_C)),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('192', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 2.50/2.70      inference('demod', [status(thm)], ['189', '190', '191'])).
% 2.50/2.70  thf('193', plain,
% 2.50/2.70      (![X0 : $i]:
% 2.50/2.70         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ X0)
% 2.50/2.70            = (k5_relat_1 @ sk_C @ (k5_relat_1 @ (k4_relat_1 @ sk_C) @ X0)))
% 2.50/2.70          | ~ (v1_relat_1 @ X0))),
% 2.50/2.70      inference('demod', [status(thm)], ['185', '186', '192'])).
% 2.50/2.70  thf('194', plain,
% 2.50/2.70      ((((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ sk_C)
% 2.50/2.70          = (k5_relat_1 @ sk_C @ (k6_partfun1 @ (k2_relat_1 @ sk_C))))
% 2.50/2.70        | ~ (v1_relat_1 @ sk_C))),
% 2.50/2.70      inference('sup+', [status(thm)], ['176', '193'])).
% 2.50/2.70  thf('195', plain, ((v1_relat_1 @ sk_C)),
% 2.50/2.70      inference('demod', [status(thm)], ['158', '159'])).
% 2.50/2.70  thf('196', plain,
% 2.50/2.70      (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ sk_C)
% 2.50/2.70         = (k5_relat_1 @ sk_C @ (k6_partfun1 @ (k2_relat_1 @ sk_C))))),
% 2.50/2.70      inference('demod', [status(thm)], ['194', '195'])).
% 2.50/2.70  thf('197', plain,
% 2.50/2.70      ((((sk_C) = (k5_relat_1 @ sk_C @ (k6_partfun1 @ (k2_relat_1 @ sk_C))))
% 2.50/2.70        | ~ (v1_relat_1 @ sk_C))),
% 2.50/2.70      inference('sup+', [status(thm)], ['164', '196'])).
% 2.50/2.70  thf('198', plain, ((v1_relat_1 @ sk_C)),
% 2.50/2.70      inference('demod', [status(thm)], ['158', '159'])).
% 2.50/2.70  thf('199', plain,
% 2.50/2.70      (((sk_C) = (k5_relat_1 @ sk_C @ (k6_partfun1 @ (k2_relat_1 @ sk_C))))),
% 2.50/2.70      inference('demod', [status(thm)], ['197', '198'])).
% 2.50/2.70  thf('200', plain,
% 2.50/2.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('201', plain,
% 2.50/2.70      (![X50 : $i, X51 : $i, X52 : $i]:
% 2.50/2.70         (((X50) = (k1_xboole_0))
% 2.50/2.70          | ~ (v1_funct_1 @ X51)
% 2.50/2.70          | ~ (v1_funct_2 @ X51 @ X52 @ X50)
% 2.50/2.70          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 2.50/2.70          | ((k5_relat_1 @ (k2_funct_1 @ X51) @ X51) = (k6_partfun1 @ X50))
% 2.50/2.70          | ~ (v2_funct_1 @ X51)
% 2.50/2.70          | ((k2_relset_1 @ X52 @ X50 @ X51) != (X50)))),
% 2.50/2.70      inference('cnf', [status(esa)], [t35_funct_2])).
% 2.50/2.70  thf('202', plain,
% 2.50/2.70      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 2.50/2.70        | ~ (v2_funct_1 @ sk_C)
% 2.50/2.70        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 2.50/2.70        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.50/2.70        | ~ (v1_funct_1 @ sk_C)
% 2.50/2.70        | ((sk_B) = (k1_xboole_0)))),
% 2.50/2.70      inference('sup-', [status(thm)], ['200', '201'])).
% 2.50/2.70  thf('203', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('204', plain, ((v2_funct_1 @ sk_C)),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('205', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 2.50/2.70      inference('demod', [status(thm)], ['167', '168', '169'])).
% 2.50/2.70  thf('206', plain,
% 2.50/2.70      (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C)
% 2.50/2.70         = (k6_partfun1 @ (k2_relat_1 @ sk_C)))),
% 2.50/2.70      inference('demod', [status(thm)], ['172', '173', '174', '175'])).
% 2.50/2.70  thf('207', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('208', plain, ((v1_funct_1 @ sk_C)),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('209', plain,
% 2.50/2.70      ((((sk_B) != (sk_B))
% 2.50/2.70        | ((k6_partfun1 @ (k2_relat_1 @ sk_C)) = (k6_partfun1 @ sk_B))
% 2.50/2.70        | ((sk_B) = (k1_xboole_0)))),
% 2.50/2.70      inference('demod', [status(thm)],
% 2.50/2.70                ['202', '203', '204', '205', '206', '207', '208'])).
% 2.50/2.70  thf('210', plain,
% 2.50/2.70      ((((sk_B) = (k1_xboole_0))
% 2.50/2.70        | ((k6_partfun1 @ (k2_relat_1 @ sk_C)) = (k6_partfun1 @ sk_B)))),
% 2.50/2.70      inference('simplify', [status(thm)], ['209'])).
% 2.50/2.70  thf('211', plain, (((sk_B) != (k1_xboole_0))),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('212', plain,
% 2.50/2.70      (((k6_partfun1 @ (k2_relat_1 @ sk_C)) = (k6_partfun1 @ sk_B))),
% 2.50/2.70      inference('simplify_reflect-', [status(thm)], ['210', '211'])).
% 2.50/2.70  thf('213', plain, (((sk_C) = (k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)))),
% 2.50/2.70      inference('demod', [status(thm)], ['199', '212'])).
% 2.50/2.70  thf('214', plain, (((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))),
% 2.50/2.70      inference('demod', [status(thm)], ['11', '61'])).
% 2.50/2.70  thf('215', plain,
% 2.50/2.70      (![X14 : $i]:
% 2.50/2.70         ((v1_relat_1 @ (k2_funct_1 @ X14))
% 2.50/2.70          | ~ (v1_funct_1 @ X14)
% 2.50/2.70          | ~ (v1_relat_1 @ X14))),
% 2.50/2.70      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.50/2.70  thf('216', plain,
% 2.50/2.70      (((v1_relat_1 @ (k4_relat_1 @ sk_D))
% 2.50/2.70        | ~ (v1_relat_1 @ sk_D)
% 2.50/2.70        | ~ (v1_funct_1 @ sk_D))),
% 2.50/2.70      inference('sup+', [status(thm)], ['214', '215'])).
% 2.50/2.70  thf('217', plain, ((v1_relat_1 @ sk_D)),
% 2.50/2.70      inference('demod', [status(thm)], ['2', '3'])).
% 2.50/2.70  thf('218', plain, ((v1_funct_1 @ sk_D)),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('219', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_D))),
% 2.50/2.70      inference('demod', [status(thm)], ['216', '217', '218'])).
% 2.50/2.70  thf('220', plain,
% 2.50/2.70      (((k5_relat_1 @ (k6_partfun1 @ sk_A) @ (k4_relat_1 @ sk_D)) = (sk_C))),
% 2.50/2.70      inference('demod', [status(thm)], ['163', '213', '219'])).
% 2.50/2.70  thf('221', plain, ((v1_relat_1 @ sk_C)),
% 2.50/2.70      inference('demod', [status(thm)], ['158', '159'])).
% 2.50/2.70  thf('222', plain,
% 2.50/2.70      (((k6_partfun1 @ (k2_relat_1 @ sk_D)) = (k6_partfun1 @ sk_A))),
% 2.50/2.70      inference('sup+', [status(thm)], ['70', '95'])).
% 2.50/2.70  thf('223', plain,
% 2.50/2.70      (((k6_partfun1 @ (k2_relat_1 @ sk_D)) = (k6_partfun1 @ sk_A))),
% 2.50/2.70      inference('sup+', [status(thm)], ['70', '95'])).
% 2.50/2.70  thf('224', plain, (((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))),
% 2.50/2.70      inference('demod', [status(thm)], ['11', '61'])).
% 2.50/2.70  thf('225', plain,
% 2.50/2.70      (((k5_relat_1 @ (k6_partfun1 @ sk_A) @ (k4_relat_1 @ sk_D)) = (sk_C))),
% 2.50/2.70      inference('demod', [status(thm)], ['163', '213', '219'])).
% 2.50/2.70  thf('226', plain,
% 2.50/2.70      (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ sk_C)
% 2.50/2.70         = (k5_relat_1 @ sk_C @ (k6_partfun1 @ (k2_relat_1 @ sk_C))))),
% 2.50/2.70      inference('demod', [status(thm)], ['194', '195'])).
% 2.50/2.70  thf('227', plain,
% 2.50/2.70      (((sk_C) = (k5_relat_1 @ sk_C @ (k6_partfun1 @ (k2_relat_1 @ sk_C))))),
% 2.50/2.70      inference('demod', [status(thm)], ['197', '198'])).
% 2.50/2.70  thf('228', plain,
% 2.50/2.70      (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ sk_C) = (sk_C))),
% 2.50/2.70      inference('demod', [status(thm)], ['226', '227'])).
% 2.50/2.70  thf('229', plain,
% 2.50/2.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('230', plain,
% 2.50/2.70      (![X50 : $i, X51 : $i, X52 : $i]:
% 2.50/2.70         (((X50) = (k1_xboole_0))
% 2.50/2.70          | ~ (v1_funct_1 @ X51)
% 2.50/2.70          | ~ (v1_funct_2 @ X51 @ X52 @ X50)
% 2.50/2.70          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 2.50/2.70          | ((k5_relat_1 @ X51 @ (k2_funct_1 @ X51)) = (k6_partfun1 @ X52))
% 2.50/2.70          | ~ (v2_funct_1 @ X51)
% 2.50/2.70          | ((k2_relset_1 @ X52 @ X50 @ X51) != (X50)))),
% 2.50/2.70      inference('cnf', [status(esa)], [t35_funct_2])).
% 2.50/2.70  thf('231', plain,
% 2.50/2.70      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 2.50/2.70        | ~ (v2_funct_1 @ sk_C)
% 2.50/2.70        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 2.50/2.70        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.50/2.70        | ~ (v1_funct_1 @ sk_C)
% 2.50/2.70        | ((sk_B) = (k1_xboole_0)))),
% 2.50/2.70      inference('sup-', [status(thm)], ['229', '230'])).
% 2.50/2.70  thf('232', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('233', plain, ((v2_funct_1 @ sk_C)),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('234', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 2.50/2.70      inference('demod', [status(thm)], ['167', '168', '169'])).
% 2.50/2.70  thf('235', plain,
% 2.50/2.70      (((k5_relat_1 @ sk_C @ (k4_relat_1 @ sk_C))
% 2.50/2.70         = (k6_partfun1 @ (k1_relat_1 @ sk_C)))),
% 2.50/2.70      inference('demod', [status(thm)], ['179', '180', '181', '182'])).
% 2.50/2.70  thf('236', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('237', plain, ((v1_funct_1 @ sk_C)),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('238', plain,
% 2.50/2.70      ((((sk_B) != (sk_B))
% 2.50/2.70        | ((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 2.50/2.70        | ((sk_B) = (k1_xboole_0)))),
% 2.50/2.70      inference('demod', [status(thm)],
% 2.50/2.70                ['231', '232', '233', '234', '235', '236', '237'])).
% 2.50/2.70  thf('239', plain,
% 2.50/2.70      ((((sk_B) = (k1_xboole_0))
% 2.50/2.70        | ((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 2.50/2.70      inference('simplify', [status(thm)], ['238'])).
% 2.50/2.70  thf('240', plain, (((sk_B) != (k1_xboole_0))),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('241', plain,
% 2.50/2.70      (((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 2.50/2.70      inference('simplify_reflect-', [status(thm)], ['239', '240'])).
% 2.50/2.70  thf('242', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_A) @ sk_C) = (sk_C))),
% 2.50/2.70      inference('demod', [status(thm)], ['228', '241'])).
% 2.50/2.70  thf('243', plain, (((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))),
% 2.50/2.70      inference('demod', [status(thm)], ['11', '61'])).
% 2.50/2.70  thf(dt_k4_relat_1, axiom,
% 2.50/2.70    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 2.50/2.70  thf('244', plain,
% 2.50/2.70      (![X2 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X2)) | ~ (v1_relat_1 @ X2))),
% 2.50/2.70      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 2.50/2.70  thf('245', plain,
% 2.50/2.70      (((k1_relat_1 @ sk_D) = (k2_relat_1 @ (k4_relat_1 @ sk_D)))),
% 2.50/2.70      inference('sup-', [status(thm)], ['4', '5'])).
% 2.50/2.70  thf(t80_relat_1, axiom,
% 2.50/2.70    (![A:$i]:
% 2.50/2.70     ( ( v1_relat_1 @ A ) =>
% 2.50/2.70       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 2.50/2.70  thf('246', plain,
% 2.50/2.70      (![X12 : $i]:
% 2.50/2.70         (((k5_relat_1 @ X12 @ (k6_relat_1 @ (k2_relat_1 @ X12))) = (X12))
% 2.50/2.70          | ~ (v1_relat_1 @ X12))),
% 2.50/2.70      inference('cnf', [status(esa)], [t80_relat_1])).
% 2.50/2.70  thf('247', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 2.50/2.70      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.50/2.70  thf('248', plain,
% 2.50/2.70      (![X12 : $i]:
% 2.50/2.70         (((k5_relat_1 @ X12 @ (k6_partfun1 @ (k2_relat_1 @ X12))) = (X12))
% 2.50/2.70          | ~ (v1_relat_1 @ X12))),
% 2.50/2.70      inference('demod', [status(thm)], ['246', '247'])).
% 2.50/2.70  thf('249', plain,
% 2.50/2.70      ((((k5_relat_1 @ (k4_relat_1 @ sk_D) @ 
% 2.50/2.70          (k6_partfun1 @ (k1_relat_1 @ sk_D))) = (k4_relat_1 @ sk_D))
% 2.50/2.70        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_D)))),
% 2.50/2.70      inference('sup+', [status(thm)], ['245', '248'])).
% 2.50/2.70  thf('250', plain,
% 2.50/2.70      ((~ (v1_relat_1 @ sk_D)
% 2.50/2.70        | ((k5_relat_1 @ (k4_relat_1 @ sk_D) @ 
% 2.50/2.70            (k6_partfun1 @ (k1_relat_1 @ sk_D))) = (k4_relat_1 @ sk_D)))),
% 2.50/2.70      inference('sup-', [status(thm)], ['244', '249'])).
% 2.50/2.70  thf('251', plain, ((v1_relat_1 @ sk_D)),
% 2.50/2.70      inference('demod', [status(thm)], ['2', '3'])).
% 2.50/2.70  thf('252', plain,
% 2.50/2.70      (((k5_relat_1 @ (k4_relat_1 @ sk_D) @ (k6_partfun1 @ (k1_relat_1 @ sk_D)))
% 2.50/2.70         = (k4_relat_1 @ sk_D))),
% 2.50/2.70      inference('demod', [status(thm)], ['250', '251'])).
% 2.50/2.70  thf('253', plain, ((v1_relat_1 @ sk_D)),
% 2.50/2.70      inference('demod', [status(thm)], ['2', '3'])).
% 2.50/2.70  thf('254', plain, ((v1_funct_1 @ sk_D)),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('255', plain, ((v2_funct_1 @ sk_D)),
% 2.50/2.70      inference('sup-', [status(thm)], ['59', '60'])).
% 2.50/2.70  thf('256', plain, (((sk_C) = (k4_relat_1 @ sk_D))),
% 2.50/2.70      inference('demod', [status(thm)],
% 2.50/2.70                ['137', '138', '220', '221', '222', '223', '224', '225', 
% 2.50/2.70                 '242', '243', '252', '253', '254', '255'])).
% 2.50/2.70  thf('257', plain, (((k1_relat_1 @ sk_D) = (k2_relat_1 @ sk_C))),
% 2.50/2.70      inference('demod', [status(thm)], ['6', '256'])).
% 2.50/2.70  thf('258', plain,
% 2.50/2.70      (((k6_partfun1 @ (k2_relat_1 @ sk_C)) = (k6_partfun1 @ sk_B))),
% 2.50/2.70      inference('simplify_reflect-', [status(thm)], ['210', '211'])).
% 2.50/2.70  thf('259', plain, (![X15 : $i]: (v1_relat_1 @ (k6_partfun1 @ X15))),
% 2.50/2.70      inference('demod', [status(thm)], ['127', '128'])).
% 2.50/2.70  thf('260', plain,
% 2.50/2.70      (![X5 : $i]:
% 2.50/2.70         (((k2_relat_1 @ X5) = (k1_relat_1 @ (k4_relat_1 @ X5)))
% 2.50/2.70          | ~ (v1_relat_1 @ X5))),
% 2.50/2.70      inference('cnf', [status(esa)], [t37_relat_1])).
% 2.50/2.70  thf('261', plain,
% 2.50/2.70      (![X0 : $i]:
% 2.50/2.70         ((k2_relat_1 @ (k6_partfun1 @ X0))
% 2.50/2.70           = (k1_relat_1 @ (k4_relat_1 @ (k6_partfun1 @ X0))))),
% 2.50/2.70      inference('sup-', [status(thm)], ['259', '260'])).
% 2.50/2.70  thf('262', plain, (![X10 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 2.50/2.70      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.50/2.70  thf('263', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 2.50/2.70      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.50/2.70  thf('264', plain,
% 2.50/2.70      (![X10 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X10)) = (X10))),
% 2.50/2.70      inference('demod', [status(thm)], ['262', '263'])).
% 2.50/2.70  thf('265', plain,
% 2.50/2.70      (![X0 : $i]: ((X0) = (k1_relat_1 @ (k4_relat_1 @ (k6_partfun1 @ X0))))),
% 2.50/2.70      inference('demod', [status(thm)], ['261', '264'])).
% 2.50/2.70  thf('266', plain,
% 2.50/2.70      (((k2_relat_1 @ sk_C)
% 2.50/2.70         = (k1_relat_1 @ (k4_relat_1 @ (k6_partfun1 @ sk_B))))),
% 2.50/2.70      inference('sup+', [status(thm)], ['258', '265'])).
% 2.50/2.70  thf('267', plain,
% 2.50/2.70      (![X0 : $i]: ((X0) = (k1_relat_1 @ (k4_relat_1 @ (k6_partfun1 @ X0))))),
% 2.50/2.70      inference('demod', [status(thm)], ['261', '264'])).
% 2.50/2.70  thf('268', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.50/2.70      inference('demod', [status(thm)], ['266', '267'])).
% 2.50/2.70  thf('269', plain, (((k1_relat_1 @ sk_D) = (sk_B))),
% 2.50/2.70      inference('demod', [status(thm)], ['257', '268'])).
% 2.50/2.70  thf('270', plain,
% 2.50/2.70      (![X11 : $i]:
% 2.50/2.70         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X11)) @ X11) = (X11))
% 2.50/2.70          | ~ (v1_relat_1 @ X11))),
% 2.50/2.70      inference('demod', [status(thm)], ['123', '124'])).
% 2.50/2.70  thf('271', plain,
% 2.50/2.70      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))
% 2.50/2.70        | ~ (v1_relat_1 @ sk_D))),
% 2.50/2.70      inference('sup+', [status(thm)], ['269', '270'])).
% 2.50/2.70  thf('272', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 2.50/2.70      inference('demod', [status(thm)], ['36', '37'])).
% 2.50/2.70  thf('273', plain,
% 2.50/2.70      (![X0 : $i, X1 : $i]:
% 2.50/2.70         (~ (v1_relat_1 @ X1)
% 2.50/2.70          | ~ (v2_funct_1 @ X0)
% 2.50/2.70          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 2.50/2.70              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 2.50/2.70          | ~ (v1_funct_1 @ X0)
% 2.50/2.70          | ~ (v1_relat_1 @ X0))),
% 2.50/2.70      inference('simplify', [status(thm)], ['106'])).
% 2.50/2.70  thf('274', plain,
% 2.50/2.70      ((((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)) @ sk_D)
% 2.50/2.70          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 2.50/2.70        | ~ (v1_relat_1 @ sk_C)
% 2.50/2.70        | ~ (v1_funct_1 @ sk_C)
% 2.50/2.70        | ~ (v2_funct_1 @ sk_C)
% 2.50/2.70        | ~ (v1_relat_1 @ sk_D))),
% 2.50/2.70      inference('sup+', [status(thm)], ['272', '273'])).
% 2.50/2.70  thf('275', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.50/2.70      inference('demod', [status(thm)], ['266', '267'])).
% 2.50/2.70  thf('276', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 2.50/2.70      inference('demod', [status(thm)], ['167', '168', '169'])).
% 2.50/2.70  thf('277', plain, ((v1_relat_1 @ sk_C)),
% 2.50/2.70      inference('demod', [status(thm)], ['158', '159'])).
% 2.50/2.70  thf('278', plain,
% 2.50/2.70      (![X5 : $i]:
% 2.50/2.70         (((k2_relat_1 @ X5) = (k1_relat_1 @ (k4_relat_1 @ X5)))
% 2.50/2.70          | ~ (v1_relat_1 @ X5))),
% 2.50/2.70      inference('cnf', [status(esa)], [t37_relat_1])).
% 2.50/2.70  thf('279', plain,
% 2.50/2.70      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 2.50/2.70      inference('sup-', [status(thm)], ['277', '278'])).
% 2.50/2.70  thf('280', plain,
% 2.50/2.70      (![X12 : $i]:
% 2.50/2.70         (((k5_relat_1 @ X12 @ (k6_partfun1 @ (k2_relat_1 @ X12))) = (X12))
% 2.50/2.70          | ~ (v1_relat_1 @ X12))),
% 2.50/2.70      inference('demod', [status(thm)], ['246', '247'])).
% 2.50/2.70  thf('281', plain,
% 2.50/2.70      (![X11 : $i]:
% 2.50/2.70         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X11)) @ X11) = (X11))
% 2.50/2.70          | ~ (v1_relat_1 @ X11))),
% 2.50/2.70      inference('demod', [status(thm)], ['123', '124'])).
% 2.50/2.70  thf('282', plain,
% 2.50/2.70      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.50/2.70         (~ (v1_relat_1 @ X6)
% 2.50/2.70          | ((k5_relat_1 @ (k5_relat_1 @ X7 @ X6) @ X8)
% 2.50/2.70              = (k5_relat_1 @ X7 @ (k5_relat_1 @ X6 @ X8)))
% 2.50/2.70          | ~ (v1_relat_1 @ X8)
% 2.50/2.70          | ~ (v1_relat_1 @ X7))),
% 2.50/2.70      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.50/2.70  thf('283', plain,
% 2.50/2.70      (![X0 : $i, X1 : $i]:
% 2.50/2.70         (((k5_relat_1 @ X0 @ X1)
% 2.50/2.70            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 2.50/2.70               (k5_relat_1 @ X0 @ X1)))
% 2.50/2.70          | ~ (v1_relat_1 @ X0)
% 2.50/2.70          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 2.50/2.70          | ~ (v1_relat_1 @ X1)
% 2.50/2.70          | ~ (v1_relat_1 @ X0))),
% 2.50/2.70      inference('sup+', [status(thm)], ['281', '282'])).
% 2.50/2.70  thf('284', plain, (![X15 : $i]: (v1_relat_1 @ (k6_partfun1 @ X15))),
% 2.50/2.70      inference('demod', [status(thm)], ['127', '128'])).
% 2.50/2.70  thf('285', plain,
% 2.50/2.70      (![X0 : $i, X1 : $i]:
% 2.50/2.70         (((k5_relat_1 @ X0 @ X1)
% 2.50/2.70            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 2.50/2.70               (k5_relat_1 @ X0 @ X1)))
% 2.50/2.70          | ~ (v1_relat_1 @ X0)
% 2.50/2.70          | ~ (v1_relat_1 @ X1)
% 2.50/2.70          | ~ (v1_relat_1 @ X0))),
% 2.50/2.70      inference('demod', [status(thm)], ['283', '284'])).
% 2.50/2.70  thf('286', plain,
% 2.50/2.70      (![X0 : $i, X1 : $i]:
% 2.50/2.70         (~ (v1_relat_1 @ X1)
% 2.50/2.70          | ~ (v1_relat_1 @ X0)
% 2.50/2.70          | ((k5_relat_1 @ X0 @ X1)
% 2.50/2.70              = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 2.50/2.70                 (k5_relat_1 @ X0 @ X1))))),
% 2.50/2.70      inference('simplify', [status(thm)], ['285'])).
% 2.50/2.70  thf('287', plain,
% 2.50/2.70      (![X0 : $i]:
% 2.50/2.70         (((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 2.50/2.70            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 2.50/2.70          | ~ (v1_relat_1 @ X0)
% 2.50/2.70          | ~ (v1_relat_1 @ X0)
% 2.50/2.70          | ~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0))))),
% 2.50/2.70      inference('sup+', [status(thm)], ['280', '286'])).
% 2.50/2.70  thf('288', plain, (![X15 : $i]: (v1_relat_1 @ (k6_partfun1 @ X15))),
% 2.50/2.70      inference('demod', [status(thm)], ['127', '128'])).
% 2.50/2.70  thf('289', plain,
% 2.50/2.70      (![X0 : $i]:
% 2.50/2.70         (((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 2.50/2.70            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 2.50/2.70          | ~ (v1_relat_1 @ X0)
% 2.50/2.70          | ~ (v1_relat_1 @ X0))),
% 2.50/2.70      inference('demod', [status(thm)], ['287', '288'])).
% 2.50/2.70  thf('290', plain,
% 2.50/2.70      (![X0 : $i]:
% 2.50/2.70         (~ (v1_relat_1 @ X0)
% 2.50/2.70          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 2.50/2.70              = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0)))),
% 2.50/2.70      inference('simplify', [status(thm)], ['289'])).
% 2.50/2.70  thf('291', plain,
% 2.50/2.70      ((((k5_relat_1 @ (k4_relat_1 @ sk_C) @ 
% 2.50/2.70          (k6_partfun1 @ (k2_relat_1 @ (k4_relat_1 @ sk_C))))
% 2.50/2.70          = (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)) @ 
% 2.50/2.70             (k4_relat_1 @ sk_C)))
% 2.50/2.70        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 2.50/2.70      inference('sup+', [status(thm)], ['279', '290'])).
% 2.50/2.70  thf('292', plain, ((v1_relat_1 @ sk_C)),
% 2.50/2.70      inference('demod', [status(thm)], ['158', '159'])).
% 2.50/2.70  thf('293', plain,
% 2.50/2.70      (![X5 : $i]:
% 2.50/2.70         (((k1_relat_1 @ X5) = (k2_relat_1 @ (k4_relat_1 @ X5)))
% 2.50/2.70          | ~ (v1_relat_1 @ X5))),
% 2.50/2.70      inference('cnf', [status(esa)], [t37_relat_1])).
% 2.50/2.70  thf('294', plain,
% 2.50/2.70      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 2.50/2.70      inference('sup-', [status(thm)], ['292', '293'])).
% 2.50/2.70  thf('295', plain,
% 2.50/2.70      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 2.50/2.70      inference('sup-', [status(thm)], ['277', '278'])).
% 2.50/2.70  thf('296', plain,
% 2.50/2.70      (![X11 : $i]:
% 2.50/2.70         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X11)) @ X11) = (X11))
% 2.50/2.70          | ~ (v1_relat_1 @ X11))),
% 2.50/2.70      inference('demod', [status(thm)], ['123', '124'])).
% 2.50/2.70  thf('297', plain,
% 2.50/2.70      ((((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)) @ 
% 2.50/2.70          (k4_relat_1 @ sk_C)) = (k4_relat_1 @ sk_C))
% 2.50/2.70        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 2.50/2.70      inference('sup+', [status(thm)], ['295', '296'])).
% 2.50/2.70  thf('298', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 2.50/2.70      inference('demod', [status(thm)], ['189', '190', '191'])).
% 2.50/2.70  thf('299', plain,
% 2.50/2.70      (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)) @ (k4_relat_1 @ sk_C))
% 2.50/2.70         = (k4_relat_1 @ sk_C))),
% 2.50/2.70      inference('demod', [status(thm)], ['297', '298'])).
% 2.50/2.70  thf('300', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 2.50/2.70      inference('demod', [status(thm)], ['189', '190', '191'])).
% 2.50/2.70  thf('301', plain,
% 2.50/2.70      (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 2.50/2.70         = (k4_relat_1 @ sk_C))),
% 2.50/2.70      inference('demod', [status(thm)], ['291', '294', '299', '300'])).
% 2.50/2.70  thf('302', plain,
% 2.50/2.70      (((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 2.50/2.70      inference('simplify_reflect-', [status(thm)], ['239', '240'])).
% 2.50/2.70  thf('303', plain,
% 2.50/2.70      (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 2.50/2.70         = (k4_relat_1 @ sk_C))),
% 2.50/2.70      inference('demod', [status(thm)], ['301', '302'])).
% 2.50/2.70  thf('304', plain, ((v1_relat_1 @ sk_C)),
% 2.50/2.70      inference('demod', [status(thm)], ['158', '159'])).
% 2.50/2.70  thf('305', plain, ((v1_funct_1 @ sk_C)),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('306', plain, ((v2_funct_1 @ sk_C)),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('307', plain, ((v1_relat_1 @ sk_D)),
% 2.50/2.70      inference('demod', [status(thm)], ['2', '3'])).
% 2.50/2.70  thf('308', plain,
% 2.50/2.70      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (k4_relat_1 @ sk_C))),
% 2.50/2.70      inference('demod', [status(thm)],
% 2.50/2.70                ['274', '275', '276', '303', '304', '305', '306', '307'])).
% 2.50/2.70  thf('309', plain, ((v1_relat_1 @ sk_D)),
% 2.50/2.70      inference('demod', [status(thm)], ['2', '3'])).
% 2.50/2.70  thf('310', plain, (((k4_relat_1 @ sk_C) = (sk_D))),
% 2.50/2.70      inference('demod', [status(thm)], ['271', '308', '309'])).
% 2.50/2.70  thf('311', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 2.50/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.50/2.70  thf('312', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 2.50/2.70      inference('demod', [status(thm)], ['167', '168', '169'])).
% 2.50/2.70  thf('313', plain, (((sk_D) != (k4_relat_1 @ sk_C))),
% 2.50/2.70      inference('demod', [status(thm)], ['311', '312'])).
% 2.50/2.70  thf('314', plain, ($false),
% 2.50/2.70      inference('simplify_reflect-', [status(thm)], ['310', '313'])).
% 2.50/2.70  
% 2.50/2.70  % SZS output end Refutation
% 2.50/2.70  
% 2.50/2.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GWzPxAfiiN

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:57 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :  250 (5995 expanded)
%              Number of leaves         :   48 (1725 expanded)
%              Depth                    :   28
%              Number of atoms          : 2513 (162219 expanded)
%              Number of equality atoms :  187 (10929 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('3',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( ( k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29 )
        = ( k5_relat_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X21 @ X22 @ X24 @ X25 @ X20 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('21',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('22',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( X13 = X16 )
      | ~ ( r2_relset_1 @ X14 @ X15 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','23'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('25',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('26',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('27',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['24','27'])).

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

thf('29',plain,(
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

thf('30',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('31',plain,(
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
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
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
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('34',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('35',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('40',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['32','35','36','37','40'])).

thf('42',plain,(
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

thf('43',plain,(
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

thf('44',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','45','46','47','48'])).

thf('50',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['50','51'])).

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
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X4 ) @ X4 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('54',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('55',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X4 ) @ X4 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('57',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','58'])).

thf('60',plain,
    ( ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['52','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('62',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['38','39'])).

thf('65',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61','62','63','64'])).

thf('66',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['41','65'])).

thf('67',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('68',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('69',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
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

thf('71',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( v2_funct_2 @ X37 @ X39 )
      | ~ ( r2_relset_1 @ X39 @ X39 @ ( k1_partfun1 @ X39 @ X38 @ X38 @ X39 @ X40 @ X37 ) @ ( k6_partfun1 @ X39 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X38 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t29_funct_2])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) @ ( k6_partfun1 @ sk_A ) )
      | ( v2_funct_2 @ sk_D @ sk_A )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) @ ( k6_partfun1 @ sk_A ) )
      | ( v2_funct_2 @ sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['69','75'])).

thf('77',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('78',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( r2_relset_1 @ X14 @ X15 @ X13 @ X16 )
      | ( X13 != X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('79',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_relset_1 @ X14 @ X15 @ X16 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['76','80','81','82','83'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('85',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v2_funct_2 @ X19 @ X18 )
      | ( ( k2_relat_1 @ X19 )
        = X18 )
      | ~ ( v5_relat_1 @ X19 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('86',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( ( k2_relat_1 @ sk_D )
      = sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['33','34'])).

thf('88',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('89',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v5_relat_1 @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('90',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['86','87','90'])).

thf('92',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['66','91'])).

thf('93',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('95',plain,(
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

thf('96',plain,(
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

thf('97',plain,(
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
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['94','100'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('102',plain,(
    ! [X3: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('103',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('104',plain,(
    ! [X3: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X3 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['101','104','105','106','107','108'])).

thf('110',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X43: $i,X44: $i] :
      ( ( X43 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('112',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X41: $i,X42: $i] :
      ( ( v2_funct_1 @ X42 )
      | ~ ( zip_tseitin_0 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('116',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['93','116'])).

thf('118',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ X4 @ ( k2_funct_1 @ X4 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('119',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('120',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ X4 @ ( k2_funct_1 @ X4 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
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

thf('123',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('130',plain,(
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

thf('131',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( r2_relset_1 @ X34 @ X34 @ ( k1_partfun1 @ X34 @ X35 @ X35 @ X34 @ X33 @ X36 ) @ ( k6_partfun1 @ X34 ) )
      | ( ( k2_relset_1 @ X35 @ X34 @ X36 )
        = X34 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['132','133','134'])).

thf('136',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['129','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','79'])).

thf('138',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['136','137','138','139','140'])).

thf('142',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['128','141'])).

thf('143',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['114','115'])).

thf('145',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['120','145'])).

thf('147',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['33','34'])).

thf('148',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['114','115'])).

thf('150',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['146','147','148','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('152',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('154',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['117','154'])).

thf('156',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ X4 @ ( k2_funct_1 @ X4 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('158',plain,(
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
    inference(demod,[status(thm)],['29','30'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ( ( k2_relat_1 @ sk_D )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_D ) ) )
    | ( sk_D
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['156','160'])).

thf('162',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('163',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61','62','63','64'])).

thf('164',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['33','34'])).

thf('165',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['114','115'])).

thf('167',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['155'])).

thf('168',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['38','39'])).

thf('169',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['155'])).

thf('170',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['155'])).

thf('172',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['86','87','90'])).

thf('174',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['155'])).

thf('175',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ X4 @ ( k2_funct_1 @ X4 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('176',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
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

thf('178',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['178','179','180','181','182'])).

thf('184',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['184','185'])).

thf('187',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['175','186'])).

thf('188',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['38','39'])).

thf('189',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['187','188','189','190'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('193',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['191','192'])).

thf('194',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('195',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['193','194'])).

thf('196',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['155'])).

thf('197',plain,
    ( ( ( k6_partfun1 @ sk_B )
     != ( k6_partfun1 @ sk_B ) )
    | ( sk_A != sk_A )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['161','162','163','164','165','166','167','168','169','170','171','172','173','174','195','196'])).

thf('198',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['197'])).

thf('199',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['198','199'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GWzPxAfiiN
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:15:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.20/1.44  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.20/1.44  % Solved by: fo/fo7.sh
% 1.20/1.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.20/1.44  % done 1623 iterations in 0.960s
% 1.20/1.44  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.20/1.44  % SZS output start Refutation
% 1.20/1.44  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.20/1.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.20/1.44  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.20/1.44  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.20/1.44  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.20/1.44  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.20/1.44  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.20/1.44  thf(sk_C_type, type, sk_C: $i).
% 1.20/1.44  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.20/1.44  thf(sk_B_type, type, sk_B: $i).
% 1.20/1.44  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.20/1.44  thf(sk_A_type, type, sk_A: $i).
% 1.20/1.44  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 1.20/1.44  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.20/1.44  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.20/1.44  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 1.20/1.44  thf(sk_D_type, type, sk_D: $i).
% 1.20/1.44  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.20/1.44  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.20/1.44  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.20/1.44  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.20/1.44  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.20/1.44  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.20/1.44  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.20/1.44  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.20/1.44  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.20/1.44  thf(t36_funct_2, conjecture,
% 1.20/1.44    (![A:$i,B:$i,C:$i]:
% 1.20/1.44     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.20/1.44         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.20/1.44       ( ![D:$i]:
% 1.20/1.44         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.20/1.44             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.20/1.44           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.20/1.44               ( r2_relset_1 @
% 1.20/1.44                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.20/1.44                 ( k6_partfun1 @ A ) ) & 
% 1.20/1.44               ( v2_funct_1 @ C ) ) =>
% 1.20/1.44             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.20/1.44               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.20/1.44  thf(zf_stmt_0, negated_conjecture,
% 1.20/1.44    (~( ![A:$i,B:$i,C:$i]:
% 1.20/1.44        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.20/1.44            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.20/1.44          ( ![D:$i]:
% 1.20/1.44            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.20/1.44                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.20/1.44              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.20/1.44                  ( r2_relset_1 @
% 1.20/1.44                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.20/1.44                    ( k6_partfun1 @ A ) ) & 
% 1.20/1.44                  ( v2_funct_1 @ C ) ) =>
% 1.20/1.44                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.20/1.44                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.20/1.44    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.20/1.44  thf('0', plain,
% 1.20/1.44      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.20/1.44        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.20/1.44        (k6_partfun1 @ sk_A))),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('1', plain,
% 1.20/1.44      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('2', plain,
% 1.20/1.44      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf(redefinition_k1_partfun1, axiom,
% 1.20/1.44    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.20/1.44     ( ( ( v1_funct_1 @ E ) & 
% 1.20/1.44         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.20/1.44         ( v1_funct_1 @ F ) & 
% 1.20/1.44         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.20/1.44       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.20/1.44  thf('3', plain,
% 1.20/1.44      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.20/1.44         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 1.20/1.44          | ~ (v1_funct_1 @ X26)
% 1.20/1.44          | ~ (v1_funct_1 @ X29)
% 1.20/1.44          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.20/1.44          | ((k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29)
% 1.20/1.44              = (k5_relat_1 @ X26 @ X29)))),
% 1.20/1.44      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.20/1.44  thf('4', plain,
% 1.20/1.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.44         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.20/1.44            = (k5_relat_1 @ sk_C @ X0))
% 1.20/1.44          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.20/1.44          | ~ (v1_funct_1 @ X0)
% 1.20/1.44          | ~ (v1_funct_1 @ sk_C))),
% 1.20/1.44      inference('sup-', [status(thm)], ['2', '3'])).
% 1.20/1.44  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('6', plain,
% 1.20/1.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.44         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.20/1.44            = (k5_relat_1 @ sk_C @ X0))
% 1.20/1.44          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.20/1.44          | ~ (v1_funct_1 @ X0))),
% 1.20/1.44      inference('demod', [status(thm)], ['4', '5'])).
% 1.20/1.44  thf('7', plain,
% 1.20/1.44      ((~ (v1_funct_1 @ sk_D)
% 1.20/1.44        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.20/1.44            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.20/1.44      inference('sup-', [status(thm)], ['1', '6'])).
% 1.20/1.44  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('9', plain,
% 1.20/1.44      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.20/1.44         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.20/1.44      inference('demod', [status(thm)], ['7', '8'])).
% 1.20/1.44  thf('10', plain,
% 1.20/1.44      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.20/1.44        (k6_partfun1 @ sk_A))),
% 1.20/1.44      inference('demod', [status(thm)], ['0', '9'])).
% 1.20/1.44  thf('11', plain,
% 1.20/1.44      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('12', plain,
% 1.20/1.44      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf(dt_k1_partfun1, axiom,
% 1.20/1.44    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.20/1.44     ( ( ( v1_funct_1 @ E ) & 
% 1.20/1.44         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.20/1.44         ( v1_funct_1 @ F ) & 
% 1.20/1.44         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.20/1.44       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.20/1.44         ( m1_subset_1 @
% 1.20/1.44           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.20/1.44           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.20/1.44  thf('13', plain,
% 1.20/1.44      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 1.20/1.44         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 1.20/1.44          | ~ (v1_funct_1 @ X20)
% 1.20/1.44          | ~ (v1_funct_1 @ X23)
% 1.20/1.44          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 1.20/1.44          | (m1_subset_1 @ (k1_partfun1 @ X21 @ X22 @ X24 @ X25 @ X20 @ X23) @ 
% 1.20/1.44             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X25))))),
% 1.20/1.44      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.20/1.44  thf('14', plain,
% 1.20/1.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.44         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.20/1.44           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.20/1.44          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.20/1.44          | ~ (v1_funct_1 @ X1)
% 1.20/1.44          | ~ (v1_funct_1 @ sk_C))),
% 1.20/1.44      inference('sup-', [status(thm)], ['12', '13'])).
% 1.20/1.44  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('16', plain,
% 1.20/1.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.44         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.20/1.44           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.20/1.44          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.20/1.44          | ~ (v1_funct_1 @ X1))),
% 1.20/1.44      inference('demod', [status(thm)], ['14', '15'])).
% 1.20/1.44  thf('17', plain,
% 1.20/1.44      ((~ (v1_funct_1 @ sk_D)
% 1.20/1.44        | (m1_subset_1 @ 
% 1.20/1.44           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.20/1.44           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.20/1.44      inference('sup-', [status(thm)], ['11', '16'])).
% 1.20/1.44  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('19', plain,
% 1.20/1.44      ((m1_subset_1 @ 
% 1.20/1.44        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.20/1.44        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.20/1.44      inference('demod', [status(thm)], ['17', '18'])).
% 1.20/1.44  thf('20', plain,
% 1.20/1.44      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.20/1.44         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.20/1.44      inference('demod', [status(thm)], ['7', '8'])).
% 1.20/1.44  thf('21', plain,
% 1.20/1.44      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.20/1.44        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.20/1.44      inference('demod', [status(thm)], ['19', '20'])).
% 1.20/1.44  thf(redefinition_r2_relset_1, axiom,
% 1.20/1.44    (![A:$i,B:$i,C:$i,D:$i]:
% 1.20/1.44     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.20/1.44         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.20/1.44       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.20/1.44  thf('22', plain,
% 1.20/1.44      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 1.20/1.44         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 1.20/1.44          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 1.20/1.44          | ((X13) = (X16))
% 1.20/1.44          | ~ (r2_relset_1 @ X14 @ X15 @ X13 @ X16))),
% 1.20/1.44      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.20/1.44  thf('23', plain,
% 1.20/1.44      (![X0 : $i]:
% 1.20/1.44         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 1.20/1.44          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 1.20/1.44          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.20/1.44      inference('sup-', [status(thm)], ['21', '22'])).
% 1.20/1.44  thf('24', plain,
% 1.20/1.44      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.20/1.44           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.20/1.44        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 1.20/1.44      inference('sup-', [status(thm)], ['10', '23'])).
% 1.20/1.44  thf(t29_relset_1, axiom,
% 1.20/1.44    (![A:$i]:
% 1.20/1.44     ( m1_subset_1 @
% 1.20/1.44       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.20/1.44  thf('25', plain,
% 1.20/1.44      (![X17 : $i]:
% 1.20/1.44         (m1_subset_1 @ (k6_relat_1 @ X17) @ 
% 1.20/1.44          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))),
% 1.20/1.44      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.20/1.44  thf(redefinition_k6_partfun1, axiom,
% 1.20/1.44    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.20/1.44  thf('26', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 1.20/1.44      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.20/1.44  thf('27', plain,
% 1.20/1.44      (![X17 : $i]:
% 1.20/1.44         (m1_subset_1 @ (k6_partfun1 @ X17) @ 
% 1.20/1.44          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))),
% 1.20/1.44      inference('demod', [status(thm)], ['25', '26'])).
% 1.20/1.44  thf('28', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.20/1.44      inference('demod', [status(thm)], ['24', '27'])).
% 1.20/1.44  thf(t64_funct_1, axiom,
% 1.20/1.44    (![A:$i]:
% 1.20/1.44     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.20/1.44       ( ![B:$i]:
% 1.20/1.44         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.20/1.44           ( ( ( v2_funct_1 @ A ) & 
% 1.20/1.44               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 1.20/1.44               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 1.20/1.44             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.20/1.44  thf('29', plain,
% 1.20/1.44      (![X5 : $i, X6 : $i]:
% 1.20/1.44         (~ (v1_relat_1 @ X5)
% 1.20/1.44          | ~ (v1_funct_1 @ X5)
% 1.20/1.44          | ((X5) = (k2_funct_1 @ X6))
% 1.20/1.44          | ((k5_relat_1 @ X5 @ X6) != (k6_relat_1 @ (k2_relat_1 @ X6)))
% 1.20/1.44          | ((k2_relat_1 @ X5) != (k1_relat_1 @ X6))
% 1.20/1.44          | ~ (v2_funct_1 @ X6)
% 1.20/1.44          | ~ (v1_funct_1 @ X6)
% 1.20/1.44          | ~ (v1_relat_1 @ X6))),
% 1.20/1.44      inference('cnf', [status(esa)], [t64_funct_1])).
% 1.20/1.44  thf('30', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 1.20/1.44      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.20/1.44  thf('31', plain,
% 1.20/1.44      (![X5 : $i, X6 : $i]:
% 1.20/1.44         (~ (v1_relat_1 @ X5)
% 1.20/1.44          | ~ (v1_funct_1 @ X5)
% 1.20/1.44          | ((X5) = (k2_funct_1 @ X6))
% 1.20/1.44          | ((k5_relat_1 @ X5 @ X6) != (k6_partfun1 @ (k2_relat_1 @ X6)))
% 1.20/1.44          | ((k2_relat_1 @ X5) != (k1_relat_1 @ X6))
% 1.20/1.44          | ~ (v2_funct_1 @ X6)
% 1.20/1.44          | ~ (v1_funct_1 @ X6)
% 1.20/1.44          | ~ (v1_relat_1 @ X6))),
% 1.20/1.44      inference('demod', [status(thm)], ['29', '30'])).
% 1.20/1.44  thf('32', plain,
% 1.20/1.44      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 1.20/1.44        | ~ (v1_relat_1 @ sk_D)
% 1.20/1.44        | ~ (v1_funct_1 @ sk_D)
% 1.20/1.44        | ~ (v2_funct_1 @ sk_D)
% 1.20/1.44        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 1.20/1.44        | ((sk_C) = (k2_funct_1 @ sk_D))
% 1.20/1.44        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.44        | ~ (v1_relat_1 @ sk_C))),
% 1.20/1.44      inference('sup-', [status(thm)], ['28', '31'])).
% 1.20/1.44  thf('33', plain,
% 1.20/1.44      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf(cc1_relset_1, axiom,
% 1.20/1.44    (![A:$i,B:$i,C:$i]:
% 1.20/1.44     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.20/1.44       ( v1_relat_1 @ C ) ))).
% 1.20/1.44  thf('34', plain,
% 1.20/1.44      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.20/1.44         ((v1_relat_1 @ X7)
% 1.20/1.44          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 1.20/1.44      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.20/1.44  thf('35', plain, ((v1_relat_1 @ sk_D)),
% 1.20/1.44      inference('sup-', [status(thm)], ['33', '34'])).
% 1.20/1.44  thf('36', plain, ((v1_funct_1 @ sk_D)),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('37', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('38', plain,
% 1.20/1.44      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('39', plain,
% 1.20/1.44      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.20/1.44         ((v1_relat_1 @ X7)
% 1.20/1.44          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 1.20/1.44      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.20/1.44  thf('40', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.44      inference('sup-', [status(thm)], ['38', '39'])).
% 1.20/1.44  thf('41', plain,
% 1.20/1.44      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 1.20/1.44        | ~ (v2_funct_1 @ sk_D)
% 1.20/1.44        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 1.20/1.44        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 1.20/1.44      inference('demod', [status(thm)], ['32', '35', '36', '37', '40'])).
% 1.20/1.44  thf('42', plain,
% 1.20/1.44      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf(t35_funct_2, axiom,
% 1.20/1.44    (![A:$i,B:$i,C:$i]:
% 1.20/1.44     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.20/1.44         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.20/1.44       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.20/1.44         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.20/1.44           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 1.20/1.44             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 1.20/1.44  thf('43', plain,
% 1.20/1.44      (![X50 : $i, X51 : $i, X52 : $i]:
% 1.20/1.44         (((X50) = (k1_xboole_0))
% 1.20/1.44          | ~ (v1_funct_1 @ X51)
% 1.20/1.44          | ~ (v1_funct_2 @ X51 @ X52 @ X50)
% 1.20/1.44          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 1.20/1.44          | ((k5_relat_1 @ (k2_funct_1 @ X51) @ X51) = (k6_partfun1 @ X50))
% 1.20/1.44          | ~ (v2_funct_1 @ X51)
% 1.20/1.44          | ((k2_relset_1 @ X52 @ X50 @ X51) != (X50)))),
% 1.20/1.44      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.20/1.44  thf('44', plain,
% 1.20/1.44      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.20/1.44        | ~ (v2_funct_1 @ sk_C)
% 1.20/1.44        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 1.20/1.44        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.20/1.44        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.44        | ((sk_B) = (k1_xboole_0)))),
% 1.20/1.44      inference('sup-', [status(thm)], ['42', '43'])).
% 1.20/1.44  thf('45', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('46', plain, ((v2_funct_1 @ sk_C)),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('47', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('48', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('49', plain,
% 1.20/1.44      ((((sk_B) != (sk_B))
% 1.20/1.44        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 1.20/1.44        | ((sk_B) = (k1_xboole_0)))),
% 1.20/1.44      inference('demod', [status(thm)], ['44', '45', '46', '47', '48'])).
% 1.20/1.44  thf('50', plain,
% 1.20/1.44      ((((sk_B) = (k1_xboole_0))
% 1.20/1.44        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 1.20/1.44      inference('simplify', [status(thm)], ['49'])).
% 1.20/1.44  thf('51', plain, (((sk_B) != (k1_xboole_0))),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('52', plain,
% 1.20/1.44      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 1.20/1.44      inference('simplify_reflect-', [status(thm)], ['50', '51'])).
% 1.20/1.44  thf(t61_funct_1, axiom,
% 1.20/1.44    (![A:$i]:
% 1.20/1.44     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.20/1.44       ( ( v2_funct_1 @ A ) =>
% 1.20/1.44         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.20/1.44             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.20/1.44           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.20/1.44             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.20/1.44  thf('53', plain,
% 1.20/1.44      (![X4 : $i]:
% 1.20/1.44         (~ (v2_funct_1 @ X4)
% 1.20/1.44          | ((k5_relat_1 @ (k2_funct_1 @ X4) @ X4)
% 1.20/1.44              = (k6_relat_1 @ (k2_relat_1 @ X4)))
% 1.20/1.44          | ~ (v1_funct_1 @ X4)
% 1.20/1.44          | ~ (v1_relat_1 @ X4))),
% 1.20/1.44      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.20/1.44  thf('54', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 1.20/1.44      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.20/1.44  thf('55', plain,
% 1.20/1.44      (![X4 : $i]:
% 1.20/1.44         (~ (v2_funct_1 @ X4)
% 1.20/1.44          | ((k5_relat_1 @ (k2_funct_1 @ X4) @ X4)
% 1.20/1.44              = (k6_partfun1 @ (k2_relat_1 @ X4)))
% 1.20/1.44          | ~ (v1_funct_1 @ X4)
% 1.20/1.44          | ~ (v1_relat_1 @ X4))),
% 1.20/1.44      inference('demod', [status(thm)], ['53', '54'])).
% 1.20/1.44  thf(t71_relat_1, axiom,
% 1.20/1.44    (![A:$i]:
% 1.20/1.44     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.20/1.44       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.20/1.44  thf('56', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 1.20/1.44      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.20/1.44  thf('57', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 1.20/1.44      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.20/1.44  thf('58', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 1.20/1.44      inference('demod', [status(thm)], ['56', '57'])).
% 1.20/1.44  thf('59', plain,
% 1.20/1.44      (![X0 : $i]:
% 1.20/1.44         (((k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 1.20/1.44            = (k2_relat_1 @ X0))
% 1.20/1.44          | ~ (v1_relat_1 @ X0)
% 1.20/1.44          | ~ (v1_funct_1 @ X0)
% 1.20/1.44          | ~ (v2_funct_1 @ X0))),
% 1.20/1.44      inference('sup+', [status(thm)], ['55', '58'])).
% 1.20/1.44  thf('60', plain,
% 1.20/1.44      ((((k1_relat_1 @ (k6_partfun1 @ sk_B)) = (k2_relat_1 @ sk_C))
% 1.20/1.44        | ~ (v2_funct_1 @ sk_C)
% 1.20/1.44        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.44        | ~ (v1_relat_1 @ sk_C))),
% 1.20/1.44      inference('sup+', [status(thm)], ['52', '59'])).
% 1.20/1.44  thf('61', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 1.20/1.44      inference('demod', [status(thm)], ['56', '57'])).
% 1.20/1.44  thf('62', plain, ((v2_funct_1 @ sk_C)),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('63', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('64', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.44      inference('sup-', [status(thm)], ['38', '39'])).
% 1.20/1.44  thf('65', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 1.20/1.44      inference('demod', [status(thm)], ['60', '61', '62', '63', '64'])).
% 1.20/1.44  thf('66', plain,
% 1.20/1.44      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 1.20/1.44        | ~ (v2_funct_1 @ sk_D)
% 1.20/1.44        | ((sk_B) != (k1_relat_1 @ sk_D))
% 1.20/1.44        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 1.20/1.44      inference('demod', [status(thm)], ['41', '65'])).
% 1.20/1.44  thf('67', plain,
% 1.20/1.44      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.20/1.44         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.20/1.44      inference('demod', [status(thm)], ['7', '8'])).
% 1.20/1.44  thf('68', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.20/1.44      inference('demod', [status(thm)], ['24', '27'])).
% 1.20/1.44  thf('69', plain,
% 1.20/1.44      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.20/1.44         = (k6_partfun1 @ sk_A))),
% 1.20/1.44      inference('demod', [status(thm)], ['67', '68'])).
% 1.20/1.44  thf('70', plain,
% 1.20/1.44      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf(t29_funct_2, axiom,
% 1.20/1.44    (![A:$i,B:$i,C:$i]:
% 1.20/1.44     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.20/1.44         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.20/1.44       ( ![D:$i]:
% 1.20/1.44         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.20/1.44             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.20/1.44           ( ( r2_relset_1 @
% 1.20/1.44               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.20/1.44               ( k6_partfun1 @ A ) ) =>
% 1.20/1.44             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 1.20/1.44  thf('71', plain,
% 1.20/1.44      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.20/1.44         (~ (v1_funct_1 @ X37)
% 1.20/1.44          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 1.20/1.44          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 1.20/1.44          | (v2_funct_2 @ X37 @ X39)
% 1.20/1.44          | ~ (r2_relset_1 @ X39 @ X39 @ 
% 1.20/1.44               (k1_partfun1 @ X39 @ X38 @ X38 @ X39 @ X40 @ X37) @ 
% 1.20/1.44               (k6_partfun1 @ X39))
% 1.20/1.44          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 1.20/1.44          | ~ (v1_funct_2 @ X40 @ X39 @ X38)
% 1.20/1.44          | ~ (v1_funct_1 @ X40))),
% 1.20/1.44      inference('cnf', [status(esa)], [t29_funct_2])).
% 1.20/1.44  thf('72', plain,
% 1.20/1.44      (![X0 : $i]:
% 1.20/1.44         (~ (v1_funct_1 @ X0)
% 1.20/1.44          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_B)
% 1.20/1.44          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.20/1.44          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.20/1.44               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ X0 @ sk_D) @ 
% 1.20/1.44               (k6_partfun1 @ sk_A))
% 1.20/1.44          | (v2_funct_2 @ sk_D @ sk_A)
% 1.20/1.44          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.20/1.44          | ~ (v1_funct_1 @ sk_D))),
% 1.20/1.44      inference('sup-', [status(thm)], ['70', '71'])).
% 1.20/1.44  thf('73', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('74', plain, ((v1_funct_1 @ sk_D)),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('75', plain,
% 1.20/1.44      (![X0 : $i]:
% 1.20/1.44         (~ (v1_funct_1 @ X0)
% 1.20/1.44          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_B)
% 1.20/1.44          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.20/1.44          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.20/1.44               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ X0 @ sk_D) @ 
% 1.20/1.44               (k6_partfun1 @ sk_A))
% 1.20/1.44          | (v2_funct_2 @ sk_D @ sk_A))),
% 1.20/1.44      inference('demod', [status(thm)], ['72', '73', '74'])).
% 1.20/1.44  thf('76', plain,
% 1.20/1.44      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 1.20/1.44           (k6_partfun1 @ sk_A))
% 1.20/1.44        | (v2_funct_2 @ sk_D @ sk_A)
% 1.20/1.44        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.20/1.44        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.20/1.44        | ~ (v1_funct_1 @ sk_C))),
% 1.20/1.44      inference('sup-', [status(thm)], ['69', '75'])).
% 1.20/1.44  thf('77', plain,
% 1.20/1.44      (![X17 : $i]:
% 1.20/1.44         (m1_subset_1 @ (k6_partfun1 @ X17) @ 
% 1.20/1.44          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X17)))),
% 1.20/1.44      inference('demod', [status(thm)], ['25', '26'])).
% 1.20/1.44  thf('78', plain,
% 1.20/1.44      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 1.20/1.44         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 1.20/1.44          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 1.20/1.44          | (r2_relset_1 @ X14 @ X15 @ X13 @ X16)
% 1.20/1.44          | ((X13) != (X16)))),
% 1.20/1.44      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.20/1.44  thf('79', plain,
% 1.20/1.44      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.20/1.44         ((r2_relset_1 @ X14 @ X15 @ X16 @ X16)
% 1.20/1.44          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.20/1.44      inference('simplify', [status(thm)], ['78'])).
% 1.20/1.44  thf('80', plain,
% 1.20/1.44      (![X0 : $i]:
% 1.20/1.44         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 1.20/1.44      inference('sup-', [status(thm)], ['77', '79'])).
% 1.20/1.44  thf('81', plain,
% 1.20/1.44      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('82', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('83', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('84', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 1.20/1.44      inference('demod', [status(thm)], ['76', '80', '81', '82', '83'])).
% 1.20/1.44  thf(d3_funct_2, axiom,
% 1.20/1.44    (![A:$i,B:$i]:
% 1.20/1.44     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 1.20/1.44       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 1.20/1.44  thf('85', plain,
% 1.20/1.44      (![X18 : $i, X19 : $i]:
% 1.20/1.44         (~ (v2_funct_2 @ X19 @ X18)
% 1.20/1.44          | ((k2_relat_1 @ X19) = (X18))
% 1.20/1.44          | ~ (v5_relat_1 @ X19 @ X18)
% 1.20/1.44          | ~ (v1_relat_1 @ X19))),
% 1.20/1.44      inference('cnf', [status(esa)], [d3_funct_2])).
% 1.20/1.44  thf('86', plain,
% 1.20/1.44      ((~ (v1_relat_1 @ sk_D)
% 1.20/1.44        | ~ (v5_relat_1 @ sk_D @ sk_A)
% 1.20/1.44        | ((k2_relat_1 @ sk_D) = (sk_A)))),
% 1.20/1.44      inference('sup-', [status(thm)], ['84', '85'])).
% 1.20/1.44  thf('87', plain, ((v1_relat_1 @ sk_D)),
% 1.20/1.44      inference('sup-', [status(thm)], ['33', '34'])).
% 1.20/1.44  thf('88', plain,
% 1.20/1.44      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf(cc2_relset_1, axiom,
% 1.20/1.44    (![A:$i,B:$i,C:$i]:
% 1.20/1.44     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.20/1.44       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.20/1.44  thf('89', plain,
% 1.20/1.44      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.20/1.44         ((v5_relat_1 @ X10 @ X12)
% 1.20/1.44          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 1.20/1.44      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.20/1.44  thf('90', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 1.20/1.44      inference('sup-', [status(thm)], ['88', '89'])).
% 1.20/1.44  thf('91', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.20/1.44      inference('demod', [status(thm)], ['86', '87', '90'])).
% 1.20/1.44  thf('92', plain,
% 1.20/1.44      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 1.20/1.44        | ~ (v2_funct_1 @ sk_D)
% 1.20/1.44        | ((sk_B) != (k1_relat_1 @ sk_D))
% 1.20/1.44        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 1.20/1.44      inference('demod', [status(thm)], ['66', '91'])).
% 1.20/1.44  thf('93', plain,
% 1.20/1.44      ((((sk_C) = (k2_funct_1 @ sk_D))
% 1.20/1.44        | ((sk_B) != (k1_relat_1 @ sk_D))
% 1.20/1.44        | ~ (v2_funct_1 @ sk_D))),
% 1.20/1.44      inference('simplify', [status(thm)], ['92'])).
% 1.20/1.44  thf('94', plain,
% 1.20/1.44      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.20/1.44         = (k6_partfun1 @ sk_A))),
% 1.20/1.44      inference('demod', [status(thm)], ['67', '68'])).
% 1.20/1.44  thf('95', plain,
% 1.20/1.44      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf(t30_funct_2, axiom,
% 1.20/1.44    (![A:$i,B:$i,C:$i,D:$i]:
% 1.20/1.44     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.20/1.44         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 1.20/1.44       ( ![E:$i]:
% 1.20/1.44         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 1.20/1.44             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 1.20/1.44           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 1.20/1.44               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 1.20/1.44             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 1.20/1.44               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 1.20/1.44  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 1.20/1.44  thf(zf_stmt_2, axiom,
% 1.20/1.44    (![C:$i,B:$i]:
% 1.20/1.44     ( ( zip_tseitin_1 @ C @ B ) =>
% 1.20/1.44       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 1.20/1.44  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.20/1.44  thf(zf_stmt_4, axiom,
% 1.20/1.44    (![E:$i,D:$i]:
% 1.20/1.44     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 1.20/1.44  thf(zf_stmt_5, axiom,
% 1.20/1.44    (![A:$i,B:$i,C:$i,D:$i]:
% 1.20/1.44     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.20/1.44         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.20/1.44       ( ![E:$i]:
% 1.20/1.44         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.20/1.44             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.20/1.44           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 1.20/1.44               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 1.20/1.44             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 1.20/1.44  thf('96', plain,
% 1.20/1.44      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 1.20/1.44         (~ (v1_funct_1 @ X45)
% 1.20/1.44          | ~ (v1_funct_2 @ X45 @ X46 @ X47)
% 1.20/1.44          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 1.20/1.44          | (zip_tseitin_0 @ X45 @ X48)
% 1.20/1.44          | ~ (v2_funct_1 @ (k1_partfun1 @ X49 @ X46 @ X46 @ X47 @ X48 @ X45))
% 1.20/1.44          | (zip_tseitin_1 @ X47 @ X46)
% 1.20/1.44          | ((k2_relset_1 @ X49 @ X46 @ X48) != (X46))
% 1.20/1.44          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X46)))
% 1.20/1.44          | ~ (v1_funct_2 @ X48 @ X49 @ X46)
% 1.20/1.44          | ~ (v1_funct_1 @ X48))),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.20/1.44  thf('97', plain,
% 1.20/1.44      (![X0 : $i, X1 : $i]:
% 1.20/1.44         (~ (v1_funct_1 @ X0)
% 1.20/1.44          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.20/1.44          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.20/1.44          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.20/1.44          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.20/1.44          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.20/1.44          | (zip_tseitin_0 @ sk_D @ X0)
% 1.20/1.44          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.20/1.44          | ~ (v1_funct_1 @ sk_D))),
% 1.20/1.44      inference('sup-', [status(thm)], ['95', '96'])).
% 1.20/1.44  thf('98', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('99', plain, ((v1_funct_1 @ sk_D)),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('100', plain,
% 1.20/1.44      (![X0 : $i, X1 : $i]:
% 1.20/1.44         (~ (v1_funct_1 @ X0)
% 1.20/1.44          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.20/1.44          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.20/1.44          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.20/1.44          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.20/1.44          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.20/1.44          | (zip_tseitin_0 @ sk_D @ X0))),
% 1.20/1.44      inference('demod', [status(thm)], ['97', '98', '99'])).
% 1.20/1.44  thf('101', plain,
% 1.20/1.44      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 1.20/1.44        | (zip_tseitin_0 @ sk_D @ sk_C)
% 1.20/1.44        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.20/1.44        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.20/1.44        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.20/1.44        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.20/1.44        | ~ (v1_funct_1 @ sk_C))),
% 1.20/1.44      inference('sup-', [status(thm)], ['94', '100'])).
% 1.20/1.44  thf(fc4_funct_1, axiom,
% 1.20/1.44    (![A:$i]:
% 1.20/1.44     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.20/1.44       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.20/1.44  thf('102', plain, (![X3 : $i]: (v2_funct_1 @ (k6_relat_1 @ X3))),
% 1.20/1.44      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.20/1.44  thf('103', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 1.20/1.44      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.20/1.44  thf('104', plain, (![X3 : $i]: (v2_funct_1 @ (k6_partfun1 @ X3))),
% 1.20/1.44      inference('demod', [status(thm)], ['102', '103'])).
% 1.20/1.44  thf('105', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('106', plain,
% 1.20/1.44      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('107', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('108', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('109', plain,
% 1.20/1.44      (((zip_tseitin_0 @ sk_D @ sk_C)
% 1.20/1.44        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.20/1.44        | ((sk_B) != (sk_B)))),
% 1.20/1.44      inference('demod', [status(thm)],
% 1.20/1.44                ['101', '104', '105', '106', '107', '108'])).
% 1.20/1.44  thf('110', plain,
% 1.20/1.44      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 1.20/1.44      inference('simplify', [status(thm)], ['109'])).
% 1.20/1.44  thf('111', plain,
% 1.20/1.44      (![X43 : $i, X44 : $i]:
% 1.20/1.44         (((X43) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X43 @ X44))),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.20/1.44  thf('112', plain,
% 1.20/1.44      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 1.20/1.44      inference('sup-', [status(thm)], ['110', '111'])).
% 1.20/1.44  thf('113', plain, (((sk_A) != (k1_xboole_0))),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('114', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 1.20/1.44      inference('simplify_reflect-', [status(thm)], ['112', '113'])).
% 1.20/1.44  thf('115', plain,
% 1.20/1.44      (![X41 : $i, X42 : $i]:
% 1.20/1.44         ((v2_funct_1 @ X42) | ~ (zip_tseitin_0 @ X42 @ X41))),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.20/1.44  thf('116', plain, ((v2_funct_1 @ sk_D)),
% 1.20/1.44      inference('sup-', [status(thm)], ['114', '115'])).
% 1.20/1.44  thf('117', plain,
% 1.20/1.44      ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (k1_relat_1 @ sk_D)))),
% 1.20/1.44      inference('demod', [status(thm)], ['93', '116'])).
% 1.20/1.44  thf('118', plain,
% 1.20/1.44      (![X4 : $i]:
% 1.20/1.44         (~ (v2_funct_1 @ X4)
% 1.20/1.44          | ((k5_relat_1 @ X4 @ (k2_funct_1 @ X4))
% 1.20/1.44              = (k6_relat_1 @ (k1_relat_1 @ X4)))
% 1.20/1.44          | ~ (v1_funct_1 @ X4)
% 1.20/1.44          | ~ (v1_relat_1 @ X4))),
% 1.20/1.44      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.20/1.44  thf('119', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 1.20/1.44      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.20/1.44  thf('120', plain,
% 1.20/1.44      (![X4 : $i]:
% 1.20/1.44         (~ (v2_funct_1 @ X4)
% 1.20/1.44          | ((k5_relat_1 @ X4 @ (k2_funct_1 @ X4))
% 1.20/1.44              = (k6_partfun1 @ (k1_relat_1 @ X4)))
% 1.20/1.44          | ~ (v1_funct_1 @ X4)
% 1.20/1.44          | ~ (v1_relat_1 @ X4))),
% 1.20/1.44      inference('demod', [status(thm)], ['118', '119'])).
% 1.20/1.44  thf('121', plain,
% 1.20/1.44      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('122', plain,
% 1.20/1.44      (![X50 : $i, X51 : $i, X52 : $i]:
% 1.20/1.44         (((X50) = (k1_xboole_0))
% 1.20/1.44          | ~ (v1_funct_1 @ X51)
% 1.20/1.44          | ~ (v1_funct_2 @ X51 @ X52 @ X50)
% 1.20/1.44          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 1.20/1.44          | ((k5_relat_1 @ X51 @ (k2_funct_1 @ X51)) = (k6_partfun1 @ X52))
% 1.20/1.44          | ~ (v2_funct_1 @ X51)
% 1.20/1.44          | ((k2_relset_1 @ X52 @ X50 @ X51) != (X50)))),
% 1.20/1.44      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.20/1.44  thf('123', plain,
% 1.20/1.44      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 1.20/1.44        | ~ (v2_funct_1 @ sk_D)
% 1.20/1.44        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.20/1.44        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.20/1.44        | ~ (v1_funct_1 @ sk_D)
% 1.20/1.44        | ((sk_A) = (k1_xboole_0)))),
% 1.20/1.44      inference('sup-', [status(thm)], ['121', '122'])).
% 1.20/1.44  thf('124', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('125', plain, ((v1_funct_1 @ sk_D)),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('126', plain,
% 1.20/1.44      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 1.20/1.44        | ~ (v2_funct_1 @ sk_D)
% 1.20/1.44        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.20/1.44        | ((sk_A) = (k1_xboole_0)))),
% 1.20/1.44      inference('demod', [status(thm)], ['123', '124', '125'])).
% 1.20/1.44  thf('127', plain, (((sk_A) != (k1_xboole_0))),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('128', plain,
% 1.20/1.44      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 1.20/1.44        | ~ (v2_funct_1 @ sk_D)
% 1.20/1.44        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 1.20/1.44      inference('simplify_reflect-', [status(thm)], ['126', '127'])).
% 1.20/1.44  thf('129', plain,
% 1.20/1.44      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.20/1.44         = (k6_partfun1 @ sk_A))),
% 1.20/1.44      inference('demod', [status(thm)], ['67', '68'])).
% 1.20/1.44  thf('130', plain,
% 1.20/1.44      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf(t24_funct_2, axiom,
% 1.20/1.44    (![A:$i,B:$i,C:$i]:
% 1.20/1.44     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.20/1.44         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.20/1.44       ( ![D:$i]:
% 1.20/1.44         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.20/1.44             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.20/1.44           ( ( r2_relset_1 @
% 1.20/1.44               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 1.20/1.44               ( k6_partfun1 @ B ) ) =>
% 1.20/1.44             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 1.20/1.44  thf('131', plain,
% 1.20/1.44      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 1.20/1.44         (~ (v1_funct_1 @ X33)
% 1.20/1.44          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 1.20/1.44          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 1.20/1.44          | ~ (r2_relset_1 @ X34 @ X34 @ 
% 1.20/1.44               (k1_partfun1 @ X34 @ X35 @ X35 @ X34 @ X33 @ X36) @ 
% 1.20/1.44               (k6_partfun1 @ X34))
% 1.20/1.44          | ((k2_relset_1 @ X35 @ X34 @ X36) = (X34))
% 1.20/1.44          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 1.20/1.44          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 1.20/1.44          | ~ (v1_funct_1 @ X36))),
% 1.20/1.44      inference('cnf', [status(esa)], [t24_funct_2])).
% 1.20/1.44  thf('132', plain,
% 1.20/1.44      (![X0 : $i]:
% 1.20/1.44         (~ (v1_funct_1 @ X0)
% 1.20/1.44          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.20/1.44          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.20/1.44          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.20/1.44          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.20/1.44               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.20/1.44               (k6_partfun1 @ sk_A))
% 1.20/1.44          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.20/1.44          | ~ (v1_funct_1 @ sk_C))),
% 1.20/1.44      inference('sup-', [status(thm)], ['130', '131'])).
% 1.20/1.44  thf('133', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('134', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('135', plain,
% 1.20/1.44      (![X0 : $i]:
% 1.20/1.44         (~ (v1_funct_1 @ X0)
% 1.20/1.44          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.20/1.44          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.20/1.44          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.20/1.44          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.20/1.44               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.20/1.44               (k6_partfun1 @ sk_A)))),
% 1.20/1.44      inference('demod', [status(thm)], ['132', '133', '134'])).
% 1.20/1.44  thf('136', plain,
% 1.20/1.44      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 1.20/1.44           (k6_partfun1 @ sk_A))
% 1.20/1.44        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 1.20/1.44        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.20/1.44        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.20/1.44        | ~ (v1_funct_1 @ sk_D))),
% 1.20/1.44      inference('sup-', [status(thm)], ['129', '135'])).
% 1.20/1.44  thf('137', plain,
% 1.20/1.44      (![X0 : $i]:
% 1.20/1.44         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 1.20/1.44      inference('sup-', [status(thm)], ['77', '79'])).
% 1.20/1.44  thf('138', plain,
% 1.20/1.44      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('139', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('140', plain, ((v1_funct_1 @ sk_D)),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('141', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))),
% 1.20/1.44      inference('demod', [status(thm)], ['136', '137', '138', '139', '140'])).
% 1.20/1.44  thf('142', plain,
% 1.20/1.44      ((((sk_A) != (sk_A))
% 1.20/1.44        | ~ (v2_funct_1 @ sk_D)
% 1.20/1.44        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 1.20/1.44      inference('demod', [status(thm)], ['128', '141'])).
% 1.20/1.44  thf('143', plain,
% 1.20/1.44      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.20/1.44        | ~ (v2_funct_1 @ sk_D))),
% 1.20/1.44      inference('simplify', [status(thm)], ['142'])).
% 1.20/1.44  thf('144', plain, ((v2_funct_1 @ sk_D)),
% 1.20/1.44      inference('sup-', [status(thm)], ['114', '115'])).
% 1.20/1.44  thf('145', plain,
% 1.20/1.44      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 1.20/1.44      inference('demod', [status(thm)], ['143', '144'])).
% 1.20/1.44  thf('146', plain,
% 1.20/1.44      ((((k6_partfun1 @ (k1_relat_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.20/1.44        | ~ (v1_relat_1 @ sk_D)
% 1.20/1.44        | ~ (v1_funct_1 @ sk_D)
% 1.20/1.44        | ~ (v2_funct_1 @ sk_D))),
% 1.20/1.44      inference('sup+', [status(thm)], ['120', '145'])).
% 1.20/1.44  thf('147', plain, ((v1_relat_1 @ sk_D)),
% 1.20/1.44      inference('sup-', [status(thm)], ['33', '34'])).
% 1.20/1.44  thf('148', plain, ((v1_funct_1 @ sk_D)),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('149', plain, ((v2_funct_1 @ sk_D)),
% 1.20/1.44      inference('sup-', [status(thm)], ['114', '115'])).
% 1.20/1.44  thf('150', plain,
% 1.20/1.44      (((k6_partfun1 @ (k1_relat_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 1.20/1.44      inference('demod', [status(thm)], ['146', '147', '148', '149'])).
% 1.20/1.44  thf('151', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 1.20/1.44      inference('demod', [status(thm)], ['56', '57'])).
% 1.20/1.44  thf('152', plain,
% 1.20/1.44      (((k1_relat_1 @ (k6_partfun1 @ sk_B)) = (k1_relat_1 @ sk_D))),
% 1.20/1.44      inference('sup+', [status(thm)], ['150', '151'])).
% 1.20/1.44  thf('153', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 1.20/1.44      inference('demod', [status(thm)], ['56', '57'])).
% 1.20/1.44  thf('154', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.20/1.44      inference('demod', [status(thm)], ['152', '153'])).
% 1.20/1.44  thf('155', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (sk_B)))),
% 1.20/1.44      inference('demod', [status(thm)], ['117', '154'])).
% 1.20/1.44  thf('156', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.20/1.44      inference('simplify', [status(thm)], ['155'])).
% 1.20/1.44  thf('157', plain,
% 1.20/1.44      (![X4 : $i]:
% 1.20/1.44         (~ (v2_funct_1 @ X4)
% 1.20/1.44          | ((k5_relat_1 @ X4 @ (k2_funct_1 @ X4))
% 1.20/1.44              = (k6_partfun1 @ (k1_relat_1 @ X4)))
% 1.20/1.44          | ~ (v1_funct_1 @ X4)
% 1.20/1.44          | ~ (v1_relat_1 @ X4))),
% 1.20/1.44      inference('demod', [status(thm)], ['118', '119'])).
% 1.20/1.44  thf('158', plain,
% 1.20/1.44      (![X5 : $i, X6 : $i]:
% 1.20/1.44         (~ (v1_relat_1 @ X5)
% 1.20/1.44          | ~ (v1_funct_1 @ X5)
% 1.20/1.44          | ((X5) = (k2_funct_1 @ X6))
% 1.20/1.44          | ((k5_relat_1 @ X5 @ X6) != (k6_partfun1 @ (k2_relat_1 @ X6)))
% 1.20/1.44          | ((k2_relat_1 @ X5) != (k1_relat_1 @ X6))
% 1.20/1.44          | ~ (v2_funct_1 @ X6)
% 1.20/1.44          | ~ (v1_funct_1 @ X6)
% 1.20/1.44          | ~ (v1_relat_1 @ X6))),
% 1.20/1.44      inference('demod', [status(thm)], ['29', '30'])).
% 1.20/1.44  thf('159', plain,
% 1.20/1.44      (![X0 : $i]:
% 1.20/1.44         (((k6_partfun1 @ (k1_relat_1 @ X0))
% 1.20/1.44            != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 1.20/1.44          | ~ (v1_relat_1 @ X0)
% 1.20/1.44          | ~ (v1_funct_1 @ X0)
% 1.20/1.44          | ~ (v2_funct_1 @ X0)
% 1.20/1.44          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.20/1.44          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.20/1.44          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.20/1.44          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.20/1.44          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.20/1.44          | ~ (v1_funct_1 @ X0)
% 1.20/1.44          | ~ (v1_relat_1 @ X0))),
% 1.20/1.44      inference('sup-', [status(thm)], ['157', '158'])).
% 1.20/1.44  thf('160', plain,
% 1.20/1.44      (![X0 : $i]:
% 1.20/1.44         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 1.20/1.44          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.20/1.44          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.20/1.44          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.20/1.44          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.20/1.44          | ~ (v2_funct_1 @ X0)
% 1.20/1.44          | ~ (v1_funct_1 @ X0)
% 1.20/1.44          | ~ (v1_relat_1 @ X0)
% 1.20/1.44          | ((k6_partfun1 @ (k1_relat_1 @ X0))
% 1.20/1.44              != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 1.20/1.44      inference('simplify', [status(thm)], ['159'])).
% 1.20/1.44  thf('161', plain,
% 1.20/1.44      ((((k6_partfun1 @ (k1_relat_1 @ sk_D))
% 1.20/1.44          != (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 1.20/1.44        | ~ (v1_relat_1 @ sk_D)
% 1.20/1.44        | ~ (v1_funct_1 @ sk_D)
% 1.20/1.44        | ~ (v2_funct_1 @ sk_D)
% 1.20/1.44        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D))
% 1.20/1.44        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 1.20/1.44        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_D))
% 1.20/1.44        | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ (k2_funct_1 @ sk_D)))
% 1.20/1.44        | ((sk_D) = (k2_funct_1 @ (k2_funct_1 @ sk_D))))),
% 1.20/1.44      inference('sup-', [status(thm)], ['156', '160'])).
% 1.20/1.44  thf('162', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.20/1.44      inference('demod', [status(thm)], ['152', '153'])).
% 1.20/1.44  thf('163', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 1.20/1.44      inference('demod', [status(thm)], ['60', '61', '62', '63', '64'])).
% 1.20/1.44  thf('164', plain, ((v1_relat_1 @ sk_D)),
% 1.20/1.44      inference('sup-', [status(thm)], ['33', '34'])).
% 1.20/1.44  thf('165', plain, ((v1_funct_1 @ sk_D)),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('166', plain, ((v2_funct_1 @ sk_D)),
% 1.20/1.44      inference('sup-', [status(thm)], ['114', '115'])).
% 1.20/1.44  thf('167', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.20/1.44      inference('simplify', [status(thm)], ['155'])).
% 1.20/1.44  thf('168', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.44      inference('sup-', [status(thm)], ['38', '39'])).
% 1.20/1.44  thf('169', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.20/1.44      inference('simplify', [status(thm)], ['155'])).
% 1.20/1.44  thf('170', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('171', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.20/1.44      inference('simplify', [status(thm)], ['155'])).
% 1.20/1.44  thf('172', plain, ((v2_funct_1 @ sk_C)),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('173', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.20/1.44      inference('demod', [status(thm)], ['86', '87', '90'])).
% 1.20/1.44  thf('174', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.20/1.44      inference('simplify', [status(thm)], ['155'])).
% 1.20/1.44  thf('175', plain,
% 1.20/1.44      (![X4 : $i]:
% 1.20/1.44         (~ (v2_funct_1 @ X4)
% 1.20/1.44          | ((k5_relat_1 @ X4 @ (k2_funct_1 @ X4))
% 1.20/1.44              = (k6_partfun1 @ (k1_relat_1 @ X4)))
% 1.20/1.44          | ~ (v1_funct_1 @ X4)
% 1.20/1.44          | ~ (v1_relat_1 @ X4))),
% 1.20/1.44      inference('demod', [status(thm)], ['118', '119'])).
% 1.20/1.44  thf('176', plain,
% 1.20/1.44      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('177', plain,
% 1.20/1.44      (![X50 : $i, X51 : $i, X52 : $i]:
% 1.20/1.44         (((X50) = (k1_xboole_0))
% 1.20/1.44          | ~ (v1_funct_1 @ X51)
% 1.20/1.44          | ~ (v1_funct_2 @ X51 @ X52 @ X50)
% 1.20/1.44          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 1.20/1.44          | ((k5_relat_1 @ X51 @ (k2_funct_1 @ X51)) = (k6_partfun1 @ X52))
% 1.20/1.44          | ~ (v2_funct_1 @ X51)
% 1.20/1.44          | ((k2_relset_1 @ X52 @ X50 @ X51) != (X50)))),
% 1.20/1.44      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.20/1.44  thf('178', plain,
% 1.20/1.44      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.20/1.44        | ~ (v2_funct_1 @ sk_C)
% 1.20/1.44        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 1.20/1.44        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.20/1.44        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.44        | ((sk_B) = (k1_xboole_0)))),
% 1.20/1.44      inference('sup-', [status(thm)], ['176', '177'])).
% 1.20/1.44  thf('179', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('180', plain, ((v2_funct_1 @ sk_C)),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('181', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('182', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('183', plain,
% 1.20/1.44      ((((sk_B) != (sk_B))
% 1.20/1.44        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 1.20/1.44        | ((sk_B) = (k1_xboole_0)))),
% 1.20/1.44      inference('demod', [status(thm)], ['178', '179', '180', '181', '182'])).
% 1.20/1.44  thf('184', plain,
% 1.20/1.44      ((((sk_B) = (k1_xboole_0))
% 1.20/1.44        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 1.20/1.44      inference('simplify', [status(thm)], ['183'])).
% 1.20/1.44  thf('185', plain, (((sk_B) != (k1_xboole_0))),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('186', plain,
% 1.20/1.44      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 1.20/1.44      inference('simplify_reflect-', [status(thm)], ['184', '185'])).
% 1.20/1.44  thf('187', plain,
% 1.20/1.44      ((((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 1.20/1.44        | ~ (v1_relat_1 @ sk_C)
% 1.20/1.44        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.44        | ~ (v2_funct_1 @ sk_C))),
% 1.20/1.44      inference('sup+', [status(thm)], ['175', '186'])).
% 1.20/1.44  thf('188', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.44      inference('sup-', [status(thm)], ['38', '39'])).
% 1.20/1.44  thf('189', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('190', plain, ((v2_funct_1 @ sk_C)),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('191', plain,
% 1.20/1.44      (((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 1.20/1.44      inference('demod', [status(thm)], ['187', '188', '189', '190'])).
% 1.20/1.44  thf('192', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 1.20/1.44      inference('demod', [status(thm)], ['56', '57'])).
% 1.20/1.44  thf('193', plain,
% 1.20/1.44      (((k1_relat_1 @ (k6_partfun1 @ sk_A)) = (k1_relat_1 @ sk_C))),
% 1.20/1.44      inference('sup+', [status(thm)], ['191', '192'])).
% 1.20/1.44  thf('194', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 1.20/1.44      inference('demod', [status(thm)], ['56', '57'])).
% 1.20/1.44  thf('195', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 1.20/1.44      inference('demod', [status(thm)], ['193', '194'])).
% 1.20/1.44  thf('196', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.20/1.44      inference('simplify', [status(thm)], ['155'])).
% 1.20/1.44  thf('197', plain,
% 1.20/1.44      ((((k6_partfun1 @ sk_B) != (k6_partfun1 @ sk_B))
% 1.20/1.44        | ((sk_A) != (sk_A))
% 1.20/1.44        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 1.20/1.44      inference('demod', [status(thm)],
% 1.20/1.44                ['161', '162', '163', '164', '165', '166', '167', '168', 
% 1.20/1.44                 '169', '170', '171', '172', '173', '174', '195', '196'])).
% 1.20/1.44  thf('198', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 1.20/1.44      inference('simplify', [status(thm)], ['197'])).
% 1.20/1.44  thf('199', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.20/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.44  thf('200', plain, ($false),
% 1.20/1.44      inference('simplify_reflect-', [status(thm)], ['198', '199'])).
% 1.20/1.44  
% 1.20/1.44  % SZS output end Refutation
% 1.20/1.44  
% 1.20/1.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

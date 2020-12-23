%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LRuPTJfpRc

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:09 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :  206 (4781 expanded)
%              Number of leaves         :   44 (1381 expanded)
%              Depth                    :   28
%              Number of atoms          : 2044 (136097 expanded)
%              Number of equality atoms :  161 (9194 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( ( k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28 )
        = ( k5_relat_1 @ X25 @ X28 ) ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X18 @ X19 @ X21 @ X22 @ X17 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X22 ) ) ) ) ),
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

thf('19',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('20',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('21',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( X13 = X16 )
      | ~ ( r2_relset_1 @ X14 @ X15 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','22'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('24',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('25',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

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

thf('26',plain,(
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

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('27',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
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
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
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
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

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
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( r2_relset_1 @ X33 @ X33 @ ( k1_partfun1 @ X33 @ X34 @ X34 @ X33 @ X32 @ X35 ) @ ( k6_partfun1 @ X33 ) )
      | ( ( k2_relset_1 @ X34 @ X33 @ X35 )
        = X33 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
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
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','9'])).

thf('39',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('40',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('41',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['37','38','41','42','43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('47',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('48',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('52',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('58',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['29','45','48','49','54','55','58'])).

thf('60',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('62',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('63',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
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

thf('65',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( zip_tseitin_0 @ X40 @ X43 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X44 @ X41 @ X41 @ X42 @ X43 @ X40 ) )
      | ( zip_tseitin_1 @ X42 @ X41 )
      | ( ( k2_relset_1 @ X44 @ X41 @ X43 )
       != X41 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X41 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X41 )
      | ~ ( v1_funct_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('66',plain,(
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
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['63','69'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('71',plain,(
    ! [X3: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('72',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('73',plain,(
    ! [X3: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X3 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['70','73','74','75','76','77'])).

thf('79',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X38: $i,X39: $i] :
      ( ( X38 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('81',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X36: $i,X37: $i] :
      ( ( v2_funct_1 @ X37 )
      | ~ ( zip_tseitin_0 @ X37 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('85',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['60','85'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('87',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ X4 @ ( k2_funct_1 @ X4 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('88',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('89',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ X4 @ ( k2_funct_1 @ X4 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
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

thf('91',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( X45 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X45 ) ) )
      | ( ( k5_relat_1 @ X46 @ ( k2_funct_1 @ X46 ) )
        = ( k6_partfun1 @ X47 ) )
      | ~ ( v2_funct_1 @ X46 )
      | ( ( k2_relset_1 @ X47 @ X45 @ X46 )
       != X45 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('92',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('94',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf('97',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['37','38','41','42','43','44'])).

thf('100',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['83','84'])).

thf('103',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['89','103'])).

thf('105',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['46','47'])).

thf('106',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['83','84'])).

thf('108',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['104','105','106','107'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('110',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['108','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('114',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['86','114'])).

thf('116',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ X4 @ ( k2_funct_1 @ X4 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('118',plain,(
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
    inference(demod,[status(thm)],['26','27'])).

thf('119',plain,(
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
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
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
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,
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
    inference('sup-',[status(thm)],['116','120'])).

thf('122',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('123',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['52','53'])).

thf('124',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['46','47'])).

thf('125',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['83','84'])).

thf('127',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['115'])).

thf('128',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['56','57'])).

thf('129',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['115'])).

thf('130',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['115'])).

thf('132',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['37','38','41','42','43','44'])).

thf('134',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['115'])).

thf('135',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ X4 @ ( k2_funct_1 @ X4 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('136',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( X45 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X45 ) ) )
      | ( ( k5_relat_1 @ X46 @ ( k2_funct_1 @ X46 ) )
        = ( k6_partfun1 @ X47 ) )
      | ~ ( v2_funct_1 @ X46 )
      | ( ( k2_relset_1 @ X47 @ X45 @ X46 )
       != X45 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('138',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['138','139','140','141','142'])).

thf('144',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['144','145'])).

thf('147',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['135','146'])).

thf('148',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['56','57'])).

thf('149',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['147','148','149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('153',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('155',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['115'])).

thf('157',plain,
    ( ( ( k6_partfun1 @ sk_B )
     != ( k6_partfun1 @ sk_B ) )
    | ( sk_A != sk_A )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['121','122','123','124','125','126','127','128','129','130','131','132','133','134','155','156'])).

thf('158',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['158','159'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LRuPTJfpRc
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:37:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.89/1.13  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.89/1.13  % Solved by: fo/fo7.sh
% 0.89/1.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.89/1.13  % done 863 iterations in 0.643s
% 0.89/1.13  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.89/1.13  % SZS output start Refutation
% 0.89/1.13  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.89/1.13  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.89/1.13  thf(sk_A_type, type, sk_A: $i).
% 0.89/1.13  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.89/1.13  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.89/1.13  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.89/1.13  thf(sk_D_type, type, sk_D: $i).
% 0.89/1.13  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.89/1.13  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.89/1.13  thf(sk_C_type, type, sk_C: $i).
% 0.89/1.13  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.89/1.13  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.89/1.13  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.89/1.13  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.89/1.13  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.89/1.13  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.89/1.13  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.89/1.13  thf(sk_B_type, type, sk_B: $i).
% 0.89/1.13  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.89/1.13  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.89/1.13  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.89/1.13  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.89/1.13  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.89/1.13  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.89/1.13  thf(t36_funct_2, conjecture,
% 0.89/1.13    (![A:$i,B:$i,C:$i]:
% 0.89/1.13     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.89/1.13         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.89/1.13       ( ![D:$i]:
% 0.89/1.13         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.89/1.13             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.89/1.13           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.89/1.13               ( r2_relset_1 @
% 0.89/1.13                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.89/1.13                 ( k6_partfun1 @ A ) ) & 
% 0.89/1.13               ( v2_funct_1 @ C ) ) =>
% 0.89/1.13             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.89/1.13               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.89/1.13  thf(zf_stmt_0, negated_conjecture,
% 0.89/1.13    (~( ![A:$i,B:$i,C:$i]:
% 0.89/1.13        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.89/1.13            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.89/1.13          ( ![D:$i]:
% 0.89/1.13            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.89/1.13                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.89/1.13              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.89/1.13                  ( r2_relset_1 @
% 0.89/1.13                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.89/1.13                    ( k6_partfun1 @ A ) ) & 
% 0.89/1.13                  ( v2_funct_1 @ C ) ) =>
% 0.89/1.13                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.89/1.13                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.89/1.13    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.89/1.13  thf('0', plain,
% 0.89/1.13      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.89/1.13        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.89/1.13        (k6_partfun1 @ sk_A))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('1', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('2', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf(redefinition_k1_partfun1, axiom,
% 0.89/1.13    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.89/1.13     ( ( ( v1_funct_1 @ E ) & 
% 0.89/1.13         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.89/1.13         ( v1_funct_1 @ F ) & 
% 0.89/1.13         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.89/1.13       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.89/1.13  thf('3', plain,
% 0.89/1.13      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.89/1.13         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.89/1.13          | ~ (v1_funct_1 @ X25)
% 0.89/1.13          | ~ (v1_funct_1 @ X28)
% 0.89/1.13          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.89/1.13          | ((k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28)
% 0.89/1.13              = (k5_relat_1 @ X25 @ X28)))),
% 0.89/1.13      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.89/1.13  thf('4', plain,
% 0.89/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.13         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.89/1.13            = (k5_relat_1 @ sk_C @ X0))
% 0.89/1.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ sk_C))),
% 0.89/1.13      inference('sup-', [status(thm)], ['2', '3'])).
% 0.89/1.13  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('6', plain,
% 0.89/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.13         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.89/1.13            = (k5_relat_1 @ sk_C @ X0))
% 0.89/1.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.89/1.13          | ~ (v1_funct_1 @ X0))),
% 0.89/1.13      inference('demod', [status(thm)], ['4', '5'])).
% 0.89/1.13  thf('7', plain,
% 0.89/1.13      ((~ (v1_funct_1 @ sk_D)
% 0.89/1.13        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.89/1.13            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.89/1.13      inference('sup-', [status(thm)], ['1', '6'])).
% 0.89/1.13  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('9', plain,
% 0.89/1.13      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.89/1.13         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.89/1.13      inference('demod', [status(thm)], ['7', '8'])).
% 0.89/1.13  thf('10', plain,
% 0.89/1.13      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.89/1.13        (k6_partfun1 @ sk_A))),
% 0.89/1.13      inference('demod', [status(thm)], ['0', '9'])).
% 0.89/1.13  thf('11', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('12', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf(dt_k1_partfun1, axiom,
% 0.89/1.13    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.89/1.13     ( ( ( v1_funct_1 @ E ) & 
% 0.89/1.13         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.89/1.13         ( v1_funct_1 @ F ) & 
% 0.89/1.13         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.89/1.13       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.89/1.13         ( m1_subset_1 @
% 0.89/1.13           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.89/1.13           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.89/1.13  thf('13', plain,
% 0.89/1.13      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.89/1.13         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.89/1.13          | ~ (v1_funct_1 @ X17)
% 0.89/1.13          | ~ (v1_funct_1 @ X20)
% 0.89/1.13          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.89/1.13          | (m1_subset_1 @ (k1_partfun1 @ X18 @ X19 @ X21 @ X22 @ X17 @ X20) @ 
% 0.89/1.13             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X22))))),
% 0.89/1.13      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.89/1.13  thf('14', plain,
% 0.89/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.13         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.89/1.13           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.89/1.13          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.89/1.13          | ~ (v1_funct_1 @ X1)
% 0.89/1.13          | ~ (v1_funct_1 @ sk_C))),
% 0.89/1.13      inference('sup-', [status(thm)], ['12', '13'])).
% 0.89/1.13  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('16', plain,
% 0.89/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.13         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.89/1.13           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.89/1.13          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.89/1.13          | ~ (v1_funct_1 @ X1))),
% 0.89/1.13      inference('demod', [status(thm)], ['14', '15'])).
% 0.89/1.13  thf('17', plain,
% 0.89/1.13      ((~ (v1_funct_1 @ sk_D)
% 0.89/1.13        | (m1_subset_1 @ 
% 0.89/1.13           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.89/1.13           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.89/1.13      inference('sup-', [status(thm)], ['11', '16'])).
% 0.89/1.13  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('19', plain,
% 0.89/1.13      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.89/1.13         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.89/1.13      inference('demod', [status(thm)], ['7', '8'])).
% 0.89/1.13  thf('20', plain,
% 0.89/1.13      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.89/1.13        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.89/1.13      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.89/1.13  thf(redefinition_r2_relset_1, axiom,
% 0.89/1.13    (![A:$i,B:$i,C:$i,D:$i]:
% 0.89/1.13     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.89/1.13         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.89/1.13       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.89/1.13  thf('21', plain,
% 0.89/1.13      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.89/1.13         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.89/1.13          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.89/1.13          | ((X13) = (X16))
% 0.89/1.13          | ~ (r2_relset_1 @ X14 @ X15 @ X13 @ X16))),
% 0.89/1.13      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.89/1.13  thf('22', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 0.89/1.13          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 0.89/1.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.89/1.13      inference('sup-', [status(thm)], ['20', '21'])).
% 0.89/1.13  thf('23', plain,
% 0.89/1.13      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.89/1.13           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.89/1.13        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 0.89/1.13      inference('sup-', [status(thm)], ['10', '22'])).
% 0.89/1.13  thf(dt_k6_partfun1, axiom,
% 0.89/1.13    (![A:$i]:
% 0.89/1.13     ( ( m1_subset_1 @
% 0.89/1.13         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.89/1.13       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.89/1.13  thf('24', plain,
% 0.89/1.13      (![X24 : $i]:
% 0.89/1.13         (m1_subset_1 @ (k6_partfun1 @ X24) @ 
% 0.89/1.13          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))),
% 0.89/1.13      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.89/1.13  thf('25', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.89/1.13      inference('demod', [status(thm)], ['23', '24'])).
% 0.89/1.13  thf(t64_funct_1, axiom,
% 0.89/1.13    (![A:$i]:
% 0.89/1.13     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.89/1.13       ( ![B:$i]:
% 0.89/1.13         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.89/1.13           ( ( ( v2_funct_1 @ A ) & 
% 0.89/1.13               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.89/1.13               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.89/1.13             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.89/1.13  thf('26', plain,
% 0.89/1.13      (![X5 : $i, X6 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X5)
% 0.89/1.13          | ~ (v1_funct_1 @ X5)
% 0.89/1.13          | ((X5) = (k2_funct_1 @ X6))
% 0.89/1.13          | ((k5_relat_1 @ X5 @ X6) != (k6_relat_1 @ (k2_relat_1 @ X6)))
% 0.89/1.13          | ((k2_relat_1 @ X5) != (k1_relat_1 @ X6))
% 0.89/1.13          | ~ (v2_funct_1 @ X6)
% 0.89/1.13          | ~ (v1_funct_1 @ X6)
% 0.89/1.13          | ~ (v1_relat_1 @ X6))),
% 0.89/1.13      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.89/1.13  thf(redefinition_k6_partfun1, axiom,
% 0.89/1.13    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.89/1.13  thf('27', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.89/1.13      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.89/1.13  thf('28', plain,
% 0.89/1.13      (![X5 : $i, X6 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X5)
% 0.89/1.13          | ~ (v1_funct_1 @ X5)
% 0.89/1.13          | ((X5) = (k2_funct_1 @ X6))
% 0.89/1.13          | ((k5_relat_1 @ X5 @ X6) != (k6_partfun1 @ (k2_relat_1 @ X6)))
% 0.89/1.13          | ((k2_relat_1 @ X5) != (k1_relat_1 @ X6))
% 0.89/1.13          | ~ (v2_funct_1 @ X6)
% 0.89/1.13          | ~ (v1_funct_1 @ X6)
% 0.89/1.13          | ~ (v1_relat_1 @ X6))),
% 0.89/1.13      inference('demod', [status(thm)], ['26', '27'])).
% 0.89/1.13  thf('29', plain,
% 0.89/1.13      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 0.89/1.13        | ~ (v1_relat_1 @ sk_D)
% 0.89/1.13        | ~ (v1_funct_1 @ sk_D)
% 0.89/1.13        | ~ (v2_funct_1 @ sk_D)
% 0.89/1.13        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.89/1.13        | ((sk_C) = (k2_funct_1 @ sk_D))
% 0.89/1.13        | ~ (v1_funct_1 @ sk_C)
% 0.89/1.13        | ~ (v1_relat_1 @ sk_C))),
% 0.89/1.13      inference('sup-', [status(thm)], ['25', '28'])).
% 0.89/1.13  thf('30', plain,
% 0.89/1.13      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.89/1.13         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.89/1.13      inference('demod', [status(thm)], ['7', '8'])).
% 0.89/1.13  thf('31', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf(t24_funct_2, axiom,
% 0.89/1.13    (![A:$i,B:$i,C:$i]:
% 0.89/1.13     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.89/1.13         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.89/1.13       ( ![D:$i]:
% 0.89/1.13         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.89/1.13             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.89/1.13           ( ( r2_relset_1 @
% 0.89/1.13               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.89/1.13               ( k6_partfun1 @ B ) ) =>
% 0.89/1.13             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.89/1.13  thf('32', plain,
% 0.89/1.13      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.89/1.13         (~ (v1_funct_1 @ X32)
% 0.89/1.13          | ~ (v1_funct_2 @ X32 @ X33 @ X34)
% 0.89/1.13          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.89/1.13          | ~ (r2_relset_1 @ X33 @ X33 @ 
% 0.89/1.13               (k1_partfun1 @ X33 @ X34 @ X34 @ X33 @ X32 @ X35) @ 
% 0.89/1.13               (k6_partfun1 @ X33))
% 0.89/1.13          | ((k2_relset_1 @ X34 @ X33 @ X35) = (X33))
% 0.89/1.13          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.89/1.13          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 0.89/1.13          | ~ (v1_funct_1 @ X35))),
% 0.89/1.13      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.89/1.13  thf('33', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.89/1.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.89/1.13          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.89/1.13          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.89/1.13               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.89/1.13               (k6_partfun1 @ sk_A))
% 0.89/1.13          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.89/1.13          | ~ (v1_funct_1 @ sk_C))),
% 0.89/1.13      inference('sup-', [status(thm)], ['31', '32'])).
% 0.89/1.13  thf('34', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('36', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.89/1.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.89/1.13          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.89/1.13          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.89/1.13               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.89/1.13               (k6_partfun1 @ sk_A)))),
% 0.89/1.13      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.89/1.13  thf('37', plain,
% 0.89/1.13      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.89/1.13           (k6_partfun1 @ sk_A))
% 0.89/1.13        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.89/1.13        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.89/1.13        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.89/1.13        | ~ (v1_funct_1 @ sk_D))),
% 0.89/1.13      inference('sup-', [status(thm)], ['30', '36'])).
% 0.89/1.13  thf('38', plain,
% 0.89/1.13      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.89/1.13        (k6_partfun1 @ sk_A))),
% 0.89/1.13      inference('demod', [status(thm)], ['0', '9'])).
% 0.89/1.13  thf('39', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf(redefinition_k2_relset_1, axiom,
% 0.89/1.13    (![A:$i,B:$i,C:$i]:
% 0.89/1.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.13       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.89/1.13  thf('40', plain,
% 0.89/1.13      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.89/1.13         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 0.89/1.13          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.89/1.13      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.89/1.13  thf('41', plain,
% 0.89/1.13      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.89/1.13      inference('sup-', [status(thm)], ['39', '40'])).
% 0.89/1.13  thf('42', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('43', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('44', plain, ((v1_funct_1 @ sk_D)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('45', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.89/1.13      inference('demod', [status(thm)], ['37', '38', '41', '42', '43', '44'])).
% 0.89/1.13  thf('46', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf(cc1_relset_1, axiom,
% 0.89/1.13    (![A:$i,B:$i,C:$i]:
% 0.89/1.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.13       ( v1_relat_1 @ C ) ))).
% 0.89/1.13  thf('47', plain,
% 0.89/1.13      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.89/1.13         ((v1_relat_1 @ X7)
% 0.89/1.13          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.89/1.13      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.89/1.13  thf('48', plain, ((v1_relat_1 @ sk_D)),
% 0.89/1.13      inference('sup-', [status(thm)], ['46', '47'])).
% 0.89/1.13  thf('49', plain, ((v1_funct_1 @ sk_D)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('50', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('51', plain,
% 0.89/1.13      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.89/1.13         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 0.89/1.13          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.89/1.13      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.89/1.13  thf('52', plain,
% 0.89/1.13      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.89/1.13      inference('sup-', [status(thm)], ['50', '51'])).
% 0.89/1.13  thf('53', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('54', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.89/1.13      inference('sup+', [status(thm)], ['52', '53'])).
% 0.89/1.13  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('56', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('57', plain,
% 0.89/1.13      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.89/1.13         ((v1_relat_1 @ X7)
% 0.89/1.13          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.89/1.13      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.89/1.13  thf('58', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.13      inference('sup-', [status(thm)], ['56', '57'])).
% 0.89/1.13  thf('59', plain,
% 0.89/1.13      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 0.89/1.13        | ~ (v2_funct_1 @ sk_D)
% 0.89/1.13        | ((sk_B) != (k1_relat_1 @ sk_D))
% 0.89/1.13        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 0.89/1.13      inference('demod', [status(thm)],
% 0.89/1.13                ['29', '45', '48', '49', '54', '55', '58'])).
% 0.89/1.13  thf('60', plain,
% 0.89/1.13      ((((sk_C) = (k2_funct_1 @ sk_D))
% 0.89/1.13        | ((sk_B) != (k1_relat_1 @ sk_D))
% 0.89/1.13        | ~ (v2_funct_1 @ sk_D))),
% 0.89/1.13      inference('simplify', [status(thm)], ['59'])).
% 0.89/1.13  thf('61', plain,
% 0.89/1.13      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.89/1.13         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.89/1.13      inference('demod', [status(thm)], ['7', '8'])).
% 0.89/1.13  thf('62', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.89/1.13      inference('demod', [status(thm)], ['23', '24'])).
% 0.89/1.13  thf('63', plain,
% 0.89/1.13      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.89/1.13         = (k6_partfun1 @ sk_A))),
% 0.89/1.13      inference('demod', [status(thm)], ['61', '62'])).
% 0.89/1.13  thf('64', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf(t30_funct_2, axiom,
% 0.89/1.13    (![A:$i,B:$i,C:$i,D:$i]:
% 0.89/1.13     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.89/1.13         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 0.89/1.13       ( ![E:$i]:
% 0.89/1.13         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 0.89/1.13             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 0.89/1.13           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 0.89/1.13               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 0.89/1.13             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 0.89/1.13               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 0.89/1.13  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 0.89/1.13  thf(zf_stmt_2, axiom,
% 0.89/1.13    (![C:$i,B:$i]:
% 0.89/1.13     ( ( zip_tseitin_1 @ C @ B ) =>
% 0.89/1.13       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 0.89/1.13  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.89/1.13  thf(zf_stmt_4, axiom,
% 0.89/1.13    (![E:$i,D:$i]:
% 0.89/1.13     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 0.89/1.13  thf(zf_stmt_5, axiom,
% 0.89/1.13    (![A:$i,B:$i,C:$i,D:$i]:
% 0.89/1.13     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.89/1.13         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.89/1.13       ( ![E:$i]:
% 0.89/1.13         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.89/1.13             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.89/1.13           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 0.89/1.13               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 0.89/1.13             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 0.89/1.13  thf('65', plain,
% 0.89/1.13      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.89/1.13         (~ (v1_funct_1 @ X40)
% 0.89/1.13          | ~ (v1_funct_2 @ X40 @ X41 @ X42)
% 0.89/1.13          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.89/1.13          | (zip_tseitin_0 @ X40 @ X43)
% 0.89/1.13          | ~ (v2_funct_1 @ (k1_partfun1 @ X44 @ X41 @ X41 @ X42 @ X43 @ X40))
% 0.89/1.13          | (zip_tseitin_1 @ X42 @ X41)
% 0.89/1.13          | ((k2_relset_1 @ X44 @ X41 @ X43) != (X41))
% 0.89/1.13          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X41)))
% 0.89/1.13          | ~ (v1_funct_2 @ X43 @ X44 @ X41)
% 0.89/1.13          | ~ (v1_funct_1 @ X43))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.89/1.13  thf('66', plain,
% 0.89/1.13      (![X0 : $i, X1 : $i]:
% 0.89/1.13         (~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.89/1.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.89/1.13          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 0.89/1.13          | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.89/1.13          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.89/1.13          | (zip_tseitin_0 @ sk_D @ X0)
% 0.89/1.13          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.89/1.13          | ~ (v1_funct_1 @ sk_D))),
% 0.89/1.13      inference('sup-', [status(thm)], ['64', '65'])).
% 0.89/1.13  thf('67', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('68', plain, ((v1_funct_1 @ sk_D)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('69', plain,
% 0.89/1.13      (![X0 : $i, X1 : $i]:
% 0.89/1.13         (~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.89/1.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.89/1.13          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 0.89/1.13          | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.89/1.13          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.89/1.13          | (zip_tseitin_0 @ sk_D @ X0))),
% 0.89/1.13      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.89/1.13  thf('70', plain,
% 0.89/1.13      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.89/1.13        | (zip_tseitin_0 @ sk_D @ sk_C)
% 0.89/1.13        | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.89/1.13        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.89/1.13        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.89/1.13        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.89/1.13        | ~ (v1_funct_1 @ sk_C))),
% 0.89/1.13      inference('sup-', [status(thm)], ['63', '69'])).
% 0.89/1.13  thf(fc4_funct_1, axiom,
% 0.89/1.13    (![A:$i]:
% 0.89/1.13     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.89/1.13       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.89/1.13  thf('71', plain, (![X3 : $i]: (v2_funct_1 @ (k6_relat_1 @ X3))),
% 0.89/1.13      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.89/1.13  thf('72', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.89/1.13      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.89/1.13  thf('73', plain, (![X3 : $i]: (v2_funct_1 @ (k6_partfun1 @ X3))),
% 0.89/1.13      inference('demod', [status(thm)], ['71', '72'])).
% 0.89/1.13  thf('74', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('75', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('76', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('77', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('78', plain,
% 0.89/1.13      (((zip_tseitin_0 @ sk_D @ sk_C)
% 0.89/1.13        | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.89/1.13        | ((sk_B) != (sk_B)))),
% 0.89/1.13      inference('demod', [status(thm)], ['70', '73', '74', '75', '76', '77'])).
% 0.89/1.13  thf('79', plain,
% 0.89/1.13      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 0.89/1.13      inference('simplify', [status(thm)], ['78'])).
% 0.89/1.13  thf('80', plain,
% 0.89/1.13      (![X38 : $i, X39 : $i]:
% 0.89/1.13         (((X38) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X38 @ X39))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.89/1.13  thf('81', plain,
% 0.89/1.13      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.89/1.13      inference('sup-', [status(thm)], ['79', '80'])).
% 0.89/1.13  thf('82', plain, (((sk_A) != (k1_xboole_0))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('83', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 0.89/1.13      inference('simplify_reflect-', [status(thm)], ['81', '82'])).
% 0.89/1.13  thf('84', plain,
% 0.89/1.13      (![X36 : $i, X37 : $i]:
% 0.89/1.13         ((v2_funct_1 @ X37) | ~ (zip_tseitin_0 @ X37 @ X36))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.89/1.13  thf('85', plain, ((v2_funct_1 @ sk_D)),
% 0.89/1.13      inference('sup-', [status(thm)], ['83', '84'])).
% 0.89/1.13  thf('86', plain,
% 0.89/1.13      ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (k1_relat_1 @ sk_D)))),
% 0.89/1.13      inference('demod', [status(thm)], ['60', '85'])).
% 0.89/1.13  thf(t61_funct_1, axiom,
% 0.89/1.13    (![A:$i]:
% 0.89/1.13     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.89/1.13       ( ( v2_funct_1 @ A ) =>
% 0.89/1.13         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.89/1.13             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.89/1.13           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.89/1.13             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.89/1.13  thf('87', plain,
% 0.89/1.13      (![X4 : $i]:
% 0.89/1.13         (~ (v2_funct_1 @ X4)
% 0.89/1.13          | ((k5_relat_1 @ X4 @ (k2_funct_1 @ X4))
% 0.89/1.13              = (k6_relat_1 @ (k1_relat_1 @ X4)))
% 0.89/1.13          | ~ (v1_funct_1 @ X4)
% 0.89/1.13          | ~ (v1_relat_1 @ X4))),
% 0.89/1.13      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.89/1.13  thf('88', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.89/1.13      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.89/1.13  thf('89', plain,
% 0.89/1.13      (![X4 : $i]:
% 0.89/1.13         (~ (v2_funct_1 @ X4)
% 0.89/1.13          | ((k5_relat_1 @ X4 @ (k2_funct_1 @ X4))
% 0.89/1.13              = (k6_partfun1 @ (k1_relat_1 @ X4)))
% 0.89/1.13          | ~ (v1_funct_1 @ X4)
% 0.89/1.13          | ~ (v1_relat_1 @ X4))),
% 0.89/1.13      inference('demod', [status(thm)], ['87', '88'])).
% 0.89/1.13  thf('90', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf(t35_funct_2, axiom,
% 0.89/1.13    (![A:$i,B:$i,C:$i]:
% 0.89/1.13     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.89/1.13         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.89/1.13       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.89/1.13         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.89/1.13           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.89/1.13             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.89/1.13  thf('91', plain,
% 0.89/1.13      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.89/1.13         (((X45) = (k1_xboole_0))
% 0.89/1.13          | ~ (v1_funct_1 @ X46)
% 0.89/1.13          | ~ (v1_funct_2 @ X46 @ X47 @ X45)
% 0.89/1.13          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X45)))
% 0.89/1.13          | ((k5_relat_1 @ X46 @ (k2_funct_1 @ X46)) = (k6_partfun1 @ X47))
% 0.89/1.13          | ~ (v2_funct_1 @ X46)
% 0.89/1.13          | ((k2_relset_1 @ X47 @ X45 @ X46) != (X45)))),
% 0.89/1.13      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.89/1.13  thf('92', plain,
% 0.89/1.13      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 0.89/1.13        | ~ (v2_funct_1 @ sk_D)
% 0.89/1.13        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.89/1.13        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.89/1.13        | ~ (v1_funct_1 @ sk_D)
% 0.89/1.13        | ((sk_A) = (k1_xboole_0)))),
% 0.89/1.13      inference('sup-', [status(thm)], ['90', '91'])).
% 0.89/1.13  thf('93', plain,
% 0.89/1.13      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.89/1.13      inference('sup-', [status(thm)], ['39', '40'])).
% 0.89/1.13  thf('94', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('95', plain, ((v1_funct_1 @ sk_D)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('96', plain,
% 0.89/1.13      ((((k2_relat_1 @ sk_D) != (sk_A))
% 0.89/1.13        | ~ (v2_funct_1 @ sk_D)
% 0.89/1.13        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.89/1.13        | ((sk_A) = (k1_xboole_0)))),
% 0.89/1.13      inference('demod', [status(thm)], ['92', '93', '94', '95'])).
% 0.89/1.13  thf('97', plain, (((sk_A) != (k1_xboole_0))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('98', plain,
% 0.89/1.13      ((((k2_relat_1 @ sk_D) != (sk_A))
% 0.89/1.13        | ~ (v2_funct_1 @ sk_D)
% 0.89/1.13        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 0.89/1.13      inference('simplify_reflect-', [status(thm)], ['96', '97'])).
% 0.89/1.13  thf('99', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.89/1.13      inference('demod', [status(thm)], ['37', '38', '41', '42', '43', '44'])).
% 0.89/1.13  thf('100', plain,
% 0.89/1.13      ((((sk_A) != (sk_A))
% 0.89/1.13        | ~ (v2_funct_1 @ sk_D)
% 0.89/1.13        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 0.89/1.13      inference('demod', [status(thm)], ['98', '99'])).
% 0.89/1.13  thf('101', plain,
% 0.89/1.13      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.89/1.13        | ~ (v2_funct_1 @ sk_D))),
% 0.89/1.13      inference('simplify', [status(thm)], ['100'])).
% 0.89/1.13  thf('102', plain, ((v2_funct_1 @ sk_D)),
% 0.89/1.13      inference('sup-', [status(thm)], ['83', '84'])).
% 0.89/1.13  thf('103', plain,
% 0.89/1.13      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 0.89/1.13      inference('demod', [status(thm)], ['101', '102'])).
% 0.89/1.13  thf('104', plain,
% 0.89/1.13      ((((k6_partfun1 @ (k1_relat_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.89/1.13        | ~ (v1_relat_1 @ sk_D)
% 0.89/1.13        | ~ (v1_funct_1 @ sk_D)
% 0.89/1.13        | ~ (v2_funct_1 @ sk_D))),
% 0.89/1.13      inference('sup+', [status(thm)], ['89', '103'])).
% 0.89/1.13  thf('105', plain, ((v1_relat_1 @ sk_D)),
% 0.89/1.13      inference('sup-', [status(thm)], ['46', '47'])).
% 0.89/1.13  thf('106', plain, ((v1_funct_1 @ sk_D)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('107', plain, ((v2_funct_1 @ sk_D)),
% 0.89/1.13      inference('sup-', [status(thm)], ['83', '84'])).
% 0.89/1.13  thf('108', plain,
% 0.89/1.13      (((k6_partfun1 @ (k1_relat_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 0.89/1.13      inference('demod', [status(thm)], ['104', '105', '106', '107'])).
% 0.89/1.13  thf(t71_relat_1, axiom,
% 0.89/1.13    (![A:$i]:
% 0.89/1.13     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.89/1.13       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.89/1.13  thf('109', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 0.89/1.13      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.89/1.13  thf('110', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.89/1.13      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.89/1.13  thf('111', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 0.89/1.13      inference('demod', [status(thm)], ['109', '110'])).
% 0.89/1.13  thf('112', plain,
% 0.89/1.13      (((k1_relat_1 @ (k6_partfun1 @ sk_B)) = (k1_relat_1 @ sk_D))),
% 0.89/1.13      inference('sup+', [status(thm)], ['108', '111'])).
% 0.89/1.13  thf('113', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 0.89/1.13      inference('demod', [status(thm)], ['109', '110'])).
% 0.89/1.13  thf('114', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.89/1.13      inference('demod', [status(thm)], ['112', '113'])).
% 0.89/1.13  thf('115', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (sk_B)))),
% 0.89/1.13      inference('demod', [status(thm)], ['86', '114'])).
% 0.89/1.13  thf('116', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.89/1.13      inference('simplify', [status(thm)], ['115'])).
% 0.89/1.13  thf('117', plain,
% 0.89/1.13      (![X4 : $i]:
% 0.89/1.13         (~ (v2_funct_1 @ X4)
% 0.89/1.13          | ((k5_relat_1 @ X4 @ (k2_funct_1 @ X4))
% 0.89/1.13              = (k6_partfun1 @ (k1_relat_1 @ X4)))
% 0.89/1.13          | ~ (v1_funct_1 @ X4)
% 0.89/1.13          | ~ (v1_relat_1 @ X4))),
% 0.89/1.13      inference('demod', [status(thm)], ['87', '88'])).
% 0.89/1.13  thf('118', plain,
% 0.89/1.13      (![X5 : $i, X6 : $i]:
% 0.89/1.13         (~ (v1_relat_1 @ X5)
% 0.89/1.13          | ~ (v1_funct_1 @ X5)
% 0.89/1.13          | ((X5) = (k2_funct_1 @ X6))
% 0.89/1.13          | ((k5_relat_1 @ X5 @ X6) != (k6_partfun1 @ (k2_relat_1 @ X6)))
% 0.89/1.13          | ((k2_relat_1 @ X5) != (k1_relat_1 @ X6))
% 0.89/1.13          | ~ (v2_funct_1 @ X6)
% 0.89/1.13          | ~ (v1_funct_1 @ X6)
% 0.89/1.13          | ~ (v1_relat_1 @ X6))),
% 0.89/1.13      inference('demod', [status(thm)], ['26', '27'])).
% 0.89/1.13  thf('119', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (((k6_partfun1 @ (k1_relat_1 @ X0))
% 0.89/1.13            != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.89/1.13          | ~ (v1_relat_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.89/1.13          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0))),
% 0.89/1.13      inference('sup-', [status(thm)], ['117', '118'])).
% 0.89/1.13  thf('120', plain,
% 0.89/1.13      (![X0 : $i]:
% 0.89/1.13         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.89/1.13          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.89/1.13          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.89/1.13          | ~ (v2_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_funct_1 @ X0)
% 0.89/1.13          | ~ (v1_relat_1 @ X0)
% 0.89/1.13          | ((k6_partfun1 @ (k1_relat_1 @ X0))
% 0.89/1.13              != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.89/1.13      inference('simplify', [status(thm)], ['119'])).
% 0.89/1.13  thf('121', plain,
% 0.89/1.13      ((((k6_partfun1 @ (k1_relat_1 @ sk_D))
% 0.89/1.13          != (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 0.89/1.13        | ~ (v1_relat_1 @ sk_D)
% 0.89/1.13        | ~ (v1_funct_1 @ sk_D)
% 0.89/1.13        | ~ (v2_funct_1 @ sk_D)
% 0.89/1.13        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D))
% 0.89/1.13        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 0.89/1.13        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_D))
% 0.89/1.13        | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ (k2_funct_1 @ sk_D)))
% 0.89/1.13        | ((sk_D) = (k2_funct_1 @ (k2_funct_1 @ sk_D))))),
% 0.89/1.13      inference('sup-', [status(thm)], ['116', '120'])).
% 0.89/1.13  thf('122', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.89/1.13      inference('demod', [status(thm)], ['112', '113'])).
% 0.89/1.13  thf('123', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.89/1.13      inference('sup+', [status(thm)], ['52', '53'])).
% 0.89/1.13  thf('124', plain, ((v1_relat_1 @ sk_D)),
% 0.89/1.13      inference('sup-', [status(thm)], ['46', '47'])).
% 0.89/1.13  thf('125', plain, ((v1_funct_1 @ sk_D)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('126', plain, ((v2_funct_1 @ sk_D)),
% 0.89/1.13      inference('sup-', [status(thm)], ['83', '84'])).
% 0.89/1.13  thf('127', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.89/1.13      inference('simplify', [status(thm)], ['115'])).
% 0.89/1.13  thf('128', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.13      inference('sup-', [status(thm)], ['56', '57'])).
% 0.89/1.13  thf('129', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.89/1.13      inference('simplify', [status(thm)], ['115'])).
% 0.89/1.13  thf('130', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('131', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.89/1.13      inference('simplify', [status(thm)], ['115'])).
% 0.89/1.13  thf('132', plain, ((v2_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('133', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.89/1.13      inference('demod', [status(thm)], ['37', '38', '41', '42', '43', '44'])).
% 0.89/1.13  thf('134', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.89/1.13      inference('simplify', [status(thm)], ['115'])).
% 0.89/1.13  thf('135', plain,
% 0.89/1.13      (![X4 : $i]:
% 0.89/1.13         (~ (v2_funct_1 @ X4)
% 0.89/1.13          | ((k5_relat_1 @ X4 @ (k2_funct_1 @ X4))
% 0.89/1.13              = (k6_partfun1 @ (k1_relat_1 @ X4)))
% 0.89/1.13          | ~ (v1_funct_1 @ X4)
% 0.89/1.13          | ~ (v1_relat_1 @ X4))),
% 0.89/1.13      inference('demod', [status(thm)], ['87', '88'])).
% 0.89/1.13  thf('136', plain,
% 0.89/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('137', plain,
% 0.89/1.13      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.89/1.13         (((X45) = (k1_xboole_0))
% 0.89/1.13          | ~ (v1_funct_1 @ X46)
% 0.89/1.13          | ~ (v1_funct_2 @ X46 @ X47 @ X45)
% 0.89/1.13          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X45)))
% 0.89/1.13          | ((k5_relat_1 @ X46 @ (k2_funct_1 @ X46)) = (k6_partfun1 @ X47))
% 0.89/1.13          | ~ (v2_funct_1 @ X46)
% 0.89/1.13          | ((k2_relset_1 @ X47 @ X45 @ X46) != (X45)))),
% 0.89/1.13      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.89/1.13  thf('138', plain,
% 0.89/1.13      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.89/1.13        | ~ (v2_funct_1 @ sk_C)
% 0.89/1.13        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.89/1.13        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.89/1.13        | ~ (v1_funct_1 @ sk_C)
% 0.89/1.13        | ((sk_B) = (k1_xboole_0)))),
% 0.89/1.13      inference('sup-', [status(thm)], ['136', '137'])).
% 0.89/1.13  thf('139', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('140', plain, ((v2_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('141', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('142', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('143', plain,
% 0.89/1.13      ((((sk_B) != (sk_B))
% 0.89/1.13        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.89/1.13        | ((sk_B) = (k1_xboole_0)))),
% 0.89/1.13      inference('demod', [status(thm)], ['138', '139', '140', '141', '142'])).
% 0.89/1.13  thf('144', plain,
% 0.89/1.13      ((((sk_B) = (k1_xboole_0))
% 0.89/1.13        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 0.89/1.13      inference('simplify', [status(thm)], ['143'])).
% 0.89/1.13  thf('145', plain, (((sk_B) != (k1_xboole_0))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('146', plain,
% 0.89/1.13      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 0.89/1.13      inference('simplify_reflect-', [status(thm)], ['144', '145'])).
% 0.89/1.13  thf('147', plain,
% 0.89/1.13      ((((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.89/1.13        | ~ (v1_relat_1 @ sk_C)
% 0.89/1.13        | ~ (v1_funct_1 @ sk_C)
% 0.89/1.13        | ~ (v2_funct_1 @ sk_C))),
% 0.89/1.13      inference('sup+', [status(thm)], ['135', '146'])).
% 0.89/1.13  thf('148', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.13      inference('sup-', [status(thm)], ['56', '57'])).
% 0.89/1.13  thf('149', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('150', plain, ((v2_funct_1 @ sk_C)),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('151', plain,
% 0.89/1.13      (((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 0.89/1.13      inference('demod', [status(thm)], ['147', '148', '149', '150'])).
% 0.89/1.13  thf('152', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 0.89/1.13      inference('demod', [status(thm)], ['109', '110'])).
% 0.89/1.13  thf('153', plain,
% 0.89/1.13      (((k1_relat_1 @ (k6_partfun1 @ sk_A)) = (k1_relat_1 @ sk_C))),
% 0.89/1.13      inference('sup+', [status(thm)], ['151', '152'])).
% 0.89/1.13  thf('154', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 0.89/1.13      inference('demod', [status(thm)], ['109', '110'])).
% 0.89/1.13  thf('155', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.89/1.13      inference('demod', [status(thm)], ['153', '154'])).
% 0.89/1.13  thf('156', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 0.89/1.13      inference('simplify', [status(thm)], ['115'])).
% 0.89/1.13  thf('157', plain,
% 0.89/1.13      ((((k6_partfun1 @ sk_B) != (k6_partfun1 @ sk_B))
% 0.89/1.13        | ((sk_A) != (sk_A))
% 0.89/1.13        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 0.89/1.13      inference('demod', [status(thm)],
% 0.89/1.13                ['121', '122', '123', '124', '125', '126', '127', '128', 
% 0.89/1.13                 '129', '130', '131', '132', '133', '134', '155', '156'])).
% 0.89/1.13  thf('158', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 0.89/1.13      inference('simplify', [status(thm)], ['157'])).
% 0.89/1.13  thf('159', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.89/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.13  thf('160', plain, ($false),
% 0.89/1.13      inference('simplify_reflect-', [status(thm)], ['158', '159'])).
% 0.89/1.13  
% 0.89/1.13  % SZS output end Refutation
% 0.89/1.13  
% 0.89/1.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

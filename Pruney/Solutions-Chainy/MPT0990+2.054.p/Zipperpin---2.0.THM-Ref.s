%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m6MbUT1s8T

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:02 EST 2020

% Result     : Theorem 0.82s
% Output     : Refutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 274 expanded)
%              Number of leaves         :   41 ( 100 expanded)
%              Depth                    :   15
%              Number of atoms          : 1362 (6652 expanded)
%              Number of equality atoms :   92 ( 478 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 )
        = ( k5_relat_1 @ X28 @ X31 ) ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X27 ) ) ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ( X9 = X12 )
      | ~ ( r2_relset_1 @ X10 @ X11 @ X9 @ X12 ) ) ),
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

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('24',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('25',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('26',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

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

thf('28',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X1
        = ( k2_funct_1 @ X2 ) )
      | ( ( k5_relat_1 @ X2 @ X1 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X2 ) ) )
      | ( ( k2_relat_1 @ X2 )
       != ( k1_relat_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t63_funct_1])).

thf('29',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('30',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X1
        = ( k2_funct_1 @ X2 ) )
      | ( ( k5_relat_1 @ X2 @ X1 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X2 ) ) )
      | ( ( k2_relat_1 @ X2 )
       != ( k1_relat_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
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
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
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

thf('33',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_2 @ X18 @ X16 @ X17 )
      | ( X16
        = ( k1_relset_1 @ X16 @ X17 @ X18 ) )
      | ~ ( zip_tseitin_1 @ X18 @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('34',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('35',plain,(
    ! [X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('37',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( zip_tseitin_0 @ X19 @ X20 )
      | ( zip_tseitin_1 @ X21 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('38',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('43',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k1_relset_1 @ X7 @ X8 @ X6 )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('44',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['34','41','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('47',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('48',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('52',plain,(
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

thf('53',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v2_funct_1 @ X35 )
      | ( ( k2_relset_1 @ X37 @ X36 @ X35 )
       != X36 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X37 @ X36 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('54',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['54','55','56','57','58'])).

thf('60',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k1_relset_1 @ X7 @ X8 @ X6 )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('62',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v2_funct_1 @ X35 )
      | ( ( k2_relset_1 @ X37 @ X36 @ X35 )
       != X36 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X35 ) @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X37 @ X36 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('65',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['65','66','67','68','69'])).

thf('71',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_2 @ X18 @ X16 @ X17 )
      | ( X16
        = ( k1_relset_1 @ X16 @ X17 @ X18 ) )
      | ~ ( zip_tseitin_1 @ X18 @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('73',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('75',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('76',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( zip_tseitin_0 @ X19 @ X20 )
      | ( zip_tseitin_1 @ X21 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('77',plain,
    ( ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['78','79'])).

thf('81',plain,
    ( sk_B
    = ( k1_relset_1 @ sk_B @ sk_A @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['73','80'])).

thf('82',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['62','81'])).

thf('83',plain,
    ( ( sk_B
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['51','82'])).

thf('84',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['46','47'])).

thf('85',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['83','84','85','86'])).

thf('88',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_2 @ X18 @ X16 @ X17 )
      | ( X16
        = ( k1_relset_1 @ X16 @ X17 @ X18 ) )
      | ~ ( zip_tseitin_1 @ X18 @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('90',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('92',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( zip_tseitin_0 @ X19 @ X20 )
      | ( zip_tseitin_1 @ X21 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('94',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('96',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['95','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k1_relset_1 @ X7 @ X8 @ X6 )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('100',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['90','97','100'])).

thf('102',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('105',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ( sk_B != sk_B )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['31','45','48','49','50','87','101','102','105'])).

thf('107',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['107','108'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m6MbUT1s8T
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:18:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.82/1.06  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.82/1.06  % Solved by: fo/fo7.sh
% 0.82/1.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.82/1.06  % done 349 iterations in 0.605s
% 0.82/1.06  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.82/1.06  % SZS output start Refutation
% 0.82/1.06  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.82/1.06  thf(sk_D_type, type, sk_D: $i).
% 0.82/1.06  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.82/1.06  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.82/1.06  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.82/1.06  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.82/1.06  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.82/1.06  thf(sk_C_type, type, sk_C: $i).
% 0.82/1.06  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.82/1.06  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.82/1.06  thf(sk_B_type, type, sk_B: $i).
% 0.82/1.06  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.82/1.06  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.82/1.06  thf(sk_A_type, type, sk_A: $i).
% 0.82/1.06  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.82/1.06  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.82/1.06  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.82/1.06  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.82/1.06  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.82/1.06  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.82/1.06  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.82/1.06  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.82/1.06  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.82/1.06  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.82/1.06  thf(t36_funct_2, conjecture,
% 0.82/1.06    (![A:$i,B:$i,C:$i]:
% 0.82/1.06     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.82/1.06         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.82/1.06       ( ![D:$i]:
% 0.82/1.06         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.82/1.06             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.82/1.06           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.82/1.06               ( r2_relset_1 @
% 0.82/1.06                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.82/1.06                 ( k6_partfun1 @ A ) ) & 
% 0.82/1.06               ( v2_funct_1 @ C ) ) =>
% 0.82/1.06             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.82/1.06               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.82/1.06  thf(zf_stmt_0, negated_conjecture,
% 0.82/1.06    (~( ![A:$i,B:$i,C:$i]:
% 0.82/1.06        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.82/1.06            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.82/1.06          ( ![D:$i]:
% 0.82/1.06            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.82/1.06                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.82/1.06              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.82/1.06                  ( r2_relset_1 @
% 0.82/1.06                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.82/1.06                    ( k6_partfun1 @ A ) ) & 
% 0.82/1.06                  ( v2_funct_1 @ C ) ) =>
% 0.82/1.06                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.82/1.06                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.82/1.06    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.82/1.06  thf('0', plain,
% 0.82/1.06      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.82/1.06        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.82/1.06        (k6_partfun1 @ sk_A))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('1', plain,
% 0.82/1.06      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('2', plain,
% 0.82/1.06      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf(redefinition_k1_partfun1, axiom,
% 0.82/1.06    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.82/1.06     ( ( ( v1_funct_1 @ E ) & 
% 0.82/1.06         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.82/1.06         ( v1_funct_1 @ F ) & 
% 0.82/1.06         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.82/1.06       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.82/1.06  thf('3', plain,
% 0.82/1.06      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.82/1.06         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.82/1.06          | ~ (v1_funct_1 @ X28)
% 0.82/1.06          | ~ (v1_funct_1 @ X31)
% 0.82/1.06          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.82/1.06          | ((k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31)
% 0.82/1.06              = (k5_relat_1 @ X28 @ X31)))),
% 0.82/1.06      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.82/1.06  thf('4', plain,
% 0.82/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.06         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.82/1.06            = (k5_relat_1 @ sk_C @ X0))
% 0.82/1.06          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.82/1.06          | ~ (v1_funct_1 @ X0)
% 0.82/1.06          | ~ (v1_funct_1 @ sk_C))),
% 0.82/1.06      inference('sup-', [status(thm)], ['2', '3'])).
% 0.82/1.06  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('6', plain,
% 0.82/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.06         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.82/1.06            = (k5_relat_1 @ sk_C @ X0))
% 0.82/1.06          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.82/1.06          | ~ (v1_funct_1 @ X0))),
% 0.82/1.06      inference('demod', [status(thm)], ['4', '5'])).
% 0.82/1.06  thf('7', plain,
% 0.82/1.06      ((~ (v1_funct_1 @ sk_D)
% 0.82/1.06        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.82/1.06            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.82/1.06      inference('sup-', [status(thm)], ['1', '6'])).
% 0.82/1.06  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('9', plain,
% 0.82/1.06      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.82/1.06         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.82/1.06      inference('demod', [status(thm)], ['7', '8'])).
% 0.82/1.06  thf('10', plain,
% 0.82/1.06      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.82/1.06        (k6_partfun1 @ sk_A))),
% 0.82/1.06      inference('demod', [status(thm)], ['0', '9'])).
% 0.82/1.06  thf('11', plain,
% 0.82/1.06      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('12', plain,
% 0.82/1.06      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf(dt_k1_partfun1, axiom,
% 0.82/1.06    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.82/1.06     ( ( ( v1_funct_1 @ E ) & 
% 0.82/1.06         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.82/1.06         ( v1_funct_1 @ F ) & 
% 0.82/1.06         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.82/1.06       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.82/1.06         ( m1_subset_1 @
% 0.82/1.06           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.82/1.06           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.82/1.06  thf('13', plain,
% 0.82/1.06      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.82/1.06         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.82/1.06          | ~ (v1_funct_1 @ X22)
% 0.82/1.06          | ~ (v1_funct_1 @ X25)
% 0.82/1.06          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.82/1.06          | (m1_subset_1 @ (k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25) @ 
% 0.82/1.06             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X27))))),
% 0.82/1.06      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.82/1.06  thf('14', plain,
% 0.82/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.06         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.82/1.06           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.82/1.06          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.82/1.06          | ~ (v1_funct_1 @ X1)
% 0.82/1.06          | ~ (v1_funct_1 @ sk_C))),
% 0.82/1.06      inference('sup-', [status(thm)], ['12', '13'])).
% 0.82/1.06  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('16', plain,
% 0.82/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.06         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.82/1.06           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.82/1.06          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.82/1.06          | ~ (v1_funct_1 @ X1))),
% 0.82/1.06      inference('demod', [status(thm)], ['14', '15'])).
% 0.82/1.06  thf('17', plain,
% 0.82/1.06      ((~ (v1_funct_1 @ sk_D)
% 0.82/1.06        | (m1_subset_1 @ 
% 0.82/1.06           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.82/1.06           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.82/1.06      inference('sup-', [status(thm)], ['11', '16'])).
% 0.82/1.06  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('19', plain,
% 0.82/1.06      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.82/1.06         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.82/1.06      inference('demod', [status(thm)], ['7', '8'])).
% 0.82/1.06  thf('20', plain,
% 0.82/1.06      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.82/1.06        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.82/1.06      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.82/1.06  thf(redefinition_r2_relset_1, axiom,
% 0.82/1.06    (![A:$i,B:$i,C:$i,D:$i]:
% 0.82/1.06     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.82/1.06         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.82/1.06       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.82/1.06  thf('21', plain,
% 0.82/1.06      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.82/1.06         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.82/1.06          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.82/1.06          | ((X9) = (X12))
% 0.82/1.06          | ~ (r2_relset_1 @ X10 @ X11 @ X9 @ X12))),
% 0.82/1.06      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.82/1.06  thf('22', plain,
% 0.82/1.06      (![X0 : $i]:
% 0.82/1.06         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 0.82/1.06          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 0.82/1.06          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.82/1.06      inference('sup-', [status(thm)], ['20', '21'])).
% 0.82/1.06  thf('23', plain,
% 0.82/1.06      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.82/1.06           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.82/1.06        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 0.82/1.06      inference('sup-', [status(thm)], ['10', '22'])).
% 0.82/1.06  thf(t29_relset_1, axiom,
% 0.82/1.06    (![A:$i]:
% 0.82/1.06     ( m1_subset_1 @
% 0.82/1.06       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.82/1.06  thf('24', plain,
% 0.82/1.06      (![X13 : $i]:
% 0.82/1.06         (m1_subset_1 @ (k6_relat_1 @ X13) @ 
% 0.82/1.06          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X13)))),
% 0.82/1.06      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.82/1.06  thf(redefinition_k6_partfun1, axiom,
% 0.82/1.06    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.82/1.06  thf('25', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 0.82/1.06      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.82/1.06  thf('26', plain,
% 0.82/1.06      (![X13 : $i]:
% 0.82/1.06         (m1_subset_1 @ (k6_partfun1 @ X13) @ 
% 0.82/1.06          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X13)))),
% 0.82/1.06      inference('demod', [status(thm)], ['24', '25'])).
% 0.82/1.06  thf('27', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.82/1.06      inference('demod', [status(thm)], ['23', '26'])).
% 0.82/1.06  thf(t63_funct_1, axiom,
% 0.82/1.06    (![A:$i]:
% 0.82/1.06     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.82/1.06       ( ![B:$i]:
% 0.82/1.06         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.82/1.06           ( ( ( v2_funct_1 @ A ) & 
% 0.82/1.06               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.82/1.06               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.82/1.06             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.82/1.06  thf('28', plain,
% 0.82/1.06      (![X1 : $i, X2 : $i]:
% 0.82/1.06         (~ (v1_relat_1 @ X1)
% 0.82/1.06          | ~ (v1_funct_1 @ X1)
% 0.82/1.06          | ((X1) = (k2_funct_1 @ X2))
% 0.82/1.06          | ((k5_relat_1 @ X2 @ X1) != (k6_relat_1 @ (k1_relat_1 @ X2)))
% 0.82/1.06          | ((k2_relat_1 @ X2) != (k1_relat_1 @ X1))
% 0.82/1.06          | ~ (v2_funct_1 @ X2)
% 0.82/1.06          | ~ (v1_funct_1 @ X2)
% 0.82/1.06          | ~ (v1_relat_1 @ X2))),
% 0.82/1.06      inference('cnf', [status(esa)], [t63_funct_1])).
% 0.82/1.06  thf('29', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 0.82/1.06      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.82/1.06  thf('30', plain,
% 0.82/1.06      (![X1 : $i, X2 : $i]:
% 0.82/1.06         (~ (v1_relat_1 @ X1)
% 0.82/1.06          | ~ (v1_funct_1 @ X1)
% 0.82/1.06          | ((X1) = (k2_funct_1 @ X2))
% 0.82/1.06          | ((k5_relat_1 @ X2 @ X1) != (k6_partfun1 @ (k1_relat_1 @ X2)))
% 0.82/1.06          | ((k2_relat_1 @ X2) != (k1_relat_1 @ X1))
% 0.82/1.06          | ~ (v2_funct_1 @ X2)
% 0.82/1.06          | ~ (v1_funct_1 @ X2)
% 0.82/1.06          | ~ (v1_relat_1 @ X2))),
% 0.82/1.06      inference('demod', [status(thm)], ['28', '29'])).
% 0.82/1.06  thf('31', plain,
% 0.82/1.06      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 0.82/1.06        | ~ (v1_relat_1 @ sk_C)
% 0.82/1.06        | ~ (v1_funct_1 @ sk_C)
% 0.82/1.06        | ~ (v2_funct_1 @ sk_C)
% 0.82/1.06        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.82/1.06        | ((sk_D) = (k2_funct_1 @ sk_C))
% 0.82/1.06        | ~ (v1_funct_1 @ sk_D)
% 0.82/1.06        | ~ (v1_relat_1 @ sk_D))),
% 0.82/1.06      inference('sup-', [status(thm)], ['27', '30'])).
% 0.82/1.06  thf('32', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf(d1_funct_2, axiom,
% 0.82/1.06    (![A:$i,B:$i,C:$i]:
% 0.82/1.06     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.82/1.06       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.82/1.06           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.82/1.06             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.82/1.06         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.82/1.06           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.82/1.06             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.82/1.06  thf(zf_stmt_1, axiom,
% 0.82/1.06    (![C:$i,B:$i,A:$i]:
% 0.82/1.06     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.82/1.06       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.82/1.06  thf('33', plain,
% 0.82/1.06      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.82/1.06         (~ (v1_funct_2 @ X18 @ X16 @ X17)
% 0.82/1.06          | ((X16) = (k1_relset_1 @ X16 @ X17 @ X18))
% 0.82/1.06          | ~ (zip_tseitin_1 @ X18 @ X17 @ X16))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.82/1.06  thf('34', plain,
% 0.82/1.06      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.82/1.06        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.82/1.06      inference('sup-', [status(thm)], ['32', '33'])).
% 0.82/1.06  thf(zf_stmt_2, axiom,
% 0.82/1.06    (![B:$i,A:$i]:
% 0.82/1.06     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.82/1.06       ( zip_tseitin_0 @ B @ A ) ))).
% 0.82/1.06  thf('35', plain,
% 0.82/1.06      (![X14 : $i, X15 : $i]:
% 0.82/1.06         ((zip_tseitin_0 @ X14 @ X15) | ((X14) = (k1_xboole_0)))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.82/1.06  thf('36', plain,
% 0.82/1.06      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.82/1.06  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.82/1.06  thf(zf_stmt_5, axiom,
% 0.82/1.06    (![A:$i,B:$i,C:$i]:
% 0.82/1.06     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.82/1.06       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.82/1.06         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.82/1.06           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.82/1.06             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.82/1.06  thf('37', plain,
% 0.82/1.06      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.82/1.06         (~ (zip_tseitin_0 @ X19 @ X20)
% 0.82/1.06          | (zip_tseitin_1 @ X21 @ X19 @ X20)
% 0.82/1.06          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19))))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.82/1.06  thf('38', plain,
% 0.82/1.06      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.82/1.06      inference('sup-', [status(thm)], ['36', '37'])).
% 0.82/1.06  thf('39', plain,
% 0.82/1.06      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.82/1.06      inference('sup-', [status(thm)], ['35', '38'])).
% 0.82/1.06  thf('40', plain, (((sk_B) != (k1_xboole_0))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('41', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.82/1.06      inference('simplify_reflect-', [status(thm)], ['39', '40'])).
% 0.82/1.06  thf('42', plain,
% 0.82/1.06      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf(redefinition_k1_relset_1, axiom,
% 0.82/1.06    (![A:$i,B:$i,C:$i]:
% 0.82/1.06     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.82/1.06       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.82/1.06  thf('43', plain,
% 0.82/1.06      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.82/1.06         (((k1_relset_1 @ X7 @ X8 @ X6) = (k1_relat_1 @ X6))
% 0.82/1.06          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.82/1.06      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.82/1.06  thf('44', plain,
% 0.82/1.06      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.82/1.06      inference('sup-', [status(thm)], ['42', '43'])).
% 0.82/1.06  thf('45', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.82/1.06      inference('demod', [status(thm)], ['34', '41', '44'])).
% 0.82/1.06  thf('46', plain,
% 0.82/1.06      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf(cc1_relset_1, axiom,
% 0.82/1.06    (![A:$i,B:$i,C:$i]:
% 0.82/1.06     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.82/1.06       ( v1_relat_1 @ C ) ))).
% 0.82/1.06  thf('47', plain,
% 0.82/1.06      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.82/1.06         ((v1_relat_1 @ X3)
% 0.82/1.06          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.82/1.06      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.82/1.06  thf('48', plain, ((v1_relat_1 @ sk_C)),
% 0.82/1.06      inference('sup-', [status(thm)], ['46', '47'])).
% 0.82/1.06  thf('49', plain, ((v1_funct_1 @ sk_C)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('50', plain, ((v2_funct_1 @ sk_C)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf(t55_funct_1, axiom,
% 0.82/1.06    (![A:$i]:
% 0.82/1.06     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.82/1.06       ( ( v2_funct_1 @ A ) =>
% 0.82/1.06         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.82/1.06           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.82/1.06  thf('51', plain,
% 0.82/1.06      (![X0 : $i]:
% 0.82/1.06         (~ (v2_funct_1 @ X0)
% 0.82/1.06          | ((k2_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.82/1.06          | ~ (v1_funct_1 @ X0)
% 0.82/1.06          | ~ (v1_relat_1 @ X0))),
% 0.82/1.06      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.82/1.06  thf('52', plain,
% 0.82/1.06      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf(t31_funct_2, axiom,
% 0.82/1.06    (![A:$i,B:$i,C:$i]:
% 0.82/1.06     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.82/1.06         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.82/1.06       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.82/1.06         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.82/1.06           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.82/1.06           ( m1_subset_1 @
% 0.82/1.06             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.82/1.06  thf('53', plain,
% 0.82/1.06      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.82/1.06         (~ (v2_funct_1 @ X35)
% 0.82/1.06          | ((k2_relset_1 @ X37 @ X36 @ X35) != (X36))
% 0.82/1.06          | (m1_subset_1 @ (k2_funct_1 @ X35) @ 
% 0.82/1.06             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.82/1.06          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 0.82/1.06          | ~ (v1_funct_2 @ X35 @ X37 @ X36)
% 0.82/1.06          | ~ (v1_funct_1 @ X35))),
% 0.82/1.06      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.82/1.06  thf('54', plain,
% 0.82/1.06      ((~ (v1_funct_1 @ sk_C)
% 0.82/1.06        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.82/1.06        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.82/1.06           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.82/1.06        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.82/1.06        | ~ (v2_funct_1 @ sk_C))),
% 0.82/1.06      inference('sup-', [status(thm)], ['52', '53'])).
% 0.82/1.06  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('56', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('57', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('58', plain, ((v2_funct_1 @ sk_C)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('59', plain,
% 0.82/1.06      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.82/1.06         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.82/1.06        | ((sk_B) != (sk_B)))),
% 0.82/1.06      inference('demod', [status(thm)], ['54', '55', '56', '57', '58'])).
% 0.82/1.06  thf('60', plain,
% 0.82/1.06      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.82/1.06        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.82/1.06      inference('simplify', [status(thm)], ['59'])).
% 0.82/1.06  thf('61', plain,
% 0.82/1.06      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.82/1.06         (((k1_relset_1 @ X7 @ X8 @ X6) = (k1_relat_1 @ X6))
% 0.82/1.06          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.82/1.06      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.82/1.06  thf('62', plain,
% 0.82/1.06      (((k1_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C))
% 0.82/1.06         = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.82/1.06      inference('sup-', [status(thm)], ['60', '61'])).
% 0.82/1.06  thf('63', plain,
% 0.82/1.06      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('64', plain,
% 0.82/1.06      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.82/1.06         (~ (v2_funct_1 @ X35)
% 0.82/1.06          | ((k2_relset_1 @ X37 @ X36 @ X35) != (X36))
% 0.82/1.06          | (v1_funct_2 @ (k2_funct_1 @ X35) @ X36 @ X37)
% 0.82/1.06          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 0.82/1.06          | ~ (v1_funct_2 @ X35 @ X37 @ X36)
% 0.82/1.06          | ~ (v1_funct_1 @ X35))),
% 0.82/1.06      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.82/1.06  thf('65', plain,
% 0.82/1.06      ((~ (v1_funct_1 @ sk_C)
% 0.82/1.06        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.82/1.06        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.82/1.06        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.82/1.06        | ~ (v2_funct_1 @ sk_C))),
% 0.82/1.06      inference('sup-', [status(thm)], ['63', '64'])).
% 0.82/1.06  thf('66', plain, ((v1_funct_1 @ sk_C)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('67', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('68', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('69', plain, ((v2_funct_1 @ sk_C)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('70', plain,
% 0.82/1.06      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A) | ((sk_B) != (sk_B)))),
% 0.82/1.06      inference('demod', [status(thm)], ['65', '66', '67', '68', '69'])).
% 0.82/1.06  thf('71', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 0.82/1.06      inference('simplify', [status(thm)], ['70'])).
% 0.82/1.06  thf('72', plain,
% 0.82/1.06      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.82/1.06         (~ (v1_funct_2 @ X18 @ X16 @ X17)
% 0.82/1.06          | ((X16) = (k1_relset_1 @ X16 @ X17 @ X18))
% 0.82/1.06          | ~ (zip_tseitin_1 @ X18 @ X17 @ X16))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.82/1.06  thf('73', plain,
% 0.82/1.06      ((~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_B)
% 0.82/1.06        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C))))),
% 0.82/1.06      inference('sup-', [status(thm)], ['71', '72'])).
% 0.82/1.06  thf('74', plain,
% 0.82/1.06      (![X14 : $i, X15 : $i]:
% 0.82/1.06         ((zip_tseitin_0 @ X14 @ X15) | ((X14) = (k1_xboole_0)))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.82/1.06  thf('75', plain,
% 0.82/1.06      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.82/1.06        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.82/1.06      inference('simplify', [status(thm)], ['59'])).
% 0.82/1.06  thf('76', plain,
% 0.82/1.06      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.82/1.06         (~ (zip_tseitin_0 @ X19 @ X20)
% 0.82/1.06          | (zip_tseitin_1 @ X21 @ X19 @ X20)
% 0.82/1.06          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19))))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.82/1.06  thf('77', plain,
% 0.82/1.06      (((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_B)
% 0.82/1.06        | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 0.82/1.06      inference('sup-', [status(thm)], ['75', '76'])).
% 0.82/1.06  thf('78', plain,
% 0.82/1.06      ((((sk_A) = (k1_xboole_0))
% 0.82/1.06        | (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_B))),
% 0.82/1.06      inference('sup-', [status(thm)], ['74', '77'])).
% 0.82/1.06  thf('79', plain, (((sk_A) != (k1_xboole_0))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('80', plain, ((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_B)),
% 0.82/1.06      inference('simplify_reflect-', [status(thm)], ['78', '79'])).
% 0.82/1.06  thf('81', plain,
% 0.82/1.06      (((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ (k2_funct_1 @ sk_C)))),
% 0.82/1.06      inference('demod', [status(thm)], ['73', '80'])).
% 0.82/1.06  thf('82', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.82/1.06      inference('sup+', [status(thm)], ['62', '81'])).
% 0.82/1.06  thf('83', plain,
% 0.82/1.06      ((((sk_B) = (k2_relat_1 @ sk_C))
% 0.82/1.06        | ~ (v1_relat_1 @ sk_C)
% 0.82/1.06        | ~ (v1_funct_1 @ sk_C)
% 0.82/1.06        | ~ (v2_funct_1 @ sk_C))),
% 0.82/1.06      inference('sup+', [status(thm)], ['51', '82'])).
% 0.82/1.06  thf('84', plain, ((v1_relat_1 @ sk_C)),
% 0.82/1.06      inference('sup-', [status(thm)], ['46', '47'])).
% 0.82/1.06  thf('85', plain, ((v1_funct_1 @ sk_C)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('86', plain, ((v2_funct_1 @ sk_C)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('87', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 0.82/1.06      inference('demod', [status(thm)], ['83', '84', '85', '86'])).
% 0.82/1.06  thf('88', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('89', plain,
% 0.82/1.06      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.82/1.06         (~ (v1_funct_2 @ X18 @ X16 @ X17)
% 0.82/1.06          | ((X16) = (k1_relset_1 @ X16 @ X17 @ X18))
% 0.82/1.06          | ~ (zip_tseitin_1 @ X18 @ X17 @ X16))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.82/1.06  thf('90', plain,
% 0.82/1.06      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 0.82/1.06        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 0.82/1.06      inference('sup-', [status(thm)], ['88', '89'])).
% 0.82/1.06  thf('91', plain,
% 0.82/1.06      (![X14 : $i, X15 : $i]:
% 0.82/1.06         ((zip_tseitin_0 @ X14 @ X15) | ((X14) = (k1_xboole_0)))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.82/1.06  thf('92', plain,
% 0.82/1.06      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('93', plain,
% 0.82/1.06      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.82/1.06         (~ (zip_tseitin_0 @ X19 @ X20)
% 0.82/1.06          | (zip_tseitin_1 @ X21 @ X19 @ X20)
% 0.82/1.06          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19))))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.82/1.06  thf('94', plain,
% 0.82/1.06      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 0.82/1.06      inference('sup-', [status(thm)], ['92', '93'])).
% 0.82/1.06  thf('95', plain,
% 0.82/1.06      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 0.82/1.06      inference('sup-', [status(thm)], ['91', '94'])).
% 0.82/1.06  thf('96', plain, (((sk_A) != (k1_xboole_0))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('97', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 0.82/1.06      inference('simplify_reflect-', [status(thm)], ['95', '96'])).
% 0.82/1.06  thf('98', plain,
% 0.82/1.06      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('99', plain,
% 0.82/1.06      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.82/1.06         (((k1_relset_1 @ X7 @ X8 @ X6) = (k1_relat_1 @ X6))
% 0.82/1.06          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.82/1.06      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.82/1.06  thf('100', plain,
% 0.82/1.06      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.82/1.06      inference('sup-', [status(thm)], ['98', '99'])).
% 0.82/1.06  thf('101', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.82/1.06      inference('demod', [status(thm)], ['90', '97', '100'])).
% 0.82/1.06  thf('102', plain, ((v1_funct_1 @ sk_D)),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('103', plain,
% 0.82/1.06      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('104', plain,
% 0.82/1.06      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.82/1.06         ((v1_relat_1 @ X3)
% 0.82/1.06          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.82/1.06      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.82/1.06  thf('105', plain, ((v1_relat_1 @ sk_D)),
% 0.82/1.06      inference('sup-', [status(thm)], ['103', '104'])).
% 0.82/1.06  thf('106', plain,
% 0.82/1.06      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 0.82/1.06        | ((sk_B) != (sk_B))
% 0.82/1.06        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 0.82/1.06      inference('demod', [status(thm)],
% 0.82/1.06                ['31', '45', '48', '49', '50', '87', '101', '102', '105'])).
% 0.82/1.06  thf('107', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 0.82/1.06      inference('simplify', [status(thm)], ['106'])).
% 0.82/1.06  thf('108', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.82/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.06  thf('109', plain, ($false),
% 0.82/1.06      inference('simplify_reflect-', [status(thm)], ['107', '108'])).
% 0.82/1.06  
% 0.82/1.06  % SZS output end Refutation
% 0.82/1.06  
% 0.82/1.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
